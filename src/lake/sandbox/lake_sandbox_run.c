/*
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
*/

/*
lake-sandbox-run [--reap] DIR -- COMMAND [ARG...]

Runs COMMAND with Landlock confining its writes to DIR (and `/dev/null`). Reads are unrestricted.

With `--reap`, the runner stays as COMMAND's parent and a child subreaper: once COMMAND exits, it
kills every remaining descendant, so no process COMMAND started outlives it. It only ever signals
its own children, never a process group or `-1`.

Exits with COMMAND's status (128 + signal if COMMAND was killed). Fails with status 125, without
running COMMAND, if Landlock with ABI version 3 or later (which restricts truncation) is not
available, if DIR cannot be opened, or, with `--reap`, if the runner cannot list its children.
*/

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

/* Defined here rather than taken from `<linux/landlock.h>`, which older build hosts lack. */
#ifndef __NR_landlock_create_ruleset
#define __NR_landlock_create_ruleset 444
#endif
#ifndef __NR_landlock_add_rule
#define __NR_landlock_add_rule 445
#endif
#ifndef __NR_landlock_restrict_self
#define __NR_landlock_restrict_self 446
#endif
#ifndef PR_SET_CHILD_SUBREAPER
#define PR_SET_CHILD_SUBREAPER 36
#endif

#define LL_CREATE_RULESET_VERSION (1U << 0)
#define LL_RULE_PATH_BENEATH 1

#define LL_FS_WRITE_FILE (1ULL << 1)
#define LL_FS_REMOVE_DIR (1ULL << 4)
#define LL_FS_REMOVE_FILE (1ULL << 5)
#define LL_FS_MAKE_CHAR (1ULL << 6)
#define LL_FS_MAKE_DIR (1ULL << 7)
#define LL_FS_MAKE_REG (1ULL << 8)
#define LL_FS_MAKE_SOCK (1ULL << 9)
#define LL_FS_MAKE_FIFO (1ULL << 10)
#define LL_FS_MAKE_BLOCK (1ULL << 11)
#define LL_FS_MAKE_SYM (1ULL << 12)
#define LL_FS_REFER (1ULL << 13)    /* ABI 2 */
#define LL_FS_TRUNCATE (1ULL << 14) /* ABI 3 */

/*
Every right that changes the file system. Landlock permits any right a ruleset does not handle, so a
write right missing here is silently allowed everywhere.
*/
#define LL_FS_WRITES                                                                           \
  (LL_FS_WRITE_FILE | LL_FS_REMOVE_DIR | LL_FS_REMOVE_FILE | LL_FS_MAKE_CHAR | LL_FS_MAKE_DIR | \
   LL_FS_MAKE_REG | LL_FS_MAKE_SOCK | LL_FS_MAKE_FIFO | LL_FS_MAKE_BLOCK | LL_FS_MAKE_SYM |     \
   LL_FS_REFER | LL_FS_TRUNCATE)

#define MIN_ABI 3
#define EXIT_SETUP 125

struct ll_ruleset_attr {
  uint64_t handled_access_fs;
};

struct ll_path_beneath_attr {
  uint64_t allowed_access;
  int32_t parent_fd;
} __attribute__((packed));

static const char *prog = "lake-sandbox-run";

static void fail(const char *what) {
  fprintf(stderr, "%s: %s: %s\n", prog, what, strerror(errno));
  exit(EXIT_SETUP);
}

static void allow(int ruleset, const char *path, uint64_t access, int flags) {
  struct ll_path_beneath_attr attr;
  attr.allowed_access = access;
  attr.parent_fd = open(path, O_PATH | O_CLOEXEC | flags);
  if (attr.parent_fd < 0) fail(path);
  if (syscall(__NR_landlock_add_rule, ruleset, LL_RULE_PATH_BENEATH, &attr, 0) != 0)
    fail("landlock_add_rule");
  close(attr.parent_fd);
}

/* Restricts the calling process's writes to `dir` and `/dev/null`. */
static void confine(int ruleset) {
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) fail("PR_SET_NO_NEW_PRIVS");
  if (syscall(__NR_landlock_restrict_self, ruleset, 0) != 0) fail("landlock_restrict_self");
  close(ruleset);
}

/* The path listing the children of this (single-threaded) process. */
static void children_path(char *buf, size_t size) {
  snprintf(buf, size, "/proc/self/task/%ld/children", (long)getpid());
}

/*
Sends `SIGKILL` to every child listed in `/proc`. Listed PIDs are this process's children, which
cannot be reused before this process reaps them, so no other process can be signalled.
*/
static void kill_children(void) {
  char path[64];
  children_path(path, sizeof path);
  FILE *f = fopen(path, "r");
  if (!f) fail(path);
  long pid;
  while (fscanf(f, "%ld", &pid) == 1) {
    if (pid > 0) kill((pid_t)pid, SIGKILL);
  }
  fclose(f);
}

int main(int argc, char **argv) {
  int i = 1;
  int reap = 0;
  if (i < argc && strcmp(argv[i], "--reap") == 0) {
    reap = 1;
    i++;
  }
  if (argc - i < 3 || strcmp(argv[i + 1], "--") != 0) {
    fprintf(stderr, "usage: %s [--reap] DIR -- COMMAND [ARG...]\n", prog);
    return EXIT_SETUP;
  }
  const char *dir = argv[i];
  char **cmd = &argv[i + 2];

  long abi = syscall(__NR_landlock_create_ruleset, NULL, 0, LL_CREATE_RULESET_VERSION);
  if (abi < MIN_ABI) {
    if (abi < 0) fail("Landlock is unavailable");
    fprintf(stderr, "%s: Landlock ABI %ld is too old (need %d)\n", prog, abi, MIN_ABI);
    return EXIT_SETUP;
  }
  struct ll_ruleset_attr attr = {.handled_access_fs = LL_FS_WRITES};
  int ruleset = (int)syscall(__NR_landlock_create_ruleset, &attr, sizeof attr, 0);
  if (ruleset < 0) fail("landlock_create_ruleset");
  allow(ruleset, dir, LL_FS_WRITES, O_DIRECTORY);
  allow(ruleset, "/dev/null", LL_FS_WRITE_FILE | LL_FS_TRUNCATE, 0);

  if (!reap) {
    confine(ruleset);
    execvp(cmd[0], cmd);
    fail(cmd[0]);
  }

  if (prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0) fail("PR_SET_CHILD_SUBREAPER");
  char path[64];
  children_path(path, sizeof path);
  if (access(path, R_OK) != 0) fail(path);

  pid_t child = fork();
  if (child < 0) fail("fork");
  if (child == 0) {
    confine(ruleset);
    execvp(cmd[0], cmd);
    fprintf(stderr, "%s: %s: %s\n", prog, cmd[0], strerror(errno));
    _exit(127);
  }
  close(ruleset);

  int status;
  while (waitpid(child, &status, 0) < 0) {
    if (errno != EINTR) fail("waitpid");
  }
  /*
  Kill and reap until no children remain. Orphaned descendants are re-parented to this process,
  so each round reaches the next generation. Reaping does not block: a descendant re-parented
  after the listing is alive and unsignalled, so it is killed in the next round instead.
  Reaping only after `kill_children` returns is what keeps the PIDs it signals from being reused.
  */
  for (;;) {
    kill_children();
    pid_t reaped = waitpid(-1, NULL, WNOHANG);
    if (reaped < 0) {
      if (errno == ECHILD) break;
      if (errno != EINTR) fail("waitpid");
    } else if (reaped == 0) {
      struct timespec pause = {0, 1000000};
      nanosleep(&pause, NULL);
    }
  }
  if (WIFEXITED(status)) return WEXITSTATUS(status);
  if (WIFSIGNALED(status)) return 128 + WTERMSIG(status);
  return EXIT_SETUP;
}
