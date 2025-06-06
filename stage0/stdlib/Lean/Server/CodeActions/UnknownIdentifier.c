// Lean compiler output
// Module: Lean.Server.CodeActions.UnknownIdentifier
// Imports: Lean.Server.FileWorker.Utils Lean.Data.Lsp.Internal Lean.Server.Requests Lean.Server.Completion.CompletionInfoSelection Lean.Server.CodeActions.Basic Lean.Server.Completion.CompletionUtils
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1;
lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___boxed(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Server_FileWorker_collectOpenNamespaces___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__4;
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3428_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__2(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2;
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__1;
static lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3;
lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_FileWorker_collectOpenNamespaces___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_NameSSet_insert___spec__7(lean_object*);
lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_toJsonCodeActionResolveData____x40_Lean_Server_CodeActions_Basic___hyg_59_(lean_object*);
uint8_t l_String_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object*);
static lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_waitAny___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4(lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__5;
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__3(lean_object*);
static lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
static lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3119_(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__3___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__1(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3;
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__3(lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
static lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_NameSSet_insert___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__2;
static lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5;
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_9, x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_7, x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
lean_inc(x_16);
lean_inc(x_2);
x_18 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2(x_1, x_2, x_3, x_14, x_16, x_11);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_16);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_27);
lean_ctor_set(x_10, 0, x_6);
x_28 = 1;
x_29 = lean_usize_add(x_9, x_28);
x_9 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
lean_inc(x_31);
lean_inc(x_2);
x_32 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2(x_1, x_2, x_3, x_14, x_31, x_11);
lean_dec(x_14);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_2);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
lean_dec(x_31);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
lean_inc(x_6);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_40);
x_42 = 1;
x_43 = lean_usize_add(x_9, x_42);
x_9 = x_43;
x_10 = x_41;
x_11 = x_39;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_push(x_2, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Lean_FileMap_ofPosition(x_2, x_7);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; 
lean_dec(x_2);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_8);
x_11 = 1;
x_12 = l_String_Range_overlaps(x_10, x_3, x_11, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1(x_10, x_4, x_15, x_6);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = l_Lean_FileMap_ofPosition(x_2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = l_String_Range_overlaps(x_20, x_3, x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_ctor_set(x_9, 0, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_9);
x_24 = lean_box(0);
x_25 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1(x_20, x_4, x_24, x_6);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
x_27 = l_Lean_FileMap_ofPosition(x_2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
x_29 = 1;
x_30 = l_String_Range_overlaps(x_28, x_3, x_29, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1(x_28, x_4, x_33, x_6);
return x_34;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_unknownIdentifierMessageTag;
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__3___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_8, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_6, x_8);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 4);
lean_inc(x_17);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_19 = l_Lean_MessageData_hasTag(x_18, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_13);
lean_inc(x_5);
lean_ctor_set(x_9, 0, x_5);
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_23 = lean_box(0);
lean_inc(x_2);
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_15, x_23, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_5);
x_28 = 1;
x_29 = lean_usize_add(x_8, x_28);
x_8 = x_29;
x_10 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_34 = l_Lean_MessageData_hasTag(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_13);
lean_inc(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_31);
x_36 = 1;
x_37 = lean_usize_add(x_8, x_36);
x_8 = x_37;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_39 = lean_box(0);
lean_inc(x_2);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_31, x_39, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_8, x_45);
x_8 = x_46;
x_9 = x_44;
x_10 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_array_size(x_7);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__3(x_1, x_2, x_3, x_7, x_8, x_9, x_7, x_11, x_12, x_10, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1(x_17, x_18, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_array_size(x_26);
x_31 = 0;
x_32 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4(x_1, x_2, x_26, x_27, x_28, x_26, x_30, x_31, x_29, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1(x_36, x_37, x_35);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_33);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_41);
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_8, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_6, x_8);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 4);
lean_inc(x_17);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_19 = l_Lean_MessageData_hasTag(x_18, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_13);
lean_inc(x_5);
lean_ctor_set(x_9, 0, x_5);
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_23 = lean_box(0);
lean_inc(x_2);
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_15, x_23, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_5);
x_28 = 1;
x_29 = lean_usize_add(x_8, x_28);
x_8 = x_29;
x_10 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_34 = l_Lean_MessageData_hasTag(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_13);
lean_inc(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_31);
x_36 = 1;
x_37 = lean_usize_add(x_8, x_36);
x_8 = x_37;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_39 = lean_box(0);
lean_inc(x_2);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_31, x_39, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_8, x_45);
x_8 = x_46;
x_9 = x_44;
x_10 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_7 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2(x_1, x_2, x_4, x_6, x_4, x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_array_size(x_18);
x_22 = 0;
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__5(x_1, x_2, x_17, x_18, x_19, x_18, x_21, x_22, x_20, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_9, x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_7, x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
lean_inc(x_16);
lean_inc(x_2);
x_18 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7(x_1, x_2, x_3, x_14, x_16, x_11);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_16);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_27);
lean_ctor_set(x_10, 0, x_6);
x_28 = 1;
x_29 = lean_usize_add(x_9, x_28);
x_9 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
lean_inc(x_31);
lean_inc(x_2);
x_32 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7(x_1, x_2, x_3, x_14, x_31, x_11);
lean_dec(x_14);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_2);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
lean_dec(x_31);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
lean_inc(x_6);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_40);
x_42 = 1;
x_43 = lean_usize_add(x_9, x_42);
x_9 = x_43;
x_10 = x_41;
x_11 = x_39;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_8, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_6, x_8);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 4);
lean_inc(x_17);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_19 = l_Lean_MessageData_hasTag(x_18, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_13);
lean_inc(x_5);
lean_ctor_set(x_9, 0, x_5);
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_23 = lean_box(0);
lean_inc(x_2);
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_15, x_23, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_5);
x_28 = 1;
x_29 = lean_usize_add(x_8, x_28);
x_8 = x_29;
x_10 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_34 = l_Lean_MessageData_hasTag(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_13);
lean_inc(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_31);
x_36 = 1;
x_37 = lean_usize_add(x_8, x_36);
x_8 = x_37;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_39 = lean_box(0);
lean_inc(x_2);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_31, x_39, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_8, x_45);
x_8 = x_46;
x_9 = x_44;
x_10 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_array_size(x_7);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__8(x_1, x_2, x_3, x_7, x_8, x_9, x_7, x_11, x_12, x_10, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1(x_17, x_18, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_array_size(x_26);
x_31 = 0;
x_32 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__9(x_1, x_2, x_26, x_27, x_28, x_26, x_30, x_31, x_29, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1(x_36, x_37, x_35);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_33);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_41);
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_8, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_6, x_8);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 4);
lean_inc(x_17);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_19 = l_Lean_MessageData_hasTag(x_18, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_13);
lean_inc(x_5);
lean_ctor_set(x_9, 0, x_5);
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_23 = lean_box(0);
lean_inc(x_2);
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_15, x_23, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_5);
x_28 = 1;
x_29 = lean_usize_add(x_8, x_28);
x_8 = x_29;
x_10 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1;
x_34 = l_Lean_MessageData_hasTag(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_13);
lean_inc(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_31);
x_36 = 1;
x_37 = lean_usize_add(x_8, x_36);
x_8 = x_37;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_39 = lean_box(0);
lean_inc(x_2);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_13, x_2, x_1, x_31, x_39, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_8, x_45);
x_8 = x_46;
x_9 = x_44;
x_10 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_7 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7(x_1, x_2, x_4, x_6, x_4, x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_array_size(x_18);
x_22 = 0;
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__10(x_1, x_2, x_17, x_18, x_19, x_18, x_21, x_22, x_20, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_6, x_1);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_9, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1;
x_20 = 1;
x_21 = l_Lean_Language_SnapshotTask_map___rarg(x_16, x_19, x_17, x_18, x_20);
lean_ctor_set(x_3, 0, x_21);
x_22 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_3, x_1);
lean_ctor_set(x_2, 1, x_22);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1;
x_28 = 1;
x_29 = l_Lean_Language_SnapshotTask_map___rarg(x_24, x_27, x_25, x_26, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_30, x_1);
lean_ctor_set(x_2, 1, x_31);
return x_2;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_34 = x_3;
} else {
 lean_dec_ref(x_3);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1;
x_39 = 1;
x_40 = l_Lean_Language_SnapshotTask_map___rarg(x_35, x_38, x_36, x_37, x_39);
if (lean_is_scalar(x_34)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_34;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_41, x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_3 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_2);
x_12 = l_Lean_Language_SnapshotTree_collectMessagesInRange(x_11, x_2);
x_13 = lean_task_get_own(x_12);
x_14 = l_Lean_MessageLog_reportedPlusUnreported(x_13);
x_15 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_16 = l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1(x_2, x_8, x_14, x_15, x_3);
lean_dec(x_14);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_28 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
x_31 = 1;
x_32 = l_Lean_Language_SnapshotTask_map___rarg(x_26, x_28, x_29, x_30, x_31);
lean_ctor_set(x_6, 0, x_32);
x_33 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_6, x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_2);
x_35 = l_Lean_Language_SnapshotTree_collectMessagesInRange(x_34, x_2);
x_36 = lean_task_get_own(x_35);
x_37 = l_Lean_MessageLog_reportedPlusUnreported(x_36);
x_38 = l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__6(x_2, x_22, x_37, x_27, x_3);
lean_dec(x_37);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_43 = lean_ctor_get(x_6, 0);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_46 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1), 2, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = 1;
x_50 = l_Lean_Language_SnapshotTask_map___rarg(x_44, x_46, x_47, x_48, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_51, x_45);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_2);
x_54 = l_Lean_Language_SnapshotTree_collectMessagesInRange(x_53, x_2);
x_55 = lean_task_get_own(x_54);
x_56 = l_Lean_MessageLog_reportedPlusUnreported(x_55);
x_57 = l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__6(x_2, x_22, x_56, x_45, x_3);
lean_dec(x_56);
lean_dec(x_2);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13, x_10, x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___lambda__3(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13, x_10, x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_forInAux___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forIn___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_FileWorker_collectOpenNamespaces___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Name_isAnonymous(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_push(x_4, x_7);
x_9 = l_Lean_Name_getPrefix(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_9);
goto _start;
}
else
{
return x_1;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Lean_Name_isAnonymous(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_push(x_12, x_15);
x_17 = l_Lean_Name_getPrefix(x_11);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_1 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Server_FileWorker_collectOpenNamespaces___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_array_mk(x_9);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_15);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_20 = x_4;
} else {
 lean_dec_ref(x_4);
 x_20 = lean_box(0);
}
x_21 = lean_array_mk(x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_1 = x_17;
x_2 = x_23;
goto _start;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set(x_4, 0, x_30);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_26;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_34);
{
lean_object* _tmp_0 = x_26;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_39 = x_4;
} else {
 lean_dec_ref(x_4);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_2);
x_1 = x_36;
x_2 = x_41;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_box(0);
x_4 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Loop_forIn_loop___at_Lean_Server_FileWorker_collectOpenNamespaces___spec__1(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_List_mapTR_loop___at_Lean_Server_FileWorker_collectOpenNamespaces___spec__2(x_2, x_3);
x_9 = lean_array_mk(x_8);
x_10 = l_Array_append___rarg(x_7, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Info_range_x3f(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = 1;
x_7 = l_String_Range_overlaps(x_5, x_1, x_6, x_6);
lean_dec(x_5);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(x_1, x_2, x_5);
x_7 = l_Lean_FileMap_utf8RangeToLspRange(x_3, x_4);
x_8 = 1;
x_9 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
lean_inc(x_6);
x_10 = l_Lean_Name_toString(x_6, x_8, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Elab_InfoTree_smallestInfo_x3f(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_string_utf8_extract(x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 5);
lean_inc(x_22);
lean_inc(x_22);
lean_inc(x_21);
x_23 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_21, x_22);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___boxed), 5, 4);
lean_closure_set(x_25, 0, x_21);
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_7);
lean_closure_set(x_25, 3, x_3);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_string_utf8_extract(x_28, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 5);
lean_inc(x_34);
lean_inc(x_34);
lean_inc(x_33);
x_35 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___boxed), 5, 4);
lean_closure_set(x_38, 0, x_33);
lean_closure_set(x_38, 1, x_34);
lean_closure_set(x_38, 2, x_7);
lean_closure_set(x_38, 3, x_3);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_string_utf8_extract(x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
lean_dec(x_41);
x_48 = lean_ctor_get(x_47, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 5);
lean_inc(x_49);
lean_inc(x_49);
lean_inc(x_48);
x_50 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_48, x_49);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_42;
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___boxed), 5, 4);
lean_closure_set(x_53, 0, x_48);
lean_closure_set(x_53, 1, x_49);
lean_closure_set(x_53, 2, x_7);
lean_closure_set(x_53, 3, x_3);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(x_1, x_2, x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
x_13 = l_Lean_FileMap_utf8RangeToLspRange(x_11, x_12);
lean_dec(x_12);
x_14 = 1;
lean_inc(x_8);
x_15 = l_Lean_Name_toString(x_8, x_14, x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Syntax_getPos_x3f(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Syntax_getTailPos_x3f(x_3, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
x_14 = l_Lean_Name_toString(x_4, x_5, x_13);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 5);
lean_inc(x_17);
lean_inc(x_17);
lean_inc(x_16);
x_18 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lambda__1), 7, 6);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_17);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_8);
lean_closure_set(x_21, 4, x_12);
lean_closure_set(x_21, 5, x_13);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_24 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
x_25 = l_Lean_Name_toString(x_4, x_5, x_24);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 5);
lean_inc(x_28);
lean_inc(x_28);
lean_inc(x_27);
x_29 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_27, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lambda__1), 7, 6);
lean_closure_set(x_32, 0, x_27);
lean_closure_set(x_32, 1, x_28);
lean_closure_set(x_32, 2, x_1);
lean_closure_set(x_32, 3, x_8);
lean_closure_set(x_32, 4, x_23);
lean_closure_set(x_32, 5, x_24);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_16; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_17, x_2, x_3, x_4, x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Server_Completion_getDotCompletionTypeNames(x_20, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_7 = x_30;
x_8 = x_31;
goto block_15;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_7 = x_32;
x_8 = x_33;
goto block_15;
}
block_15:
{
uint8_t x_9; 
x_9 = l_Lean_Exception_isInterrupt(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Exception_isRuntime(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Lean_FileMap_utf8RangeToLspRange(x_3, x_5);
lean_dec(x_5);
x_7 = l_Lean_Name_getString_x21(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Lean_Syntax_getPos_x3f(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Syntax_getTailPos_x3f(x_9, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 3);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
lean_inc(x_2);
x_22 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_2, x_19, x_21, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
x_35 = lean_string_utf8_extract(x_34, x_14, x_18);
lean_dec(x_34);
x_36 = lean_array_size(x_33);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(x_36, x_37, x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__2), 4, 3);
lean_closure_set(x_42, 0, x_14);
lean_closure_set(x_42, 1, x_18);
lean_closure_set(x_42, 2, x_7);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_23, 0, x_43);
return x_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_23, 0);
lean_inc(x_44);
lean_dec(x_23);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_string_utf8_extract(x_45, x_14, x_18);
lean_dec(x_45);
x_47 = lean_array_size(x_44);
x_48 = 0;
x_49 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(x_47, x_48, x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__2), 4, 3);
lean_closure_set(x_53, 0, x_14);
lean_closure_set(x_53, 1, x_18);
lean_closure_set(x_53, 2, x_7);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_22, 0, x_55);
return x_22;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
x_57 = lean_ctor_get(x_23, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_58 = x_23;
} else {
 lean_dec_ref(x_23);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
x_60 = lean_string_utf8_extract(x_59, x_14, x_18);
lean_dec(x_59);
x_61 = lean_array_size(x_57);
x_62 = 0;
x_63 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(x_61, x_62, x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lambda__2), 4, 3);
lean_closure_set(x_67, 0, x_14);
lean_closure_set(x_67, 1, x_18);
lean_closure_set(x_67, 2, x_7);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_67);
if (lean_is_scalar(x_58)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_58;
}
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_56);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_22);
if (x_71 == 0)
{
return x_22;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_22, 0);
x_73 = lean_ctor_get(x_22, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_22);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_cleanupAnnotations(x_9);
x_12 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_cleanupAnnotations(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; 
lean_free_object(x_7);
x_14 = l_Lean_Server_Completion_getDotCompletionTypeNames(x_13, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = l_Lean_Exception_isInterrupt(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
x_26 = lean_box(0);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
else
{
return x_14;
}
}
else
{
return x_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = l_Lean_Exception_isInterrupt(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_7, 0, x_35);
return x_7;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = l_Lean_Expr_cleanupAnnotations(x_36);
x_39 = l_Lean_Expr_getAppFn(x_38);
lean_dec(x_38);
x_40 = l_Lean_Expr_cleanupAnnotations(x_39);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; 
x_41 = l_Lean_Server_Completion_getDotCompletionTypeNames(x_40, x_2, x_3, x_4, x_5, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Exception_isInterrupt(x_47);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Exception_isRuntime(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_47);
x_52 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
 lean_ctor_set_tag(x_53, 0);
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; 
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
lean_object* x_55; 
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_49;
}
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_40);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_37);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
x_9 = l_Lean_FileMap_utf8RangeToLspRange(x_7, x_8);
lean_dec(x_8);
x_10 = l_Lean_Name_getString_x21(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_Syntax_getPos_x3f(x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_3, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_2);
x_21 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_2, x_5, x_20, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
x_34 = l_Lean_Name_toString(x_4, x_8, x_33);
x_35 = lean_array_size(x_32);
x_36 = 0;
x_37 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(x_35, x_36, x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__2), 4, 3);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_12);
lean_closure_set(x_41, 2, x_18);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_22, 0, x_42);
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
lean_dec(x_22);
x_44 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
x_45 = l_Lean_Name_toString(x_4, x_8, x_44);
x_46 = lean_array_size(x_43);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(x_46, x_47, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__2), 4, 3);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_12);
lean_closure_set(x_52, 2, x_18);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_21, 0, x_54);
return x_21;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_dec(x_21);
x_56 = lean_ctor_get(x_22, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_57 = x_22;
} else {
 lean_dec_ref(x_22);
 x_57 = lean_box(0);
}
x_58 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
x_59 = l_Lean_Name_toString(x_4, x_8, x_58);
x_60 = lean_array_size(x_56);
x_61 = 0;
x_62 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_computeDotQuery_x3f___spec__1(x_60, x_61, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_dec(x_2);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lambda__2), 4, 3);
lean_closure_set(x_66, 0, x_1);
lean_closure_set(x_66, 1, x_12);
lean_closure_set(x_66, 2, x_18);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_66);
if (lean_is_scalar(x_57)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_57;
}
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_55);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = 1;
lean_inc(x_9);
lean_inc(x_1);
x_11 = l_Lean_Server_RequestM_findCmdDataAtPos(x_1, x_9, x_10);
x_12 = lean_task_get_own(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_17);
x_18 = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(x_8, x_9, x_16, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
x_22 = lean_array_get_size(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
x_25 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f(x_1, x_2, x_3, x_17);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_array_fget(x_20, x_23);
lean_dec(x_20);
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_lt(x_23, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f(x_1, x_2, x_3, x_17);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_array_fget(x_26, x_23);
lean_dec(x_26);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_30);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Server_FileWorker_computeDotQuery_x3f(x_1, x_35, x_36, x_5);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = l_Lean_Server_RequestError_ofIoError(x_43);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = l_Lean_Server_RequestError_ofIoError(x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
case 1:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_dec(x_32);
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_49, x_50, x_51);
lean_dec(x_50);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 0, x_52);
return x_30;
}
case 2:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_30);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_ctor_get(x_34, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_34, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_34, 3);
lean_inc(x_57);
lean_dec(x_34);
x_58 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_53, x_54, x_55, x_56, x_57, x_5);
lean_dec(x_54);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = l_Lean_Server_RequestError_ofIoError(x_64);
lean_ctor_set(x_58, 0, x_65);
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_58, 0);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_58);
x_68 = l_Lean_Server_RequestError_ofIoError(x_66);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
case 6:
{
uint8_t x_70; 
lean_free_object(x_30);
lean_dec(x_32);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_34);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_34, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_34, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set_tag(x_34, 0);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_34, 0, x_73);
return x_34;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_34);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
return x_75;
}
}
default: 
{
lean_object* x_76; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_1);
x_76 = lean_box(0);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 0, x_76);
return x_30;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_30, 0);
lean_inc(x_77);
lean_dec(x_30);
x_78 = lean_ctor_get(x_77, 2);
lean_inc(x_78);
switch (lean_obj_tag(x_78)) {
case 0:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Server_FileWorker_computeDotQuery_x3f(x_1, x_79, x_80, x_5);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
x_89 = l_Lean_Server_RequestError_ofIoError(x_86);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
case 1:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
lean_dec(x_77);
x_92 = lean_ctor_get(x_78, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_91, x_92, x_93);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
}
case 2:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_dec(x_77);
x_97 = lean_ctor_get(x_78, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_78, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 3);
lean_inc(x_100);
lean_dec(x_78);
x_101 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_96, x_97, x_98, x_99, x_100, x_5);
lean_dec(x_97);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_108 = x_101;
} else {
 lean_dec_ref(x_101);
 x_108 = lean_box(0);
}
x_109 = l_Lean_Server_RequestError_ofIoError(x_106);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
case 6:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_77);
lean_dec(x_1);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_111 = x_78;
} else {
 lean_dec_ref(x_78);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
 lean_ctor_set_tag(x_113, 0);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_5);
return x_113;
}
default: 
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_1);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_5);
return x_115;
}
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_18, 0);
lean_inc(x_116);
lean_dec(x_18);
x_117 = lean_array_get_size(x_116);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_nat_dec_lt(x_118, x_117);
lean_dec(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_116);
x_120 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f(x_1, x_2, x_3, x_17);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_5);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_array_fget(x_116, x_118);
lean_dec(x_116);
x_123 = lean_array_get_size(x_122);
x_124 = lean_nat_dec_lt(x_118, x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_122);
x_125 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f(x_1, x_2, x_3, x_17);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_5);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_array_fget(x_122, x_118);
lean_dec(x_122);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_128, 2);
lean_inc(x_130);
switch (lean_obj_tag(x_130)) {
case 0:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_129);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Server_FileWorker_computeDotQuery_x3f(x_1, x_131, x_132, x_5);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Server_RequestError_ofIoError(x_138);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
}
case 1:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_128, 1);
lean_inc(x_143);
lean_dec(x_128);
x_144 = lean_ctor_get(x_130, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_130, 1);
lean_inc(x_145);
lean_dec(x_130);
x_146 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_143, x_144, x_145);
lean_dec(x_144);
if (lean_is_scalar(x_129)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_129;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_5);
return x_147;
}
case 2:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_129);
x_148 = lean_ctor_get(x_128, 1);
lean_inc(x_148);
lean_dec(x_128);
x_149 = lean_ctor_get(x_130, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_130, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_130, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_130, 3);
lean_inc(x_152);
lean_dec(x_130);
x_153 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_148, x_149, x_150, x_151, x_152, x_5);
lean_dec(x_149);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_160 = x_153;
} else {
 lean_dec_ref(x_153);
 x_160 = lean_box(0);
}
x_161 = l_Lean_Server_RequestError_ofIoError(x_158);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
return x_162;
}
}
case 6:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_1);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_163 = x_130;
} else {
 lean_dec_ref(x_130);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
 lean_ctor_set_tag(x_165, 0);
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_5);
return x_165;
}
default: 
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_1);
x_166 = lean_box(0);
if (lean_is_scalar(x_129)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_129;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_5);
return x_167;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_computeQuery_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknownIdentifiers", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Import all unambiguous unknown identifiers", 42, 42);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_toJsonCodeActionResolveData____x40_Lean_Server_CodeActions_Basic___hyg_59_(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__1;
x_11 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_4);
lean_ctor_set(x_11, 4, x_3);
lean_ctor_set(x_11, 5, x_3);
lean_ctor_set(x_11, 6, x_3);
lean_ctor_set(x_11, 7, x_3);
lean_ctor_set(x_11, 8, x_3);
lean_ctor_set(x_11, 9, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_2);
x_11 = l_Lean_Server_FileWorker_computeQuery_x3f(x_2, x_1, x_10, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_array_push(x_6, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_6 = x_19;
x_8 = x_17;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_le(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_usize_of_nat(x_4);
x_16 = lean_usize_of_nat(x_5);
x_17 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__2(x_1, x_2, x_3, x_15, x_16, x_17, x_6, x_7);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot parse server request response: ", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3428_(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_free_object(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_3);
x_7 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = 0;
x_15 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_17);
x_18 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3428_(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Json_compress(x_17);
x_21 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_19);
lean_dec(x_19);
x_26 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
return x_1;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_33);
return x_35;
}
}
}
}
static lean_object* _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 5);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3119_(x_2);
x_7 = lean_apply_3(x_5, x_1, x_6, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___closed__1;
x_11 = l_Task_Priority_default;
x_12 = 1;
x_13 = lean_task_map(x_10, x_9, x_11, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___closed__1;
x_17 = l_Task_Priority_default;
x_18 = 1;
x_19 = lean_task_map(x_16, x_14, x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Import ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" from ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quickfix", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Change to ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_1(x_13, x_2);
if (x_3 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_15 = lean_box(0);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = 1;
x_18 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
x_19 = l_Lean_Name_toString(x_16, x_17, x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_Name_toString(x_4, x_17, x_18);
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__5;
x_30 = lean_string_append(x_29, x_24);
lean_dec(x_24);
x_31 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_15);
lean_ctor_set(x_33, 3, x_15);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_mk(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__4;
x_43 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_15);
lean_ctor_set(x_43, 2, x_27);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_15);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_15);
lean_ctor_set(x_43, 7, x_41);
lean_ctor_set(x_43, 8, x_15);
lean_ctor_set(x_43, 9, x_15);
x_44 = lean_array_push(x_9, x_43);
if (x_7 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_box(x_8);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_12);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_box(x_17);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_12);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_6);
lean_dec(x_4);
x_53 = lean_box(0);
x_54 = lean_ctor_get(x_14, 0);
lean_inc(x_54);
x_55 = 1;
x_56 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
x_57 = l_Lean_Name_toString(x_54, x_55, x_56);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__6;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3;
x_61 = lean_string_append(x_59, x_60);
x_62 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_dec(x_14);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_mk(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__4;
x_71 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_71, 0, x_53);
lean_ctor_set(x_71, 1, x_53);
lean_ctor_set(x_71, 2, x_61);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_53);
lean_ctor_set(x_71, 5, x_53);
lean_ctor_set(x_71, 6, x_53);
lean_ctor_set(x_71, 7, x_69);
lean_ctor_set(x_71, 8, x_53);
lean_ctor_set(x_71, 9, x_53);
x_72 = lean_array_push(x_9, x_71);
x_73 = lean_box(x_8);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_12);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_8, x_7);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_14 = lean_array_uget(x_6, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = 1;
lean_inc(x_16);
lean_inc(x_21);
x_23 = l_Lean_Environment_contains(x_21, x_16, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Environment_mainModule(x_21);
lean_dec(x_21);
x_25 = lean_name_eq(x_15, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_free_object(x_9);
x_26 = lean_box(0);
x_27 = lean_unbox(x_19);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_3);
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1(x_3, x_16, x_23, x_15, x_1, x_2, x_17, x_27, x_20, x_26, x_10, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 1;
x_33 = lean_usize_add(x_8, x_32);
x_8 = x_33;
x_9 = x_31;
x_11 = x_30;
goto _start;
}
else
{
size_t x_35; size_t x_36; 
lean_dec(x_16);
lean_dec(x_15);
x_35 = 1;
x_36 = lean_usize_add(x_8, x_35);
x_8 = x_36;
goto _start;
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_21);
lean_free_object(x_9);
x_38 = lean_box(0);
x_39 = lean_unbox(x_19);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_3);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1(x_3, x_16, x_23, x_15, x_1, x_2, x_17, x_39, x_20, x_38, x_10, x_11);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 1;
x_45 = lean_usize_add(x_8, x_44);
x_8 = x_45;
x_9 = x_43;
x_11 = x_42;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
x_50 = 1;
lean_inc(x_16);
lean_inc(x_49);
x_51 = l_Lean_Environment_contains(x_49, x_16, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Environment_mainModule(x_49);
lean_dec(x_49);
x_53 = lean_name_eq(x_15, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
x_54 = lean_box(0);
x_55 = lean_unbox(x_47);
lean_dec(x_47);
lean_inc(x_2);
lean_inc(x_3);
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1(x_3, x_16, x_51, x_15, x_1, x_2, x_17, x_55, x_48, x_54, x_10, x_11);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = 1;
x_61 = lean_usize_add(x_8, x_60);
x_8 = x_61;
x_9 = x_59;
x_11 = x_58;
goto _start;
}
else
{
lean_object* x_63; size_t x_64; size_t x_65; 
lean_dec(x_16);
lean_dec(x_15);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_47);
lean_ctor_set(x_63, 1, x_48);
x_64 = 1;
x_65 = lean_usize_add(x_8, x_64);
x_8 = x_65;
x_9 = x_63;
goto _start;
}
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; 
lean_dec(x_49);
x_67 = lean_box(0);
x_68 = lean_unbox(x_47);
lean_dec(x_47);
lean_inc(x_2);
lean_inc(x_3);
x_69 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1(x_3, x_16, x_51, x_15, x_1, x_2, x_17, x_68, x_48, x_67, x_10, x_11);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = 1;
x_74 = lean_usize_add(x_8, x_73);
x_8 = x_74;
x_9 = x_72;
x_11 = x_71;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_8, x_7);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_6, x_8);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_18, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_18, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_dec(x_27);
x_28 = lean_array_fget(x_19, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_20, x_29);
lean_dec(x_20);
lean_ctor_set(x_18, 1, x_30);
x_31 = lean_box(0);
x_32 = lean_array_size(x_28);
lean_inc(x_5);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5(x_1, x_5, x_14, x_28, x_31, x_28, x_32, x_3, x_16, x_10, x_11);
lean_dec(x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
size_t x_37; size_t x_38; 
lean_ctor_set(x_9, 1, x_34);
x_37 = 1;
x_38 = lean_usize_add(x_8, x_37);
x_8 = x_38;
x_11 = x_35;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_9, 1, x_42);
x_43 = 1;
x_44 = lean_usize_add(x_8, x_43);
x_8 = x_44;
x_11 = x_35;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; 
lean_dec(x_18);
x_46 = lean_array_fget(x_19, x_20);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_20, x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_21);
x_50 = lean_box(0);
x_51 = lean_array_size(x_46);
lean_inc(x_5);
x_52 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5(x_1, x_5, x_14, x_46, x_50, x_46, x_51, x_3, x_16, x_10, x_11);
lean_dec(x_46);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_9, 1, x_58);
lean_ctor_set(x_9, 0, x_49);
x_59 = 1;
x_60 = lean_usize_add(x_8, x_59);
x_8 = x_60;
x_11 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_9, 0);
x_63 = lean_ctor_get(x_16, 0);
x_64 = lean_ctor_get(x_16, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_16);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 2);
lean_inc(x_67);
x_68 = lean_nat_dec_lt(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_14);
lean_dec(x_5);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_9, 1, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_11);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; 
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
x_72 = lean_array_fget(x_65, x_66);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_66, x_73);
lean_dec(x_66);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 3, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_67);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_63);
lean_ctor_set(x_77, 1, x_64);
x_78 = lean_array_size(x_72);
lean_inc(x_5);
x_79 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5(x_1, x_5, x_14, x_72, x_76, x_72, x_78, x_3, x_77, x_10, x_11);
lean_dec(x_72);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_84 = x_80;
} else {
 lean_dec_ref(x_80);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_9, 1, x_85);
lean_ctor_set(x_9, 0, x_75);
x_86 = 1;
x_87 = lean_usize_add(x_8, x_86);
x_8 = x_87;
x_11 = x_81;
goto _start;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = lean_ctor_get(x_9, 1);
x_90 = lean_ctor_get(x_9, 0);
lean_inc(x_89);
lean_inc(x_90);
lean_dec(x_9);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_93 = x_89;
} else {
 lean_dec_ref(x_89);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 2);
lean_inc(x_96);
x_97 = lean_nat_dec_lt(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_14);
lean_dec(x_5);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_92);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_90);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_11);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; size_t x_117; size_t x_118; 
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 x_101 = x_90;
} else {
 lean_dec_ref(x_90);
 x_101 = lean_box(0);
}
x_102 = lean_array_fget(x_94, x_95);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_95, x_103);
lean_dec(x_95);
if (lean_is_scalar(x_101)) {
 x_105 = lean_alloc_ctor(0, 3, 0);
} else {
 x_105 = x_101;
}
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_96);
x_106 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_93;
}
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_92);
x_108 = lean_array_size(x_102);
lean_inc(x_5);
x_109 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5(x_1, x_5, x_14, x_102, x_106, x_102, x_108, x_3, x_107, x_10, x_11);
lean_dec(x_102);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_105);
lean_ctor_set(x_116, 1, x_115);
x_117 = 1;
x_118 = lean_usize_add(x_8, x_117);
x_8 = x_118;
x_9 = x_116;
x_11 = x_111;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("$/lean/queryModule", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_array_size(x_1);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__3(x_11, x_12, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__1;
lean_inc(x_9);
x_16 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg(x_15, x_14, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__2;
x_21 = l_Task_Priority_default;
x_22 = 1;
x_23 = lean_task_map(x_20, x_18, x_21, x_22);
x_24 = lean_ctor_get(x_3, 4);
x_25 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_24);
x_26 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__3;
x_27 = lean_task_map(x_26, x_25, x_21, x_22);
x_28 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_16);
x_30 = l_Lean_Server_ServerTask_waitAny___rarg(x_29, lean_box(0), x_19);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_4, 1);
x_38 = lean_ctor_get(x_37, 2);
x_39 = 0;
x_40 = l_Lean_Syntax_getTailPos_x3f(x_38, x_39);
x_41 = lean_array_get_size(x_36);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_toSubarray___rarg(x_36, x_42, x_41);
x_44 = lean_box(0);
x_45 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4;
lean_ctor_set(x_30, 1, x_45);
lean_ctor_set(x_30, 0, x_43);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_64; 
lean_dec(x_7);
x_64 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6;
x_46 = x_64;
goto block_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_40, 0);
lean_inc(x_65);
lean_dec(x_40);
x_66 = l_Lean_FileMap_utf8PosToLspPos(x_7, x_65);
lean_dec(x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_67, x_68);
lean_dec(x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_42);
x_46 = x_70;
goto block_63;
}
block_63:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6(x_5, x_1, x_12, x_44, x_47, x_1, x_11, x_12, x_30, x_9, x_34);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5;
x_55 = lean_unbox(x_52);
lean_dec(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
x_56 = lean_box(0);
x_57 = lean_apply_4(x_54, x_53, x_56, x_9, x_51);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3;
x_59 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_6, x_58);
x_60 = lean_array_push(x_53, x_59);
x_61 = lean_box(0);
x_62 = lean_apply_4(x_54, x_60, x_61, x_9, x_51);
return x_62;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_30, 1);
lean_inc(x_71);
lean_dec(x_30);
x_72 = lean_ctor_get(x_32, 0);
lean_inc(x_72);
lean_dec(x_32);
x_73 = lean_ctor_get(x_4, 1);
x_74 = lean_ctor_get(x_73, 2);
x_75 = 0;
x_76 = l_Lean_Syntax_getTailPos_x3f(x_74, x_75);
x_77 = lean_array_get_size(x_72);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Array_toSubarray___rarg(x_72, x_78, x_77);
x_80 = lean_box(0);
x_81 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4;
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_101; 
lean_dec(x_7);
x_101 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6;
x_83 = x_101;
goto block_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_76, 0);
lean_inc(x_102);
lean_dec(x_76);
x_103 = l_Lean_FileMap_utf8PosToLspPos(x_7, x_102);
lean_dec(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_104, x_105);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_78);
x_83 = x_107;
goto block_100;
}
block_100:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_inc(x_83);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6(x_5, x_1, x_12, x_80, x_84, x_1, x_11, x_12, x_82, x_9, x_71);
lean_dec(x_1);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5;
x_92 = lean_unbox(x_89);
lean_dec(x_89);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_6);
x_93 = lean_box(0);
x_94 = lean_apply_4(x_91, x_90, x_93, x_9, x_88);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3;
x_96 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_6, x_95);
x_97 = lean_array_push(x_90, x_96);
x_98 = lean_box(0);
x_99 = lean_apply_4(x_91, x_97, x_98, x_9, x_88);
return x_99;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_108 = lean_ctor_get(x_30, 1);
lean_inc(x_108);
lean_dec(x_30);
x_109 = l_Lean_Server_RequestM_checkCancelled(x_9, x_108);
lean_dec(x_9);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
lean_dec(x_111);
x_112 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
lean_ctor_set(x_109, 0, x_112);
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
x_114 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_109);
if (x_116 == 0)
{
return x_109;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_109, 0);
x_118 = lean_ctor_get(x_109, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_109);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_120 = lean_ctor_get(x_30, 1);
lean_inc(x_120);
lean_dec(x_30);
x_121 = l_Lean_Server_RequestM_checkCancelled(x_9, x_120);
lean_dec(x_9);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
lean_dec(x_123);
x_124 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
lean_ctor_set(x_121, 0, x_124);
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
lean_dec(x_121);
x_126 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_121);
if (x_128 == 0)
{
return x_121;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_121, 0);
x_130 = lean_ctor_get(x_121, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_121);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_132 = lean_ctor_get(x_16, 0);
x_133 = lean_ctor_get(x_16, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_16);
x_134 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__2;
x_135 = l_Task_Priority_default;
x_136 = 1;
x_137 = lean_task_map(x_134, x_132, x_135, x_136);
x_138 = lean_ctor_get(x_3, 4);
x_139 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_138);
x_140 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__3;
x_141 = lean_task_map(x_140, x_139, x_135, x_136);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_137);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_Server_ServerTask_waitAny___rarg(x_144, lean_box(0), x_133);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec(x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_ctor_get(x_4, 1);
x_152 = lean_ctor_get(x_151, 2);
x_153 = 0;
x_154 = l_Lean_Syntax_getTailPos_x3f(x_152, x_153);
x_155 = lean_array_get_size(x_150);
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Array_toSubarray___rarg(x_150, x_156, x_155);
x_158 = lean_box(0);
x_159 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4;
if (lean_is_scalar(x_149)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_149;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_179; 
lean_dec(x_7);
x_179 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6;
x_161 = x_179;
goto block_178;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_154, 0);
lean_inc(x_180);
lean_dec(x_154);
x_181 = l_Lean_FileMap_utf8PosToLspPos(x_7, x_180);
lean_dec(x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_nat_add(x_182, x_183);
lean_dec(x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_156);
x_161 = x_185;
goto block_178;
}
block_178:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_161);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6(x_5, x_1, x_12, x_158, x_162, x_1, x_11, x_12, x_160, x_9, x_148);
lean_dec(x_1);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5;
x_170 = lean_unbox(x_167);
lean_dec(x_167);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_6);
x_171 = lean_box(0);
x_172 = lean_apply_4(x_169, x_168, x_171, x_9, x_166);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3;
x_174 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_6, x_173);
x_175 = lean_array_push(x_168, x_174);
x_176 = lean_box(0);
x_177 = lean_apply_4(x_169, x_175, x_176, x_9, x_166);
return x_177;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_186 = lean_ctor_get(x_145, 1);
lean_inc(x_186);
lean_dec(x_145);
x_187 = l_Lean_Server_RequestM_checkCancelled(x_9, x_186);
lean_dec(x_9);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_189;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_188);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_187, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_194 = x_187;
} else {
 lean_dec_ref(x_187);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_146);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_196 = lean_ctor_get(x_145, 1);
lean_inc(x_196);
lean_dec(x_145);
x_197 = l_Lean_Server_RequestM_checkCancelled(x_9, x_196);
lean_dec(x_9);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_197, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_197, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_204 = x_197;
} else {
 lean_dec_ref(x_197);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_get_size(x_4);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_13 = l_Array_filterMapM___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__1(x_3, x_7, x_4, x_12, x_11, x_5, x_6);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Array_isEmpty___rarg(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_13);
x_18 = lean_box(0);
lean_inc(x_5);
x_19 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4(x_15, x_1, x_5, x_8, x_7, x_2, x_10, x_18, x_5, x_16);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Array_isEmpty___rarg(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
lean_inc(x_5);
x_25 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4(x_21, x_1, x_5, x_8, x_7, x_2, x_10, x_24, x_5, x_22);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__2(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_filterMapM___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_13, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__6(x_1, x_2, x_12, x_4, x_5, x_6, x_13, x_14, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_uget(x_3, x_4);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_string_utf8_byte_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_inc(x_1);
x_15 = l_Lean_Server_FileWorker_computeQuery_x3f(x_1, x_14, x_10, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_array_push(x_6, x_22);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_6 = x_23;
x_8 = x_21;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_le(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_usize_of_nat(x_4);
x_16 = lean_usize_of_nat(x_5);
x_17 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__2(x_1, x_2, x_3, x_15, x_16, x_17, x_6, x_7);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_5, x_7);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
lean_dec(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_7, x_12);
{
size_t _tmp_6 = x_13;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = 1;
x_18 = l_Lean_Environment_contains(x_15, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
size_t x_23; size_t x_24; 
lean_dec(x_10);
x_23 = 1;
x_24 = lean_usize_add(x_7, x_23);
{
size_t _tmp_6 = x_24;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_push(x_4, x_9);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_sub(x_23, x_24);
x_26 = lean_usize_land(x_22, x_25);
x_27 = lean_array_uget(x_13, x_26);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_NameSSet_insert___spec__6(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_12, x_29);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
x_33 = lean_array_uset(x_13, x_26, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_nat_mul(x_30, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_NameSSet_insert___spec__7(x_33);
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_30);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_5);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_30);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_8);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_27);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_10);
lean_ctor_set(x_49, 1, x_5);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_53 = lean_ctor_get(x_5, 0);
x_54 = lean_ctor_get(x_5, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_5);
x_55 = lean_array_get_size(x_54);
x_56 = l_Lean_Name_hash___override(x_2);
x_57 = 32;
x_58 = lean_uint64_shift_right(x_56, x_57);
x_59 = lean_uint64_xor(x_56, x_58);
x_60 = 16;
x_61 = lean_uint64_shift_right(x_59, x_60);
x_62 = lean_uint64_xor(x_59, x_61);
x_63 = lean_uint64_to_usize(x_62);
x_64 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_65 = 1;
x_66 = lean_usize_sub(x_64, x_65);
x_67 = lean_usize_land(x_63, x_66);
x_68 = lean_array_uget(x_54, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_NameSSet_insert___spec__6(x_2, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_53, x_70);
lean_dec(x_53);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_68);
x_74 = lean_array_uset(x_54, x_67, x_73);
x_75 = lean_unsigned_to_nat(4u);
x_76 = lean_nat_mul(x_71, x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_div(x_76, x_77);
lean_dec(x_76);
x_79 = lean_array_get_size(x_74);
x_80 = lean_nat_dec_le(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_NameSSet_insert___spec__7(x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_10);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_3);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_8);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_71);
lean_ctor_set(x_87, 1, x_74);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_10);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_3);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_8);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_68);
lean_dec(x_2);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_53);
lean_ctor_set(x_92, 1, x_54);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_3);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_8);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, x_2);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lean_Name_hash___override(x_3);
x_16 = 32;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = 16;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_sub(x_23, x_24);
x_26 = lean_usize_land(x_22, x_25);
x_27 = lean_array_uget(x_13, x_26);
lean_dec(x_13);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_NameSSet_insert___spec__6(x_3, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = 1;
x_30 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1;
lean_inc(x_3);
x_31 = l_Lean_Name_toString(x_3, x_29, x_30);
x_32 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__5;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_array_push(x_6, x_37);
x_39 = lean_box(0);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__1(x_12, x_3, x_4, x_38, x_7, x_39, x_9, x_10);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
x_41 = lean_box(0);
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__1(x_12, x_3, x_4, x_6, x_7, x_41, x_9, x_10);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__2;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_7, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_array_uget(x_5, x_7);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_16 = x_8;
} else {
 lean_dec_ref(x_8);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_19 = x_14;
} else {
 lean_dec_ref(x_14);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 2);
lean_inc(x_22);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
if (lean_is_scalar(x_19)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_19;
}
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
if (lean_is_scalar(x_16)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_16;
}
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_28 = lean_ctor_get(x_15, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_15, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_15, 0);
lean_dec(x_30);
x_31 = lean_array_fget(x_20, x_21);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_21, x_32);
lean_dec(x_21);
lean_ctor_set(x_15, 1, x_33);
x_54 = lean_box(0);
x_55 = lean_array_size(x_31);
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__1;
lean_inc(x_13);
x_57 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__3(x_13, x_31, x_54, x_56, x_31, x_55, x_2, x_56);
lean_dec(x_31);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__3;
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_17);
lean_ctor_set(x_60, 1, x_18);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_15);
lean_ctor_set(x_61, 1, x_60);
x_62 = 1;
x_63 = lean_usize_add(x_7, x_62);
x_7 = x_63;
x_8 = x_61;
goto _start;
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_34 = x_65;
goto block_53;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_17);
lean_ctor_set(x_67, 1, x_18);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_15);
lean_ctor_set(x_68, 1, x_67);
x_69 = 1;
x_70 = lean_usize_add(x_7, x_69);
x_7 = x_70;
x_8 = x_68;
goto _start;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec(x_66);
x_34 = x_72;
goto block_53;
}
}
block_53:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
x_38 = l_Lean_Environment_mainModule(x_37);
lean_dec(x_37);
x_39 = lean_name_eq(x_35, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_19);
lean_dec(x_16);
x_40 = lean_box(0);
lean_inc(x_4);
x_41 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__2(x_13, x_36, x_35, x_15, x_4, x_17, x_18, x_40, x_9, x_10);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
x_10 = x_43;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_13);
if (lean_is_scalar(x_19)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_19;
}
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_18);
if (lean_is_scalar(x_16)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_16;
}
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_7, x_50);
x_7 = x_51;
x_8 = x_49;
goto _start;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_15);
x_73 = lean_array_fget(x_20, x_21);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_21, x_74);
lean_dec(x_21);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_20);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_22);
x_97 = lean_box(0);
x_98 = lean_array_size(x_73);
x_99 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__1;
lean_inc(x_13);
x_100 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__3(x_13, x_73, x_97, x_99, x_73, x_98, x_2, x_99);
lean_dec(x_73);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__3;
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_17);
lean_ctor_set(x_103, 1, x_18);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_76);
lean_ctor_set(x_104, 1, x_103);
x_105 = 1;
x_106 = lean_usize_add(x_7, x_105);
x_7 = x_106;
x_8 = x_104;
goto _start;
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
x_77 = x_108;
goto block_96;
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
lean_dec(x_101);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_17);
lean_ctor_set(x_110, 1, x_18);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_76);
lean_ctor_set(x_111, 1, x_110);
x_112 = 1;
x_113 = lean_usize_add(x_7, x_112);
x_7 = x_113;
x_8 = x_111;
goto _start;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
lean_dec(x_109);
x_77 = x_115;
goto block_96;
}
}
block_96:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_13, 1);
lean_inc(x_80);
x_81 = l_Lean_Environment_mainModule(x_80);
lean_dec(x_80);
x_82 = lean_name_eq(x_78, x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; 
lean_dec(x_19);
lean_dec(x_16);
x_83 = lean_box(0);
lean_inc(x_4);
x_84 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__2(x_13, x_79, x_78, x_76, x_4, x_17, x_18, x_83, x_9, x_10);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = 1;
x_89 = lean_usize_add(x_7, x_88);
x_7 = x_89;
x_8 = x_87;
x_10 = x_86;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_13);
if (lean_is_scalar(x_19)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_19;
}
lean_ctor_set(x_91, 0, x_17);
lean_ctor_set(x_91, 1, x_18);
if (lean_is_scalar(x_16)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_16;
}
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
x_93 = 1;
x_94 = lean_usize_add(x_7, x_93);
x_7 = x_94;
x_8 = x_92;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1;
x_2 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_array_size(x_1);
x_11 = 0;
lean_inc(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__3(x_10, x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__1;
lean_inc(x_8);
x_15 = l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg(x_14, x_13, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_task_get_own(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_22, 2);
x_24 = 0;
x_25 = l_Lean_Syntax_getTailPos_x3f(x_23, x_24);
x_26 = lean_array_get_size(x_20);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_toSubarray___rarg(x_20, x_27, x_26);
x_29 = lean_box(0);
x_30 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__4;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_100; 
lean_dec(x_6);
x_100 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6;
x_32 = x_100;
goto block_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_25, 0);
lean_inc(x_101);
lean_dec(x_25);
x_102 = l_Lean_FileMap_utf8PosToLspPos(x_6, x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_103, x_104);
lean_dec(x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_27);
x_32 = x_106;
goto block_99;
}
block_99:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4(x_1, x_11, x_29, x_33, x_1, x_10, x_11, x_31, x_8, x_18);
lean_dec(x_8);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_4);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_4, 7);
lean_dec(x_43);
x_44 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
lean_ctor_set(x_36, 1, x_40);
lean_ctor_set(x_36, 0, x_44);
x_45 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_36);
if (lean_is_scalar(x_21)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_21;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_4, 7, x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_34, 0, x_47);
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
x_50 = lean_ctor_get(x_4, 2);
x_51 = lean_ctor_get(x_4, 3);
x_52 = lean_ctor_get(x_4, 4);
x_53 = lean_ctor_get(x_4, 5);
x_54 = lean_ctor_get(x_4, 6);
x_55 = lean_ctor_get(x_4, 8);
x_56 = lean_ctor_get(x_4, 9);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_57 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
lean_ctor_set(x_36, 1, x_40);
lean_ctor_set(x_36, 0, x_57);
x_58 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_36);
if (lean_is_scalar(x_21)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_21;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set(x_60, 2, x_50);
lean_ctor_set(x_60, 3, x_51);
lean_ctor_set(x_60, 4, x_52);
lean_ctor_set(x_60, 5, x_53);
lean_ctor_set(x_60, 6, x_54);
lean_ctor_set(x_60, 7, x_59);
lean_ctor_set(x_60, 8, x_55);
lean_ctor_set(x_60, 9, x_56);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_34, 0, x_61);
return x_34;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_36, 0);
lean_inc(x_62);
lean_dec(x_36);
x_63 = lean_ctor_get(x_4, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_4, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_4, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_4, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_4, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_4, 6);
lean_inc(x_69);
x_70 = lean_ctor_get(x_4, 8);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 9);
lean_inc(x_71);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_72 = x_4;
} else {
 lean_dec_ref(x_4);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_62);
x_75 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_74);
if (lean_is_scalar(x_21)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_21;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_75);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 10, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_63);
lean_ctor_set(x_77, 1, x_64);
lean_ctor_set(x_77, 2, x_65);
lean_ctor_set(x_77, 3, x_66);
lean_ctor_set(x_77, 4, x_67);
lean_ctor_set(x_77, 5, x_68);
lean_ctor_set(x_77, 6, x_69);
lean_ctor_set(x_77, 7, x_76);
lean_ctor_set(x_77, 8, x_70);
lean_ctor_set(x_77, 9, x_71);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_34, 0, x_78);
return x_34;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_34, 1);
lean_inc(x_79);
lean_dec(x_34);
x_80 = lean_ctor_get(x_36, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_81 = x_36;
} else {
 lean_dec_ref(x_36);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_4, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_4, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_4, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_4, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_4, 5);
lean_inc(x_87);
x_88 = lean_ctor_get(x_4, 6);
lean_inc(x_88);
x_89 = lean_ctor_get(x_4, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_4, 9);
lean_inc(x_90);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_91 = x_4;
} else {
 lean_dec_ref(x_4);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
if (lean_is_scalar(x_81)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_81;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_80);
x_94 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_93);
if (lean_is_scalar(x_21)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_21;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 10, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_82);
lean_ctor_set(x_96, 1, x_83);
lean_ctor_set(x_96, 2, x_84);
lean_ctor_set(x_96, 3, x_85);
lean_ctor_set(x_96, 4, x_86);
lean_ctor_set(x_96, 5, x_87);
lean_ctor_set(x_96, 6, x_88);
lean_ctor_set(x_96, 7, x_95);
lean_ctor_set(x_96, 8, x_89);
lean_ctor_set(x_96, 9, x_90);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_79);
return x_98;
}
}
}
else
{
lean_object* x_107; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_107 = lean_box(0);
lean_ctor_set(x_15, 0, x_107);
return x_15;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_15, 0);
x_109 = lean_ctor_get(x_15, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_15);
x_110 = lean_task_get_own(x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_3, 1);
x_114 = lean_ctor_get(x_113, 2);
x_115 = 0;
x_116 = l_Lean_Syntax_getTailPos_x3f(x_114, x_115);
x_117 = lean_array_get_size(x_111);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Array_toSubarray___rarg(x_111, x_118, x_117);
x_120 = lean_box(0);
x_121 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__4;
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_150; 
lean_dec(x_6);
x_150 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6;
x_123 = x_150;
goto block_149;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_116, 0);
lean_inc(x_151);
lean_dec(x_116);
x_152 = l_Lean_FileMap_utf8PosToLspPos(x_6, x_151);
lean_dec(x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_add(x_153, x_154);
lean_dec(x_153);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_118);
x_123 = x_156;
goto block_149;
}
block_149:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_inc(x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4(x_1, x_11, x_120, x_124, x_1, x_10, x_11, x_122, x_8, x_109);
lean_dec(x_8);
lean_dec(x_1);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_129 = x_125;
} else {
 lean_dec_ref(x_125);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_4, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_4, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_4, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_4, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_4, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_4, 5);
lean_inc(x_137);
x_138 = lean_ctor_get(x_4, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_4, 8);
lean_inc(x_139);
x_140 = lean_ctor_get(x_4, 9);
lean_inc(x_140);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_141 = x_4;
} else {
 lean_dec_ref(x_4);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_5);
if (lean_is_scalar(x_131)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_131;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_130);
x_144 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_143);
if (lean_is_scalar(x_112)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_112;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_144);
if (lean_is_scalar(x_141)) {
 x_146 = lean_alloc_ctor(0, 10, 0);
} else {
 x_146 = x_141;
}
lean_ctor_set(x_146, 0, x_132);
lean_ctor_set(x_146, 1, x_133);
lean_ctor_set(x_146, 2, x_134);
lean_ctor_set(x_146, 3, x_135);
lean_ctor_set(x_146, 4, x_136);
lean_ctor_set(x_146, 5, x_137);
lean_ctor_set(x_146, 6, x_138);
lean_ctor_set(x_146, 7, x_145);
lean_ctor_set(x_146, 8, x_139);
lean_ctor_set(x_146, 9, x_140);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
if (lean_is_scalar(x_129)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_129;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_128);
return x_148;
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_110);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_109);
return x_158;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_get_size(x_3);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_12 = l_Array_filterMapM___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__1(x_6, x_9, x_3, x_11, x_10, x_4, x_5);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Array_isEmpty___rarg(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_17 = lean_box(0);
x_18 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1(x_14, x_1, x_7, x_2, x_6, x_9, x_17, x_4, x_15);
lean_dec(x_6);
lean_dec(x_7);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l_Array_isEmpty___rarg(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1(x_20, x_1, x_7, x_2, x_6, x_9, x_23, x_4, x_21);
lean_dec(x_6);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__2(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_filterMapM___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4(x_1, x_11, x_3, x_4, x_5, x_12, x_13, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_CodeActions_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_CodeActions_UnknownIdentifier(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_FileWorker_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_waitUnknownIdentifierRanges___spec__4___closed__1);
l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1 = _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lambda__1___closed__1);
l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1 = _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1);
l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2 = _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2);
l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1 = _init_l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lambda__3___closed__1);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1 = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__2 = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__2);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__1 = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__1);
l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__1 = _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__1);
l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2 = _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__2);
l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3 = _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___lambda__1___closed__3);
l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___closed__1 = _init_l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_RequestM_sendServerRequest___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__4___rarg___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___spec__5___lambda__1___closed__6);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__1 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__1);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__2 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__2);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__3 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__3);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__4);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__5);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lambda__4___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___spec__4___closed__3);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__1 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__1);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__2 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__2);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__3 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__3);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__4 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
