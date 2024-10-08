// Lean compiler output
// Module: Lean.Elab.PreDefinition.Nonrec.Eqns
// Imports: Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Split Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Eqns Lean.Meta.ArgsPacker.Basic Init.Data.Array.Basic
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__20;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__21;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22;
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__17;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__4;
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Elab_Nonrec_mkEqns___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Nonrec_mkEqns___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__16;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Nonrec_mkEqns___closed__2;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__14;
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__4;
lean_object* l_Lean_Option_set___at_Lean_Meta_getEqnsFor_x3f___spec__1(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_mkEqnTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__2;
static uint32_t l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__6;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__6;
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__5;
extern lean_object* l_Lean_Meta_eqnThmSuffixBase;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__3;
lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__18;
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__13;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_backward_eqns_nonrecursive;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__19;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__10;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__11;
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553____closed__1;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__15;
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__2___closed__1;
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__7;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__3;
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 2);
lean_dec(x_15);
x_16 = lean_box(0);
lean_inc(x_14);
x_17 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_14, x_16);
x_18 = l_Lean_Expr_const___override(x_13, x_17);
x_19 = l_Lean_mkAppN(x_18, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_20 = l_Lean_Meta_mkEq(x_19, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
x_24 = 1;
x_25 = 1;
lean_inc(x_4);
x_26 = l_Lean_Meta_mkForallFVars(x_4, x_21, x_23, x_24, x_25, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Meta_mkEqRefl(x_19, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_mkLambdaFVars(x_4, x_30, x_23, x_24, x_23, x_25, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Name_append(x_2, x_3);
lean_inc(x_35);
lean_ctor_set(x_11, 2, x_27);
lean_ctor_set(x_11, 0, x_35);
lean_inc(x_35);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_16);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_addDecl(x_38, x_8, x_9, x_34);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_35);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_27);
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_27);
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_26);
if (x_58 == 0)
{
return x_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_26, 0);
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_26);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_20);
if (x_62 == 0)
{
return x_20;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_20, 0);
x_64 = lean_ctor_get(x_20, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_20);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
x_68 = lean_box(0);
lean_inc(x_67);
x_69 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_67, x_68);
x_70 = l_Lean_Expr_const___override(x_66, x_69);
x_71 = l_Lean_mkAppN(x_70, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_71);
x_72 = l_Lean_Meta_mkEq(x_71, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = 0;
x_76 = 1;
x_77 = 1;
lean_inc(x_4);
x_78 = l_Lean_Meta_mkForallFVars(x_4, x_73, x_75, x_76, x_77, x_6, x_7, x_8, x_9, x_74);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_81 = l_Lean_Meta_mkEqRefl(x_71, x_6, x_7, x_8, x_9, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_mkLambdaFVars(x_4, x_82, x_75, x_76, x_75, x_77, x_6, x_7, x_8, x_9, x_83);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Name_append(x_2, x_3);
lean_inc(x_87);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_67);
lean_ctor_set(x_88, 2, x_79);
lean_inc(x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_68);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_89);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_addDecl(x_91, x_8, x_9, x_86);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_87);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_87);
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_79);
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_ctor_get(x_84, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_84, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_103 = x_84;
} else {
 lean_dec_ref(x_84);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_79);
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_ctor_get(x_81, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_81, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_107 = x_81;
} else {
 lean_dec_ref(x_81);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_ctor_get(x_78, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_78, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_111 = x_78;
} else {
 lean_dec_ref(x_78);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_ctor_get(x_72, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_72, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_115 = x_72;
} else {
 lean_dec_ref(x_72);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_free_object(x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm___lambda__1), 10, 3);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
x_19 = 1;
x_20 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_11);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = lean_environment_find(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm___lambda__1), 10, 3);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_2);
x_32 = 1;
x_33 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_30, x_31, x_32, x_3, x_4, x_5, x_6, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_10 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
static uint32_t _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__4;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__6;
x_3 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__10() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__1;
x_4 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__2;
x_5 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
x_6 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__9;
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint32(x_9, sizeof(void*)*5, x_4);
lean_ctor_set_uint32(x_9, sizeof(void*)*5 + 4, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*5 + 8, x_8);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__14() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__13;
x_3 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__12;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8;
x_2 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__14;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__11;
x_2 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_135 = lean_ctor_get(x_4, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_4, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_4, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_4, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_4, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_4, 5);
lean_inc(x_140);
x_141 = !lean_is_exclusive(x_135);
if (x_141 == 0)
{
uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; 
x_142 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_143 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_144 = lean_ctor_get_uint8(x_135, 9);
x_145 = 0;
x_146 = l_Lean_Meta_TransparencyMode_lt(x_144, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_147, 0, x_135);
lean_ctor_set(x_147, 1, x_136);
lean_ctor_set(x_147, 2, x_137);
lean_ctor_set(x_147, 3, x_138);
lean_ctor_set(x_147, 4, x_139);
lean_ctor_set(x_147, 5, x_140);
lean_ctor_set_uint8(x_147, sizeof(void*)*6, x_142);
lean_ctor_set_uint8(x_147, sizeof(void*)*6 + 1, x_143);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_148 = l_Lean_Elab_Eqns_tryURefl(x_1, x_147, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_9 = x_151;
x_10 = x_150;
goto block_134;
}
else
{
uint8_t x_152; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_148);
if (x_152 == 0)
{
return x_148;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_148, 0);
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_148);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_ctor_set_uint8(x_135, 9, x_145);
x_156 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_156, 0, x_135);
lean_ctor_set(x_156, 1, x_136);
lean_ctor_set(x_156, 2, x_137);
lean_ctor_set(x_156, 3, x_138);
lean_ctor_set(x_156, 4, x_139);
lean_ctor_set(x_156, 5, x_140);
lean_ctor_set_uint8(x_156, sizeof(void*)*6, x_142);
lean_ctor_set_uint8(x_156, sizeof(void*)*6 + 1, x_143);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_157 = l_Lean_Elab_Eqns_tryURefl(x_1, x_156, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_unbox(x_158);
lean_dec(x_158);
x_9 = x_160;
x_10 = x_159;
goto block_134;
}
else
{
uint8_t x_161; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_157);
if (x_161 == 0)
{
return x_157;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_157, 0);
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_157);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
else
{
uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; 
x_165 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_166 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_167 = lean_ctor_get_uint8(x_135, 0);
x_168 = lean_ctor_get_uint8(x_135, 1);
x_169 = lean_ctor_get_uint8(x_135, 2);
x_170 = lean_ctor_get_uint8(x_135, 3);
x_171 = lean_ctor_get_uint8(x_135, 4);
x_172 = lean_ctor_get_uint8(x_135, 5);
x_173 = lean_ctor_get_uint8(x_135, 6);
x_174 = lean_ctor_get_uint8(x_135, 7);
x_175 = lean_ctor_get_uint8(x_135, 8);
x_176 = lean_ctor_get_uint8(x_135, 9);
x_177 = lean_ctor_get_uint8(x_135, 10);
x_178 = lean_ctor_get_uint8(x_135, 11);
x_179 = lean_ctor_get_uint8(x_135, 12);
lean_dec(x_135);
x_180 = 0;
x_181 = l_Lean_Meta_TransparencyMode_lt(x_176, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_182, 0, x_167);
lean_ctor_set_uint8(x_182, 1, x_168);
lean_ctor_set_uint8(x_182, 2, x_169);
lean_ctor_set_uint8(x_182, 3, x_170);
lean_ctor_set_uint8(x_182, 4, x_171);
lean_ctor_set_uint8(x_182, 5, x_172);
lean_ctor_set_uint8(x_182, 6, x_173);
lean_ctor_set_uint8(x_182, 7, x_174);
lean_ctor_set_uint8(x_182, 8, x_175);
lean_ctor_set_uint8(x_182, 9, x_176);
lean_ctor_set_uint8(x_182, 10, x_177);
lean_ctor_set_uint8(x_182, 11, x_178);
lean_ctor_set_uint8(x_182, 12, x_179);
x_183 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_136);
lean_ctor_set(x_183, 2, x_137);
lean_ctor_set(x_183, 3, x_138);
lean_ctor_set(x_183, 4, x_139);
lean_ctor_set(x_183, 5, x_140);
lean_ctor_set_uint8(x_183, sizeof(void*)*6, x_165);
lean_ctor_set_uint8(x_183, sizeof(void*)*6 + 1, x_166);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_184 = l_Lean_Elab_Eqns_tryURefl(x_1, x_183, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_unbox(x_185);
lean_dec(x_185);
x_9 = x_187;
x_10 = x_186;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_190 = x_184;
} else {
 lean_dec_ref(x_184);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_192, 0, x_167);
lean_ctor_set_uint8(x_192, 1, x_168);
lean_ctor_set_uint8(x_192, 2, x_169);
lean_ctor_set_uint8(x_192, 3, x_170);
lean_ctor_set_uint8(x_192, 4, x_171);
lean_ctor_set_uint8(x_192, 5, x_172);
lean_ctor_set_uint8(x_192, 6, x_173);
lean_ctor_set_uint8(x_192, 7, x_174);
lean_ctor_set_uint8(x_192, 8, x_175);
lean_ctor_set_uint8(x_192, 9, x_180);
lean_ctor_set_uint8(x_192, 10, x_177);
lean_ctor_set_uint8(x_192, 11, x_178);
lean_ctor_set_uint8(x_192, 12, x_179);
x_193 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_136);
lean_ctor_set(x_193, 2, x_137);
lean_ctor_set(x_193, 3, x_138);
lean_ctor_set(x_193, 4, x_139);
lean_ctor_set(x_193, 5, x_140);
lean_ctor_set_uint8(x_193, sizeof(void*)*6, x_165);
lean_ctor_set_uint8(x_193, sizeof(void*)*6 + 1, x_166);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_194 = l_Lean_Elab_Eqns_tryURefl(x_1, x_193, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_9 = x_197;
x_10 = x_196;
goto block_134;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_200 = x_194;
} else {
 lean_dec_ref(x_194);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
block_134:
{
if (x_9 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_Elab_Eqns_tryContradiction(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_15 = l_Lean_Elab_Eqns_simpMatch_x3f(x_1, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Lean_Elab_Eqns_simpIf_x3f(x_1, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_21 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_1, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__10;
x_26 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
x_27 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__16;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_28 = l_Lean_Meta_simpTargetStar(x_1, x_25, x_26, x_24, x_27, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
switch (lean_obj_tag(x_30)) {
case 0:
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_38 = l_Lean_Meta_casesOnStuckLHS_x3f(x_1, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_42 = l_Lean_Meta_splitTarget_x3f(x_1, x_41, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_MessageData_ofName(x_2);
x_46 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__18;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__20;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_1);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_53, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = l_List_forM___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__1(x_2, x_56, x_4, x_5, x_6, x_7, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_42);
if (x_58 == 0)
{
return x_42;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_42, 0);
x_60 = lean_ctor_get(x_42, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_42);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_38);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_38, 1);
x_64 = lean_ctor_get(x_38, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
lean_dec(x_39);
x_66 = lean_array_get_size(x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_lt(x_67, x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_69 = lean_box(0);
lean_ctor_set(x_38, 0, x_69);
return x_38;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_66, x_66);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_71 = lean_box(0);
lean_ctor_set(x_38, 0, x_71);
return x_38;
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_38);
x_72 = 0;
x_73 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_74 = lean_box(0);
x_75 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__2(x_2, x_65, x_72, x_73, x_74, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_65);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_38, 1);
lean_inc(x_76);
lean_dec(x_38);
x_77 = lean_ctor_get(x_39, 0);
lean_inc(x_77);
lean_dec(x_39);
x_78 = lean_array_get_size(x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_lt(x_79, x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_78, x_78);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_76);
return x_85;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = 0;
x_87 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_88 = lean_box(0);
x_89 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__2(x_2, x_77, x_86, x_87, x_88, x_4, x_5, x_6, x_7, x_76);
lean_dec(x_77);
return x_89;
}
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
return x_38;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_38, 0);
x_92 = lean_ctor_get(x_38, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_38);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
default: 
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_94 = lean_ctor_get(x_28, 1);
lean_inc(x_94);
lean_dec(x_28);
x_95 = lean_ctor_get(x_30, 0);
lean_inc(x_95);
lean_dec(x_30);
x_96 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(x_2, x_95, x_4, x_5, x_6, x_7, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_28);
if (x_97 == 0)
{
return x_28;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_28, 0);
x_99 = lean_ctor_get(x_28, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_28);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_101 = lean_ctor_get(x_21, 1);
lean_inc(x_101);
lean_dec(x_21);
x_102 = lean_ctor_get(x_22, 0);
lean_inc(x_102);
lean_dec(x_22);
x_103 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(x_2, x_102, x_4, x_5, x_6, x_7, x_101);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_21);
if (x_104 == 0)
{
return x_21;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_21, 0);
x_106 = lean_ctor_get(x_21, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_21);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_108 = lean_ctor_get(x_18, 1);
lean_inc(x_108);
lean_dec(x_18);
x_109 = lean_ctor_get(x_19, 0);
lean_inc(x_109);
lean_dec(x_19);
x_110 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(x_2, x_109, x_4, x_5, x_6, x_7, x_108);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_18);
if (x_111 == 0)
{
return x_18;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_18, 0);
x_113 = lean_ctor_get(x_18, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_18);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_1);
x_115 = lean_ctor_get(x_15, 1);
lean_inc(x_115);
lean_dec(x_15);
x_116 = lean_ctor_get(x_16, 0);
lean_inc(x_116);
lean_dec(x_16);
x_117 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(x_2, x_116, x_4, x_5, x_6, x_7, x_115);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_15);
if (x_118 == 0)
{
return x_15;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_15, 0);
x_120 = lean_ctor_get(x_15, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_15);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_11);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_11, 0);
lean_dec(x_123);
x_124 = lean_box(0);
lean_ctor_set(x_11, 0, x_124);
return x_11;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_11, 1);
lean_inc(x_125);
lean_dec(x_11);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_11);
if (x_128 == 0)
{
return x_11;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_11, 0);
x_130 = lean_ctor_get(x_11, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_11);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_10);
return x_133;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqns", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__2;
x_3 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("step\n", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4;
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1(x_2, x_1, x_13, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
lean_inc(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__6;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_8, x_21, x_3, x_4, x_5, x_6, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1(x_2, x_1, x_23, x_3, x_4, x_5, x_6, x_24);
lean_dec(x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
lean_inc(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_8, x_31, x_3, x_4, x_5, x_6, x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1(x_2, x_1, x_33, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
lean_inc(x_3);
x_9 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_mvarId_x21(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_MVarId_intros(x_12, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 5);
lean_inc(x_40);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_44 = lean_ctor_get_uint8(x_35, 9);
x_45 = 0;
x_46 = l_Lean_Meta_TransparencyMode_lt(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set(x_47, 4, x_39);
lean_ctor_set(x_47, 5, x_40);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*6 + 1, x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_16);
x_48 = l_Lean_Elab_Eqns_tryURefl(x_16, x_47, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_49);
lean_dec(x_49);
x_17 = x_51;
x_18 = x_50;
goto block_34;
}
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_ctor_set_uint8(x_35, 9, x_45);
x_56 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_56, 0, x_35);
lean_ctor_set(x_56, 1, x_36);
lean_ctor_set(x_56, 2, x_37);
lean_ctor_set(x_56, 3, x_38);
lean_ctor_set(x_56, 4, x_39);
lean_ctor_set(x_56, 5, x_40);
lean_ctor_set_uint8(x_56, sizeof(void*)*6, x_42);
lean_ctor_set_uint8(x_56, sizeof(void*)*6 + 1, x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_16);
x_57 = l_Lean_Elab_Eqns_tryURefl(x_16, x_56, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_17 = x_60;
x_18 = x_59;
goto block_34;
}
else
{
uint8_t x_61; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; 
x_65 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_66 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_67 = lean_ctor_get_uint8(x_35, 0);
x_68 = lean_ctor_get_uint8(x_35, 1);
x_69 = lean_ctor_get_uint8(x_35, 2);
x_70 = lean_ctor_get_uint8(x_35, 3);
x_71 = lean_ctor_get_uint8(x_35, 4);
x_72 = lean_ctor_get_uint8(x_35, 5);
x_73 = lean_ctor_get_uint8(x_35, 6);
x_74 = lean_ctor_get_uint8(x_35, 7);
x_75 = lean_ctor_get_uint8(x_35, 8);
x_76 = lean_ctor_get_uint8(x_35, 9);
x_77 = lean_ctor_get_uint8(x_35, 10);
x_78 = lean_ctor_get_uint8(x_35, 11);
x_79 = lean_ctor_get_uint8(x_35, 12);
lean_dec(x_35);
x_80 = 0;
x_81 = l_Lean_Meta_TransparencyMode_lt(x_76, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_82, 0, x_67);
lean_ctor_set_uint8(x_82, 1, x_68);
lean_ctor_set_uint8(x_82, 2, x_69);
lean_ctor_set_uint8(x_82, 3, x_70);
lean_ctor_set_uint8(x_82, 4, x_71);
lean_ctor_set_uint8(x_82, 5, x_72);
lean_ctor_set_uint8(x_82, 6, x_73);
lean_ctor_set_uint8(x_82, 7, x_74);
lean_ctor_set_uint8(x_82, 8, x_75);
lean_ctor_set_uint8(x_82, 9, x_76);
lean_ctor_set_uint8(x_82, 10, x_77);
lean_ctor_set_uint8(x_82, 11, x_78);
lean_ctor_set_uint8(x_82, 12, x_79);
x_83 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_36);
lean_ctor_set(x_83, 2, x_37);
lean_ctor_set(x_83, 3, x_38);
lean_ctor_set(x_83, 4, x_39);
lean_ctor_set(x_83, 5, x_40);
lean_ctor_set_uint8(x_83, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_83, sizeof(void*)*6 + 1, x_66);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_16);
x_84 = l_Lean_Elab_Eqns_tryURefl(x_16, x_83, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_17 = x_87;
x_18 = x_86;
goto block_34;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_90 = x_84;
} else {
 lean_dec_ref(x_84);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_92, 0, x_67);
lean_ctor_set_uint8(x_92, 1, x_68);
lean_ctor_set_uint8(x_92, 2, x_69);
lean_ctor_set_uint8(x_92, 3, x_70);
lean_ctor_set_uint8(x_92, 4, x_71);
lean_ctor_set_uint8(x_92, 5, x_72);
lean_ctor_set_uint8(x_92, 6, x_73);
lean_ctor_set_uint8(x_92, 7, x_74);
lean_ctor_set_uint8(x_92, 8, x_75);
lean_ctor_set_uint8(x_92, 9, x_80);
lean_ctor_set_uint8(x_92, 10, x_77);
lean_ctor_set_uint8(x_92, 11, x_78);
lean_ctor_set_uint8(x_92, 12, x_79);
x_93 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_36);
lean_ctor_set(x_93, 2, x_37);
lean_ctor_set(x_93, 3, x_38);
lean_ctor_set(x_93, 4, x_39);
lean_ctor_set(x_93, 5, x_40);
lean_ctor_set_uint8(x_93, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_93, sizeof(void*)*6 + 1, x_66);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_16);
x_94 = l_Lean_Elab_Eqns_tryURefl(x_16, x_93, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unbox(x_95);
lean_dec(x_95);
x_17 = x_97;
x_18 = x_96;
goto block_34;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_100 = x_94;
} else {
 lean_dec_ref(x_94);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
block_34:
{
if (x_17 == 0)
{
lean_object* x_19; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Eqns_deltaLHS(x_16, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go(x_2, x_20, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_10, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_2);
x_33 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_10, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_13);
if (x_102 == 0)
{
return x_13;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_13, 0);
x_104 = lean_ctor_get(x_13, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_13);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__2), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = 0;
x_11 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proving: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4;
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3(x_2, x_1, x_13, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
lean_inc(x_2);
x_18 = l_Lean_MessageData_ofExpr(x_2);
x_19 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__2;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_8, x_21, x_3, x_4, x_5, x_6, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3(x_2, x_1, x_23, x_3, x_4, x_5, x_6, x_24);
lean_dec(x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
lean_inc(x_2);
x_27 = l_Lean_MessageData_ofExpr(x_2);
x_28 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_8, x_31, x_3, x_4, x_5, x_6, x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3(x_2, x_1, x_33, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(x_1);
x_14 = l_Lean_Name_str___override(x_1, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = lean_name_append_index_after(x_14, x_16);
lean_inc(x_17);
x_18 = lean_array_push(x_6, x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
x_19 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof(x_1, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(x_3, x_20, x_10, x_11, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
x_30 = lean_ctor_get(x_24, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_24, 0);
lean_dec(x_31);
lean_inc(x_17);
lean_ctor_set(x_24, 2, x_28);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 0, x_17);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_23);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_addDecl(x_33, x_10, x_11, x_25);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_18);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_18);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_dec(x_24);
lean_inc(x_17);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 0, x_17);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_23);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_addDecl(x_50, x_10, x_11, x_25);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_18);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_18);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_58 = x_51;
} else {
 lean_dec_ref(x_51);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_23, 0);
x_61 = lean_ctor_get(x_23, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_23);
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_63 = x_24;
} else {
 lean_dec_ref(x_24);
 x_63 = lean_box(0);
}
lean_inc(x_17);
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 3, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_17);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_17);
lean_ctor_set(x_65, 1, x_5);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_addDecl(x_67, x_10, x_11, x_25);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_18);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_18);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_19);
if (x_77 == 0)
{
return x_19;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_19, 0);
x_79 = lean_ctor_get(x_19, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_19);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqnType[", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_8, x_7);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_74; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_6, x_19);
lean_dec(x_6);
x_21 = lean_nat_dec_lt(x_7, x_5);
x_22 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4;
x_74 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_22, x_11, x_12, x_13, x_14, x_15);
if (x_21 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_instInhabitedExpr;
x_78 = l_outOfBounds___rarg(x_77);
x_79 = lean_unbox(x_75);
lean_dec(x_75);
x_23 = x_78;
x_24 = x_79;
x_25 = x_76;
goto block_73;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_array_fget(x_3, x_7);
x_83 = lean_unbox(x_80);
lean_dec(x_80);
x_23 = x_82;
x_24 = x_83;
x_25 = x_81;
goto block_73;
}
block_73:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___lambda__1(x_1, x_7, x_23, x_2, x_4, x_10, x_26, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_37;
x_10 = x_36;
x_15 = x_35;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_7);
x_43 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_MessageData_ofFormat(x_44);
x_46 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_23);
x_50 = l_Lean_MessageData_ofExpr(x_23);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_22, x_53, x_11, x_12, x_13, x_14, x_25);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___lambda__1(x_1, x_7, x_23, x_2, x_4, x_10, x_55, x_11, x_12, x_13, x_14, x_56);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_67;
x_10 = x_66;
x_15 = x_65;
goto _start;
}
}
else
{
uint8_t x_69; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_57);
if (x_69 == 0)
{
return x_57;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_57, 0);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_57);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_10);
lean_ctor_set(x_84, 1, x_15);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_10);
lean_ctor_set(x_85, 1, x_15);
return x_85;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_11, x_12);
x_14 = l_Lean_Expr_const___override(x_2, x_13);
x_15 = l_Lean_mkAppN(x_14, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_mkEq(x_15, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_5);
x_20 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_19, x_5, x_6, x_7, x_8, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 2;
lean_ctor_set_uint8(x_25, 9, x_27);
x_28 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
x_29 = l_Lean_Elab_Eqns_mkEqnTypes(x_28, x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get_uint8(x_25, 0);
x_39 = lean_ctor_get_uint8(x_25, 1);
x_40 = lean_ctor_get_uint8(x_25, 2);
x_41 = lean_ctor_get_uint8(x_25, 3);
x_42 = lean_ctor_get_uint8(x_25, 4);
x_43 = lean_ctor_get_uint8(x_25, 5);
x_44 = lean_ctor_get_uint8(x_25, 6);
x_45 = lean_ctor_get_uint8(x_25, 7);
x_46 = lean_ctor_get_uint8(x_25, 8);
x_47 = lean_ctor_get_uint8(x_25, 10);
x_48 = lean_ctor_get_uint8(x_25, 11);
x_49 = lean_ctor_get_uint8(x_25, 12);
lean_dec(x_25);
x_50 = 2;
x_51 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_51, 0, x_38);
lean_ctor_set_uint8(x_51, 1, x_39);
lean_ctor_set_uint8(x_51, 2, x_40);
lean_ctor_set_uint8(x_51, 3, x_41);
lean_ctor_set_uint8(x_51, 4, x_42);
lean_ctor_set_uint8(x_51, 5, x_43);
lean_ctor_set_uint8(x_51, 6, x_44);
lean_ctor_set_uint8(x_51, 7, x_45);
lean_ctor_set_uint8(x_51, 8, x_46);
lean_ctor_set_uint8(x_51, 9, x_50);
lean_ctor_set_uint8(x_51, 10, x_47);
lean_ctor_set_uint8(x_51, 11, x_48);
lean_ctor_set_uint8(x_51, 12, x_49);
lean_ctor_set(x_5, 0, x_51);
x_52 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
x_53 = l_Lean_Elab_Eqns_mkEqnTypes(x_52, x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_62 = lean_ctor_get(x_5, 0);
x_63 = lean_ctor_get(x_5, 1);
x_64 = lean_ctor_get(x_5, 2);
x_65 = lean_ctor_get(x_5, 3);
x_66 = lean_ctor_get(x_5, 4);
x_67 = lean_ctor_get(x_5, 5);
x_68 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_5);
x_70 = lean_ctor_get_uint8(x_62, 0);
x_71 = lean_ctor_get_uint8(x_62, 1);
x_72 = lean_ctor_get_uint8(x_62, 2);
x_73 = lean_ctor_get_uint8(x_62, 3);
x_74 = lean_ctor_get_uint8(x_62, 4);
x_75 = lean_ctor_get_uint8(x_62, 5);
x_76 = lean_ctor_get_uint8(x_62, 6);
x_77 = lean_ctor_get_uint8(x_62, 7);
x_78 = lean_ctor_get_uint8(x_62, 8);
x_79 = lean_ctor_get_uint8(x_62, 10);
x_80 = lean_ctor_get_uint8(x_62, 11);
x_81 = lean_ctor_get_uint8(x_62, 12);
if (lean_is_exclusive(x_62)) {
 x_82 = x_62;
} else {
 lean_dec_ref(x_62);
 x_82 = lean_box(0);
}
x_83 = 2;
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 0, 13);
} else {
 x_84 = x_82;
}
lean_ctor_set_uint8(x_84, 0, x_70);
lean_ctor_set_uint8(x_84, 1, x_71);
lean_ctor_set_uint8(x_84, 2, x_72);
lean_ctor_set_uint8(x_84, 3, x_73);
lean_ctor_set_uint8(x_84, 4, x_74);
lean_ctor_set_uint8(x_84, 5, x_75);
lean_ctor_set_uint8(x_84, 6, x_76);
lean_ctor_set_uint8(x_84, 7, x_77);
lean_ctor_set_uint8(x_84, 8, x_78);
lean_ctor_set_uint8(x_84, 9, x_83);
lean_ctor_set_uint8(x_84, 10, x_79);
lean_ctor_set_uint8(x_84, 11, x_80);
lean_ctor_set_uint8(x_84, 12, x_81);
x_85 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_63);
lean_ctor_set(x_85, 2, x_64);
lean_ctor_set(x_85, 3, x_65);
lean_ctor_set(x_85, 4, x_66);
lean_ctor_set(x_85, 5, x_67);
lean_ctor_set_uint8(x_85, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_85, sizeof(void*)*6 + 1, x_69);
x_86 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
x_87 = l_Lean_Elab_Eqns_mkEqnTypes(x_86, x_23, x_85, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_96 = !lean_is_exclusive(x_16);
if (x_96 == 0)
{
return x_16;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_16, 0);
x_98 = lean_ctor_get(x_16, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_16);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_mkEqns___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 4);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_dec(x_14);
x_15 = l_Lean_Elab_Nonrec_mkEqns___lambda__2___closed__1;
x_16 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_15);
lean_ctor_set(x_9, 4, x_16);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*12, x_2);
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_3, x_17, x_4, x_5, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_array_get_size(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
lean_inc(x_22);
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1(x_6, x_7, x_19, x_21, x_22, x_22, x_23, x_22, x_24, x_25, x_4, x_5, x_9, x_10, x_20);
lean_dec(x_22);
lean_dec(x_19);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 3);
x_42 = lean_ctor_get(x_9, 5);
x_43 = lean_ctor_get(x_9, 6);
x_44 = lean_ctor_get(x_9, 7);
x_45 = lean_ctor_get(x_9, 8);
x_46 = lean_ctor_get(x_9, 9);
x_47 = lean_ctor_get(x_9, 10);
x_48 = lean_ctor_get(x_9, 11);
x_49 = lean_ctor_get_uint8(x_9, sizeof(void*)*12 + 1);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_50 = l_Lean_Elab_Nonrec_mkEqns___lambda__2___closed__1;
x_51 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_50);
x_52 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_40);
lean_ctor_set(x_52, 2, x_1);
lean_ctor_set(x_52, 3, x_41);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_42);
lean_ctor_set(x_52, 6, x_43);
lean_ctor_set(x_52, 7, x_44);
lean_ctor_set(x_52, 8, x_45);
lean_ctor_set(x_52, 9, x_46);
lean_ctor_set(x_52, 10, x_47);
lean_ctor_set(x_52, 11, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_52, sizeof(void*)*12 + 1, x_49);
x_53 = 0;
lean_inc(x_10);
lean_inc(x_52);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_3, x_53, x_4, x_5, x_52, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = lean_array_get_size(x_55);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_unsigned_to_nat(1u);
x_61 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3;
lean_inc(x_58);
x_62 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1(x_6, x_7, x_55, x_57, x_58, x_58, x_59, x_58, x_60, x_61, x_4, x_5, x_52, x_10, x_56);
lean_dec(x_58);
lean_dec(x_55);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = lean_ctor_get(x_54, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_73 = x_54;
} else {
 lean_dec_ref(x_54);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_mkEqns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_mkEqns___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_mkEqns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Nonrec_mkEqns___lambda__1___boxed), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg___boxed), 8, 3);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
x_14 = l_Lean_Elab_Nonrec_mkEqns___closed__1;
x_15 = 0;
x_16 = l_Lean_Option_set___at_Lean_Meta_getEqnsFor_x3f___spec__1(x_13, x_14, x_15);
x_17 = l_Lean_Elab_Nonrec_mkEqns___closed__2;
x_18 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_16, x_17);
x_19 = lean_st_ref_get(x_6, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Kernel_isDiagnosticsEnabled(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_18 == 0)
{
x_24 = x_10;
goto block_52;
}
else
{
x_24 = x_15;
goto block_52;
}
}
else
{
if (x_18 == 0)
{
x_24 = x_15;
goto block_52;
}
else
{
x_24 = x_10;
goto block_52;
}
}
block_52:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_st_ref_take(x_6, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 4);
lean_dec(x_30);
x_31 = l_Lean_Kernel_enableDiag(x_29, x_18);
x_32 = l_Lean_Elab_Nonrec_mkEqns___closed__3;
lean_ctor_set(x_26, 4, x_32);
lean_ctor_set(x_26, 0, x_31);
x_33 = lean_st_ref_set(x_6, x_26, x_27);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Nonrec_mkEqns___lambda__2(x_16, x_18, x_12, x_3, x_4, x_1, x_2, x_35, x_5, x_6, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_26, 2);
x_40 = lean_ctor_get(x_26, 3);
x_41 = lean_ctor_get(x_26, 5);
x_42 = lean_ctor_get(x_26, 6);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_43 = l_Lean_Kernel_enableDiag(x_37, x_18);
x_44 = l_Lean_Elab_Nonrec_mkEqns___closed__3;
x_45 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_39);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_41);
lean_ctor_set(x_45, 6, x_42);
x_46 = lean_st_ref_set(x_6, x_45, x_27);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Nonrec_mkEqns___lambda__2(x_16, x_18, x_12, x_3, x_4, x_1, x_2, x_48, x_5, x_6, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l_Lean_Elab_Nonrec_mkEqns___lambda__2(x_16, x_18, x_12, x_3, x_4, x_1, x_2, x_50, x_5, x_6, x_21);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Nonrec_mkEqns___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_mkEqns___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Nonrec_mkEqns___lambda__2(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_backward_eqns_nonrecursive;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_unfoldThmSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_5, 2);
lean_inc(x_18);
x_19 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1;
x_20 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_free_object(x_13);
x_21 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2;
x_22 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm(x_1, x_21, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3;
x_35 = lean_array_push(x_34, x_33);
lean_ctor_set(x_23, 0, x_35);
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3;
x_38 = lean_array_push(x_37, x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
x_43 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3;
x_44 = lean_array_push(x_43, x_41);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
return x_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
x_51 = l_Lean_Elab_Nonrec_mkEqns(x_1, x_17, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_ctor_set(x_13, 0, x_53);
lean_ctor_set(x_51, 0, x_13);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set(x_13, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_13);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_13);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_box(0);
lean_ctor_set(x_8, 0, x_61);
return x_8;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_13, 0);
lean_inc(x_62);
lean_dec(x_13);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_free_object(x_8);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_5, 2);
lean_inc(x_64);
x_65 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1;
x_66 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_67 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2;
x_68 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm(x_1, x_67, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3;
x_79 = lean_array_push(x_78, x_76);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_84 = x_68;
} else {
 lean_dec_ref(x_68);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; 
x_86 = l_Lean_Elab_Nonrec_mkEqns(x_1, x_63, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_87);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_94 = x_86;
} else {
 lean_dec_ref(x_86);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_box(0);
lean_ctor_set(x_8, 0, x_96);
return x_8;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_8, 0);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_8);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_1);
x_100 = lean_environment_find(x_99, x_1);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
if (lean_obj_tag(x_103) == 1)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_5, 2);
lean_inc(x_106);
x_107 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1;
x_108 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_106, x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_105);
lean_dec(x_104);
x_109 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2;
x_110 = l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkSimpleEqThm(x_1, x_109, x_3, x_4, x_5, x_6, x_98);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_119 = x_111;
} else {
 lean_dec_ref(x_111);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3;
x_121 = lean_array_push(x_120, x_118);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_121);
if (lean_is_scalar(x_117)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_117;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_116);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_110, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_110, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_126 = x_110;
} else {
 lean_dec_ref(x_110);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; 
x_128 = l_Lean_Elab_Nonrec_mkEqns(x_1, x_105, x_3, x_4, x_5, x_6, x_98);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_104;
}
lean_ctor_set(x_132, 0, x_129);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_104);
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_98);
return x_139;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_7 = l_Lean_Meta_isRecursiveDefinition(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1(x_1, x_11, x_2, x_3, x_4, x_5, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Nonrec_getEqnsFor_x3f), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553____closed__1;
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ArgsPacker_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Nonrec_Eqns(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__2();
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__5);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__6);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__7);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__8);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__9);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__10);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__11);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__12);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__13 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__13);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__14);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__15 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__15);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__16 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__16);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__17 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__17);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__18 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__18();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__18);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__19 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__19();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__19);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__20 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__20();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__20);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__21 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__21();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__21);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___lambda__1___closed__22);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__1);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__2);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__3);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__4);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__5);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof_go___closed__6);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__1);
l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Nonrec_Eqns_0__Lean_Elab_Nonrec_mkProof___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__3);
l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Nonrec_mkEqns___spec__1___closed__4);
l_Lean_Elab_Nonrec_mkEqns___lambda__2___closed__1 = _init_l_Lean_Elab_Nonrec_mkEqns___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Nonrec_mkEqns___lambda__2___closed__1);
l_Lean_Elab_Nonrec_mkEqns___closed__1 = _init_l_Lean_Elab_Nonrec_mkEqns___closed__1();
lean_mark_persistent(l_Lean_Elab_Nonrec_mkEqns___closed__1);
l_Lean_Elab_Nonrec_mkEqns___closed__2 = _init_l_Lean_Elab_Nonrec_mkEqns___closed__2();
lean_mark_persistent(l_Lean_Elab_Nonrec_mkEqns___closed__2);
l_Lean_Elab_Nonrec_mkEqns___closed__3 = _init_l_Lean_Elab_Nonrec_mkEqns___closed__3();
lean_mark_persistent(l_Lean_Elab_Nonrec_mkEqns___closed__3);
l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1 = _init_l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__1);
l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2 = _init_l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__2);
l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3 = _init_l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Nonrec_getEqnsFor_x3f___lambda__1___closed__3);
l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553____closed__1 = _init_l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553____closed__1();
lean_mark_persistent(l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553____closed__1);
if (builtin) {res = l_Lean_Elab_Nonrec_initFn____x40_Lean_Elab_PreDefinition_Nonrec_Eqns___hyg_1553_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
