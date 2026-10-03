// Lean compiler output
// Module: Main
// Imports: public import Init public meta import Init
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tlmc057_part(lean_object*);
LEAN_EXPORT lean_object* lp_tlmc057_part___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tlmc057_adj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tlmc057_adj___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tlmc057_partAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tlmc057_partAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tlmc057_part(lean_object* v_v_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_2_ = lean_unsigned_to_nat(6u);
v___x_3_ = lean_nat_mod(v_v_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(3u);
v___x_5_ = lean_nat_dec_lt(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tlmc057_part___boxed(lean_object* v_v_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lp_tlmc057_part(v_v_6_);
lean_dec(v_v_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT uint8_t lp_tlmc057_adj(lean_object* v_v_9_, lean_object* v_w_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; uint8_t v___y_16_; 
v___x_11_ = lean_unsigned_to_nat(6u);
v___x_12_ = lean_nat_div(v_v_9_, v___x_11_);
v___x_13_ = lean_nat_div(v_w_10_, v___x_11_);
v___x_14_ = lean_nat_dec_eq(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_12_);
if (v___x_14_ == 0)
{
return v___x_14_;
}
else
{
uint8_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = lp_tlmc057_part(v_v_9_);
v___x_19_ = lp_tlmc057_part(v_w_10_);
if (v___x_18_ == 0)
{
if (v___x_19_ == 0)
{
v___y_16_ = v___x_14_;
goto v___jp_15_;
}
else
{
v___y_16_ = v___x_18_;
goto v___jp_15_;
}
}
else
{
v___y_16_ = v___x_19_;
goto v___jp_15_;
}
}
v___jp_15_:
{
if (v___y_16_ == 0)
{
return v___x_14_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = 0;
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tlmc057_adj___boxed(lean_object* v_v_20_, lean_object* v_w_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = lp_tlmc057_adj(v_v_20_, v_w_21_);
lean_dec(v_w_21_);
lean_dec(v_v_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t lp_tlmc057_partAt(lean_object* v_l_24_, lean_object* v_i_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_26_ = l_List_lengthTR___redArg(v_l_24_);
v___x_27_ = lean_nat_mod(v_i_25_, v___x_26_);
lean_dec(v___x_26_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = l_List_getD___redArg(v_l_24_, v___x_27_, v___x_28_);
v___x_30_ = lp_tlmc057_part(v___x_29_);
lean_dec(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tlmc057_partAt___boxed(lean_object* v_l_31_, lean_object* v_i_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = lp_tlmc057_partAt(v_l_31_, v_i_32_);
lean_dec(v_i_32_);
lean_dec(v_l_31_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tlmc057_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
