header {* Compiling high-level programs to low-level programs *}

theory RSP_compiler imports 
  RSP_high_level_PL
  RSP_low_level_PL
begin
    
type_synonym L_ins_monad = "register \<Rightarrow> (register \<times> L_ins list)"

datatype version = Old | New

fun compile_expr :: "version \<Rightarrow> H_expr \<Rightarrow> L_ins_monad"
where
  "compile_expr _ (Const n) r = (r, [IMM r n])"
 
| "compile_expr V (e1 +\<^sub>\<H> e2) r = (
  let (r',inss1) = compile_expr V e1 r in 
  let (r'',inss2) = compile_expr V e2 (next_reg r') in 
  (next_reg r'', inss1 @ inss2 @ [ADD (next_reg r'') r' r'']))"
  
| "compile_expr V (atomic_load (x, S_wi, _)) r = (r, 
  [LD r x (* do the actual load *)])"

| "compile_expr V (atomic_load (x, S_wg, _)) r = (r, 
  [LD r x (* do the actual load *)])"

| "compile_expr Old (atomic_load (x, S_dv, Normal)) r = (r,
  (* NB: This implementation leads to a confirmed bug in AMD's proposal. *)
  [CAC (INVAL_L1, S_wg) (* invalidate my L1 cache *),
  LD r x (* do the actual load *)])"

| "compile_expr New (atomic_load (x, S_dv, Normal)) r = (r, 
  [LD r x (* do the actual load *), 
   CAC (INVAL_L1, S_wg) (* invalidate my L1 cache *)])"   

| "compile_expr Old (atomic_load (x, S_sy, Normal)) r = 
  undefined (* not included in this formalisation *)"
   
| "compile_expr New (atomic_load (x, S_sy, Normal)) r = 
  undefined (* not included in this formalisation *)"
 
| "compile_expr Old (atomic_load (x, S_dv, Remote)) r = (r, 
  [LK x, (* lock x's cacheline in L2 *)
   CAC (FLUSH_L1, S_dv) (* flush all the L1 caches in my device *), 
   CAC (INVAL_L1, S_wg) (* invalidate my L1 cache *),
   LD r x (* do the actual load *),
   UNLK x (* release x's cacheline *)])"
   
| "compile_expr New (atomic_load (x, S_dv, Remote)) r = (r, 
  [LD r x (* do the actual load *), 
   CAC (FLUSH_L1, S_dv) (* flush all the L1 caches in my device *), 
   CAC (INVAL_L1, S_wg) (* invalidate my L1 cache *)])"

| "compile_expr Old (atomic_load (x, S_sy, Remote)) r = 
  undefined (* not included in this formalisation *)"
   
| "compile_expr New (atomic_load (x, S_sy, Remote)) r = 
  undefined (* not included in this formalisation *)"
   
| "compile_expr _ (atomic_inc (x, S_wi, _)) r = 
  undefined (* can't have non-atomic RMW *)"

| "compile_expr Old (atomic_inc (x, S_wg, _)) r = (r, 
  [INC_L1 r x (* do the actual rmw on the L1 cache *)])"

| "compile_expr New (atomic_inc (x, S_wg, _)) r = (r, 
  [INC_L1 r x (* do the actual rmw on the L1 cache *)])"

| "compile_expr Old (atomic_inc (x, S_dv, Normal)) r = (r, 
  (* NB: This implementation (INVAL before INC) leads to a confirmed bug in
  AMD's proposal. *)
  [CAC (FLUSH_L1, S_wg) (* flush my L1 cache *),
   CAC (INVAL_L1, S_wg) (* invalidate my L1 cache *),
   INC_L2 r x (* do the actual rmw on the L2 cache *)])"

| "compile_expr New (atomic_inc (x, S_dv, Normal)) r = (r, 
  [CAC (FLUSH_L1, S_wg) (* flush my L1 cache *),
   INC_L2 r x (* do the actual rmw on the L2 cache *), 
   CAC (INVAL_L1, S_wg) (* invalidate my L1 cache *)])"
   
| "compile_expr Old (atomic_inc (x, S_sy, Normal)) r = 
  undefined (* not included in this formalisation *)"
   
| "compile_expr New (atomic_inc (x, S_sy, Normal)) r = 
  undefined (* not included in this formalisation *)"

| "compile_expr Old (atomic_inc (x, S_dv, Remote)) r = (r, 
  [CAC(LK_rmw, S_dv) (* prevent simultaneous RMWs in my device *),
   LK x (* lock x's cacheline in L2 *),
   CAC (FLUSH_L1, S_dv) (* flush all L1 caches in my device *),
   CAC (INVAL_L1, S_wg) (* flush my L1 cache *),
   INC_L2 r x (* do the actual rmw on the L2 cache *),  
   CAC (INVAL_L1, S_dv) (* invalidate all L1 caches in my device *),
   UNLK x (* release x's cacheline *),
   CAC(UNLK_rmw, S_dv) (* re-enable RMWs *)])"
   
| "compile_expr New (atomic_inc (x, S_dv, Remote)) r = (r, 
  [CAC(LK_rmw, S_dv) (* prevent simultaneous RMWs in my device *),
   CAC (FLUSH_L1, S_wg) (* flush my L1 cache *),
   CAC (INVAL_L1, S_dv) (* invalidate all L1 caches in my device *),
   INC_L2 r x (* do the actual rmw on the L2 cache *), 
   CAC (FLUSH_L1, S_dv) (* flush all L1 caches in my device *), 
   CAC (INVAL_L1, S_wg) (* invalidate my L1 cache *),
   CAC(UNLK_rmw, S_dv) (* re-enable RMWs *)])"

| "compile_expr Old (atomic_inc (x, S_sy, Remote)) r = 
  undefined (* not included in this formalisation *)"   
   
| "compile_expr New (atomic_inc (x, S_sy, Remote)) r = 
  undefined (* not included in this formalisation *)"
 
lemma "compile_expr Old (Const 3 +\<^sub>\<H> Const 4) (Reg 0) = (Reg 2, 
  [IMM (Reg 0) 3, IMM (Reg 1) 4, ADD (Reg 2) (Reg 0) (Reg 1)])"
by simp

fun compile_ins :: "version \<Rightarrow> H_ins \<Rightarrow> L_ins_monad"
and compile_ins_list :: "version \<Rightarrow> H_ins list \<Rightarrow> L_ins_monad"
where
 "compile_ins_list _ [] r = (r, [])"

| "compile_ins_list V (h_ins # h_inss) r = (
  let (r', ins) = compile_ins V h_ins r in
  let (r'',inss) = compile_ins_list V h_inss r' in
  (r'', ins @ inss))"
    
| "compile_ins V (If x h_inss1 h_inss2) r = (
  let (r', inss1) = compile_ins_list V h_inss1 (next_reg r) in
  let (r'', inss2) = compile_ins_list V h_inss2 r' in
  (r'', [ST x r] @ map (IF r True) inss1 @ map (IF r False) inss2))"

| "compile_ins V (atomic_store (x, e, S_wi, _)) r = (
  let (r', inss) = compile_expr V e r in (r', inss @ 
  [ST x r' (* do the actual store *)]))"
  
| "compile_ins V (atomic_store (x, e, S_wg, _)) r = (
  let (r', inss) = compile_expr V e r in (r', inss @ 
  [ST x r' (* do the actual store *)]))"
  
| "compile_ins V (atomic_store (x, e, S_dv, Normal)) r = (
  let (r', inss) = compile_expr V e r in (r', inss @ 
  [CAC (FLUSH_L1, S_wg) (* flush my L1 cache *),
   ST x r' (* do the actual store *)]))" 
  
| "compile_ins Old (atomic_store (x, e, S_sy, Normal)) r = 
  undefined" 
   
| "compile_ins New (atomic_store (x, e, S_sy, Normal)) r = 
  undefined" 
  
| "compile_ins Old (atomic_store (x, e, S_dv, Remote)) r = (
  let (r', inss) = compile_expr Old e r in (r', inss @ 
  [LK x (* lock x's L2 cacheline *),
   CAC (FLUSH_L1, S_wg) (* flush my L1 cache *),
   ST x r' (* do the actual store *),
   CAC (INVAL_L1, S_dv) (* invalidate all L1 caches in my device *),
   UNLK x (* unlock x's L2 cacheline *)]))" 
   
| "compile_ins New (atomic_store (x, e, S_dv, Remote)) r = (
  let (r', inss) = compile_expr New e r in (r', inss @ 
  [CAC (LK_rmw, S_dv) (* prevent simultaneous RMWs in my device *),
   CAC (FLUSH_L1, S_wg) (* flush my L1 cache *),
   CAC (INVAL_L1, S_dv) (* invalidate all L1 caches in my device *),  
   ST x r' (* do the actual store *),
   CAC (UNLK_rmw, S_dv) (* re-enable RMWs *)]))"
  
| "compile_ins Old (atomic_store (x, e, S_sy, Remote)) r = 
  undefined" 
   
| "compile_ins New (atomic_store (x, e, S_sy, Remote)) r = 
  undefined" 
  
fun compile_thd :: "version \<Rightarrow> H_ins thread \<Rightarrow> L_ins thread"
where
  "compile_thd V thd = snd (compile_ins_list V thd (Reg 0))"
  
lemma compiling_example:
  "compile_thd Old [store x (load y +\<^sub>\<H> Const 4)] = 
  [ LD (Reg 0) y, 
    IMM (Reg 1) 4, 
    ADD (Reg 2) (Reg 0) (Reg 1), 
    ST x (Reg 2) ]"
by simp
  
fun compile_prog :: "version \<Rightarrow> H_ins program \<Rightarrow> L_ins program"
where
  "compile_prog V P = map (map (map (compile_thd V))) P"



end

