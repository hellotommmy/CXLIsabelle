header {* Syntax and semantics of high-level programs *}

theory RSP_high_level_PL imports 
  RSP_common
begin

section {* Syntax of high-level programs *}

text {* Remote operations *}
datatype remoteness = Remote | Normal 

text {* High-level expressions and instructions *}

datatype H_expr =
  Const val -- {* Constant *}
| Plus H_expr H_expr (infixr "+\<^sub>\<H>" 65) -- {* Addition *}
| atomic_load "addr \<times> scope \<times> remoteness" -- {* Atomic scoped load-acquire *}
| atomic_inc "addr \<times> scope \<times> remoteness" -- {* Atomic scoped increment *}

(* declare [[coercion Const]] *)

datatype H_ins = 
  atomic_store "addr \<times> H_expr \<times> scope \<times> remoteness" 
    -- {* Atomic scoped store-release *}
| If addr "H_ins list" "H_ins list" -- {* Conditionals *}
(* AD: Consider adding whiles *)

text {* Abbreviations for non-atomic instructions *}
abbreviation "load x \<equiv> atomic_load(x, S_wi, Normal)"
abbreviation "store x e \<equiv> atomic_store(x, e, S_wi, Normal)"

section {* High-level run-time memory events *}

type_synonym H_lbl = "(scope \<times> remoteness, unit) lbl"

text {* A high-level execution *}
type_synonym H_pre_exn = "H_lbl pre_exn"
type_synonym H_exn = "H_lbl exn"
  
section {* Semantics of high-level programs *}

type_synonym 'ret H_pre_exnmonad = 
  "nat (*eid*) \<Rightarrow> (nat (*eid*) \<times> 'ret \<times> H_pre_exn) set"

subsection {* Semantics of expressions *}

fun H_sem_expr :: "dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> H_expr \<Rightarrow> val H_pre_exnmonad"
where
  "H_sem_expr d w t (Const v) e = {(e, v, nil_pre_exn)}"
  
| "H_sem_expr d w t (exp1 +\<^sub>\<H> exp2) e = 
  { (e'', v1 + v2, Xo1 @@ Xo2) | e' e'' Xo1 Xo2 v1 v2.
    (e', v1, Xo1) \<in> H_sem_expr d w t exp1 e \<and> 
    (e'', v2, Xo2) \<in> H_sem_expr d w t exp2 e'}"
    
| "H_sem_expr d w t (atomic_load(x, s, rem)) e = 
  { (e + 1, v, sing_pre_exn (E e) (R x v (s,rem)) d w t) | v. True }"
  
| "H_sem_expr d w t (atomic_inc(x, s, rem)) e = 
  { (e + 1, v, sing_pre_exn (E e) (RMW x v (v+1) (s,rem)) d w t) | v. True }"

subsection {* Semantics of instructions and lists of instructions *}
    
fun H_sem_ins :: "dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> H_ins \<Rightarrow> unit H_pre_exnmonad"
and H_sem_thd :: "dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> H_ins list \<Rightarrow> unit H_pre_exnmonad"
where
  "H_sem_ins d w t (atomic_store(x, exp, s, rem)) e = 
  { (e' + 1, (), Xo @@ sing_pre_exn (E e') (W Noninit x v (s,rem)) d w t) | 
    e' v Xo. (e', v, Xo) \<in> H_sem_expr d w t exp e}"
    
| "H_sem_ins d w t (If x inss1 inss2) e = 
  { (e', (), sing_pre_exn (E e) (R x v (S_wi, Normal)) d w t @@ Xo) | e' v Xo. 
    (e', (), Xo) \<in> H_sem_thd d w t (if v \<noteq> 0 then inss1 else inss2) e }"
      
| "H_sem_thd d w t [] e = { (e, (), nil_pre_exn) }"
      
| "H_sem_thd d w t (ins # inss) e = 
  { (e'', (), Xo1 @@ Xo2) | e' e'' Xo1 Xo2. 
    (e', (), Xo1) \<in> H_sem_ins d w t ins e \<and>
    (e'', (), Xo2) \<in> H_sem_thd d w t inss e' }"

subsection {* Example: a writing thread, a reading thread *}
  
definition [simp]: 
  "my_Wr_thd x y \<equiv> 
  [store x (Const 1), atomic_store(y, (Const 1), S_wg, Normal)]"

definition [simp]: 
  "my_Rd_thd r1 r2 y x \<equiv> 
  [store r1 (atomic_load(y, S_wg, Normal)), store r2 (load x)]"
  
lemma example1:
  "H_sem_thd (Dv 0) (Cu 0) (Pe 0) (my_Wr_thd x y) 0 = { (2, (), \<lparr> 
  events = {E 0, E 1}, 
  lbl = {E 0 \<mapsto> W Noninit x 1 (S_wi, Normal), E 1 \<mapsto> W Noninit y 1 (S_wg, Normal)}, 
  dvid = {E 0 \<mapsto> Dv 0, E 1 \<mapsto> Dv 0}, 
  cuid = {E 0 \<mapsto> Cu 0, E 1 \<mapsto> Cu 0},
  peid = {E 0 \<mapsto> Pe 0, E 1 \<mapsto> Pe 0}, 
  sb = {(E 0, E 1)} \<rparr> ) }"
by auto

lemma example2:
  "H_sem_thd (Dv 0) (Cu 0) (Pe 0) (my_Rd_thd r1 r2 y x) 0 = { (4, (), \<lparr>
  events = {E 0, E 1, E 2, E 3},
  lbl = {E 0 \<mapsto> R y v (S_wg, Normal), E 1 \<mapsto> W Noninit r1 v (S_wi, Normal),
         E 2 \<mapsto> R x w (S_wi, Normal), E 3 \<mapsto> W Noninit r2 w (S_wi, Normal)},
  dvid = {E 0 \<mapsto> Dv 0, E 1 \<mapsto> Dv 0, E 2 \<mapsto> Dv 0, E 3 \<mapsto> Dv 0},
  cuid = {E 0 \<mapsto> Cu 0, E 1 \<mapsto> Cu 0, E 2 \<mapsto> Cu 0, E 3 \<mapsto> Cu 0},
  peid = {E 0 \<mapsto> Pe 0, E 1 \<mapsto> Pe 0, E 2 \<mapsto> Pe 0, E 3 \<mapsto> Pe 0},
  sb = {(E 0, E 1), (E 0, E 2), (E 0, E 3), 
        (E 1, E 2), (E 1, E 3), (E 2, E 3)} \<rparr>) | v w. True }"
apply auto
apply (rule exI)+
apply auto
apply (rule exI)+
apply auto+
done

subsection {* Semantics of a workgroup *}

fun H_sem_workgroup :: "dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> H_ins workgroup \<Rightarrow> 
  unit H_pre_exnmonad"
where
  "H_sem_workgroup d w _ [] e = { (e, (), nil_pre_exn) }"
  
| "H_sem_workgroup d w t (P # Ps) e = (
  let sem_thd = H_sem_thd d w t P e in
  let sem_rest = H_sem_workgroup d w (Pe (nat_of_peid t + 1)) Ps in
  { (e'', (), Xo \<parallel> Xo') | e' e'' Xo Xo'. 
  (e', (), Xo) \<in> sem_thd \<and> (e'', (), Xo') \<in> sem_rest e'})"

subsection {* Semantics of an NDrange *}

fun H_sem_ndrange :: "dvid \<Rightarrow> cuid \<Rightarrow> H_ins ndrange \<Rightarrow> unit H_pre_exnmonad"
where
  "H_sem_ndrange dv _ [] e = { (e, (), nil_pre_exn) }"
  
| "H_sem_ndrange dv cu (P # Ps) e = (
  let sem_wg = H_sem_workgroup dv cu (Pe 0) P e in
  let sem_rest = H_sem_ndrange dv (Cu (nat_of_cuid cu + 1)) Ps in
  { (e'', (), Xo \<parallel> Xo') | e' e'' Xo Xo'. 
  (e', (), Xo) \<in> sem_wg \<and> (e'', (), Xo') \<in> sem_rest e'})"

subsection {* Semantics of a whole program *}

fun H_sem_prog :: "dvid \<Rightarrow> H_ins program \<Rightarrow> unit H_pre_exnmonad"
where
  "H_sem_prog _ [] e = { (e, (), nil_pre_exn) }"
  
| "H_sem_prog dv (P # Ps) e = (
  let sem_ndr = H_sem_ndrange dv (Cu 0) P e in
  let sem_rest = H_sem_prog (Dv (nat_of_dvid dv + 1)) Ps in
  { (e'', (), Xo \<parallel> Xo') | e' e'' Xo Xo'. 
  (e', (), Xo) \<in> sem_ndr \<and> (e'', (), Xo') \<in> sem_rest e'})"
  
text {* Candidate executions of a high-level program *}

fun H_candidate_exns :: "H_ins program \<Rightarrow> H_pre_exn set" ("\<langle> _ \<rangle>\<^sub>\<H>")
where
  "\<langle> P \<rangle>\<^sub>\<H> = add_init_events (S_wi, Normal) ` thd3 ` H_sem_prog (Dv 0) P 0" 

subsection {* Example: Two writing threads *}
  
lemma writing_example:
  "H_sem_prog (Dv 0) [[[my_Wr_thd x y, my_Wr_thd y x]]] 0 =
  { (4, (), \<lparr> 
  events = {E 0, E 1, E 2, E 3},
  lbl = {E 0 \<mapsto> W Noninit x 1 (S_wi, Normal), E 1 \<mapsto> W Noninit y 1 (S_wg, Normal),
         E 2 \<mapsto> W Noninit y 1 (S_wi, Normal), E 3 \<mapsto> W Noninit x 1 (S_wg, Normal)},
  dvid = {E 0 \<mapsto> Dv 0, E 1 \<mapsto> Dv 0, E 2 \<mapsto> Dv 0, E 3 \<mapsto> Dv 0}, 
  cuid = {E 0 \<mapsto> Cu 0, E 1 \<mapsto> Cu 0, E 2 \<mapsto> Cu 0, E 3 \<mapsto> Cu 0},
  peid = {E 0 \<mapsto> Pe 0, E 1 \<mapsto> Pe 0, E 2 \<mapsto> Pe 1, E 3 \<mapsto> Pe 1},
  sb = {(E 0, E 1), (E 2, E 3)} \<rparr> ) }"        
by auto

subsection {* Example: The message-passing test *}

lemma mp_example:
  fixes r1 r2 y x
  defines [simp]: "Xo_writers :: nat \<Rightarrow> nat \<Rightarrow> H_pre_exn \<equiv> \<lambda>v w. \<lparr> 
  events = {E 0, E 1},
  lbl = {E 0 \<mapsto> W Noninit x 1 (S_wi, Normal), E 1 \<mapsto> W Noninit y 1 (S_wg, Normal)},
  dvid = {E 0 \<mapsto> Dv 0, E 1 \<mapsto> Dv 0}, cuid = {E 0 \<mapsto> Cu 0, E 1 \<mapsto> Cu 0}, 
  peid = {E 0 \<mapsto> Pe 0, E 1 \<mapsto> Pe 0}, sb = {(E 0, E 1)} \<rparr>"
  defines [simp]: "Xo_readers :: nat \<Rightarrow> nat \<Rightarrow> H_pre_exn \<equiv> \<lambda>v w. \<lparr> 
  events = {E 2, E 3, E 4, E 5},
  lbl = {E 2 \<mapsto> R y v (S_wg, Normal), E 3 \<mapsto> W Noninit r1 v (S_wi, Normal),
         E 4 \<mapsto> R x w (S_wi, Normal), E 5 \<mapsto> W Noninit r2 w (S_wi, Normal)},
  dvid = {E 2 \<mapsto> Dv 0, E 3 \<mapsto> Dv 0, E 4 \<mapsto> Dv 0, E 5 \<mapsto> Dv 0}, 
  cuid = {E 2 \<mapsto> Cu 0, E 3 \<mapsto> Cu 0, E 4 \<mapsto> Cu 0, E 5 \<mapsto> Cu 0}, 
  peid = {E 2 \<mapsto> Pe 1, E 3 \<mapsto> Pe 1, E 4 \<mapsto> Pe 1, E 5 \<mapsto> Pe 1}, 
  sb = {(E 2, E 3), (E 2, E 4), (E 2, E 5), 
        (E 3, E 4), (E 3, E 5), (E 4, E 5)} \<rparr>"
  defines [simp]: "Xo \<equiv> \<lambda>v w. Xo_writers v w \<parallel> Xo_readers v w"
  shows "H_sem_prog (Dv 0) [[[my_Wr_thd x y, my_Rd_thd r1 r2 y x]]] 0 =
  { (6, (), Xo v w ) | v w. True }"
apply auto+
apply (rule_tac exI)+
apply auto+
apply (rule_tac x="Xo v w" in exI)+
apply auto+
apply (rule_tac x="Xo v w" in exI)+
apply auto+
apply (rule_tac x="Xo_readers v w" in exI)+
apply auto+
apply (rule_tac exI)+
apply auto+
done
  
end

