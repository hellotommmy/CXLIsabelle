header{* Hand-transcribed memory model following opencl_no_rs.cat *}

theory "RSP_opencl_mm" imports 
 	 RSP_common
   RSP_high_level_PL
begin 

(* Basic underpinnings *)

fun symcl :: "eid relation \<Rightarrow> eid relation"
where
  "symcl r = r \<union> r^-1"

fun value_of :: "H_exn \<Rightarrow> eid \<Rightarrow> val option"
where
  "value_of X a = 
  (case (lbl (Pre X) a) of W _ _ v _ \<Rightarrow> Some v | R _ v _ \<Rightarrow> Some v | _ \<Rightarrow> None)"
(* JW: This is wrong, we need read_value and write_value, in order to handle RMWs properly. *)

fun is_write :: "H_exn \<Rightarrow> eid \<Rightarrow> bool" where
  "is_write X a = (case (lbl (Pre X) a) of W _ _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

fun is_read :: "H_exn \<Rightarrow> eid \<Rightarrow> bool" where
  "is_read X a = (case (lbl (Pre X) a) of R _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

fun is_remote :: "H_exn \<Rightarrow> eid \<Rightarrow> bool" where
  "is_remote X a = (case (lbl (Pre X) a) of 
    R _ _ (_,Remote) \<Rightarrow> True | 
    W _ _ _ (_,Remote) \<Rightarrow> True | 
    RMW _ _ _ (_,Remote) \<Rightarrow> True | 
    _ \<Rightarrow> False)"
  
fun addr_of :: "H_exn \<Rightarrow> eid \<Rightarrow> addr option" 
where
  "addr_of X a = 
  (case (lbl (Pre X) a) of W _ x _ _ \<Rightarrow> Some x | R x _ _ \<Rightarrow> Some x | _ \<Rightarrow> None)"

fun set_from_p :: " ('a exn \<Rightarrow> eid \<Rightarrow> bool) \<Rightarrow> 'a exn \<Rightarrow> eid set"
where 
  "set_from_p p X = {a. a \<in> events (Pre X) \<and> p X a }"

fun rel_from_f :: "('a exn \<Rightarrow> eid \<Rightarrow> _) \<Rightarrow> 'a exn \<Rightarrow> eid relation"
where 
  "rel_from_f f X = {(a,b). {a,b} \<subseteq> events (Pre X) \<and> (f X a = f X b) }"

fun Wrs :: " H_exn \<Rightarrow> eid set" 
where 
  "Wrs X = set_from_p is_write X"

fun Rds :: " H_exn \<Rightarrow> eid set"
where
  "Rds X = set_from_p is_read X"
  
fun is_nonatomicloc :: "H_exn \<Rightarrow> eid \<Rightarrow> bool"
where
 "is_nonatomicloc X a = 
   (case addr_of X a of Some (Nonatomic _) \<Rightarrow> True | _ \<Rightarrow> False)"
   
fun nonatomicloc :: "H_exn \<Rightarrow> eid set"
where 
  "nonatomicloc X = set_from_p is_nonatomicloc X"
  
fun is_rem :: "H_exn \<Rightarrow> eid set"
where 
  "is_rem X = set_from_p is_remote X"

fun is_init_write :: "H_exn \<Rightarrow> eid \<Rightarrow> bool"
where
 "is_init_write X a = 
   (case lbl (Pre X) a of W Init _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  
fun I :: " H_exn \<Rightarrow> eid set"
where 
  "I X = set_from_p is_init_write X"
  
fun loc :: " H_exn \<Rightarrow> eid relation" 
where 
  "loc X = rel_from_f addr_of X"

fun conflict :: " H_exn \<Rightarrow> eid relation "
where 
  "conflict X = 
  ((Wrs X \<times> Wrs X) \<union> (Wrs X \<times> Rds X) \<union> (Rds X \<times> Wrs X)) \<inter> loc X"

fun stor :: " eid set \<Rightarrow> eid relation " ("\<lceil> _ \<rceil>")
where 
  "\<lceil> s \<rceil> = {(a,b). a = b \<and> a \<in> s}"

(* sb and witness relations *)

fun Sb :: "_ exn \<Rightarrow> eid relation"
where 
  "Sb X = sb (Pre X)"

fun rf :: "_ exn \<Rightarrow> eid relation"
where 
  "rf X = Rf (Wit X)"

fun mo  :: "_ exn \<Rightarrow> eid relation" 
where 
  "mo X = Mo (Wit X)"

(* memory orders (MB: Should we model NAs separately from atomics? the current
fun conflates them.) *)

fun lab_acq :: "H_lbl \<Rightarrow> bool"
where
  "lab_acq (R _ _ (s,_)) = (s \<noteq> S_wi)"
| "lab_acq _             = False"

fun lab_rel :: "H_lbl \<Rightarrow> bool"
where
  "lab_rel (W _ _ _ (s,_)) = (s \<noteq> S_wi)"
| "lab_rel _             = False"

fun lab_na :: "H_lbl \<Rightarrow> bool"
where
  "lab_na (W _ _ _ (s,_)) = (s = S_wi)"
| "lab_na (R _ _ (s,_)) = (s = S_wi)"
| "lab_na _             = False"

fun is_acq :: "H_exn \<Rightarrow> eid \<Rightarrow> bool"
where 
  "is_acq X a = lab_acq (lbl (Pre X) a)"
  
fun is_rel :: "H_exn \<Rightarrow> eid \<Rightarrow> bool"  
where 
  "is_rel X a = lab_rel (lbl (Pre X) a)"
  
fun is_na :: "H_exn \<Rightarrow> eid \<Rightarrow> bool " 
where 
  "is_na X a = lab_na (lbl (Pre X) a)"

fun acq :: "H_exn \<Rightarrow> eid set"
where 
  "acq X = set_from_p is_acq X"

fun rel :: "H_exn \<Rightarrow> eid set" 
where 
  "rel X = set_from_p is_rel X"

(*  scope sets and relations *)

fun scope_of :: "H_lbl \<Rightarrow> scope option"
where
  "scope_of (R _ _ (s,_)) = Some s"
| "scope_of (W _ _ _ (s,_)) = Some s"
| "scope_of _             = None"

fun scope_is :: "scope \<Rightarrow> H_exn \<Rightarrow> eid \<Rightarrow> bool" 
where
  "scope_is scope X a = (scope_of (lbl (Pre X) a) = Some scope)"
  
fun s_wi :: "_ exn \<Rightarrow> eid set" 
where
  "s_wi X = set_from_p (scope_is S_wi) X"
  
fun s_wg :: "_ exn \<Rightarrow> eid set" 
where 
  "s_wg X = set_from_p (scope_is S_wg) X"
  
fun s_dv :: "_ exn \<Rightarrow> eid set" 
where
  "s_dv X = set_from_p (scope_is S_dv) X"
  
fun s_all :: "_ exn \<Rightarrow> eid set" 
where 
  "s_all X = set_from_p (scope_is S_sy) X"

(* scope-distance relations *)

fun same_dv :: "'a exn \<Rightarrow> eid relation" 
where
  "same_dv X = rel_from_f (dvid \<circ> Pre) X"

fun same_wg :: "'a exn \<Rightarrow> eid relation" 
where
  "same_wg X = same_dv X \<inter> rel_from_f (cuid \<circ> Pre) X"
  
fun same_thd :: "'a exn \<Rightarrow> eid relation" 
where
  "same_thd X = same_wg X \<inter> rel_from_f (peid \<circ> Pre) X"
  

(* happens before  *)

(*
fun incl :: " H_exn \<Rightarrow> eid relation " 
where 
  "incl X = (same_pe X) \<inter> (s_wi X \<times> s_wi X) \<union> 
            (same_cu X) \<inter> (s_wg X \<times> s_wg X) \<union> 
            (same_dv X) \<inter> (s_dv X \<times> s_dv X) \<union> 
            s_all X \<times> s_all X"
*)

fun incl1 :: "H_exn \<Rightarrow> eid relation"
where
  "incl1 X = ((stor (s_wi X)) O same_thd X) 
        \<union> ((stor (s_wg X)) O same_wg X)
        \<union> ((stor (s_dv X)) O same_dv X)
        \<union> ((stor (s_all X)) O {x. True})"
            
fun incl :: "H_exn \<Rightarrow> eid relation"
where
  "incl X = ((incl1 X \<inter> (incl1 X)^-1) 
         \<union> (stor (is_rem X) O incl1 X) 
         \<union> ((incl1 X)^-1 O stor (is_rem X)))"
  
        
fun sw :: " H_exn \<Rightarrow> eid relation"
where 
  "sw X = 
  \<lceil> rel X - s_wi X \<rceil> O rf X O \<lceil> acq X - s_wi X \<rceil> \<inter> (incl X - same_thd X)"
  
fun hb :: "H_exn \<Rightarrow> eid relation"
where 
  "hb X = (Sb X \<union> ((I X \<times> - I X) \<union> sw X))\<^sup>+"

(* data-race and faulty fun *)

fun dr :: "H_exn \<Rightarrow> eid relation"
where 
  "dr X = conflict X \<inter> (- hb X \<inter> (-(hb X)\<inverse> \<inter> - incl X))"

fun faulty :: "H_exn \<Rightarrow> bool" 
where
  "faulty X = (dr X = {})"

(* well formed threads *)

(* no need for well_formed_actions without memory orders *)

fun well_formed_sb :: "H_exn \<Rightarrow> bool"
where 
  "well_formed_sb X =
    (trans (Sb X) \<and>
      irrefl (Sb X) \<and>
      (Domain (Sb X) \<subseteq> events (Pre X)) \<and>
      (Range (Sb X) \<subseteq> events (Pre X)) \<and>
      (\<forall>a b. (a,b) \<in> symcl (Sb X) \<longleftrightarrow>
        (a \<noteq> b \<and> (a,b) \<in> same_thd X)))"

(* MB: We might need actions_respect_location_kinds X *)

fun rf_for_every_read  :: "H_exn \<Rightarrow> bool"
where 
  "rf_for_every_read X = (
    \<forall>r \<in> Collect (is_read X). \<exists>w. (w,r) \<in> rf X)"

fun well_formed_rf :: "H_exn \<Rightarrow> bool"
where 
  "well_formed_rf X = (
   \<forall>(a,b) \<in> rf X. 
    (a,b) \<in> loc X \<and>           
    is_write X a \<and> is_read X b \<and>      
    value_of X b = value_of X a \<and>
    (\<forall>a'. (a',b) \<in> rf X \<longrightarrow> a = a'))"
    
fun well_formed_mo  :: "H_exn \<Rightarrow> bool"
where 
  "well_formed_mo X = (
    trans (mo X) \<and>
    irrefl (mo X) \<and>
    (\<forall>a b. (a,b) \<in> symcl (mo X) \<longleftrightarrow>
      (a \<noteq> b \<and> is_write X a \<and> is_write X b \<and> (a,b) \<in> loc X)))"
(* JW: The above is wrong; we need to mention that mo only relates 
       *atomic* writes. *)

fun herd_provides :: "H_exn \<Rightarrow> bool" 
where 
  "herd_provides X = (
  well_formed_sb X \<and> rf_for_every_read X \<and> 
  well_formed_rf X \<and> well_formed_mo X)"

(* consistency fun *)

fun O_Hb_G :: "H_exn \<Rightarrow> bool"
where 
  "O_Hb_G X = irrefl (hb X)"

fun coh :: " H_exn \<Rightarrow> eid relation"
where 
  "coh X = ((rf X)^-1)\<^sup>= O mo X O (rf X)\<^sup>= O hb X"
  
fun O_Coh_G :: "H_exn \<Rightarrow> bool"  
where 
  "O_Coh_G X = irrefl (coh X)"

fun O_Rf :: "H_exn \<Rightarrow> bool" 
where 
  "O_Rf X = irrefl (rf X O hb X)"

fun vis :: "H_exn \<Rightarrow> eid relation"
where 
  "vis X = 
  (Wrs X \<times> Rds X) \<inter> hb X \<inter> loc X \<inter> -((hb X \<inter> loc X) O \<lceil> Wrs X \<rceil> O hb X)"

fun O_Narf_G :: "H_exn \<Rightarrow> bool"
where 
  "O_Narf_G X = irrefl (rf X O \<lceil> nonatomicloc X \<rceil> O -(vis X)\<inverse>)"

fun O_Rmw :: "H_exn \<Rightarrow> bool"
where
  "O_Rmw X = irrefl (rf X \<union> (mo X O mo X O (rf X)^-1) \<union> (mo X O rf X))"
  
fun H_consistent :: "H_exn \<Rightarrow> bool" 
where
  "H_consistent X = 
  (herd_provides X \<and> O_Hb_G X \<and> O_Coh_G X \<and> O_Rf X \<and> O_Narf_G X \<and> O_Rmw X)"
  
text {* The allowed behaviours of a high-level program are: its consistent
executions if none of the consistent executions are faulty, and anything at all
if any of its consistent executions are faulty. *}

fun H_behaviours :: "H_ins program \<Rightarrow> H_exn set" ("\<lbrakk> _ \<rbrakk>\<^sub>\<H>")
where
  "\<lbrakk> P \<rbrakk>\<^sub>\<H> = (
  let Xs = {X. Pre X \<in> \<langle> P \<rangle>\<^sub>\<H> \<and> H_consistent X} in
  if (\<exists>X \<in> Xs. faulty X) then {X. True} else Xs)"

end
