(*header (* Syntax and semantics of low-level programs *)*)

theory RSP_low_level_PL imports 
  RSP_state
begin

section {* Syntax of low-level programs *}

datatype cache_action = 
  FLUSH_L1  (* Add flush marker(s) to L1 cache(s) *)
| FLUSH_L2   (* Add flush marker(s) to L2 cache(s) *)
| INVAL_L1 (* Invalidate entire L1 cache(s) *)
| LK_rmw   (* Acquire lock on RMW operations *)
| UNLK_rmw (* Release lock on RMW operations *)

text {* Low-level instructions *}

datatype L_ins = 
  LD register addr    (* Load into register *)
| ST addr register    (* Store from register *)
| INC_L1 register addr    (* Atomic increment @ L1 cache *)
| INC_L2 register addr    (* Atomic increment @ L2 cache *)
| LK addr    (* Block access to given address @ L2 *)
| UNLK addr    (* Unblock access to given address @ L2 *)
| CAC "cache_action \<times> scope"
(* The rest aren't interesting    could omit from presentation *)
| IMM register val    (* Load constant into register *)
| ADD register register register    (* Addition on registers *)
| IF register bool L_ins    (* Execute given instruction if given register 
      (interpreted as a bool) is equal to the given bool *)
(* Consider adding arbitrary jumps *)

text {*
  CAC (FLUSH_L1, S_wg) = add flush marker to my L1 cache
  CAC (FLUSH_L1, S_dv) = add flush markers to all L1 caches in my device
  CAC (FLUSH_L1, S_sy) = add flush markers to all L1 caches in all devices
  CAC (FLUSH_L2, S_dv) = add flush markers to my L2 cache
  CAC (FLUSH_L2, S_sy) = add flush markers to all L2 caches in all devices
  CAC (INVAL_L1, S_wg) = invalidate all entries in my L1 cache
  CAC (INVAL_L1, S_dv) = invalidate all entries in all L1 caches in my device
  CAC (INVAL_L1, S_sy) = invalidate all entries in all L1 caches in all devices
  CAC (LK_rmw, S_wg) = lock rmw operations in current workgroup
  CAC (LK_rmw, S_dv) = lock rmw operations in current device
  CAC (LK_rmw, S_sy) = lock rmw operations in all devices
  CAC (UNLK_rmw, S_wg) = unlock rmw operations in current workgroup
  CAC (UNLK_rmw, S_dv) = unlock rmw operations in current device
  CAC (UNLK_rmw, S_sy) = unlock rmw operations in all devices
  CAC (_, _, _) = no-op
*}


section {* Low-level run-time memory events *}

text {* Labels on low-level memory events *}

type_synonym L_lbl = "(unit, cache_action \<times> scope) lbl"
type_synonym L_pre_exn = "L_lbl pre_exn"
type_synonym L_exn = "L_lbl exn"
  
section {* Transitions by the environment *}





text {* The following inductively-defined relation represents state transitions
effected by the environment (i.e. independently of instructions scheduled by the
programmer). *}




inductive env_trans :: "(eid \<times> eid list) sy_state \<Rightarrow> 
  (eid \<times> eid list) sy_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>\<e>" 50)
where
  evict_clean_L1:
  "\<lbrakk> Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x = Some (_, _, Clean, _) ; 
     (dv :=\<^sub>\<d> cu :=\<^sub>\<c> update_L1 (x :=\<^sub>\<s> None)) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow>
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
| evict_clean_L2:
  "\<lbrakk> Store (L2cache (\<Sigma>[dv]\<^sub>\<d>)) x = Some (_, _, Clean, _) ; 
     (dv :=\<^sub>\<d> update_L2 (x :=\<^sub>\<s> None)) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow>
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
| fetch_into_L1:
  "\<lbrakk> Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x \<in> {None, Some (_, _, Clean, _)} ;
     locked (\<Sigma>[dv]\<^sub>\<d>) x = Unlocked ;
     Store (L2cache (\<Sigma>[dv]\<^sub>\<d>)) x = Some (v, (e_w, _), _, Valid) ;
     (dv :=\<^sub>\<d> cu :=\<^sub>\<c> update_L1 (x :=\<^sub>\<s> Some (v, (e_w, []), Clean, Valid))) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow>
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
| fetch_into_L2:
  "\<lbrakk> Store (L2cache (\<Sigma>[dv]\<^sub>\<d>)) x \<in> {None, Some (_, _, Clean, _)} ;
     locked (\<Sigma>[dv]\<^sub>\<d>) x = Unlocked ;
     Global_mem \<Sigma> x = Some (v, (e_w, _)) ;
     (dv :=\<^sub>\<d> update_L2 (x :=\<^sub>\<s> Some (v, (e_w, []), Clean, Valid))) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow>
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
| deq_fifo_flush_L1: 
  "\<lbrakk> L1c = L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>) ;
     length (Fifo L1c) > 0 ;
     last (Fifo L1c) = Flush _ ;
     (dv :=\<^sub>\<d> cu :=\<^sub>\<c> update_L1 deq_Fifo) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
| deq_fifo_flush_L2: 
  "\<lbrakk> L2c = L2cache (\<Sigma>[dv]\<^sub>\<d>) ;
     length (Fifo L2c) > 0 ;
     last (Fifo L2c) = Flush _ ;
     (dv :=\<^sub>\<d> update_L2 deq_Fifo) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
| deq_fifo_addr_L1: 
  "\<lbrakk> L1c = L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>) ;
     length (Fifo L1c) > 0 ;
     last (Fifo L1c) = Addr x;
     Store L1c x \<in> { None, Some(_, _, Clean, _) } ;
     (dv :=\<^sub>\<d> cu :=\<^sub>\<c> update_L1 deq_Fifo) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
| deq_fifo_addr_L2: 
  "\<lbrakk> L2c = L2cache (\<Sigma>[dv]\<^sub>\<d>) ;
     length (Fifo L2c) > 0 ;
     last (Fifo L2c) = Addr x;
     Store L2c x \<in> { None, Some(_, _, Clean, _) } ;
     (dv :=\<^sub>\<d> update_L2 deq_Fifo) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
  
|  flush_dirty_L1:
  "\<lbrakk> Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x = Some (v, (e_w,mo_L1), Dirty, validity) ;
     locked (\<Sigma>[dv]\<^sub>\<d>) x = Unlocked ;
     mo_L2 = (case Store (L2cache (\<Sigma>[dv]\<^sub>\<d>)) x of None \<Rightarrow> [] | Some (_,(_,mo),_,_) \<Rightarrow> mo) ;
     (dv :=\<^sub>\<d> cu :=\<^sub>\<c> update_L1 (x :=\<^sub>\<s> Some (v, (e_w,[]), Clean, validity)) ;; 
     (dv :=\<^sub>\<d> update_L2 (x :=\<^sub>\<s> Some (v, (e_w, mo_L2 @ mo_L1), Dirty, validity)))) \<Sigma> = \<Sigma>'  \<rbrakk> \<Longrightarrow>
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"

|  flush_dirty_L2:
  "\<lbrakk> Store (L2cache (\<Sigma>[dv]\<^sub>\<d>)) x = Some (v, (e_w, mo_L2), Dirty, validity) ;
     mo_global = (case Global_mem \<Sigma> x of None \<Rightarrow> [] | Some (_,(_,mo)) \<Rightarrow> mo) ;
     (dv :=\<^sub>\<d> update_L2 (x :=\<^sub>\<s> (Some (v, (e_w, []), Clean, validity))) ;;
     update_global_mem (\<lambda>\<sigma>. \<sigma>(x \<mapsto> (v, (e_w, mo_global @ mo_L2))))) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow>
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"
 
 
section {* Semantics of low-level programs *}

type_synonym sy_state' = "(eid \<times> eid list) sy_state"
type_synonym dv_state' = "(eid \<times> eid list) dv_state"
type_synonym cu_state' = "(eid \<times> eid list) cu_state"
 
type_synonym 'a config = "'a \<times> L_exn \<times> nat "(*eid*)

subsection {* Semantics of low-level programs with memory subsystem engaged *}

fun unflushed :: "(dvid \<times> cuid \<times> peid) \<Rightarrow> _ sy_state \<Rightarrow> bool"
where 
  "unflushed lid \<Sigma> = 
  list_ex (\<lambda>\<Delta>. Flush lid \<in> set (Fifo (L2cache \<Delta>)) \<or> 
  list_ex (\<lambda>\<Gamma>. Flush lid \<in> set (Fifo (L1cache \<Gamma>))) (cus \<Delta>)) (dvs \<Sigma>)"


 (* append read event to execution *)
 (* write given value (v) to register r *)
 (* Add rf-edge from given event (e_w) to the current event (E e). *)
 (* block if L1 needs flushing *)
 (* L1 contains a valid cacheline for x, so use it *)
fun Lred_ins :: "L_ins \<Rightarrow> dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> sy_state' config \<Rightarrow> 
  sy_state' config set"
where 
  "Lred_ins (LD r x) dv cu pe (\<Sigma>,X,e) = (
  let add_rd_evt = \<lambda>v.
    update_pre (append_evt (E e) (R x v ()) dv cu pe) 
  in
  let upd_reg = \<lambda>v.
    (dv :=\<^sub>\<d> cu :=\<^sub>\<c> pe :=\<^sub>\<p> r :=\<^sub>\<r> v) 
  in
  let add_rf_edge = \<lambda>e_w. 
    update_wit (update_L_rf (union {(e_w, E e)}))
  in
  if unflushed (dv,cu,pe) \<Sigma> then {} else 
  case Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x of 
    Some (v, (e_w,_), _, Valid) \<Rightarrow> 

    {(upd_reg v \<Sigma>, (add_rd_evt v ;; add_rf_edge e_w) X, e + 1)}
  | _ \<Rightarrow> {})"
(* lookup value of r in register file *)
(* append write event to execution *)
 (* block if L1 needs flushing *)
 (* block until invalid cacheline has been flushed *)
 (* block until invalid cacheline has been flushed *)
    (* Store directly to L1 cache *)
    (* Store directly to L2 cache *)
    (* Add rf-edge from given event (e_w) to the current event (E e). *)
(* block until invalid cacheline has been flushed *)
(* block if L1 needs flushing *)
(* block if RMW ops are stalled *)
(* append rmw event to execution *)
 (* write given value (v) to register r *)
      (* Store directly to global memory *)
 (* append rmw event to execution *)
 (* write given value (v) to register r *)
(* block if L1 needs flushing *)
 (* Add rf-edge from given event (e_w) to the current event (E e). *)
(* block if RMW ops are stalled *)
(* block if cacheline is locked *)
(* block until dirty cacheline has been flushed *) 
 (* block if L1 needs flushing *)
(* block if any of the locks are already taken *)
(* block if L1 needs flushing *)
(* block if address already locked *)
(* block if L1 needs flushing *)


| "Lred_ins (ST x r) dv cu pe (\<Sigma>,X,e) = (
  let v = (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>[pe]\<^sub>\<p>) r  in 
  let add_wr_evt = 
    update_pre (append_evt (E e) (W Noninit x v ()) dv cu pe) 
  in
  if unflushed (dv,cu,pe) \<Sigma> then {} else 
  case Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x of 
    Some (_, (_,_), Dirty, Invalid) \<Rightarrow> 
    {} 
  | None \<Rightarrow> (
    let inval_L2 = \<lambda>dv'. dv' :=\<^sub>\<d> update_L2 (invalidate_line x) in
    if locked (\<Sigma>[dv]\<^sub>\<d>) x = Locked then {} else
    case Store (L2cache (\<Sigma>[dv]\<^sub>\<d>)) x of 
      Some (_, (_,_), Dirty, Invalid) \<Rightarrow> 
      {} 
    | None \<Rightarrow> (

      {((foldr inval_L2 (dvids \<Sigma>) ;; 
         write_global x v (E e)) \<Sigma>, 
      add_wr_evt X, e + 1)}
    )
    | _ \<Rightarrow>

    {((foldr inval_L2 (dvids \<Sigma>) ;; 
       dv :=\<^sub>\<d> write_to_L2 x v (E e)) \<Sigma>, 
    add_wr_evt X, e + 1)})
  | _ \<Rightarrow>

    {((dv :=\<^sub>\<d> cu :=\<^sub>\<c> write_to_L1 x v (E e)) \<Sigma>, 
    add_wr_evt X, e + 1)})"

| "Lred_ins (INC_L1 r x) dv cu pe (\<Sigma>,X,e) = ( 
  let add_rmw_evt = \<lambda>v. 
    update_pre (append_evt (E e) (RMW x v (v+1) ()) dv cu pe) 
  in
  let upd_reg = \<lambda>v.
    (dv :=\<^sub>\<d> cu :=\<^sub>\<c> pe :=\<^sub>\<p> r :=\<^sub>\<r> v) 
  in
  let add_rf_edge = \<lambda>e_w. 

    update_wit (update_L_rf (union {(e_w, E e)}))
  in
  if unflushed (dv,cu,pe) \<Sigma> then 
  {}  else
  if rmw_lock (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>) = Locked then 
  {}  else
  case Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x of 
    Some (v, (e_w,_), _, Valid) \<Rightarrow> 
    {(((dv :=\<^sub>\<d> cu :=\<^sub>\<c> write_to_L1 x (v+1) (E e)) ;; upd_reg v) \<Sigma>, 
     (add_rmw_evt v ;; add_rf_edge e_w) X, e + 1)}
  | _ \<Rightarrow> {} )"
    
| "Lred_ins (INC_L2 r x) dv cu pe (\<Sigma>,X,e) = ( 
  let add_rmw_evt = \<lambda>v.
    update_pre (append_evt (E e) (RMW x v (v+1) ()) dv cu pe) 
  in
  let upd_reg = \<lambda>v.
    (dv :=\<^sub>\<d> cu :=\<^sub>\<c> pe :=\<^sub>\<p> r :=\<^sub>\<r> v) 
  in
  let add_rf_edge = \<lambda>e_w. 
   
    update_wit (update_L_rf (union {(e_w,E e)}))
  in
  if unflushed (dv,cu,pe) \<Sigma> then 
  {}  else 
  if rmw_lock (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>) = Locked then 
  {}  else
  if locked (\<Sigma>[dv]\<^sub>\<d>) x = Locked then 
  {}  else
  case Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x of 
    Some (_, (_,_), Dirty, _) \<Rightarrow> 
    {} 
  | _ \<Rightarrow> (
  case Store (L2cache (\<Sigma>[dv]\<^sub>\<d>)) x of 
    Some (v, (e_w,_), _, Valid) \<Rightarrow> 
    let inval_L2 = \<lambda>dv'. dv' :=\<^sub>\<d> update_L2 (invalidate_line x) in
    {(((dv :=\<^sub>\<d> cu :=\<^sub>\<c> update_L1 (invalidate_line x)) ;; 
       foldr inval_L2 (dvids \<Sigma>) ;;
       (dv :=\<^sub>\<d> write_to_L2 x (v+1) (E e)) ;; 
       upd_reg v) \<Sigma>, 
      (add_rmw_evt v ;; add_rf_edge e_w) X, e + 1)}
  | _ \<Rightarrow> {} ))"
  
| "Lred_ins (CAC (cac, scope)) dv cu pe (\<Sigma>,X,e) = (
  let add_tau_evt = update_pre (append_evt (E e) (Tau (cac, scope)) dv cu pe) in
  if unflushed (dv,cu,pe) \<Sigma> then 
  {} else 
  case cac of 
    FLUSH_L1 \<Rightarrow> (
    let do_actions = \<lambda>\<Sigma>.
      let do_action = \<lambda>dv' cu'.
        dv' :=\<^sub>\<d> cu' :=\<^sub>\<c> update_L1 (enq_Fifo (Flush (dv,cu,pe)))
      in
      case scope of
        S_wi \<Rightarrow> \<Sigma> 
      | S_wg \<Rightarrow> do_action dv cu \<Sigma>
      | S_dv \<Rightarrow> foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>)) \<Sigma>
      | S_sy \<Rightarrow> foldr (\<lambda>dv. foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>))) (dvids \<Sigma>)
      \<Sigma>
    in
    {(do_actions \<Sigma>, add_tau_evt X, e + 1)})
  | FLUSH_L2 \<Rightarrow> (
    let do_actions = \<lambda>\<Sigma>.
      let do_action = \<lambda>dv'. dv' :=\<^sub>\<d> update_L2 (enq_Fifo (Flush (dv,cu,pe))) in
      case scope of
        S_wi \<Rightarrow> \<Sigma> 
      | S_wg \<Rightarrow> \<Sigma>
      | S_dv \<Rightarrow> do_action dv \<Sigma>
      | S_sy \<Rightarrow> foldr do_action (dvids \<Sigma>) \<Sigma>
    in
    {(do_actions \<Sigma>, add_tau_evt X, e + 1)})
  | INVAL_L1 \<Rightarrow> (
    let do_actions = \<lambda>\<Sigma>.
      let do_action = \<lambda>dv' cu'.
        dv' :=\<^sub>\<d> cu' :=\<^sub>\<c> update_L1 invalidate_all
      in
      case scope of
        S_wi \<Rightarrow> \<Sigma> 
      | S_wg \<Rightarrow> do_action dv cu \<Sigma>
      | S_dv \<Rightarrow> foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>)) \<Sigma>
      | S_sy \<Rightarrow> foldr (\<lambda>dv. foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>))) (dvids \<Sigma>) \<Sigma>
    in
    {(do_actions \<Sigma>, add_tau_evt X, e + 1)})
  | LK_rmw \<Rightarrow> (
    let is_unlocked = \<lambda>\<Sigma> dv' cu'. (rmw_lock (\<Sigma>[dv']\<^sub>\<d>[cu']\<^sub>\<c>) = Unlocked) in
    let do_action = \<lambda>dv' cu'. (dv' :=\<^sub>\<d> cu' :=\<^sub>\<c> (\<lambda>\<Gamma>. \<Gamma> \<lparr> rmw_lock := Locked \<rparr>)) in
    let do_actions = \<lambda>\<Sigma>. 
      case scope of 
        S_wi \<Rightarrow> \<Sigma> 
      | S_wg \<Rightarrow> do_action dv cu \<Sigma>
      | S_dv \<Rightarrow> foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>)) \<Sigma>
      | S_sy \<Rightarrow> foldr (\<lambda>dv. foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>))) (dvids \<Sigma>) \<Sigma>
    in
    let is_unlocked = case scope of
        S_wi \<Rightarrow> True
      | S_wg \<Rightarrow> is_unlocked \<Sigma> dv cu
      | S_dv \<Rightarrow> list_all (is_unlocked \<Sigma> dv) (cuids (\<Sigma>[dv]\<^sub>\<d>))
      | S_sy \<Rightarrow> 
        list_all (\<lambda>dv. list_all (is_unlocked \<Sigma> dv) (cuids (\<Sigma>[dv]\<^sub>\<d>))) (dvids \<Sigma>)
    in
    if \<not> is_unlocked then {} 
    else {(do_actions \<Sigma>, X, e)})
  | UNLK_rmw \<Rightarrow> (
    let do_action = \<lambda>dv' cu'. (dv' :=\<^sub>\<d> cu' :=\<^sub>\<c> (\<lambda>\<Gamma>. \<Gamma> \<lparr> rmw_lock := Unlocked \<rparr>)) in
    let do_actions = \<lambda>\<Sigma>. 
      case scope of 
        S_wi \<Rightarrow> \<Sigma> 
      | S_wg \<Rightarrow> do_action dv cu \<Sigma>
      | S_dv \<Rightarrow> foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>)) \<Sigma>
      | S_sy \<Rightarrow> foldr (\<lambda>dv. foldr (do_action dv) (cuids (\<Sigma>[dv]\<^sub>\<d>))) (dvids \<Sigma>) \<Sigma>
    in
    {(do_actions \<Sigma>, X, e)}))"
  
| "Lred_ins (LK x) dv cu pe (\<Sigma>,X,e) = (
  if unflushed (dv,cu,pe) \<Sigma> then 
  {}  else
  case locked (\<Sigma>[dv]\<^sub>\<d>) x of 
    Locked \<Rightarrow> {} 
  | Unlocked \<Rightarrow> {((dv :=\<^sub>\<d> lock_L2 x) \<Sigma>, X, e)})"
   
| "Lred_ins (UNLK x) dv cu pe (\<Sigma>,X,e) = (
  if unflushed (dv,cu,pe) \<Sigma> then 
  {}  else
  {((dv :=\<^sub>\<d> unlock_L2 x) \<Sigma>, X, e)})"

| "Lred_ins (ADD r r1 r2) dv cu pe (\<Sigma>,X,e) = (
  let v1 = (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>[pe]\<^sub>\<p>) r1 in 
  let v2 = (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>[pe]\<^sub>\<p>) r2 in 
  {((dv :=\<^sub>\<d> cu :=\<^sub>\<c> pe :=\<^sub>\<p> r :=\<^sub>\<r> v1 + v2) \<Sigma>, X, e)})"

| "Lred_ins (IMM r v) dv cu pe (\<Sigma>,X,e) = (
  {((dv :=\<^sub>\<d> cu :=\<^sub>\<c> pe :=\<^sub>\<p> r :=\<^sub>\<r> v) \<Sigma>, X, e)})"

| "Lred_ins (IF r b ins) dv cu pe (\<Sigma>,X,e) = (
  let v = (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>[pe]\<^sub>\<p>) r in
  if b = (v \<noteq> 0) then Lred_ins ins dv cu pe (\<Sigma>,X,e) 
  else {(\<Sigma>,X,e)} )"

    
inductive Lred :: "(L_ins program \<times> sy_state' config) \<Rightarrow> 
  (L_ins program \<times> sy_state' config) \<Rightarrow> bool" (infix "\<leadsto>" 50)
where
  environment_step: 
  "env_trans \<Sigma> \<Sigma>' \<Longrightarrow> (P,\<Sigma>,X,e) \<leadsto> (P,\<Sigma>',X,e)"
  
| program_step: 
  "\<lbrakk> Dv dv \<in> set (dvids \<Sigma>) ; 
     Cu cu \<in> set (cuids (\<Sigma>[Dv dv]\<^sub>\<d>)) ; 
     Pe pe \<in> set (peids (\<Sigma>[Dv dv]\<^sub>\<d>[Cu cu]\<^sub>\<c>)) ;
     P ! dv ! cu ! pe = ins # inss ;
     (\<Sigma>',X',e') \<in> Lred_ins ins (Dv dv) (Cu cu) (Pe pe) (\<Sigma>,X,e) \<rbrakk> \<Longrightarrow> 
    (P,\<Sigma>,X,e) \<leadsto>      
    (P [dv := (P ! dv)[cu := (P ! dv ! cu)[pe := inss]]], \<Sigma>', X', e')"  
  
subsection {* Semantics of low-level programs with memory subsystem disengaged
*}
    
fun Lred_nomem_ins :: "L_ins \<Rightarrow> dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> 
  pe_state config \<Rightarrow> pe_state config set"
where 
  "Lred_nomem_ins (LD r x) dv cu pe (\<sigma>p,X,e) = 
  {((r :=\<^sub>\<r> v) \<sigma>p, 
  update_pre (append_evt (E e) (R x v ()) dv cu pe) X, 
  e + 1) | v. True }"

| "Lred_nomem_ins (ST x r) dv cu pe (\<sigma>p,X,e) =
  {(\<sigma>p, update_pre (append_evt (E e) (W Noninit x (\<sigma>p r) ()) dv cu pe) X, e + 1)}"
  
| "Lred_nomem_ins (INC_L1 r x) dv cu pe (\<sigma>p,X,e) =
  {((r :=\<^sub>\<r> v) \<sigma>p, 
  update_pre (append_evt (E e) (RMW x v (v+1) ()) dv cu pe) X, 
  e + 1) | v. True }"
  
| "Lred_nomem_ins (INC_L2 r x) dv cu pe (\<sigma>p,X,e) =
  {((r :=\<^sub>\<r> v) \<sigma>p, 
  update_pre (append_evt (E e) (RMW x v (v+1) ()) dv cu pe) X, 
  e + 1) | v. True }"

| "Lred_nomem_ins (ADD r r1 r2) _ _ _ (\<sigma>p,X,e) = 
  {((r :=\<^sub>\<r> \<sigma>p r1 + \<sigma>p r2) \<sigma>p, X, e)}"
  
| "Lred_nomem_ins (LK x) _ _ _ (\<sigma>p,X,e) = {(\<sigma>p, X, e)}"
| "Lred_nomem_ins (UNLK x) _ _ _ (\<sigma>p,X,e) = {(\<sigma>p, X, e)}"

| "Lred_nomem_ins (IMM r v) _ _ _ (\<sigma>p,X,e) = {((r :=\<^sub>\<r> v) \<sigma>p, X, e)}"

| "Lred_nomem_ins (IF r b ins) dv cu pe (\<sigma>p,X,e) = (
  if b = (\<sigma>p r \<noteq> 0) then {(\<sigma>p,X,e)} else 
  Lred_nomem_ins ins dv cu pe (\<sigma>p,X,e))"

| "Lred_nomem_ins (CAC(cac, scope)) dv cu pe (\<sigma>p,X,e) =
  {(\<sigma>p, update_pre (append_evt (E e) (Tau (cac, scope)) dv cu pe) X, e + 1)}"
  
inductive Lred_nomem :: "(L_ins program \<times> sy_state' config) \<Rightarrow>
  (L_ins program \<times> sy_state' config) \<Rightarrow> bool" (infix "\<langle>\<leadsto>\<rangle>" 50)
where
  stutter:
  "\<gamma> = \<gamma>' \<Longrightarrow> \<gamma> \<langle>\<leadsto>\<rangle> \<gamma>'" 

| program_step: 
  "\<lbrakk> Dv dv \<in> set (dvids \<Sigma>) ; 
     Cu cu \<in> set (cuids (\<Sigma>[Dv dv]\<^sub>\<d>)) ; 
     Pe pe \<in> set (peids (\<Sigma>[Dv dv]\<^sub>\<d>[Cu cu]\<^sub>\<c>)) ;
     P ! dv ! cu ! pe = ins # inss ;
     (\<sigma>p',X',e') \<in> Lred_nomem_ins ins (Dv dv) (Cu cu) (Pe pe) (\<sigma>p,X,e) ;
     \<sigma>p = \<Sigma>[Dv dv]\<^sub>\<d>[Cu cu]\<^sub>\<c>[Pe pe]\<^sub>\<p> ;
     \<Sigma>' = (Dv dv :=\<^sub>\<d> Cu cu :=\<^sub>\<c> Pe pe :=\<^sub>\<p> (\<lambda>_. \<sigma>p)) \<Sigma> ;
     P' = P[dv := (P ! dv)[cu := (P ! dv ! cu)[pe := inss]]]
   \<rbrakk> \<Longrightarrow> 
   (P,\<Sigma>,X,e) \<langle>\<leadsto>\<rangle> (P', \<Sigma>',X',e')"
   
fun nothing_left_to_do :: "'ins program \<Rightarrow> bool"
where
  "nothing_left_to_do P = list_all (list_all (list_all (\<lambda>t. t = []))) P"
  
fun stuck :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "stuck rel x = (\<forall>y. \<not> rel x y)"
  
fun reductions :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list set"
where
  "reductions P \<gamma> = { \<rho>. \<rho> \<noteq> [] \<and> list_all_pairs P \<rho> \<and> hd \<rho> = \<gamma> }" 
  
(* If a thread has something left to do, then progress can be made. *)
lemma no_deadlock:
  "stuck Lred \<gamma> \<Longrightarrow> nothing_left_to_do (fst3 \<gamma>)"
oops
(* This can be argued by looking through each rule, and noting that every time
the execution blocks, there exists an environmental transition that can fire. *)

fun add_mo :: "sy_state' \<Rightarrow> L_exn \<Rightarrow> L_exn"
where
  "add_mo \<Sigma> X = 
  (let mo = 
    \<Union> { total_order_of (snd (snd (the (Global_mem \<Sigma> x)))) | x . 
                case x of Atomic _ \<Rightarrow> True | Nonatomic _ \<Rightarrow> False } 
  in update_wit (\<lambda>wit. wit \<lparr> Mo := mo \<rparr>) X)"
 
fun L_candidate_exns_prog :: "L_ins program \<Rightarrow> sy_state' config \<Rightarrow> 
  sy_state' config set"
where
  "L_candidate_exns_prog P \<gamma>0 = 
  { (\<Sigma>, erase_witness X, e') | P' \<Sigma> X e'. \<exists>\<rho> \<in> reductions (Lred_nomem) (P, \<gamma>0).
    last \<rho> = (P',\<Sigma>, X, e') \<and> nothing_left_to_do P'}"
    
fun L_candidate_exns :: "L_ins program \<Rightarrow> L_exn set" ("\<langle> _ \<rangle>\<^sub>\<L>")
where
  "\<langle> P \<rangle>\<^sub>\<L> = 
  snd3 ` L_candidate_exns_prog P (mk_initial_state (\<lambda>x. (InitE x, [])) P, update_pre (add_init_events ()) nil_exn, 0)"

fun L_consistent_exns :: "L_ins program \<Rightarrow> L_exn set" ("\<lbrakk> _ \<rbrakk>\<^sub>\<L>")
where
  "\<lbrakk> P \<rbrakk>\<^sub>\<L> = 
  (let \<gamma>0 = (mk_initial_state (\<lambda>x. (InitE x, [])) P, update_pre (add_init_events ()) nil_exn, 0) in
  { X . \<exists>\<rho> \<in> reductions Lred (P,\<gamma>0). 
    X = add_mo (snd4 (last \<rho>)) (thd4 (last \<rho>)) \<and> stuck Lred (last \<rho>) })"
  
(* MB: I think we need an additional restriction here that makes sure that R starts with a valid
start state: particularly an empty ghost state. *)
fun L_consistent :: "L_exn \<Rightarrow> bool"
where
  "L_consistent X = 
   (\<exists>\<rho>. list_all_pairs Lred \<rho> \<and> X = add_mo (snd4 (last \<rho>)) (thd4 (last \<rho>)))"

text \<open>The following lemma states that every consistent low-level execution can
be obtained by first generating a low-level execution in the absence of the
memory subsystem, and then rerunning that execution with the memory subsystem
reengaged. \<close>

fun clear_L1_cache :: "'tag cu_state \<Rightarrow> 'tag cu_state"
where
  "clear_L1_cache \<sigma>c = \<sigma>c \<lparr> L1cache := \<lparr> Fifo = [], Store = \<lambda>_. None \<rparr> \<rparr>"

fun clear_caches :: "'tag dv_state \<Rightarrow> 'tag dv_state"
where
  "clear_caches \<sigma>d = \<sigma>d \<lparr> cus := map clear_L1_cache (cus \<sigma>d) \<rparr>"

fun clear_memory_and_caches :: "sy_state' \<Rightarrow> sy_state'" ("\<lfloor> _ \<rfloor>")
where
  "\<lfloor>\<Sigma>\<rfloor> = \<Sigma> \<lparr> dvs := map clear_caches (dvs \<Sigma>), 
        Global_mem := initial_global_mem (\<lambda>x. (InitE x, [])) \<rparr>"

lemma environment_preserves_erasure:
  "env_trans \<Sigma> \<Sigma>' \<Longrightarrow> \<lfloor>\<Sigma>\<rfloor> = \<lfloor>\<Sigma>'\<rfloor>"
oops 

lemma erasure_preserves_thread_state [simp]:
  assumes "dv \<in> set (dvids \<Sigma>)" 
  and "cu \<in> set (cuids (\<Sigma> [dv]\<^sub>\<d>))"
  and "pe \<in> set (peids (\<Sigma> [dv]\<^sub>\<d>[cu]\<^sub>\<c>))"
  shows "\<lfloor>\<Sigma>\<rfloor> [dv]\<^sub>\<d>[cu]\<^sub>\<c>[pe]\<^sub>\<p> = \<Sigma> [dv]\<^sub>\<d>[cu]\<^sub>\<c>[pe]\<^sub>\<p>"
using assms by auto

fun erase_memory_and_witness :: "sy_state' config \<Rightarrow> sy_state' config" 
where
  "erase_memory_and_witness (\<Sigma>, X, e) = (\<lfloor>\<Sigma>\<rfloor>, erase_witness X, e)" 

lemma trace_imp_rerun_candidate:
  assumes "X \<in> \<lbrakk> P \<rbrakk>\<^sub>\<L>"
  shows "X \<in> \<langle> P \<rangle>\<^sub>\<L> \<and> L_consistent X"
oops

value "undefined (f := 3)"

end

