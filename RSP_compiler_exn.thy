theory RSP_compiler_exn imports
  RSP_high_level_PL
  RSP_low_level_PL
begin

subsection {* Compiling executions *}

text {* Each high-level instruction is mapped to a sequence of low-level
instructions. *}

fun compile_evt_lbl :: "H_lbl \<Rightarrow> nat \<times> L_lbl list"
where
  "compile_evt_lbl (Tau ()) = (0,[])" 
     
| "compile_evt_lbl (R x v (S_wi, _)) = (0, [R x v ()])"  
| "compile_evt_lbl (R x v (S_wg, _)) = (0, [R x v ()])"
| "compile_evt_lbl (R x v (S_dv, Normal)) = 
    (0, [R x v (), Tau (INVAL_L1, S_wg)])" 
| "compile_evt_lbl (R x v (S_dv, Remote)) = 
    (0, [R x v (), Tau (FLUSH_L1, S_dv), Tau (INVAL_L1, S_wg)])"
| "compile_evt_lbl (R x v (S_sy, _)) = undefined" 
    
| "compile_evt_lbl (W i x v (S_wi, _)) = (0, [W i x v ()])"
| "compile_evt_lbl (W i x v (S_wg, _)) = (0, [W i x v ()])"
| "compile_evt_lbl (W i x v (S_dv, Normal)) = 
    (1, [Tau (FLUSH_L1, S_wg), W i x v ()])"
| "compile_evt_lbl (W i x v (S_dv, Remote)) = 
    (3, [Tau (LK_rmw, S_dv), Tau (FLUSH_L1, S_wg), Tau (INVAL_L1, S_dv), W i x v (), Tau (UNLK_rmw, S_dv)])"
| "compile_evt_lbl (W i x v (S_sy, _)) = undefined"

| "compile_evt_lbl (RMW x v v' (S_wi, _)) = undefined"
| "compile_evt_lbl (RMW x v v' (S_wg, _)) = (0, [RMW x v v' ()])"
| "compile_evt_lbl (RMW x v v' (S_dv, Normal)) = 
    (1, [Tau (FLUSH_L1, S_wg), RMW x v v' (), Tau (INVAL_L1, S_wg) ])"
| "compile_evt_lbl (RMW x v v' (S_dv, Remote)) = 
    (3, [Tau (LK_rmw, S_dv), Tau (FLUSH_L1, S_wg), Tau (INVAL_L1, S_dv), RMW x v v' (), Tau (FLUSH_L1, S_dv), Tau (INVAL_L1, S_wg), Tau (UNLK_rmw, S_dv)])"
| "compile_evt_lbl (RMW x v v' (S_sy, _)) = undefined"


text {* The compilation is valid if there exists a function c that maps each
high-level eid to a list of low-level eids and satisfies various properties. *}
  
fun compile_pre_exn_under :: "(eid \<Rightarrow> eid list) \<Rightarrow> H_pre_exn \<Rightarrow> L_pre_exn \<Rightarrow> 
  bool"
where
  "compile_pre_exn_under c X Y = 
  
  (* The low-level events are the image under c of the high-event events *)
  (events Y = \<Union> (set ` c ` events X) \<and> 
  
  (* The labelling function agrees with the compile_event_lbl function *) 
  map (lbl Y) \<circ> c \<langle>=, events X\<rangle> snd \<circ> compile_evt_lbl \<circ> lbl X \<and>
  
  (* The device/workgroup/thread id functions are preserved *)
  (\<forall>e \<in> events X. list_all (op= (dvid X e) \<circ> dvid Y) (c e)) \<and>
  (\<forall>e \<in> events X. list_all (op= (cuid X e) \<circ> cuid Y) (c e)) \<and>
  (\<forall>e \<in> events X. list_all (op= (peid X e) \<circ> peid Y) (c e)) \<and>
  
  (* The low-level program order is obtained from the high-level program
  order, together with extra po-edges to link the events in the compiled
  sequence. *)
  sb Y = (\<Union> { set (c e1) \<times> set (c e2) | e1 e2. (e1, e2) \<in> sb X}) \<union> 
  (\<Union> (total_order_of ` c ` events X)))"  
  
fun inj_list_on :: "(eid \<Rightarrow> eid list) \<Rightarrow> eid set \<Rightarrow> bool"
where
  "inj_list_on c es = 
  ((\<forall>e \<in> es. distinct (c e)) \<and> (\<forall>e \<in> es. \<forall>e' \<in> es. e \<noteq> e' \<longrightarrow> set (c e) \<not>\<inter> set (c e')))"
  
fun compile_pre_exn :: "H_pre_exn \<Rightarrow> L_pre_exn \<Rightarrow> bool"
where
  "compile_pre_exn X Y = 
  (\<exists>c. inj_list_on c (events X) \<and> compile_pre_exn_under c X Y)"
  

end
