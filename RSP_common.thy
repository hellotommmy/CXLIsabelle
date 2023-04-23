(*header {* Definitions common to high-level and low-level PLs *}*)

theory RSP_common imports 
  RSP_helper
begin

typedecl raw_addr (* {* memory addresses *}*)
datatype addr = Atomic raw_addr | Nonatomic raw_addr










type_synonym val = nat  (* {* memory values *}*)









datatype RegNum = Reg nat

type_synonym Val = int

datatype MESI_State = Modified| Exclusive| Shared| Invalid

(*type_synonym Loc = nat*)

datatype ClusterID = Dev nat

(*datatype ByteLoc = Byte nat*)

(*
definition ByteLoc :: "nat set" where
  "ByteLoc = {..< 64}"*)
datatype BlockID = Block nat
(*
definition BlockID :: "nat set" where
  "BlockID = {..< 4}"
*)


datatype UTID = Utid nat

datatype CoreID = Core nat

record CLEntry = 
  content :: Val
  block_state :: MESI_State

record DevCLMap = 
  clid :: ClusterID
  coreid  :: CoreID
  bid  :: BlockID
  clentry :: CLEntry

type_synonym DevCLMap1= "ClusterID \<rightharpoonup> CoreID \<rightharpoonup> BlockID \<rightharpoonup> CLEntry "
(*tuple*)

type_synonym Cluster_State_Table = "ClusterID \<rightharpoonup> MESI_State"


text \<open>the name cl_state_mapping seems quite un-friendly for first time readers\<close>
record HostCLMap = 
  content :: "BlockID \<Rightarrow> Val"
  cl_state_mapping :: "BlockID \<Rightarrow> Cluster_State_Table"

definition empty_host_cl_map :: "HostCLMap"
  where [simp]:
  "empty_host_cl_map \<equiv> \<lparr> content = \<lambda>_. 0, cl_state_mapping = \<lambda>_. (\<lambda>id. None ) \<rparr>"



value "(content empty_host_cl_map) (Block 2)"
value "(cl_state_mapping empty_host_cl_map)  (Block 2) (Dev 2) "

text \<open>update the state of block bid_i in device clid_i to mesi_i in the host cacheline mapping table\<close>
fun update_host_cl_map_state :: "ClusterID \<Rightarrow> BlockID \<Rightarrow> MESI_State  \<Rightarrow> HostCLMap \<Rightarrow> HostCLMap"
  where
"update_host_cl_map_state cl b st \<Delta> = \<Delta> \<lparr> 
  cl_state_mapping :=   ( cl_state_mapping \<Delta>) (b := ((cl_state_mapping \<Delta>) b) ( cl := Some st)) 
                                                     \<rparr>
  "


value "let dev2shared = update_host_cl_map_state (Dev 2) (Block 2) Shared empty_host_cl_map in (cl_state_mapping dev2shared (Block 2) (Dev 2))"



datatype Instruction = 
      Write ClusterID CoreID BlockID Val RegNum
    | Read ClusterID CoreID BlockID RegNum
    | Evict ClusterID CoreID BlockID 
(*a equence of events one cluster issues, a sequence of events another cluster issues
read event v.s. load
cluster  issue messages *)


datatype DTHReqType = RdShared | RdOwn | RdAny | RdCurr | CleanEvict



record DTHReq = 
  utid :: UTID 
  bid :: BlockID
  dthreqop :: DTHReqType
  clid :: ClusterID

(*
record DTHReqFields =   
  bid :: BlockID
  dthreqop :: DTHReqType
  clid :: ClusterID

type_synonym DTHReq = "UTID \<rightharpoonup> DTHReqFields"
*)

type_synonym DTHReqs = "ClusterID \<Rightarrow> DTHReq list"
(*
type_synonym DTHReqs = "ClusterID \<rightharpoonup> DTHReq"
*)


datatype DTHRespType = RspIHitSE | RspIFwdM

record DTHRespFields = 
  bid :: BlockID
  dthresptype :: DTHRespType
  clid :: ClusterID


(*proposal: change it to utid \<Rightarrow> other fields*)
type_synonym DTHResp = "UTID \<rightharpoonup> DTHRespFields"

record DTHDataFields =  
  bid :: BlockID
  content :: Val
  clid :: ClusterID

  
type_synonym DTHData = "UTID \<rightharpoonup> DTHDataFields"

 

 
type_synonym DTHResps = "ClusterID \<Rightarrow> DTHResp list"

type_synonym DTHDatas = "ClusterID \<Rightarrow> DTHData list"



datatype HTDReqType = SnpData | SnpInv | SnpCur

record HTDReq = 
  utid :: UTID 
  bid :: BlockID
  htdreqop :: HTDReqType
  clid :: ClusterID

datatype HTDRespType = RspIHitSE | RspIFwdM


record HTDResp = 
  utid :: UTID
  bid :: BlockID
  htdresptype :: HTDRespType
  clid :: ClusterID

record HTDData = 
  utid :: UTID
  bid :: BlockID
  content :: Val
  clid :: ClusterID



type_synonym HTDReqs = "ClusterID \<Rightarrow> HTDReq list"

 
type_synonym HTDResps = "ClusterID \<Rightarrow> HTDResp list"

type_synonym HTDDatas = "ClusterID \<Rightarrow> HTDData list"


record DevTracker = 
  coreid  :: CoreID
  bid     :: BlockID
  st      :: MESI_State
  dNeeded :: bool
  dRecvd  :: bool
  rRecvd  :: bool
  dthreqtype :: DTHReqType

text \<open>Our model only deals with transactions initiated by a DTHRequest.\<close>

type_synonym DevTrackers = "UTID \<Rightarrow> DevTracker"
  
  
record HostTracker = 
  coreid  :: CoreID
  bid     :: BlockID
  st      :: MESI_State
  dNeeded :: bool
  dSent  :: bool
  rSent  :: bool
  dthreqtype :: DTHReqType

text \<open>Our model only deals with transactions initiated by a DTHRequest. Likewise trackers only
records DTH request types.\<close>

type_synonym HostTrackers = "UTID \<Rightarrow> DevTracker"





record Type1State = 
  hostmappings      :: HostCLMap
  devicemappings    :: DevCLMap
  dthreqs           :: DTHReqs
  dthresps          :: DTHResps
  dthdatas          :: DTHDatas
  htdreqs           :: HTDReqs
  htdresps          :: HTDResps
  htddatas          :: HTDDatas
  htrackers         :: HostTrackers
  dtrackers         :: DevTrackers
  





text{*for CXL*}
inductive state_transition :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool"
(infix "\<leadsto>ev" 30)
  where
"\<lbrakk> dthreqs \<Sigma>  dev_i = \<lparr>utid = utid1, bid = block_X, dthreqop = RdOwn, clid = dev_i\<rparr> # tail; 
   dthreqs \<Sigma>' dev_i = tail \<rbrakk> \<Longrightarrow> 
  
    
  \<Sigma> \<leadsto>ev \<Sigma>'"





(*

inductive env_trans :: "(eid \<times> eid list) sy_state \<Rightarrow> 
  (eid \<times> eid list) sy_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>\<e>" 50)
where
  evict_clean_L1:
  "\<lbrakk> Store (L1cache (\<Sigma>[dv]\<^sub>\<d>[cu]\<^sub>\<c>)) x = Some (_, _, Clean, _) ; 
     (dv :=\<^sub>\<d> cu :=\<^sub>\<c> update_L1 (x :=\<^sub>\<s> None)) \<Sigma> = \<Sigma>' \<rbrakk> \<Longrightarrow>
  \<Sigma> \<leadsto>\<^sub>\<e> \<Sigma>'"

Input = (Write(dev_i, cj, X, 1) ++ tail)
HostCLMap = (X, _(block data field not needed), dev_i, Invalid)

———————————————————————————————————————
DTHReqs[dev_i := [ (UCounter, X, RdOwn),  DTHReqs[dev_i] ] ]
HostTrackers = hd ++ (utid1, dev_i, block_x, RdOwn, 1, 1, 0) ++ tl
HostCLMap =  hd ++ (X, _, hd1 ++ (dev1, S) ++ hd2 ++ (dev_i, I) ++hd3)
UCounter := UCounter + 1

inductive state_transition :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool"
  where
*)

(*
definition empty_cache :: "_ cache"
where [simp]:
  "empty_cache \<equiv> \<lparr> Fifo = [], Store = (\<lambda>_. None) \<rparr>" 

*)











text {* Scope annotations *}
datatype scope =
  S_wi  (* Work item scope *)
(* | S_sg  {* Sub-group scope *} *)
| S_wg  (* Work-group scope *)
| S_dv  (* Device scope *)
| S_sy  (* System scope *)

text {* A thread is a list of instructions. *}
type_synonym 'ins thread = "'ins list"

text {* A workgroup is a list of threads. *}
type_synonym 'ins workgroup = "'ins thread list"

text {* An NDrange is a list of workgroups. *}
type_synonym 'ins ndrange = "'ins workgroup list"

text {* A program is a list of NDranges *}
type_synonym 'ins program = "'ins ndrange list"

datatype eid = E nat | InitE addr  (* identifies an event *) 
datatype dvid = Dv nat  (* identifies device *)
datatype cuid = Cu nat  (* identifies compute unit within device *)
datatype peid = Pe nat  (* identifies processing element within compute unit *)

fun nat_of_dvid where "nat_of_dvid (Dv i) = i"
fun nat_of_cuid where "nat_of_cuid (Cu i) = i"
fun nat_of_peid where "nat_of_peid (Pe i) = i"

(*
declare [[coercion nat_of_eid]]
declare [[coercion nat_of_dvid]]
declare [[coercion nat_of_cuid]]
declare [[coercion nat_of_peid]]
*)

text {* Labels on observable memory events *}

datatype write_type = Init | Noninit

datatype ('extra_info, 'tau_evt) lbl = 
  R addr val 'extra_info  (* read memory address at specific value *)
| W write_type addr val 'extra_info  (* write memory address with specific value *)
| RMW addr val val 'extra_info  (* rmw on memory address *) 
| Tau 'tau_evt

fun is_Tau :: "(_,_) lbl \<Rightarrow> bool"
where
  "is_Tau (Tau _) = True"
| "is_Tau _ = False"

type_synonym basic_lbl = "(unit, unit) lbl"

fun erase_evt :: "(_, _) lbl \<Rightarrow> basic_lbl"
where
  "erase_evt (R x v _) = R x v ()"
| "erase_evt (W wt x v _) = W wt x v ()"
| "erase_evt (RMW x v v' _) = RMW x v v' ()"
| "erase_evt (Tau _) = Tau ()"

record 'lbl pre_exn =
  events :: "eid set"
  lbl :: "eid \<Rightarrow> 'lbl"  (* label on event *)
  dvid :: "eid \<Rightarrow> dvid"  (* device responsible for event *)
  cuid :: "eid \<Rightarrow> cuid"  (* compute unit responsible for event *)
  peid :: "eid \<Rightarrow> peid"  (* processing element responsible for event *)
  sb :: "eid relation"  (* program order *)
  
fun erase_pre_exn :: "(_, _) lbl pre_exn \<Rightarrow> basic_lbl pre_exn"
where
  "erase_pre_exn X = \<lparr> 
    events = {e \<in> events X. \<not> is_Tau (lbl X e) },
    lbl = erase_evt \<circ> lbl X, 
    dvid = dvid X, 
    cuid = cuid X, 
    peid = peid X, 
    sb = {(e1,e2) \<in> sb X. \<not> is_Tau (lbl X e1) \<and> \<not> is_Tau (lbl X e2)} \<rparr>"
  
fun isomorphic_under :: "(eid \<Rightarrow> eid) \<Rightarrow> basic_lbl pre_exn \<Rightarrow> 
  basic_lbl pre_exn \<Rightarrow> bool" 
where
  "isomorphic_under \<pi> X Y = 
  (events Y = \<pi> ` events X \<and> 
  lbl X \<langle>=, events X\<rangle> lbl Y \<circ> \<pi> \<and> 
  dvid X \<langle>=, events X\<rangle> dvid Y \<circ> \<pi> \<and>
  cuid X \<langle>=, events X\<rangle> cuid Y \<circ> \<pi> \<and> 
  peid X \<langle>=, events X\<rangle> peid Y \<circ> \<pi> \<and> 
  sb Y = map_prod \<pi> \<pi> ` sb X)"
  
fun isomorphic :: "basic_lbl pre_exn \<Rightarrow> basic_lbl pre_exn \<Rightarrow> bool" 
  (infix "\<simeq>" 50)
where
  "X \<simeq> Y = (\<exists>\<pi>. inj_on \<pi> (events X) \<and> isomorphic_under \<pi> X Y)"




lemma 
  "\<lparr> events = {E 0, E 1, E 2}, 
     lbl = {E 0 \<mapsto> l1, E 1 \<mapsto> l2, E 2 \<mapsto> l3},
     dvid = {E 0 \<mapsto> Dv 0, E 1 \<mapsto> Dv 0, E 2 \<mapsto> Dv 1}, 
     cuid = {E 0 \<mapsto> Cu 0, E 1 \<mapsto> Cu 1, E 2 \<mapsto> Cu 0},
     peid = {E 0 \<mapsto> Pe 1, E 1 \<mapsto> Pe 2, E 2 \<mapsto> Pe 4}, 
     sb = {(E 0, E 1), (E 0, E 2), (E 1, E 2)} \<rparr> \<simeq> 
  \<lparr> events = {E 7, E 8, E 9}, 
    lbl = {E 7 \<mapsto> l1, E 8 \<mapsto> l2, E 9 \<mapsto> l3},
    dvid = {E 7 \<mapsto> Dv 0, E 8 \<mapsto> Dv 0, E 9 \<mapsto> Dv 1}, 
    cuid = {E 7 \<mapsto> Cu 0, E 8 \<mapsto> Cu 1, E 9 \<mapsto> Cu 0},
    peid = {E 7 \<mapsto> Pe 1, E 8 \<mapsto> Pe 2, E 9 \<mapsto> Pe 4}, 
    sb = {(E 7, E 8), (E 7, E 9), (E 8, E 9)} \<rparr>"

apply simp
apply (rule_tac x="{E 0 \<mapsto> E 7, E 1 \<mapsto> E 8, E 2 \<mapsto> E 9}" in exI)
apply simp
done

fun add_init_events :: "'extra_info \<Rightarrow> 
  ('extra_info, 'tau_evt) lbl pre_exn \<Rightarrow> ('extra_info, 'tau_evt) lbl pre_exn"
where
  "add_init_events extra_info X = X \<lparr> 
    events := events X \<union> {InitE x | x. True},
    lbl := (\<lambda>e. case e of E e \<Rightarrow> lbl X (E e) | InitE x \<Rightarrow> W Init x 0 extra_info)
  \<rparr>"

definition nil_pre_exn :: "'lbl pre_exn"
where [simp]:
  "nil_pre_exn = \<lparr> events = {}, lbl = undefined, dvid = undefined, 
  cuid = undefined, peid = undefined, sb = {} \<rparr>"

fun sing_pre_exn :: "eid \<Rightarrow> 'lbl \<Rightarrow> dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> 'lbl pre_exn"
where
  "sing_pre_exn e a dv cu pe = \<lparr> events = {e}, lbl = {e \<mapsto> a}, 
  dvid = {e \<mapsto> dv}, cuid = {e \<mapsto> cu}, peid = {e \<mapsto> pe}, sb = {} \<rparr>"
  
fun append_pre_exn :: "'lbl pre_exn \<Rightarrow> 'lbl pre_exn \<Rightarrow> 'lbl pre_exn" 
  (infix "@@" 65) 
where
  "\<lparr> events = E1, lbl = a1, dvid = dvid1, cuid = cuid1, peid = peid1, sb = sb1 \<rparr> @@ 
  \<lparr> events = E2, lbl = a2, dvid = dvid2, cuid = cuid2, peid = peid2, sb = sb2 \<rparr> =
  \<lparr> events = E1 \<union> E2, lbl = (a1,E1) \<oplus> (a2,E2), 
  dvid = (dvid1,E1) \<oplus> (dvid2,E2), cuid = (cuid1,E1) \<oplus> (cuid2,E2), 
  peid = (peid1,E1) \<oplus> (peid2,E2), sb = sb1 \<union> (E1 \<times> E2) \<union> sb2 \<rparr>"
  
fun par_pre_exn :: "'lbl pre_exn \<Rightarrow> 'lbl pre_exn \<Rightarrow> 'lbl pre_exn" 
  (infix "\<parallel>" 65) 
where
  "\<lparr> events = E1, lbl = a1, dvid = dvid1, cuid = cuid1, peid = peid1, sb = sb1 \<rparr>
  \<parallel>
  \<lparr> events = E2, lbl = a2, dvid = dvid2, cuid = cuid2, peid = peid2, sb = sb2 \<rparr> =
  \<lparr> events = E1 \<union> E2, lbl = (a1,E1) \<oplus> (a2,E2), 
  dvid = (dvid1,E1) \<oplus> (dvid2,E2), cuid = (cuid1,E1) \<oplus> (cuid2,E2), 
  peid = (peid1,E1) \<oplus> (peid2,E2), sb = sb1 \<union> sb2 \<rparr>"
  
fun append_evt :: "eid \<Rightarrow> 'lbl \<Rightarrow> dvid \<Rightarrow> cuid \<Rightarrow> peid \<Rightarrow> 'lbl pre_exn \<Rightarrow> 
  'lbl pre_exn"
where
  "append_evt e a dv cu pe X = 
  X \<lparr> events := events X \<union> {e}, 
  lbl := (lbl X) (e := a), 
  dvid := (dvid X) (e := dv), 
  cuid := (cuid X) (e := cu), 
  peid := (peid X) (e := pe), 
  sb := sb X \<union> {(e',e) | e'. dvid X e' = dv \<and> cuid X e' = cu \<and> peid X e' = pe } \<rparr>"

record witness =
  Rf :: "eid relation"
  Mo :: "eid relation" 
  
fun update_L_rf where "update_L_rf f Xo = Xo \<lparr> Rf := f (Rf Xo) \<rparr>"
fun update_L_mo where "update_L_mo f Xo = Xo \<lparr> Mo := f (Mo Xo) \<rparr>"  

record 'lbl exn = 
  Pre :: "'lbl pre_exn"
  Wit :: "witness"
  
fun update_pre where "update_pre f X = X \<lparr> Pre := f (Pre X) \<rparr>"
fun update_wit where "update_wit f X = X \<lparr> Wit := f (Wit X) \<rparr>"

fun erase_witness :: "'lbl exn \<Rightarrow> 'lbl exn"
where
  "erase_witness X = X \<lparr> Wit := \<lparr> Rf = {}, Mo = {} \<rparr> \<rparr>"
  
definition nil_exn :: "_ exn"
where [simp]:
  "nil_exn = \<lparr> Pre = nil_pre_exn, Wit = \<lparr> Rf = {}, Mo = {} \<rparr> \<rparr>"

end
