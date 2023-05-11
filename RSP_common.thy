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
  content :: "Val option"
  block_state :: MESI_State

(*
record DevCLMap = 
  clid :: ClusterID
  coreid  :: CoreID
  bid  :: BlockID
  clentry :: CLEntry
*)
type_synonym ClusterMap = "CoreID \<Rightarrow> BlockID \<rightharpoonup> CLEntry"
(*model a map entry as tuple and set restrictions in the starting state *)
(*Why not a function with many arrows? Not possible to (easily) add restrictions on a function?*)

type_synonym DevCLMap = "ClusterID \<Rightarrow> ClusterMap"

definition empty_dev_cl_map :: "DevCLMap"
  where [simp]:
  "empty_dev_cl_map \<equiv> \<lambda>clid. \<lambda>coreid. \<lambda>bid. None"



(*Alternative of using tuples, waiting to be seen which is better*)
type_synonym Cluster_State_Table = "ClusterID \<rightharpoonup> MESI_State "
text \<open>the name cl_state_mapping seems quite un-friendly for first time readers\<close>
record HostCLMap = 
  cl_content_mapping  :: "BlockID \<Rightarrow> Val"
  cl_state_mapping    :: "BlockID \<Rightarrow> Cluster_State_Table"

definition empty_host_cl_map :: "HostCLMap"
  where [simp]:
  "empty_host_cl_map \<equiv> \<lparr> cl_content_mapping = \<lambda>_. 0, cl_state_mapping = \<lambda>_. (\<lambda>id. None ) \<rparr>"


(*Initial state of the host cacheline: values are in their initial value, and no devices holds copies of host memory*)
value "(cl_content_mapping empty_host_cl_map) (Block 2)"
value "(cl_state_mapping empty_host_cl_map)  (Block 2) (Dev 2) "

type_synonym DevEntryUpdate = "(BlockID \<rightharpoonup> CLEntry) \<Rightarrow> BlockID \<Rightarrow>  CLEntry \<Rightarrow> (BlockID \<rightharpoonup> CLEntry)"


fun update_dev_with_entry :: DevEntryUpdate
  where "update_dev_with_entry devmap bid  entry = devmap (bid := Some entry)"



fun update_dev_cl_map_with_entry :: "ClusterID \<Rightarrow> CoreID \<Rightarrow> BlockID \<Rightarrow> CLEntry \<Rightarrow> DevCLMap \<Rightarrow> DevCLMap"
  where
"update_dev_cl_map_with_entry cl co block entry \<Delta> = \<Delta> ( cl := (\<Delta> cl) (co := ( (\<Delta> cl co ) (block := Some entry) )     ) ) "

fun update_dev_cl_map_with_state :: "ClusterID \<Rightarrow> CoreID \<Rightarrow> BlockID \<Rightarrow> MESI_State \<Rightarrow> DevCLMap \<Rightarrow> DevCLMap"
  where
"update_dev_cl_map_with_state cl co block state \<Delta> = \<Delta> ( cl := (\<Delta> cl) (co := ( (\<Delta> cl co ) (block := Some \<lparr>CLEntry.content = None, block_state = state\<rparr>) )     ) ) "


text \<open>update the state of block bid_i in device clid_i to mesi_i in the host cacheline mapping table\<close>
fun update_host_cl_map_state :: "ClusterID \<Rightarrow> BlockID \<Rightarrow> MESI_State  \<Rightarrow> HostCLMap \<Rightarrow> HostCLMap"
  where
"update_host_cl_map_state cl b st \<Delta> = \<Delta> \<lparr> 
  cl_state_mapping :=   ( cl_state_mapping \<Delta>) (b := ((cl_state_mapping \<Delta>) b) ( cl := Some st)) 
                                                     \<rparr>
  "


value "let dev2shared = update_host_cl_map_state (Dev 2) (Block 2) Shared empty_host_cl_map in 
          (cl_state_mapping dev2shared (Block 2) (Dev 2))"



datatype Instruction = 
      Write ClusterID CoreID BlockID Val RegNum
    | Read ClusterID CoreID BlockID RegNum
    | Evict ClusterID CoreID BlockID 
(*a sequence of events one cluster issues, a sequence of events another cluster issues
read event v.s. load
cluster  issue messages *)
type_synonym Program = "ClusterID \<Rightarrow> (CoreID \<Rightarrow> Instruction list)"

definition empty_program :: Program where [simp]:
"empty_program \<equiv> \<lambda>clid. \<lambda>coreid. []"

fun add_i :: "Program \<Rightarrow> Instruction \<Rightarrow> ClusterID \<Rightarrow> CoreID \<Rightarrow> Program"
  where "add_i P i clid core = P (clid := ( (P clid  ) (  core := (P clid core) @ [i])))"

definition write1 :: Instruction where "write1 = (Write (Dev 1) (Core 1) (Block 1) 2 (Reg 1))"
definition write2 :: Instruction where "write2 = (Write (Dev 2) (Core 2) (Block 1) 3 (Reg 1))"


definition two_devices_writing_at_same_location :: Program where
"two_devices_writing_at_same_location = add_i (add_i empty_program write1 (Dev 1) (Core 1)) write2 (Dev 2) (Core 2)"

datatype DTHReqType = RdShared | RdOwn | RdOwnNoData | RdAny | RdCurr | CleanEvict | DirtyEvict | CleanEvictNoData | 
  ItoMWrite | WrCur | CLFlush | CacheFlushed | WOWrInv | WOWrInvF | WrInv



record DTHReq = 
  utid :: UTID 
  bid :: BlockID
  dthreqtype :: DTHReqType
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

definition empty_dthreqs :: DTHReqs where [simp]:
"empty_dthreqs \<equiv> \<lambda>clid. []"


datatype DTHRespType = RspIHitI | RspIHitSE |RspSHitSE | RspVHitV | RspIFwdM  | RspVFwdV  | RspSFwdM

record DTHResp = 
  utid:: UTID
  bid :: BlockID
  dthresptype :: DTHRespType
  clid :: ClusterID



record DTHData =  
  utid:: UTID
  bid :: BlockID
  content :: Val
  clid :: ClusterID
  bogus :: bool

  
(*type_synonym DTHData = "UTID \<rightharpoonup> DTHDataFields" *)



 
type_synonym DTHResps = "ClusterID \<Rightarrow> DTHResp list"

definition empty_dthresps :: DTHResps where [simp]:
"empty_dthresps \<equiv> \<lambda>clid. []"


type_synonym DTHDatas = "ClusterID \<Rightarrow> DTHData list"

definition empty_dthdatas :: DTHDatas where [simp]:
"empty_dthdatas \<equiv> \<lambda>clid. []"



datatype HTDReqType = SnpData | SnpInv | SnpCur

record HTDReq = 
  utid :: UTID 
  bid :: BlockID
  htdreqtype :: HTDReqType
  clid :: ClusterID

datatype HTDRespType = GO | GO_WritePull | GO_WritePullDrop | WritePull | 
    GO_Err | FastGO_WritePull | GO_Err_WritePull | ExtCmp


record HTDResp = 
  utid :: UTID
  bid :: BlockID
  htdresptype :: HTDRespType
  clid :: ClusterID
  state_granted :: MESI_State

record HTDData = 
  utid :: UTID
  bid :: BlockID
  content :: Val
  clid :: ClusterID



type_synonym HTDReqs = "ClusterID \<Rightarrow> HTDReq list"

definition empty_htdreqs :: HTDReqs where [simp]:
"empty_htdreqs \<equiv> \<lambda>clid. []"

 
type_synonym HTDResps = "ClusterID \<Rightarrow> HTDResp list"
definition empty_htdresps :: HTDResps where [simp]:
"empty_htdresps \<equiv> \<lambda>clid. []"

type_synonym HTDDatas = "ClusterID \<Rightarrow> HTDData list"
definition empty_htddatas :: HTDDatas where [simp]:
"empty_htddatas \<equiv> \<lambda>clid. []"

record DevTracker = 
  clusterid :: ClusterID
  coreid  :: CoreID
  bid     :: BlockID
  st      :: MESI_State
  dNeeded :: bool
  dataCompleted  :: bool
  rRecvd  :: bool
  dthreqtype :: DTHReqType

text \<open>Our model only deals with transactions initiated by a DTHRequest.\<close>

type_synonym DevTrackers = "UTID \<rightharpoonup> DevTracker"
definition empty_devtrackers :: DevTrackers where [simp]:
"empty_devtrackers \<equiv> \<lambda>utid. None"


record HostTracker = 
  clusterid :: ClusterID
  coreid  :: CoreID
  bid     :: BlockID
  st      :: MESI_State
  dNeeded :: bool
  dSent  :: bool
  rSent  :: bool
  dthreqtype :: DTHReqType

text \<open>Our model only deals with transactions initiated by a DTHRequest. Likewise trackers only
records DTH request types.\<close>

type_synonym HostTrackers = "UTID \<rightharpoonup> HostTracker"

definition empty_hosttrackers :: HostTrackers where [simp]:
"empty_hosttrackers \<equiv> \<lambda>utid. None"




record Type1State = 
  hostclmap      :: HostCLMap
  devclmap    :: DevCLMap
  dthreqs           :: DTHReqs
  dthresps          :: DTHResps
  dthdatas          :: DTHDatas
  htdreqs           :: HTDReqs
  htdresps          :: HTDResps
  htddatas          :: HTDDatas
  hosttrackers         :: HostTrackers
  devtrackers         :: DevTrackers
  





text \<open> for CXL \<close>
fun differ_one_instruction :: "Program \<Rightarrow> Program \<Rightarrow> 
  ClusterID \<Rightarrow> CoreID \<Rightarrow> Instruction \<Rightarrow> bool"
  where "differ_one_instruction P P' dev_i core_j i = 
    (P = P'(dev_i := (P' dev_i) (core_j := (i # P' dev_i core_j ))))"

fun host_mapping_state :: "Type1State \<Rightarrow> ClusterID \<Rightarrow>
  BlockID \<Rightarrow> MESI_State \<Rightarrow> bool"
  where "host_mapping_state \<Sigma> dev_i X mesi_state = 
    ((cl_state_mapping (hostclmap \<Sigma>) ) X dev_i = Some mesi_state)"

fun host_stored_val_is :: "Type1State  \<Rightarrow>
  BlockID \<Rightarrow> Val \<Rightarrow> bool"
  where "host_stored_val_is \<Sigma> X v = 
    ((cl_content_mapping (hostclmap \<Sigma>) ) X  =  v)"

fun dev_stored_val_is :: "Type1State \<Rightarrow> ClusterID \<Rightarrow> CoreID \<Rightarrow> BlockID \<Rightarrow> Val \<Rightarrow> bool"
  where "dev_stored_val_is \<Sigma> devi corej X v = 
    (\<exists>dontCareState. ((devclmap \<Sigma>) devi corej X = Some \<lparr>CLEntry.content = Some v, block_state = dontCareState \<rparr> ))"

fun dequeued_dthreq :: "Type1State \<Rightarrow> Type1State \<Rightarrow> ClusterID \<Rightarrow> DTHReq \<Rightarrow> bool"
  where "dequeued_dthreq \<Sigma> \<Sigma>' dev_i msg = 
    (\<Sigma>' = \<Sigma> \<lparr>dthreqs := ((dthreqs \<Sigma>) (dev_i := (dthreqs \<Sigma>) dev_i  @ [msg] )) \<rparr> ) "


(*TODO: Bogus field? Once the device has issued this command (DirtyEvict)
and the address is subsequently snooped, but before the device 
has received the GO-WritePull, the device must set the Bogus field in 
all D2H Data messages to indicate that the data is now stale.
*)
(*
definition State0, State1, etc.
*)


inductive internal_transition :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool"
(infix "\<leadsto>env" 30)
  where
RdOwn_requesting: "\<lbrakk>  
    dthreqs \<Sigma>  dev_i = \<lparr>DTHReq.utid = utid1, bid = block_X, dthreqtype = RdOwn, clid = dev_i\<rparr> # tail ;
    dthreqs \<Sigma>'  dev_i = tail; 
    
    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = RdOwn \<rparr>;

    \<forall> dev_ip \<in> Sharers. 
      (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_ip = Some Shared;
    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - Sharers). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;
    (hosttrackers \<Sigma>) utid1 = None;

    dthreqs \<Sigma>' dev_i = tail;
    (hosttrackers \<Sigma>') utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = False, dthreqtype = RdOwn  \<rparr>;
    \<forall> dev_ip \<in> Sharers. (htdreqs \<Sigma>') dev_ip = ((htdreqs \<Sigma>) dev_ip) @ [\<lparr>HTDReq.utid = utid1, bid = block_X, 
      htdreqtype = SnpInv, clid = dev_ip \<rparr>];
    (htddatas \<Sigma>') dev_i = (htddatas \<Sigma>') dev_i @ [\<lparr>HTDData.utid = utid1, bid = block_X, content = v, clid = dev_i \<rparr>]
\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
| RdOwn_requesting_owned: "\<lbrakk>  
    dthreqs \<Sigma>  dev_i = \<lparr>DTHReq.utid = utid1, bid = block_X, dthreqtype = RdOwn, clid = dev_i\<rparr> # tail ; 
    dthreqs \<Sigma>' dev_i = tail;

    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = RdOwn \<rparr>;


    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_owner = Some Exclusive;
    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - {dev_owner}). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = Some Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;
    (hosttrackers \<Sigma>) utid1 = None;


    (hosttrackers \<Sigma>') utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = False, dthreqtype = RdOwn  \<rparr>;
    (htdreqs \<Sigma>') dev_owner =  ((htdreqs \<Sigma>) dev_owner) @ [\<lparr>HTDReq.utid = utid1, bid = block_X, 
      htdreqtype = SnpInv, clid = dev_owner \<rparr>]
\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
|
RdOwn_DTHResp_shared: "\<lbrakk>  

    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = RdOwn \<rparr>;
    dev_ip \<in> Sharers;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_ip = Some Shared;
    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - Sharers). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = Some Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;


    (hosttrackers \<Sigma>) utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = False, dthreqtype = RdOwn  \<rparr>;
    (htdreqs \<Sigma>) dev_ip =  \<lparr>HTDReq.utid = utid1, bid = block_X, 
      htdreqtype = SnpInv, clid = dev_ip \<rparr> # tailh;
    (htdreqs \<Sigma>') dev_ip = tailh;

    (dthresps \<Sigma>) dev_ip = inith;
    (dthresps \<Sigma>') dev_ip = inith @ [\<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIHitSE, clid = dev_ip\<rparr>]

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
|
RdOwn_DTHResp_owned_Exclusive: "\<lbrakk>  

    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = RdOwn \<rparr>;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_owner = Some Exclusive;
    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - {dev_owner}). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = Some Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;

    (devclmap \<Sigma>) dev_owner core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Exclusive \<rparr>;
    (devclmap \<Sigma>') dev_owner core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Invalid \<rparr>;


    (hosttrackers \<Sigma>) utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = False, dthreqtype = RdOwn  \<rparr>;
    (htdreqs \<Sigma>) dev_owner =  \<lparr>HTDReq.utid = utid1, bid = block_X, 
      htdreqtype = SnpInv, clid = dev_ip \<rparr> # tailh;
    (htdreqs \<Sigma>') dev_owner = tailh;

    (dthresps \<Sigma>) dev_owner = inith;
    (dthresps \<Sigma>') dev_owner = inith @ [\<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIHitSE, clid = dev_ip\<rparr>]

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
|
RdOwn_DTHResp_owned_Modified: "\<lbrakk>  

    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = RdOwn \<rparr>;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_owner = Some Exclusive \<or> 
      (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_owner = Some Modified;


    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - {dev_owner}). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = Some Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;
    
    (devclmap \<Sigma>) dev_owner core_j X = Some \<lparr>CLEntry.content = Some v', block_state = Modified \<rparr>;
    (devclmap \<Sigma>') dev_owner core_j X = Some \<lparr>CLEntry.content = Some v', block_state = Invalid \<rparr>;

    (hosttrackers \<Sigma>) utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = False, dthreqtype = RdOwn  \<rparr>;
    (htdreqs \<Sigma>) dev_owner =  \<lparr>HTDReq.utid = utid1, bid = block_X, 
      htdreqtype = SnpInv, clid = dev_ip \<rparr> # tailh;
    (htdreqs \<Sigma>') dev_owner = tailh;

    (dthresps \<Sigma>) dev_owner = inith;
    (dthresps \<Sigma>') dev_owner = inith @ [\<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIFwdM, clid = dev_ip\<rparr>];

    (dthdatas \<Sigma>) dev_owner = initd;
    (dthdatas \<Sigma>') dev_owner = initd @ [\<lparr>DTHData.utid = utid1, bid = block_X, content = v', clid = dev_owner, bogus = False \<rparr>]

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
| RdOwn_HTDResp_owned_Exclusive: "\<lbrakk>  
    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = RdOwn \<rparr>;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_owner = Some Exclusive;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) 
        block_X dev_owner = Some Invalid;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_i = Some Invalid;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) 
        block_X dev_i = Some Exclusive \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) 
        block_X dev_i = Some Modified;
    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - {dev_owner}). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = Some Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;


    (hosttrackers \<Sigma>) utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = dSentbool, rSent = False, dthreqtype = RdOwn  \<rparr>;
    (hosttrackers \<Sigma>') utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = dSentbool, rSent = True, dthreqtype = RdOwn  \<rparr>;


    (dthresps \<Sigma>) dev_owner =  \<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIHitSE, clid = dev_owner\<rparr> # tailDTHResp \<or>
      (dthresps \<Sigma>) dev_owner =  \<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIHitI, clid = dev_owner\<rparr> # tailDTHResp;
    (dthresps \<Sigma>') dev_owner = tailDTHResp;
    (htdresps \<Sigma>) dev_i = p_init;
    (htdresps \<Sigma>') dev_i = p_init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = Exclusive \<rparr>]

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
| HTDResp_owned_Modified: "\<lbrakk>  
    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = dataCompletedbool, rRecvd = False, dthreqtype = dthrequired \<rparr>;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_owner = Some Exclusive \<or>     
      (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_owner = Some Modified;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) block_X dev_owner = Some Invalid;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_i = Some Invalid;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) block_X dev_i = Some Exclusive;
    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - {dev_owner}). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = Some Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;


    (hosttrackers \<Sigma>) utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = dSentbool, rSent = False, dthreqtype = RdOwn  \<rparr>;
    (hosttrackers \<Sigma>') utid1 = (if(dSentbool) then None else Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = True, dthreqtype = RdOwn  \<rparr>);

    (dthresps \<Sigma>) dev_owner =  \<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIFwdM, clid = dev_owner\<rparr> # tailDTHResp;
    (dthresps \<Sigma>') dev_owner = tailDTHResp;
    (htdresps \<Sigma>) dev_i = p_init;
    (htdresps \<Sigma>') dev_i = (if(dthrequired = RdOwn) then p_init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = Exclusive \<rparr>]
                            else if (dthrequired = RdShared) then p_init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = Shared \<rparr>]
                            else if (dthrequired = RdCurr) then   p_init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = Invalid \<rparr>]
                            else if (dthrequired = RdAny)  then   p_init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = Exclusive \<rparr>]
                            else p_init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = Exclusive \<rparr>])



\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
| HTDData_sending: "
\<lbrakk>    (dthdatas \<Sigma>) dev_owner = \<lparr>DTHData.utid = utid1, bid = block_X, content = v', clid = dev_owner, bogus = False\<rparr> # tailDTHData;
    (dthdatas \<Sigma>') dev_owner = tailDTHData;

    (hosttrackers \<Sigma>) utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = rSentbool, dthreqtype = dthreq1  \<rparr>;
    (hosttrackers \<Sigma>') utid1 = (if (\<not>rSentbool) then Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Exclusive,
      dNeeded = True, dSent = True, rSent = rSentbool, dthreqtype = dthreq1  \<rparr> else None );
    
    (cl_content_mapping (hostclmap \<Sigma>')) block_X = v';

    (htddatas \<Sigma>) dev_i = init_HTDData;
    (htddatas \<Sigma>') dev_i = init_HTDData @ [\<lparr>HTDData.utid = utid1, bid = block_X, content = v', clid = dev_i\<rparr>]\<rbrakk> \<Longrightarrow> \<Sigma> \<leadsto>env \<Sigma>'
"
| RdOwn_HTDResp_Shared: "\<lbrakk>  
    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = dCompletedBool, rRecvd = False, dthreqtype = RdOwn \<rparr>;
    

    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_is = Some Shared \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_is = Some Invalid;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) 
        block_X dev_is = Some Invalid;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_i = Some Invalid \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_i = None;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) block_X dev_i = Some Exclusive;
    \<forall> dev_iq \<in> ((UNIV::ClusterID set) - Sharers). 
       (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = None \<or> (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) block_X dev_iq = Some Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v;


    (hosttrackers \<Sigma>) utid1 = Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = dNeededbool, dSent = dSentbool, rSent = False, dthreqtype = RdOwn  \<rparr>;
    (hosttrackers \<Sigma>') utid1 = (if (dSentbool \<or> \<not>dNeededbool) then None else Some \<lparr>HostTracker.clusterid = dev_i, coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = dNeededbool, dSent = dSentbool, rSent = True, dthreqtype = RdOwn  \<rparr>);

    (dthresps \<Sigma>) dev_is =  \<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIHitSE, clid = dev_is\<rparr> # tailDTHResp \<or>
      (dthresps \<Sigma>) dev_is =  \<lparr>DTHResp.utid = utid1, bid = block_X, dthresptype = RspIHitI, clid = dev_is\<rparr> # tailDTHResp;
    (dthresps \<Sigma>') dev_is = tailDTHResp;
    (htdresps \<Sigma>) dev_i = i_init;
    (htdresps \<Sigma>') dev_i = i_init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = Exclusive \<rparr>];
    (if (dNeededbool \<and> \<not>dSentbool) then (htddatas \<Sigma>') dev_i = 
                                        ((htddatas \<Sigma>) dev_i) @ [\<lparr>HTDData.utid = utid1, bid = block_X, content = v, clid = dev_i\<rparr>] else True)

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"

| finish_GO: "\<lbrakk>  
    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = _,
    dNeeded = True, dataCompleted = dataCompletedBool, rRecvd = False, dthreqtype = dthreq \<rparr>;
    devtrackers \<Sigma>' utid1 = (if(dataCompletedBool) then None else Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = _,
    dNeeded = True, dataCompleted = dataCompletedBool, rRecvd = True, dthreqtype = dthreq \<rparr>);

    (htdresps \<Sigma>) dev_i = \<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO, clid = dev_i, state_granted = S \<rparr> # itail;
    (htdresps \<Sigma>') dev_i = i_tail;

    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_i = Some S;


    (devclmap \<Sigma>) dev_i core_j block_X = _;
    (devclmap \<Sigma>') dev_i core_j block_X = Some \<lparr>CLEntry.content = Some 0, block_state = S\<rparr>

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"

| finish_Data: "\<lbrakk>  
    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = _,
    dNeeded = True, dataCompleted = False, rRecvd = rRecvdBool, dthreqtype = dthreq \<rparr>;
    devtrackers \<Sigma>' utid1 = (if(rRecvdBool) then None else Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = _,
    dNeeded = True, dataCompleted = True, rRecvd = rRecvdBool, dthreqtype = dthreq \<rparr>);

    (htddatas \<Sigma>) dev_i = \<lparr>HTDData.utid = utid1, bid = block_X, content = v', clid = dev_i \<rparr> # itail;
    (htddatas \<Sigma>') dev_i = i_tail;

    (devclmap \<Sigma>) dev_i core_j block_X = Some \<lparr>CLEntry.content = _, block_state = S\<rparr>;
    (devclmap \<Sigma>') dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v', block_state = S\<rparr>

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"

| DirtyEvict_responding: "\<lbrakk>  
    dthreqs \<Sigma>  dev_i = \<lparr>DTHReq.utid = utid1, bid = block_X, dthreqtype = DirtyEvict, clid = dev_i\<rparr> # tail ; 
    dthreqs \<Sigma>' dev_i = tail;

    htdresps \<Sigma>  dev_i = init;
    htdresps \<Sigma>' dev_i =  init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO_WritePull, clid = dev_i, state_granted = Invalid \<rparr>];

    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Modified,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = DirtyEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = DirtyEvict \<rparr>;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_i = Some Modified;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) 
        block_X dev_i = Some Invalid;
    (hosttrackers \<Sigma>) utid1 = None;

    
    (hosttrackers \<Sigma>') utid1 = Some \<lparr>HostTracker.clusterid = dev_i, HostTracker.coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = True, dthreqtype = DirtyEvict  \<rparr>
\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
| DirtyEvict_data_sending: " \<lbrakk>
    (hosttrackers \<Sigma>) utid1 =  Some \<lparr>HostTracker.clusterid = dev_i, HostTracker.coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = False, dthreqtype = DirtyEvict  \<rparr>;
     htdresps \<Sigma> dev_i = \<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO_WritePull, clid = dev_i, state_granted = _ \<rparr> # tail;
     htdresps \<Sigma>' dev_i = tail;

    devtrackers \<Sigma> utid1 = Some \<lparr> DevTracker.clusterid = dev_i, DevTracker.coreid = core_j, DevTracker.bid = block_X, st = Invalid, 
      dNeeded = True, dataCompleted = _, rRecvd = _, dthreqtype = DirtyEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = Some \<lparr>DevTracker.clusterid = dev_i,  DevTracker.coreid = core_j, DevTracker.bid = block_X, st = Invalid, 
      dNeeded = True, dataCompleted = True, rRecvd = True, dthreqtype = DirtyEvict \<rparr>;

    (dthdatas \<Sigma>)  dev_i = init;
    (dthdatas \<Sigma>') dev_i = init @ [ \<lparr>DTHData.utid = utid1, bid = block_X, content = v, clid = dev_i, bogus = False \<rparr>];

    (devclmap \<Sigma>) dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Modified \<rparr>;
    (devclmap \<Sigma>') dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Invalid \<rparr>;

    (cl_state_mapping (hostclmap \<Sigma>)) block_X dev_i = Some Invalid;
    (cl_state_mapping (hostclmap \<Sigma>')) block_X dev_i = Some Invalid
      
    \<rbrakk> \<Longrightarrow> \<Sigma> \<leadsto>env \<Sigma>'"
| DirtyEvict_finish: "\<lbrakk>
    (hosttrackers \<Sigma>) utid1 =  Some \<lparr>HostTracker.clusterid = dev_i, HostTracker.coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = True, dthreqtype = DirtyEvict  \<rparr>;
    (hosttrackers \<Sigma>') utid1 = None;

    devtrackers \<Sigma> utid1 = Some \<lparr> DevTracker.clusterid = dev_i, DevTracker.coreid = core_j, DevTracker.bid = block_X, st = Invalid, 
      dNeeded = True, dataCompleted = False, rRecvd = True, dthreqtype = DirtyEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = None;

    (dthdatas \<Sigma>)  dev_i =   \<lparr>DTHData.utid = utid1, bid = block_X, content = v, clid = dev_i, bogus = False \<rparr> # dtail;
    (dthdatas \<Sigma>') dev_i = dtail;

    (devclmap \<Sigma>) dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Modified \<rparr>;
    (devclmap \<Sigma>') dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Invalid \<rparr>;

    (cl_content_mapping (hostclmap \<Sigma>)) block_X  = v;
    (cl_state_mapping (hostclmap \<Sigma>')) block_X dev_i = Some Invalid
      
    \<rbrakk> \<Longrightarrow> \<Sigma> \<leadsto>env \<Sigma>'"
| CleanEvict_responding_requires_data: "\<lbrakk>  
    dthreqs \<Sigma>  dev_i = \<lparr>DTHReq.utid = utid1, bid = block_X, 
      dthreqtype = CleanEvict, clid = dev_i\<rparr> # tail ; 
    dthreqs \<Sigma>' dev_i = tail;

    htdresps \<Sigma>  dev_i = init;
    htdresps \<Sigma>' dev_i =  init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO_WritePull, clid = dev_i, state_granted = Invalid \<rparr>];

    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Exclusive,
    dNeeded = False, dataCompleted = False, rRecvd = False, dthreqtype = CleanEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = CleanEvict \<rparr>;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_i = Some Modified;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>')) 
        block_X dev_i = Some Invalid;
    (hosttrackers \<Sigma>) utid1 = None;

    
    (hosttrackers \<Sigma>') utid1 = Some \<lparr>HostTracker.clusterid = dev_i, HostTracker.coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = True, dthreqtype = CleanEvict  \<rparr>


\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
| CleanEvict_responding_nodata: "\<lbrakk>  
    dthreqs \<Sigma>  dev_i = \<lparr>DTHReq.utid = utid1, bid = block_X, 
      dthreqtype = CleanEvict, clid = dev_i\<rparr> # tail ; 
    dthreqs \<Sigma>' dev_i = tail;

    htdresps \<Sigma>  dev_i = init;
    htdresps \<Sigma>' dev_i =  init @ [\<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO_WritePullDrop, clid = dev_i, state_granted = Invalid \<rparr>];

    devtrackers \<Sigma> utid1 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Exclusive,
    dNeeded = False, dataCompleted = False, rRecvd = False, dthreqtype = CleanEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = devtrackers \<Sigma> utid1;
    (HostCLMap.cl_state_mapping (hostclmap \<Sigma>)) 
        block_X dev_i = Some Invalid;
    (hosttrackers \<Sigma>) utid1 = None;

    
    (hosttrackers \<Sigma>') utid1 = Some \<lparr>HostTracker.clusterid = dev_i, HostTracker.coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = False, dSent = False, rSent = True, dthreqtype = CleanEvict  \<rparr>

\<rbrakk> \<Longrightarrow> 
  \<Sigma> \<leadsto>env \<Sigma>'"
| CleanEvict_DTHData: " \<lbrakk>
    (hosttrackers \<Sigma>) utid1 =  Some \<lparr>HostTracker.clusterid = dev_i, HostTracker.coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = False, dthreqtype = CleanEvict  \<rparr>;
     htdresps \<Sigma> dev_i = \<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO_WritePull, clid = dev_i, state_granted = _ \<rparr> # tail;
     htdresps \<Sigma>' dev_i = tail;

    devtrackers \<Sigma> utid1 = Some \<lparr> DevTracker.clusterid = dev_i, DevTracker.coreid = core_j, DevTracker.bid = block_X, st = Invalid, 
      dNeeded = _, dataCompleted = False, rRecvd = False, dthreqtype = CleanEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = None;

    (dthdatas \<Sigma>)  dev_i = init;
    (dthdatas \<Sigma>') dev_i = init @ [ \<lparr>DTHData.utid = utid1, bid = block_X, content = v, clid = dev_i, bogus = False \<rparr>];

    (devclmap \<Sigma>) dev_i  core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Modified \<rparr>;
    (devclmap \<Sigma>') dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Invalid \<rparr>;

    (cl_state_mapping (hostclmap \<Sigma>)) block_X dev_i = Some Invalid;
    (cl_state_mapping (hostclmap \<Sigma>')) block_X dev_i = Some Invalid
      
    \<rbrakk> \<Longrightarrow> \<Sigma> \<leadsto>env \<Sigma>'"
| CleanEvict_nodata_finish: " \<lbrakk>
    (hosttrackers \<Sigma>) utid1 =  None;
    (hosttrackers \<Sigma>') utid1 =  None;
     htdresps \<Sigma> dev_i = \<lparr>HTDResp.utid = utid1, bid = block_X, htdresptype = GO_WritePullDrop, clid = dev_i, state_granted = _\<rparr> # tail;
     htdresps \<Sigma>' dev_i = tail;

    devtrackers \<Sigma> utid1 = Some \<lparr> DevTracker.clusterid = dev_i, DevTracker.coreid = core_j, DevTracker.bid = block_X, st = Invalid, 
      dNeeded = False, dataCompleted = False, rRecvd = rRecvdBool, dthreqtype = CleanEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = None;

    (dthdatas \<Sigma>)  dev_i = (dthdatas \<Sigma>') dev_i;

    (devclmap \<Sigma>) dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Modified \<rparr>;
    (devclmap \<Sigma>') dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Invalid \<rparr>;

    (cl_state_mapping (hostclmap \<Sigma>)) block_X dev_i = Some Invalid;
    (cl_state_mapping (hostclmap \<Sigma>')) block_X dev_i = Some Invalid
      
    \<rbrakk> \<Longrightarrow> \<Sigma> \<leadsto>env \<Sigma>'"
| CleanEvict_finish_data: "\<lbrakk>
    (hosttrackers \<Sigma>) utid1 =  Some \<lparr>HostTracker.clusterid = dev_i, HostTracker.coreid = core_j, HostTracker.bid = block_X, st = Invalid,
      dNeeded = True, dSent = False, rSent = rSentBool, dthreqtype = CleanEvict  \<rparr>;
    (hosttrackers \<Sigma>') utid1 = None;

    devtrackers \<Sigma> utid1 = Some \<lparr> DevTracker.clusterid = dev_i, DevTracker.coreid = core_j, DevTracker.bid = block_X, st = Invalid, 
      dNeeded = True, dataCompleted = False, rRecvd = True, dthreqtype = CleanEvict \<rparr>;
    devtrackers \<Sigma>' utid1 = None;

    (dthdatas \<Sigma>)  dev_i =   \<lparr>DTHData.utid = utid1, bid = block_X, content = v, clid = dev_i, bogus = False \<rparr> # dtail;
    (dthdatas \<Sigma>') dev_i = dtail;

    (devclmap \<Sigma>) dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Modified \<rparr>;
    (devclmap \<Sigma>') dev_i core_j X = Some \<lparr>CLEntry.content = Some v, block_state = Invalid \<rparr>;

    (cl_content_mapping (hostclmap \<Sigma>)) block_X  = v;
    (cl_state_mapping (hostclmap \<Sigma>')) block_X dev_i = Some Invalid
      
    \<rbrakk> \<Longrightarrow> \<Sigma> \<leadsto>env \<Sigma>'"

   



(*Still psuedo-code, should express \<Sigma> and \<Sigma>' only differ in those
places, rather than "they are different in these places, can be arbitrary
in other places we didn't mention. Need to use \<Sigma>[ i := X] type of syntax"*)
inductive external_trans :: "(Type1State * Program * nat * Instruction option * UTID) \<Rightarrow> (Type1State * Program * nat * Instruction option * UTID) \<Rightarrow> bool"
(infixr "\<leadsto>ext" 30)
where
RdOwn_start: 
" \<lbrakk>  
    differ_one_instruction P P' dev_i core_j (Write dev_i core_j block_X v reg) ;

    host_mapping_state \<Sigma> dev_i block_X Invalid;

    utid2 = Utid UCounter;
    dequeued_dthreq \<Sigma> \<Sigma>' dev_i \<lparr>DTHReq.utid = utid2, bid = block_X, dthreqtype = RdOwn, clid = dev_i \<rparr>;

    (devclmap \<Sigma>) dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v, block_state = Invalid \<rparr>;
    (devclmap \<Sigma>) = (devclmap \<Sigma>');

    devtrackers \<Sigma>  utid2 = None;
    devtrackers \<Sigma>' utid2 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Invalid,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = RdOwn \<rparr>
  
    
\<rbrakk>
\<Longrightarrow>
(\<Sigma>, P, UCounter, None, _) \<leadsto>ext (\<Sigma>', P', UCounter + 1, Some (Write dev_i core_j block_X v reg), utid2 )"
|
RdOwn_finish: 
" \<lbrakk>  

    host_mapping_state \<Sigma> dev_i block_X Exclusive;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v';

    (devclmap \<Sigma>) dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v', block_state = Exclusive \<rparr>;
    (devclmap \<Sigma>') dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v'', block_state = Modified \<rparr>;

    (hosttrackers \<Sigma>) utid2 = None;
    
    (devtrackers \<Sigma>) utid2 = None
    
\<rbrakk>
\<Longrightarrow>
(\<Sigma>, P, UCounter,  Some (Write dev_i core_j block_X v'' reg), utid2) \<leadsto>ext (\<Sigma>', P', UCounter, None, _ )"
|
DirtyEvict_start: 
" \<lbrakk>  
    differ_one_instruction P P' dev_i core_j (Evict dev_i core_j block_X ) ;

    host_mapping_state \<Sigma> dev_i block_X Modified;

    utid2 = Utid UCounter;
    dequeued_dthreq \<Sigma> \<Sigma>' dev_i \<lparr>DTHReq.utid = utid2, bid = block_X, dthreqtype = DirtyEvict, clid = dev_i \<rparr>;

    (devclmap \<Sigma>) dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v, block_state = Modified \<rparr>;
    (devclmap \<Sigma>) = (devclmap \<Sigma>');

    (devtrackers \<Sigma>)  utid2 = None;
    (devtrackers \<Sigma>') utid2 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Modified,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = DirtyEvict \<rparr>
    
\<rbrakk>
\<Longrightarrow>
(\<Sigma>, P, UCounter, None, _) \<leadsto>ext (\<Sigma>', P', UCounter + 1, Some (Evict dev_i core_j block_X ), utid2)"
|DirtyEvict_start': 
" \<lbrakk>  
    P = P' ;

    host_mapping_state \<Sigma> dev_i block_X Modified;

    utid2 = Utid UCounter;
    dequeued_dthreq \<Sigma> \<Sigma>' dev_i \<lparr>DTHReq.utid = utid2, bid = block_X, dthreqtype = DirtyEvict, clid = dev_i \<rparr>;

    (devclmap \<Sigma>) dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v, block_state = Modified \<rparr>;
    (devclmap \<Sigma>) = (devclmap \<Sigma>');

    (devtrackers \<Sigma>)  utid2 = None;
    (devtrackers \<Sigma>') utid2 = Some \<lparr>DevTracker.clusterid = dev_i, coreid = core_j, DevTracker.bid  = block_X, st = Modified,
    dNeeded = True, dataCompleted = False, rRecvd = False, dthreqtype = DirtyEvict \<rparr>
    
\<rbrakk>
\<Longrightarrow>
(\<Sigma>, P, UCounter, None, _) \<leadsto>ext (\<Sigma>', P', UCounter + 1, None, utid2)"
|
DirtyEvict_finish:
" \<lbrakk>  

    host_mapping_state \<Sigma> dev_i block_X Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v';

    (devclmap \<Sigma>) dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v', block_state = Invalid \<rparr> \<or>
      (devclmap \<Sigma>) dev_i core_j block_X = None;
    (devclmap \<Sigma>') dev_i core_j block_X = (devclmap \<Sigma>) dev_i core_j block_X;

    (hosttrackers \<Sigma>) utid2 = None;
    (devtrackers \<Sigma>) utid2 = None
    
\<rbrakk>
\<Longrightarrow>
(\<Sigma>, P, UCounter, Some (Evict dev_i core_j block_X ), utid2) \<leadsto>ext (\<Sigma>', P', UCounter, None, _)"
|
DirtyEvict_finish':
" \<lbrakk>  

    host_mapping_state \<Sigma> dev_i block_X Invalid;
    (cl_content_mapping (hostclmap \<Sigma>)) block_X = v';

    (devclmap \<Sigma>) dev_i core_j block_X = Some \<lparr>CLEntry.content = Some v', block_state = Invalid \<rparr> \<or>
      (devclmap \<Sigma>) dev_i core_j block_X = None;
    (devclmap \<Sigma>') dev_i core_j block_X = (devclmap \<Sigma>) dev_i core_j block_X;

    (hosttrackers \<Sigma>) utid2 = None;
    (devtrackers \<Sigma>) utid2 = None
    
\<rbrakk>
\<Longrightarrow>
(\<Sigma>, P, UCounter, None, utid2) \<leadsto>ext (\<Sigma>', P', UCounter, None, _)"
|
CleanEvictStart: "
(\<Sigma>, P) \<leadsto>ext (\<Sigma>', P')"
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
inductive e_transition ::  "(Type1State * Program * nat * Instruction option * UTID) \<Rightarrow> (Type1State * Program * nat * Instruction option * UTID) \<Rightarrow> bool"
(infixr "\<leadsto>e" 30)
where
  one_step_trans1 : "\<lbrakk> \<Sigma> \<leadsto>env \<Sigma>' \<rbrakk> \<Longrightarrow> (\<Sigma>, P, n, i, u) \<leadsto>e (\<Sigma>', P, n, i, u)"
| one_step_trans2 : "\<lbrakk> (\<Sigma>, P, n, i, u) \<leadsto>ext (\<Sigma>', P', n', i', u') \<rbrakk> \<Longrightarrow> (\<Sigma>, P, n, i, u) \<leadsto>e (\<Sigma>', P', n', i', u') "

inductive e_transition_star :: "(Type1State * Program * nat * Instruction option * UTID) \<Rightarrow> (Type1State * Program * nat * Instruction option * UTID) \<Rightarrow> bool"
(infixr "\<leadsto>e*" 30)
where
  one_step_trans : "\<lbrakk>(\<Sigma>, P, n, i, u) \<leadsto>e (\<Sigma>', P', n', i', u') \<rbrakk> \<Longrightarrow> (\<Sigma>, P, n, i, u) \<leadsto>e* (\<Sigma>', P', n', i', u')"
| e_star : "\<lbrakk> (\<Sigma>, P, n, i, u) \<leadsto>e (\<Sigma>', P', n', i', u'); (\<Sigma>', P', n', i', u') \<leadsto>e* (\<Sigma>'', P'', n'', i'', u'') \<rbrakk> \<Longrightarrow> 
            (\<Sigma>, P, n, i, u) \<leadsto>e* (\<Sigma>'', P'', n'', i'', u'')"



definition start_configuration :: "Type1State"
  where " start_configuration = \<lparr>hostclmap = empty_host_cl_map,
                                 devclmap = empty_dev_cl_map, 
  dthreqs           = empty_dthreqs,
  dthresps          = empty_dthresps,
  dthdatas          = empty_dthdatas,
  htdreqs           = empty_htdreqs,
  htdresps          = empty_htdresps,
  htddatas          = empty_htddatas,
  hosttrackers      = empty_hosttrackers,
  devtrackers       = empty_devtrackers
   \<rparr>"

lemma "( (start_configuration, two_devices_writing_at_same_location, 0, None, Utid 999) \<leadsto>e* (\<Sigma>', P', n', i', u) \<Longrightarrow>
\<nexists>dev1 dev2. dev1 \<noteq> dev2 \<and>     host_mapping_state \<Sigma>' dev_1 (Block 1) Exclusive \<and>     host_mapping_state \<Sigma>' dev_2 (Block 1) Exclusive)"
  sorry


(*invariant storng to ensure the property*)





end
