(** Machine state *}*)

theory RSP_state imports 
  RSP_common
begin

subsection {* State of a processing element *}

text {* The state of a PE consists of a register file. *}

datatype register = Reg nat

fun next_reg :: "register \<Rightarrow> register" where "next_reg (Reg i) = Reg (Suc i)"

type_synonym pe_state = "register \<Rightarrow> val"

fun mk_initial_pe_state :: "pe_state"
where
  "mk_initial_pe_state _ = 0"
  
fun update_reg :: "register \<Rightarrow> val \<Rightarrow> pe_state \<Rightarrow> pe_state"
  (infixr ":=\<^sub>\<r>" 60)
where
  "(x :=\<^sub>\<r> v) \<sigma>p = \<sigma>p (x := v)"

value "((Reg 0 :=\<^sub>\<r> 4) mk_initial_pe_state) (Reg 0)"
value "((Reg 0 :=\<^sub>\<r> 4) mk_initial_pe_state) (Reg 1 := 43)"


subsection {* Memory stores *}

text {* A store is a partial function from addresses to values. It is partial in
order to make it possible for an address not to be mapped in a given store. Each
entry is tagged with a piece of ghost state, usually an event identifier, to
record which event was responsible for storing the currently-held value. If the
event identifier is None, it means that this address still holds its initial
value. *}

type_synonym 'tag store = "addr \<rightharpoonup> (val \<times> 'tag)"

type_synonym machine_store = "unit store"

subsection {* Caches *}

text {* A cache's FIFO buffer contains dirty addresses and special 'flush'
markers. *}

datatype fifo_element = Flush "dvid \<times> cuid \<times> peid" | Addr addr
datatype hygiene = Clean | Dirty
datatype validity = Invalid | Valid
type_synonym cacheline_status = "hygiene \<times> validity"
type_synonym 'tag cacheline = "val \<times> 'tag \<times> cacheline_status"

record 'tag cache = 
  Fifo :: "fifo_element list"
  Store :: "('tag \<times> cacheline_status) store"
  
  
text {* Functions for modifying a cache. *}
  
fun update_Fifo :: "(fifo_element list \<Rightarrow> fifo_element list) \<Rightarrow> 
  'tag cache \<Rightarrow> 'tag cache"
where
  "update_Fifo f C = C \<lparr> Fifo := f (Fifo C) \<rparr>"
  
fun enq_Fifo :: "fifo_element \<Rightarrow> 'tag cache \<Rightarrow> 'tag cache"
where
  "enq_Fifo e C = update_Fifo (\<lambda>es. es @ [e]) C"
  
fun deq_Fifo :: "'tag cache \<Rightarrow> 'tag cache"
where
  "deq_Fifo C = update_Fifo tl C"

definition empty_cache :: "_ cache"
where [simp]:
  "empty_cache \<equiv> \<lparr> Fifo = [], Store = (\<lambda>_. None) \<rparr>" 
  
fun update_Store :: "addr \<Rightarrow> 'tag cacheline option \<Rightarrow> 'tag cache \<Rightarrow> 
  'tag cache" (infixr ":=\<^sub>\<s>" 60)
where
  "(x :=\<^sub>\<s> v) C = C \<lparr> Store := (Store C) (x := v)  \<rparr>"

fun invalidate_cacheline :: "'tag cacheline option \<Rightarrow> 'tag cacheline option"
where
  "invalidate_cacheline None = None"
| "invalidate_cacheline (Some (v,eo,hyg,_)) = Some (v,eo,hyg,Invalid)"
  
fun invalidate_all :: "'tag cache \<Rightarrow> 'tag cache"
where
  "invalidate_all C = C \<lparr> Store := (\<lambda>x. invalidate_cacheline (Store C x)) \<rparr>"
  
text {* The state of a compute unit consists of a cache (L1), plus the state of all
of its threads. *}
  
datatype lock_status = Locked | Unlocked

record 'tag cu_state = 
  pes :: "pe_state list"
  L1cache :: "'tag cache"
  rmw_lock :: "lock_status"


value "replicate (3) [a]"
  
fun mk_initial_cu_state :: "'ins workgroup \<Rightarrow> 'tag cu_state"
where
  "mk_initial_cu_state P = \<lparr> 
    pes = replicate (length P) mk_initial_pe_state, 
    L1cache = empty_cache, 
    rmw_lock = Unlocked 
  \<rparr>" 





text {* Functions for setting/getting the components of a workgroup's state. *}
 
fun update_pe :: "peid \<Rightarrow> (pe_state \<Rightarrow> pe_state) \<Rightarrow> 
  'tag cu_state \<Rightarrow> 'tag cu_state" (infixr ":=\<^sub>\<p>" 60) 
where "(Pe pe :=\<^sub>\<p> f) \<sigma>c = \<sigma>c \<lparr> pes := (pes \<sigma>c) [pe := f (pes \<sigma>c ! pe)] \<rparr>"

fun return_Ts :: "_ cu_state \<Rightarrow> peid \<Rightarrow> pe_state" 
  ("_ [ _ ]\<^sub>\<p>" [100,0] 101)
where "\<sigma>c[Pe pe]\<^sub>\<p> = pes \<sigma>c ! pe"
  
fun update_L1 :: "('tag cache \<Rightarrow> 'tag cache) \<Rightarrow> 'tag cu_state \<Rightarrow> 
  'tag cu_state"
where
  "update_L1 f \<sigma>c = \<sigma>c \<lparr> L1cache := f (L1cache \<sigma>c) \<rparr>"
  
fun write_to_L1 :: "addr \<Rightarrow> val \<Rightarrow> eid \<Rightarrow> (eid \<times> eid list) cu_state \<Rightarrow> 
  (eid \<times> eid list) cu_state"
where
  "write_to_L1 x v e \<Gamma> = (
  let mo = 
    case Store (L1cache \<Gamma>) x of 
    None \<Rightarrow> [] | Some (_, (_,mo), _, _) \<Rightarrow> mo
  in
  update_L1 (
    (x :=\<^sub>\<s> Some (v, (e, mo @ [e]), Dirty, Valid)) ;; 
    enq_Fifo (Addr x)
  ) \<Gamma>)"


fun invalidate_line :: "addr \<Rightarrow> 'tag cache \<Rightarrow> 'tag cache"
where
  "invalidate_line x C = C \<lparr> Store := (Store C) (x := 
    case Store C x of None \<Rightarrow> None | 
      Some (v, eo, h, _) \<Rightarrow> Some (v, eo, h, Invalid)) \<rparr>"
  
fun peids :: "'tag cu_state \<Rightarrow> peid list"
where
  "peids \<sigma>c = map Pe [0..<length (pes \<sigma>c)]"
  
subsection {* Device state *}
  
text {* The state of a device consists of the state of all of
its compute units *}

record 'tag dv_state =
  cus :: "'tag cu_state list"
  L2cache :: "'tag cache"
  locked :: "addr \<Rightarrow> lock_status"
  
fun mk_initial_dv_state :: "_ ndrange \<Rightarrow> _ dv_state"
where
  "mk_initial_dv_state ndr = \<lparr> 
    cus = map mk_initial_cu_state ndr, 
    L2cache = empty_cache,
    locked = (\<lambda>_. Unlocked)
  \<rparr>"

text {* Functions for setting/getting the components of a device's state. *}
  
fun update_\<sigma>c :: "cuid \<Rightarrow> ('tag cu_state \<Rightarrow> 'tag cu_state) \<Rightarrow>
  'tag dv_state \<Rightarrow> 'tag dv_state" (infixr ":=\<^sub>\<c>" 60) 
where "(Cu cu :=\<^sub>\<c> f) \<sigma>d = \<sigma>d \<lparr> cus := (cus \<sigma>d) [cu := f (cus \<sigma>d ! cu)] \<rparr>"

fun return_Ws :: "'tag dv_state \<Rightarrow> cuid \<Rightarrow> 'tag cu_state" 
  ("_ [ _ ]\<^sub>\<c>" [100,0] 101)
where "\<sigma>d[Cu cu]\<^sub>\<c>  = cus \<sigma>d ! cu"
 
fun cuids :: "_ dv_state \<Rightarrow> cuid list"
where
  "cuids \<sigma>d = map Cu [0..<length (cus \<sigma>d)]" 
 
fun update_L2 :: "('tag cache \<Rightarrow> 'tag cache) \<Rightarrow> 'tag dv_state \<Rightarrow> 'tag dv_state"
where
  "update_L2 f \<sigma>d = \<sigma>d \<lparr> L2cache := f (L2cache \<sigma>d) \<rparr>"
  
fun lock_L2 :: "addr \<Rightarrow> 'tag dv_state \<Rightarrow> 'tag dv_state"
where
  "lock_L2 x \<sigma>d = \<sigma>d \<lparr> locked := (locked \<sigma>d) (x := Locked) \<rparr>"
  
fun unlock_L2 :: "addr \<Rightarrow> 'tag dv_state \<Rightarrow> 'tag dv_state"
where
  "unlock_L2 x \<sigma>d = \<sigma>d \<lparr> locked := (locked \<sigma>d) (x := Unlocked) \<rparr>"
  
fun write_to_L2 :: "addr \<Rightarrow> val \<Rightarrow> eid \<Rightarrow> (eid \<times> eid list) dv_state \<Rightarrow> 
  (eid \<times> eid list) dv_state"
where
  "write_to_L2 x v e \<Delta> = (
  let mo = 
    case Store (L2cache \<Delta>) x of 
    None \<Rightarrow> [] | Some (_, (_,mo), _, _) \<Rightarrow> mo
  in
  update_L2 (
    (x :=\<^sub>\<s> Some (v, (e, mo @ [e]), Dirty, Valid)) ;; 
    enq_Fifo (Addr x)
  ) \<Delta>)"

subsection {* Whole-system state *}

text {* The state of the whole system consists of the global memory, plus the
state of all of its devices. *}

record 'tag sy_state = 
  dvs :: "'tag dv_state list"
  Global_mem :: "'tag store"

fun initial_global_mem :: "(addr \<Rightarrow> 'tag) \<Rightarrow> 'tag store"
where
  "initial_global_mem g = (\<lambda>x. Some (0, g x))" 
  
fun mk_initial_state :: "(addr \<Rightarrow> 'tag) \<Rightarrow> _ program \<Rightarrow> 'tag sy_state"
where
  "mk_initial_state g P = 
  \<lparr> dvs = map mk_initial_dv_state P, Global_mem = initial_global_mem g \<rparr>"
  
text {* Functions for setting/getting the components of the system's state. *}
  
fun update_Ds :: "dvid \<Rightarrow> 
  ('tag dv_state \<Rightarrow> 'tag dv_state) \<Rightarrow> 
  'tag sy_state \<Rightarrow> 'tag sy_state" (infixr ":=\<^sub>\<d>" 60) 
where "(Dv dv :=\<^sub>\<d> f) \<Sigma> = \<Sigma> \<lparr> dvs := (dvs \<Sigma>) [dv := f (dvs \<Sigma> ! dv)] \<rparr>"

fun return_Ds :: "'tag sy_state \<Rightarrow> dvid \<Rightarrow> 'tag dv_state" 
  ("_ [ _ ]\<^sub>\<d>" [100,0] 101)
where "\<Sigma>[Dv dv]\<^sub>\<d> = dvs \<Sigma> ! dv"
  
fun update_global_mem :: "('tag store \<Rightarrow> 'tag store) \<Rightarrow> 'tag sy_state \<Rightarrow> 
  'tag sy_state"
where
  "update_global_mem f \<Sigma> = \<Sigma> \<lparr> Global_mem := f (Global_mem \<Sigma>) \<rparr>"
  
fun write_global :: "addr \<Rightarrow> val \<Rightarrow> eid \<Rightarrow> (eid \<times> eid list) sy_state \<Rightarrow> 
  (eid \<times> eid list) sy_state"
where
  "write_global x v e \<Sigma> = (
  let mo = 
    case Global_mem \<Sigma> x of 
    None \<Rightarrow> [] | Some (_, (_,mo)) \<Rightarrow> mo
  in
  update_global_mem (\<lambda>\<sigma>. \<sigma>(x \<mapsto> (v, (e, mo @ [e])))) \<Sigma>)"
  
fun dvids :: "'tag sy_state \<Rightarrow> dvid list"
where
  "dvids \<Sigma> = map Dv [0..<length (dvs \<Sigma>)]"

end
