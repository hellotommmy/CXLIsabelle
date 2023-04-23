theory RSP_soundness imports 
  RSP_helper
  RSP_high_level_PL
  RSP_opencl_MM
  RSP_low_level_PL
  RSP_compiler
  RSP_compiler_exn
begin

section {* Main theorem *}

text {* A notion of observational equivalence *}

fun obs_equiv :: "H_exn \<Rightarrow> L_exn \<Rightarrow> bool" (infix "\<cong>" 50)
where
  "X \<cong> Y = (erase_pre_exn (Pre X) \<simeq> erase_pre_exn (Pre Y))"

text {* Every execution (say Y) of the compiled program is observationally
equivalent to a consistent execution (say X) of the original program. *}
  
theorem soundness:
  "\<forall>Y \<in> \<lbrakk> compile_prog New P \<rbrakk>\<^sub>\<L>. \<exists>X \<in> \<lbrakk> P \<rbrakk>\<^sub>\<H> . X \<cong> Y"
oops


end
