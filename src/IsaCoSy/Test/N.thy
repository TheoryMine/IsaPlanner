theory N
imports IsaP

begin
datatype N = zero  ("0\<^isub>N")
           | suc N ("suc\<^isub>N _" [500] 500)
syntax
  "_suc"     :: "N => N" ("suc _" [500] 500)
translations
  "0" == "0\<^isub>N"
  "suc x" == "suc\<^isub>N x"
declare N.inject[impwrule]

primrec plus_N :: "N \<Rightarrow> N \<Rightarrow> N" (infix "+" 509)
where
  add_0[wrule]:  "0 + y = y"
| add_suc[wrule]:"(suc x) + y = suc (x + y)"

primrec mult_N :: "N \<Rightarrow> N \<Rightarrow> N" (infix "*" 509)
where
  mult_0[wrule]:  "0 * y = 0"
| mult_suc[wrule]:"(suc x) * y = y + (x * y)"

ML{*


val def_thms = [@{thm "add_0"}, @{thm "add_suc"}, @{thm "mult_0"}, @{thm "mult_suc"}]

val cparams = ConstraintParams.empty @{context}
        |> ConstraintParams.add_eq @{context}
        |> ConstraintParams.add_datatype @{context} @{typ "N"}
        |> ConstraintParams.add_consts_of_string_names @{context} ["N.plus_N", "N.mult_N"]
        |> ConstraintParams.add_thms @{context} def_thms;
*}
ML{*
(*
val ctxt = @{context
val (assoc_opt, commute_opt) = ConstraintParamSchemes.synth_ac_thrms 
                                         ctxt (const_nm,ty) def_thms
*)
*}

ML{*
val (init_ctxt1, init_cparams1) = 
  ConstraintParams.add_ac_properties_of_const @{context}
                  ("N.plus_N",@{typ "N => N \<Rightarrow> N"}) @{thms "plus_N.simps"} cparams;

val (init_ctxt, init_cparams) = 
  ConstraintParams.add_ac_properties_of_const init_ctxt1
                  ("N.mult_N",@{typ "N \<Rightarrow> N \<Rightarrow> N"}) @{thms "mult_N.simps"} init_cparams1;

TheoryConstraints.print init_ctxt (TheoryConstraints.init init_ctxt init_cparams);
*}

ML{*
val (nw_cparams, nw_ctxt) = SynthInterface.thm_synth
  SynthInterface.rippling_prover 
  SynthInterface.quickcheck 
  SynthInterface.wave_rule_config
  SynthInterface.var_allowed_in_lhs
  {max_size = 6, min_size = 1, max_vars = 3, max_nesting= SOME 2} 
  (SynthNames.ConstantName.mk "HOL.eq") (init_cparams, init_ctxt); 

*}
ML{*
SynthInterface.print_thms (nw_cparams, nw_ctxt);
*}
ML{*
SynthOutput.Ctxt.get nw_ctxt;
*}
end
