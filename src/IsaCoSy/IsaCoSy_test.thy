theory IsaCoSy_test
imports 
  "~~/src/HOL/Library/Refute"
  "../build/HOL_IsaP" 
begin

(* This is from IsaCoSy v1; v2 of IsaCoSy is in the synthesis subdirectory. *)

ML_file "synth_output.ML"
ML_file "synth_prf_tools.ML" (* Update this *)
ML_file "synth_lib.ML"
ML_file "constraint_param_schemes.ML"
ML_file "constraint_params.ML"
ML_file "synthNames.ML"
ML_file "thyConstr.ML"
ML_file "constInfo.ML"
ML_file "theoryConstraints.ML"
ML_file "synthConstr.ML"
ML_file "sterm.ML"
ML_file "term_synhesis.ML"
ML_file "order_terms.ML"
ML_file "synth_interface.ML"


datatype mynat = ZZero | SSuc mynat

fun pplus where 
  "pplus ZZero x = x"
| "pplus (SSuc x) y = SSuc(pplus x y)"

 
lemmas plus_rules = pplus.simps
lemmas inject[impwrule] = mynat.inject
lemmas wrules[wrule] = plus_rules


ML {*
val (Const(pplus_const,pplus_ty)) = @{term "pplus"}

val ctxt = @{context};

*}
ML{*
  (* set constraint params *)
  val cparams0 = 
  ConstraintParams.empty @{context}
  |> ConstraintParams.add_eq @{context} 
  |> ConstraintParams.add_datatype @{context} @{typ "mynat"}
  |> ((ConstraintParams.add_consts o map Term.dest_Const) [@{term "pplus"}])
  |> ConstraintParams.add_thms @{context} (@{thms "plus_rules"});


(*  val (init_ctxt, cparams) = 
  ConstraintParams.add_ac_properties_of_const @{context}
                  (pplus_const,pplus_ty) @{thms "plus_rules"} cparams0;
*)
val (init_ctxt, cparams) = (@{context},cparams0);


*}



ML{*

val (nw_cparams, nw_ctxt) = SynthInterface.thm_synth
  SynthInterface.rippling_prover 
  SynthInterface.quickcheck 
  (* SynthInterface.try_reprove_config *)
  SynthInterface.wave_rule_config
  SynthInterface.var_allowed_in_lhs
  {max_size = 5, min_size = 1, max_vars = 3, max_nesting= SOME 2} 
  (SynthNames.ConstantName.mk "HOL.eq") (cparams, init_ctxt); 

*}

ML{*
 
SynthInterface.print_thms (nw_cparams, nw_ctxt);

*}

end;