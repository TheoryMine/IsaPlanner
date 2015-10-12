theory IsaCoSy2
imports HOL_IsaP 

uses 

("synth_output.ML")
("synth_prf_tools.ML") (* Update this *)
("synth_lib.ML")
("constraint_param_schemes.ML")
("constraint_params.ML")
("synthNames.ML")
("thyConstr.ML")
("constInfo.ML")
("theoryConstraints.ML")
("synthConstr.ML")
("sterm.ML")
("term_synhesis.ML")
("synth_interface.ML")
("order_terms.ML")
begin
ML{*
Trm.pretty
;
*}

use "synth_lib.ML"
use "synth_prf_tools.ML"
use "synth_output.ML"
use "constraint_param_schemes.ML"
use "constraint_params.ML"
use "synthNames.ML"
use "thyConstr.ML"
use "constInfo.ML"
use "theoryConstraints.ML"
use "synthConstr.ML"
use "sterm.ML"
use "term_synhesis.ML"
use "order_terms.ML"
use "synth_interface.ML"

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
ML{*


*}

end;