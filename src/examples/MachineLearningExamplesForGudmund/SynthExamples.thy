header{* Generate some test examples for Gundmunds machine learning project. *}
theory SynthTestExamples
imports IsaP
begin

ML{*

*}
ML {*
val datatypes = [@{typ "nat"}, @{typ "nat list"}];

val functions = map Term.dest_Const
  [@{term "Groups.plus_class.plus :: nat \<Rightarrow> nat \<Rightarrow> nat"},
  @{term "Groups.minus_class.minus :: nat \<Rightarrow> nat \<Rightarrow> nat"},
  @{term "Groups.times_class.times :: nat \<Rightarrow> nat \<Rightarrow> nat"},
  @{term "List.hd :: nat list \<Rightarrow> nat"},
  @{term "List.tl :: nat list \<Rightarrow> nat list"},
  @{term "List.append :: nat list \<Rightarrow> nat list \<Rightarrow> nat list"}];

val def_thrms = [@{thms "Nat.plus_nat.simps"}, @{thms "Nat.minus_nat.simps"},  @{thms "Nat.times_nat.simps"},
            @{thms "List.hd.simps"}, @{thms "List.tl.simps"}, @{thms "List.append.simps"}];
val thrms = flat def_thrms;

val fundefs = functions ~~ def_thrms;

(* Don't want to synthesise undefined terms *)
val constr_trms = [Trm.change_frees_to_fresh_vars @{term "hd([])"},
                   Trm.change_frees_to_fresh_vars @{term "tl([])"}
  ]

*}
 
ML{*

(* set constraint params *)
  val cparams0 = 
      ConstraintParams.empty 
        |> ThyConstraintParams.add_eq @{context}
        |> ThyConstraintParams.add_datatype' @{context} @{typ "nat"}
        |> ThyConstraintParams.add_datatype' @{context} @{typ "nat list"}
        |> (ConstraintParams.add_consts functions)
        |> ConstraintParams.add_arb_terms @{context} constr_trms
        |> ConstraintParams.add_thms @{context} thrms;

val (init_ctxt, cparams) = 
  ConstraintParams.add_ac_properties_of_consts @{context} fundefs cparams0;

 ConstraintParams.print init_ctxt cparams; 
*}


ML {*
val thy_constraints = (Constraints.init init_ctxt cparams);
val top_term = Thm.term_of @{cpat "op = :: ?'a => ?'a => bool"};
val top_const = (Constant.mk (fst (Term.dest_Const top_term)));

val dummy_prover = SynthInterface.Prover(fn ctxt => fn term => (NONE,[]));

*}

ML{*
val (nw_cparams, nw_ctxt) = SynthInterface.thm_synth
  dummy_prover 
  SynthInterface.quickcheck 
  SynthInterface.wave_rule_config
  SynthInterface.var_allowed_in_lhs   
  {max_size = 8, min_size = 3, max_vars = 3, max_nesting= SOME 2} 
  (Constant.mk "HOL.eq") (cparams0,@{context}); 


map (Trm.print nw_ctxt) (SynthOutput.get_all (SynthOutput.Ctxt.get nw_ctxt));


*}
ML{*
map (Trm.print nw_ctxt) (SynthOutput.get_conjs (SynthOutput.Ctxt.get nw_ctxt));

*}