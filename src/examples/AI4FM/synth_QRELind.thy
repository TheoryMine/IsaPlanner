theory synth_QRELind
imports QRELind3 HOL_IsaP IsaCoSy
 uses "synth_setup.ML" "nitpick_setup.ML"

begin

ML{*
 use "experiment.ML" 
*}


ML{*
val ctxt =  @{context};
val setmem = Thm.term_of @{cpat "Set.member :: X => (X => bool) => bool"}
val ((eq,eqty),eqair) = (Term.dest_Const @{term "HOL.eq"},2)

val consts =  [(@{term "QRELind3.root"},2), (@{term "QRELind3.roots"}, 1), 
  (@{term "QRELind3.collapse"}, 1), (@{term "QRELind3.collect"}, 2), (@{term "QRELind3.xapp"},2), 
  (@{term "QRELind3.rngrestr"}, 2), (@{term "HOL.Not"}, 1), (setmem, 2)]
  |> map (fn (c,airity)  => (Term.dest_Const c, airity))

val airities = SynthNames.Constant.NTab.of_list (map (fn ((cnm,ty), airity) => 
                                                      (SynthNames.Constant.mk cnm,airity)) 
                                                (((eq,eqty),eqair)::(consts)))

(* We add some constraints: collapse and root are idempotent, no nested range restrictions, roots(collapse x) = empty set *)
val constr_terms = [Trm.change_frees_to_fresh_vars @{term "collapse(collapse x)"},
                    Trm.change_frees_to_fresh_vars @{term "QRELind3.root (QRELind3.root x b) b"},
                    Trm.change_frees_to_fresh_vars @{term "rngrestr (rngrestr a b) b"},
                     Trm.change_frees_to_fresh_vars @{term "roots(collapse x)"},
                      Trm.change_frees_to_fresh_vars @{term "HOL.Not(HOL.Not x)"}]

(* Add equality so its used during synthesis *)
fun myaddeq ctxt = ConstraintParams.add_termrws ctxt 
                   ThyConstraintParams.termrws_for_eq o ConstraintParams.add_consts 
                   ThyConstraintParams.consts_for_eq;

(* Compute parameters for IsaCoSy, given our constants and constraints *)
val topeqparams = 
  ConstraintParams.empty
  |> ThyConstraintParams.add_eq ctxt 
  (* |> myaddeq ctxt *)
  |> ((ConstraintParams.add_consts o map fst) consts)
  |> (ConstraintParams.add_arb_terms ctxt constr_terms);

val params2 = 
  ConstraintParams.empty
  (* |> ThyConstraintParams.add_eq ctxt *)
  |> myaddeq ctxt 
  |> ((ConstraintParams.add_consts o map fst) consts)
  |> (ConstraintParams.add_arb_terms ctxt constr_terms);
*}
ML {*


(* A silly prover and counter-example checker that does nothing *)
val dummy_prover = SynthInterface.Prover(fn ctxt => fn term => (NONE,[]));
val dummy_cex_checker = SynthInterface.CExFinder(fn ctxt => fn term => true);
val no_bool_vars = SynthInterface.VarAllowedFun(SynthSetup.not_bool_hole);
val not_bool_in_lhs = SynthInterface.VarAllowedFun(SynthSetup.not_bool_in_lhs);

(* Synthesise some equalities *)
val (eq_cparams, eq_ctxt) = SynthSetup.thm_synth 
  dummy_prover
  dummy_cex_checker
  SynthSetup.ai4fm_result_config
  (* SynthInterface.var_allowed_in_lhs *)
   not_bool_in_lhs
  {max_size = 10, min_size = 3, max_vars = 3, max_nesting= SOME 2} 
  (Constant.mk "HOL.eq") airities (topeqparams,@{context})

; 
*}

 
ML {* 
(* Get results and attach relevant assmuptions *)

val eq_conjs = SynthOutput.get_all (SynthOutput.Ctxt.get eq_ctxt);

val myconjs = map_filter (Experiment.get_forest_and_elem_frees) eq_conjs;

val forest_conjs_w_asm = map (fn (c, forests,_) => Experiment.mk_forest_conjs (c,forests)) myconjs;
val neg_root_conjs_w_asm = maps (fn (c, forests,elems) => Experiment.mk_neg_roots_conj (c,forests, elems)) myconjs;
val pos_root_conjs_w_asm = flat (map_filter (fn (c, forests,elems) => Experiment.mk_roots_conjs (c,forests, elems)) myconjs);
val elem2_conjs_w_asm = flat (map_filter (fn (c, forests,elems) => Experiment.mk_two_roots_conjs (c,forests, elems)) myconjs);


*}
ML{*
(* Nitpick the results*)
NitpickSetup.nitpick_results_to_file "eq1" @{context} @{theory} forest_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "eq2" @{context} @{theory} neg_root_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "eq3" @{context} @{theory} pos_root_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "eq4" @{context} @{theory} elem2_conjs_w_asm;
*}

ML{*  
(* Synthesise some terms about set membership *)
 val (mem_cparams, mem_ctxt) =  
  SynthSetup.thm_synth 
  dummy_prover
  dummy_cex_checker
  SynthSetup.ai4fm_result_config
  no_bool_vars
  (* (SynthInterface.VarAllowedFun(fn h => fn st => true)) *)
  {max_size = 10, min_size = 3, max_vars = 3, max_nesting= SOME 2} 
  (Constant.mk "Set.member") airities (params2,@{context})
; 

val mem_conjs = SynthOutput.get_all (SynthOutput.Ctxt.get mem_ctxt);

val myconjs = map_filter (Experiment.get_forest_and_elem_frees) mem_conjs;

val forest_conjs_w_asm = map (fn (c, forests,_) => Experiment.mk_forest_conjs (c,forests)) myconjs;
val neg_root_conjs_w_asm = maps (fn (c, forests,elems) => Experiment.mk_neg_roots_conj (c,forests, elems)) myconjs;
val pos_root_conjs_w_asm = flat (map_filter (fn (c, forests,elems) => Experiment.mk_roots_conjs (c,forests, elems)) myconjs);
val elem2_conjs_w_asm = flat (map_filter (fn (c, forests,elems) => Experiment.mk_two_roots_conjs (c,forests, elems)) myconjs);

*}
ML{*
(* Nitpick the results*)
NitpickSetup.nitpick_results_to_file "mem1" @{context} @{theory} forest_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "mem2" @{context} @{theory} neg_root_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "mem3" @{context} @{theory} pos_root_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "mem4" @{context} @{theory} elem2_conjs_w_asm;
*}

ML{*  
(* Synthesise some terms about negation *)

 val (not_cparams, not_ctxt) =  
  SynthSetup.thm_synth 
  dummy_prover
  dummy_cex_checker
  SynthSetup.ai4fm_result_config
  no_bool_vars
  (* (SynthInterface.VarAllowedFun(fn h => fn st => true)) *)
  {max_size = 10, min_size = 3, max_vars = 3, max_nesting= SOME 2} 
  (Constant.mk "HOL.Not") airities (params2,@{context})

; 

val not_conjs = SynthOutput.get_all (SynthOutput.Ctxt.get not_ctxt);

val myconjs = map_filter (Experiment.get_forest_and_elem_frees) not_conjs;

val forest_conjs_w_asm = map (fn (c, forests,_) => Experiment.mk_forest_conjs (c,forests)) myconjs;
val neg_root_conjs_w_asm = maps (fn (c, forests,elems) => Experiment.mk_neg_roots_conj (c,forests, elems)) myconjs;
val pos_root_conjs_w_asm = flat (map_filter (fn (c, forests,elems) => Experiment.mk_roots_conjs (c,forests, elems)) myconjs);
val elem2_conjs_w_asm = flat (map_filter (fn (c, forests,elems) => Experiment.mk_two_roots_conjs (c,forests, elems)) myconjs);

*}
ML{*
(* Nitpick the results*)
NitpickSetup.nitpick_results_to_file "neg1" @{context} @{theory} forest_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "neg2" @{context} @{theory} neg_root_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "neg3" @{context} @{theory} pos_root_conjs_w_asm;
NitpickSetup.nitpick_results_to_file "neg4" @{context} @{theory} elem2_conjs_w_asm;
*}



end