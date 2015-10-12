structure TCoSy =
struct 


datatype prover_f = Prover of 
        Proof.context -> Term.term 
        -> Thm.thm option;

datatype result_config_f = ResultConfig of 
         {conjs : term list, 
          thms : Thm.thm list}
      -> ConstraintParams.T * Proof.context * TheoryConstraints.T
      -> ConstraintParams.T * Proof.context;

(* ------------------------------------------------------------------------------------*)
(* ---- IsaPlanner rippling prover ---- *)
(* ------------------------------------------------------------------------------------*)
val rippling_prover = Prover (SynthPrfTools.just_ripple_conjecture2);

fun wrule_and_constraints {conjs,thms} (cparams,ctxt,old_thy_constrs) =
    let
      val (rw_thms,non_rw_thms) =  SynthLib.map_partition 
                                     (OrderTerms.mk_valid_rw_def_prec old_thy_constrs)
                                     thms
       (* Check if there are any commutativity theorems among the non-rw rules *)
        val commutativity = map_filter SynthLib.is_commutativity non_rw_thms                          
        val nw_constr_params =  cparams
                                  |> ConstraintParams.add_thms ctxt rw_thms 
                                  |> ConstraintParams.add_commute_terms commutativity 
        (* Subsumption check built into SynthOutput *)
        val nw_ctxt = ctxt 
                       |> (fold SynthPrfTools.add_to_wrules thms)
                       |> SynthOutput.add_thms' thms
                       |> SynthOutput.add_conjs conjs
      in (nw_constr_params, nw_ctxt) end;

val wave_rule_config = ResultConfig (wrule_and_constraints); 

(* Don't bother with proof. *)
val dummy_prover = Prover(fn _ => fn _ => NONE);

fun dummy_config_f {conjs, thms} (cparams,ctxt,old_thy_constrs) =
    let
      val (rw_trms,non_rw_trms) =  SynthLib.map_partition 
                                     (OrderTerms.mk_valid_rw_def_prec_trm old_thy_constrs)
                                     conjs;
      val commutativity = map_filter SynthLib.is_commutativity_trm non_rw_trms   
      val nw_cparams =  (ConstraintParams.add_terms ctxt rw_trms cparams)
                          |> ConstraintParams.add_commute_terms commutativity 
      val nw_ctxt = ctxt 
                      |> SynthOutput.add_conjs conjs
    in
      (nw_cparams, nw_ctxt)
    end;

val dummy_config = ResultConfig (dummy_config_f);

(* ------------------------------------------------------------------------------------*)
(* ------------------------------------------------------------------------------------*)


fun synthesise_one_size prover_f result_config_f  
                        consts size (constr_params, ctxt, existing_trms) =
    let 
      val thyConstrs = TheoryConstraints.init ctxt constr_params

      fun synth_one_const top_const = 
          (* Compute current thy constraints and synthesise some terms *)
          (Test.synthesise_terms top_const 
                            {size = size, max_vars = 1} (* dummy, we're not generating any vars *)
                            ctxt thyConstrs)
            |> Seq.map STerm.get_term
            |> Seq.list_of;

      (* New terms synthesised for this size *)
      val trms = maps synth_one_const consts
      (* New equations and remaining terms not yet in equations. *)
      val(eqs,rem_trms) = EqClass.try_mk_eqs ctxt (trms @ existing_trms) ([],[])

      (* Try to prove the equations generated from above *) 
      val (conjs, thms) = 
          fold (fn conj_t => fn (conjs,thms) => 
                                (case prover_f ctxt conj_t of 
                                   (SOME thm) => (conjs, thm::thms)
                                 | _ => (conj_t::conjs,thms)))
               (map SynthPrfTools.poss_add_Trueprop eqs)
               ([], []);
          
      (* Compute new constraints, update the known theorems etc. *)
      val (constr_params2,ctxt2) = 
          result_config_f {conjs = conjs, thms = thms} 
                        (constr_params,ctxt,thyConstrs)
    in 
      (constr_params2, ctxt2, rem_trms)
    end;

fun dbg_synth consts size (constr_params, ctxt) = 
    let
      val thyConstrs = TheoryConstraints.init ctxt constr_params

      fun synth_one_const top_const = 
          (* Compute current thy constraints and synthesise some terms *)
          (Test.synthesise_terms top_const 
                            {size = size, max_vars = 1} (* dummy, we're not generating any vars *)
                            ctxt thyConstrs)
            |> Seq.map STerm.get_term
            |> Seq.list_of;
      (* New terms synthesised for this size *)
      val trms = maps synth_one_const consts;
    in
      trms
    end;

fun mk_single_vars consts (constr_params, ctxt) =
    let
      val thyConstrs = TheoryConstraints.init ctxt constr_params
      val types =  Library.distinct (uncurry Trm.typ_name_eq)
                                    (map (fn cinfo => cinfo 
                                                        |> ConstInfo.get_typ 
                                                        |> Term.body_type)
                                         (map_filter (SynthNames.ConstantName.NTab.lookup thyConstrs) consts))
    in 
      map (fn ty => Var (("h",0),ty)) types
    end;
                                       

(* Synthesise equational theorems *)
fun eq_thm_synth (Prover prover) (ResultConfig result_config)
                 consts {max_size, min_size, max_nesting} (init_constr_params, init_ctxt) = 
    let 
      val single_vars = mk_single_vars consts (init_constr_params,init_ctxt);
      val constr_params = ConstraintParams.add_nesting_constrs init_ctxt max_nesting init_constr_params
    in
      fold (synthesise_one_size prover result_config consts) 
           (min_size upto max_size) (constr_params, init_ctxt, single_vars)
  (*    (maps 
         (gen_trms_of_size consts (constr_params, init_ctxt)) 
         (min_size upto max_size))
      @ single_vars   *)       
    end;

fun run consts size_params (constr_params, init_ctxt) =
    let 
      val (cparams, ctxt, rem) =
          eq_thm_synth dummy_prover dummy_config 
                       consts size_params (constr_params, init_ctxt)
    in
       (cparams,ctxt,rem) 
    (* SynthInterface.print_thms (cparams, ctxt) *)
    end;

end;

