
(* Top-level functions for calling IsaCoSy *)


signature SYNTH_INTERFACE = sig
  datatype prover_f = Prover of 
      Proof.context -> Term.term 
      -> ((string (* proof description *)
          * Thm.thm) option (* proved or not *)
          * (string * Thm.thm) list); (* lemmas found during proof *)
  
  (*datatype cexfinder_f = CExFinder of Proof.context -> Term.term -> bool; *)

  (* Returns pair of lists, first is conjectures passing counter-ex checking, second is non-theorems. Currently records non-theorems for creating test-data for QuickCheck developers, it can be removed later. *)
  datatype cexfinder_f = CExFinder of Proof.context -> Term.term -> bool

  datatype result_config_f = ResultConfig of 
         {conjs : term list, 
          thrms : ((string * Thm.thm) (* proof and thm *)
                   * (string * Thm.thm) list (* lemmas conjectured in this proof *)) list}
      -> ConstraintParams.T * Proof.context * TheoryConstraints.T
      -> ConstraintParams.T * Proof.context;

  datatype var_allowed_f = VarAllowedFun of SynthNames.HoleName.name -> STerm.T -> bool;

  type size_restr = {max_size : int, min_size : int, max_vars : int, max_nesting : int option};

  val thm_synth : prover_f -> cexfinder_f -> result_config_f -> var_allowed_f
      -> size_restr -> SynthNames.ConstantName.NTab.name (* string name of const *)
      -> ConstraintParams.T * Proof.context 
      -> ConstraintParams.T * Proof.context;

  val var_allowed_in_lhs : var_allowed_f;
  val rippling_prover : prover_f;
  val quickcheck : cexfinder_f;
  val wave_rule_config : result_config_f; (* Should also update constraints from new theorems, possibly orienting them.*)
  val try_reprove_config : result_config_f;

  val print_thms : (ConstraintParams.T  * Proof.context) -> unit; 
end;

structure DB_SynthInterface
= struct
local open SynthNames 
in
  
  datatype prover_f = Prover of 
        Proof.context -> Term.term 
        -> ((string (* proof description *)
             * Thm.thm) option (* proved or not *)
            * (string * Thm.thm) list); (* lemmas found during proof *)
  
  datatype cexfinder_f = CExFinder of Proof.context -> Term.term -> bool;
    
  datatype result_config_f = ResultConfig of 
           {conjs : term list, 
            thrms : ((string * Thm.thm) (* proof and thm *)
                     * (string * Thm.thm) list (* lemmas conjectured in this proof *)) list}
        -> ConstraintParams.T * Proof.context * TheoryConstraints.T
        -> ConstraintParams.T * Proof.context;
  
  
  datatype var_allowed_f = VarAllowedFun of HoleName.name -> STerm.T -> bool;
    
  
  type size_restr = {max_size : int,
                     min_size : int,
                     max_vars : int,
                     max_nesting : int option};
  
  
  (* substructure for functions that say what variable is allowed in what hole *)
  structure VarAllowed = struct
    (* Check if this hole is in the LHS of an equality.
     Only allow new variables to occur in the LHS as we want nice rewrite rules. 
     Only works if we do the LHS first, ie depth-first search inst of breath first.*)
    fun is_hole_in_lhs hole_nm synth_trm =
        SynthLib.is_hole_in_lhs (HoleName.dest hole_nm) (STerm.get_term synth_trm);
          
    fun always_yes hole_nm synth_trm = true;
  end;
  
  (* Default variable-allowance function *)
  val var_allowed_in_lhs = VarAllowedFun(VarAllowed.is_hole_in_lhs);
  
  (* Default rippling prover for IsaCoSy: rippling + lemma calc. *)
  val rippling_prover = Prover(SynthPrfTools.ripple_timeout);
  
  (* Default counter-example checker *)
  val quickcheck = CExFinder(SynthPrfTools.counter_ex_check)



(* Check if this is a commutativity theorem for a binary function.*)
(* In the future, generalise this to cover commutativity in general.*)
fun tryget_commutative_symbol_of_term_eq (lhs,rhs) = 
      let val (lhs_f, lhs_args) = Term.strip_comb lhs
          val (rhs_f, rhs_args)  = Term.strip_comb rhs
      in if (Term.is_Const lhs_f andalso lhs_f = rhs_f) 
         then
           (case (lhs_args, rhs_args) of 
              ([a1, a2], [b1, b2]) => 
                 if (a1 = b2 andalso a2 = b1)
                 then SOME (fst (Term.dest_Const lhs_f)) else NONE
               | _ => NONE)
         else NONE
      end;

fun is_commutativity thm = 
    let 
      val t = Thm.concl_of thm
      val z = Zipper.mktop t
      val lhs_t = (Subst.move_to_lhs_of_eq z) |> Zipper.trm
      val rhs_t = (Subst.move_to_rhs_of_eq z) |> Zipper.trm
      val commute_fun = tryget_commutative_symbol_of_term_eq (lhs_t,rhs_t)
    in
      case commute_fun of
        SOME const => SOME (const,t)
      | NONE => NONE
      end handle Eq_LData_HOL.bad_term_exp _ => NONE;

(* What to do after an interation of synthesis: 
Add theorems as wrules and make new constraints. *) 
 fun wrules_and_constraints (c_thms as {conjs,thrms}) (constr_params, ctxt, old_thy_constrs) =
      let
        val (thms_w_prfs,lems_w_prfs) = fold (fn (thm,lemmas) => 
                                              fn (all_thms,all_lemmas) =>
                                             (thm::all_thms, lemmas@all_lemmas)) thrms ([],[])
        val just_thms = map snd thms_w_prfs
        val just_lemmas = map snd lems_w_prfs

        (* Generate constraints from valid rewrites only *)
        val (rw_thms,non_rw_thms) =  
          SynthLib.map_partition 
            (fn (prf,thm) => 
                case (OrderTerms.mk_valid_rw_def_prec old_thy_constrs thm) of
                  NONE => NONE
                (*Slightly dogdy, prf could now be for symmetric version, 
                 but it's just a string description anyway. *)
                | SOME thm' => SOME (prf,thm')) 
            (thms_w_prfs@lems_w_prfs)
       (* Check if there are any commutativity theorems among the non-rw rules *)
        val commutativity = map_filter (is_commutativity o snd) non_rw_thms                          
        val nw_constr_params =  constr_params
                                  |> ConstraintParams.add_thms ctxt (map snd rw_thms) 
                                  |> ConstraintParams.add_commute_terms commutativity
        (* Subsumption check built into SynthOutput *)
        val nw_ctxt = ctxt 
                       |> (fold SynthPrfTools.add_to_wrules (just_thms@just_lemmas))
                       |> SynthOutput.add_thms (rw_thms @ non_rw_thms)
                      (* |> SynthOutput.add_thms thms_w_prfs
                       |> SynthOutput.add_thms lems_w_prfs *)
                       |> SynthOutput.add_conjs conjs
      in (nw_constr_params, nw_ctxt) end;
  
(* As above, but try to re-prove the open conjectures. Might have
   found a lemma that some previous proof missed. *)

 fun wrules_constr_reprove (Prover prover) c_thms (constr_params, ctxt, old_thy_constrs) =
     let 
       val (constr_params2, ctxt2) = 
           wrules_and_constraints c_thms (constr_params, ctxt, old_thy_constrs)
       val (still_conjs,now_thms) = 
           fold (fn conj_t => fn (conjs,thms1) => 
                                 (case prover ctxt2 conj_t of 
                                    (SOME thm, lemmas) => (conjs,(thm,lemmas)::thms1)
                                  | _ => (conj_t::conjs,thms1)))
                (SynthOutput.get_conjs (SynthOutput.Ctxt.get ctxt2)) ([],[])

       val (thms_w_prfs,lems_w_prfs) = 
           fold (fn (thm,lemmas) => 
                 fn (all_thms,all_lemmas) =>
                    (thm::all_thms, lemmas@all_lemmas)) now_thms ([],[])  
  
       val just_thms = map snd thms_w_prfs
       val just_lemmas = map snd lems_w_prfs

       (*Generate constraints from valid rewrites *)
        val (rw_thms,non_rw_thms) =  SynthLib.map_partition 
                                       (fn (prf,thm) => 
                                           case (OrderTerms.mk_valid_rw_def_prec old_thy_constrs thm) of
                                             NONE => NONE
                                           (*Slightly dogdy, prf could now be for symmetric version, 
                                            but it's just a string description anyway. *)
                                           | SOME thm' => SOME (prf,thm')
                                       ) 
                                      (thms_w_prfs@lems_w_prfs)
      
       val commutativity = map_filter (is_commutativity o snd) non_rw_thms                          

       (* val constr_thms = just_thms @ just_lemmas *)
       val nw_constr_params =  
           (ConstraintParams.add_thms ctxt2 (map snd rw_thms) constr_params2)
             |> ConstraintParams.add_commute_terms commutativity
(* ALSO add commute thrms if we found any *)
           (* Can lemmas already be assumed to be added as wrules? *)
       val nw_ctxt = ctxt2 
                       |> (fold SynthPrfTools.add_to_wrules (just_thms@just_lemmas))
                       |> SynthOutput.add_thms (rw_thms@non_rw_thms)
                    (*   |> SynthOutput.add_thms ((map (fn (p,t) => (p,t,true)) rw_thms) @ 
                                                (map (fn (p,t) => (p,t,false)) non_rw_thms)) *)
                     (*  |> SynthOutput.add_thms thms_w_prfs
                       |> SynthOutput.add_thms lems_w_prfs *)
                       |> SynthOutput.set_conjs still_conjs 
      in (nw_constr_params, nw_ctxt) end;

  val wave_rule_config = ResultConfig(wrules_and_constraints);
  val try_reprove_config = ResultConfig(wrules_constr_reprove rippling_prover);

  (* Main function: Call IsaCoSy *)
  fun thm_synth (Prover prover) (CExFinder cex_finder) (ResultConfig result_config) 
      (VarAllowedFun var_allowed_fn) {max_size, min_size, max_vars, max_nesting}
      top_const (init_constr_params, init_ctxt) =
      let
        fun synth_one_size this_size (constr_params, ctxt0) =
            let 
              (* Compute current thy constraints and synthesise some terms *)
              val thy_constrs = TheoryConstraints.init ctxt0 constr_params;
              val synth_trms = 
                  (TermSynthesis.synthesise_terms top_const var_allowed_fn 
                                                  {size = this_size, max_vars = max_vars} 
                                                  ctxt0 thy_constrs)
                |> Seq.map (SynthPrfTools.poss_add_Trueprop o Type.legacy_freeze o STerm.get_term)
                |> Seq.list_of;
              (* Record how many terms were synthesised for this size *)
              val ctxt = SynthOutput.add_to_tot this_size (List.length synth_trms) ctxt0;
                     (*    |>SynthOutput.add_sterms synth_trms;   *)           
   
                         
              (* Counter example check *)
            (*  val (cand_trms, non_thms) = (* filter (cex_finder ctxt) synth_trms *)
                  cex_finder ctxt1 synth_trms; *)
              (* Record the non-theorems *)
              val ctxt = SynthOutput.add_non_thms synth_trms ctxt;

                  
              (* val _ = tracing ""; *)
              val cand_trms = filter (cex_finder ctxt) synth_trms;
              
              (* Check which conjectures can be proved. *)
              val (conjs1, thms1) = 
                  fold (fn conj_t => fn (conjs,thms1) => 
                           (case prover ctxt conj_t of 
                              (SOME thm, lemmas) => (conjs,(thm,lemmas)::thms1)
                             | _ => (conj_t::conjs,thms1)))
                       cand_trms
                       ([], []);
  
              (* Do relevant updates to the prover, theory constratints etc, from new theorems *)
              val (constr_params2,ctxt2) = 
                  result_config {conjs = conjs1, thrms = thms1} 
                                (constr_params,ctxt,thy_constrs)
            in 
              (constr_params2, ctxt2)
            end;
      in
        (*fold synth_one_size (min_size upto max_size) (init_constr_params, init_ctxt) *)
         fold synth_one_size (min_size upto max_size) 
             ((ConstraintParams.add_nesting_constrs init_ctxt max_nesting init_constr_params), 
              init_ctxt)
      end;

fun pretty_output (params,ctxt) = 
    let 
      val output = SynthOutput.Ctxt.get ctxt
      val thms = SynthOutput.get_thms output
      val conjs = SynthOutput.get_conjs output
      val (rw_thms,non_rw_thms) = 
          List.partition (OrderTerms.is_valid_rw (TheoryConstraints.init ctxt params) o snd) thms
    in
      Pretty.chunks[
      Pretty.chunks ((Pretty.str "Rewrite rules:") :: (map ((Trm.pretty ctxt) o Thm.concl_of o snd) rw_thms)),
      Pretty.chunks ((Pretty.str "Non-rewrite rules:") :: (map ((Trm.pretty ctxt) o Thm.concl_of o snd) non_rw_thms)),
      Pretty.chunks ((Pretty.str "Conjectures:") :: (map (Trm.pretty ctxt) conjs))
      ]
    end;

fun print_thms (params,ctxt) = Pretty.writeln (pretty_output (params, ctxt)); 
    
(*fun thm_synth_ac_pre (Prover prover) (CExFinder cex_finder) (ResultConfig result_config) 
      (VarAllowedFun var_allowed_fn) {max_size, min_size, max_vars, max_nesting}
      top_const (init_constr_params, init_ctxt) =
*)
(*
val max_size_parser = Parse.keyword_with (fn x => x = "max_term_size") |-- Parse.int;
val min_size_parser = Parse.keyword_with (fn x => x = "min_term_size") |-- Parse.int;
val max_vars_parser = Parse.keyword_with (fn x => x = "max_vars_size") |-- Parse.int;
val myparser = max_size_parser -- min_size_parser -- max_vars_parser

val _ = Keyword.keyword "max_term_size";
val _ = 
    Outer_Syntax.local_theory "sizes"
      "Max/Min term size and max number of different vars for synthesised terms." 
      Keyword.thy_decl
      (myparser >> (fn ((max_size,min_size),max_vars) => fn ctxt => (tracing (string_of_int max_size);ctxt)))


*)
end (*local open *)

end;

structure SynthInterface : SYNTH_INTERFACE = DB_SynthInterface;





(*-----------------------------------------------------------------------------*)
(* Synthesis of Equalities                                                     *) 
(* Old, update or delete *)
(*-----------------------------------------------------------------------------*)

(* Synthesise equational terms *)
(*
fun synthesise_eq_terms (min_size, max_size) max_vars ctxt0 constInfoTab = 
    synthesise_terms (Constant.mk "HOL.eq") VarAllowed.is_hole_in_lhs 
                     (min_size, max_size) max_vars ctxt0 
                     constInfoTab;

(* A type for secording statistics for a particular sized synthesis attempt. *)
type stats = {theorems : int, conjs: int, false_conjs : int, subsumed: int,
              synth_time: Time.time, update_time : Time.time, subs_time : Time.time,
              counterex_time: Time.time, prf_time: Time.time}


(* Print out pretty results and some stats *)
fun synth_w_stats (min_size, max_size) max_vars ctxt0 constInfoTab =
    let 
      val ((cinfo, ctxt), (conjs, thrms)) =  
          synthesise_eq_terms (min_size, max_size) max_vars ctxt0 constInfoTab
      val conjectures = map fst conjs
      val theorems = map fst thrms 
      val (ac_things, comm_thms) =  
          (map (fn (nm, cinfo) => 
                   if ((Constant.dest nm) = "HOL.eq")
                   then ([], []) (* Exclude = as these thms are built in *)
                   else
                     let 
                       val assoc = Constraints.get_assoc_opt cinfo
                       val comm = Constraints.get_commute_opt cinfo
                       val com_defs = Constraints.get_commuted_defs cinfo
                     in 
                       ((map_filter I [assoc, comm]), com_defs)
                     end) 
               (Constant.NTab.list_of cinfo))
            |> (fn thms => (flat (map fst thms), flat (map snd thms)))
           
      val line =  Pretty.str "-----------------------";
      val pretty_thms =  line::(Pretty.str "Synthesised theorems: ")::
                         (map (fn trm => Trm.pretty ctxt trm) theorems)
      val pretty_conjs = line::(Pretty.str "Synthesised conjectures (not proved): ")::
                         (map (fn trm => Trm.pretty ctxt trm) conjectures)
      val pretty_ac = line::(Pretty.str "AC-properties found: ")::
                      (map (fn trm => Trm.pretty ctxt trm) ac_things)
      val pretty_commutes = line::(Pretty.str "Commuted versions of defs: ")::
                      (map (fn trm => Trm.pretty ctxt trm) comm_thms)
      val _ = Pretty.writeln (Pretty.chunks(pretty_thms @ pretty_conjs 
                                            @ pretty_ac @ pretty_commutes))
      val _ = writeln ("\n False conjectures synthesised: " ^(Int.toString (!counter_ex_counter)))
    in
      ((cinfo, ctxt), (conjs, thrms)) 
    end;

*)

