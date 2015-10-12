(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_rtechn.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Modified:   Dominic Mulligan, University of Edinburgh
                dpm_edinburgh@yahoo.com
                12 Sept 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Relational rippling reasoning technique.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
signature RRIPPLE_RTECHN =
sig
  exception rrippling_rtechn_exp of string
  structure RRippleCInfo : RRIPPLE_CINFO 

  (* basic rippling tools *)
  val startr :  RTechn.T 
  val possible_steps : PPlan.gname -> RTechn.T
  val update_step : DTac.T -> ((string * Term.term) * RRippleCInfo.RippleSkel.T option) list -> RTechn.T
  val steps :  RTechn.T
  (*val cached_steps : RTechn.T *)
  val endr :  RTechn.T
  val weak_fert:  RTechn.T 

  (* without conjecturing *)
  val simplify_basecase : RTechn.T
  val ripple_stepcase :  RTechn.T
  val induct_and_ripple : RTechn.T
  val induct_and_ripple_with_rule : xstring -> RTechn.T

  (* with conjecturing *)
  val conj_critic : 
      RTechn.T (* lemma rtechn *)
      -> RTechn.T (* techn to be critiqued *)
      -> RTechn.T 
  val induct_ripple_conj : RTechn.T
  val induct_ripple_conj_with_rule : string -> RTechn.T

  
(* for the stand alone rippling tactic *)
(*  val fix_assume_and_prepare_ripping :
      Term.term list * Thm.thm list -> RTechn.T
  val just_ripple : Term.term list * Thm.thm list -> RTechn.T
*)
end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
functor RRippleRTechnFUN
          (structure RRippleCInfo : RRIPPLE_CINFO
           structure ConjRTechn : CONJ_RTECHN) :> RIPPLE_RTECHN =
  struct

(* prepare the skeleton, ie change object level "all's" and meta level
all's to schematic var representation. *)

(* IDEA: use records for autmatic type checking of results and for
passing back and taking information... this can capture state
transition requirements, such as needing explore to be true etc - this
would provide some compile-time code checking. *)

  (* val prep_skeleton = Data.rulify o Drule.gen_all; *)
  structure RRippleCInfo = RRippleCInfo;

  local 
    open RTechnEnv;
  in

    exception rippling_rtechn_exp of string;


(* Reasoning state pretty printing functions *)
    val basecaseN = RstName.str "Solve the base case by simplification.";
    val induct_and_rippleN = RstName.str "Solve using Induction and Rippling.";
    val induct_and_ripple_with_ruleN = RstName.str "Solve using Induction (custom rule) and Rippling.";
    val induct_and_ripple_lemcalcN = RstName.str "Solve using Induction, Rippling and Conjecturing.";
    val induct_and_ripple_lemacalc_with_ruleN = RstName.str "Solve using Induction (custom rule), Rippling and Conjecturing.";
    val strong_fertN = RstName.str "Strong fertilisation";  
    val weak_fertN = RstName.str "Weak fertilisation"; 
    
    fun start_ripplingN goal = 
      RstName.chunks [RstName.str "Start Rippling with state: ", (fn rst => RRippleCInfo.pretty_skels rst goal)];

    fun update_stepN dtac =
      RstName.f (fn rst => Pretty.chunks 
                             [Pretty.block 
                                [Pretty.str "Ripple Step by ", DTac.pretty dtac],
                                  RippleCInfo.pretty_curgoals_skels rst]);
    val solved_by_ripplingN = RstName.str "Rippling solves the goal directly";
    val stepcase_by_ripplingN = RstName.str "Solve the step case using rippling.";


    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Fertilisation                                                      *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (* Strong Fertilisation *)
    fun fert_critic goal rst =
      let 
        val skels = RippleCInfo.skeleton_names_of rst goal
      in
        ((SplitterRTechn.split_if_rtechn goal) thenr (map_then (fn g => (givename strong_fertN 
    (orr_list (map (fn s => apply_res s g) skels)))) try1_orelse DTacRTechn.simp_no_asm_simp_changes_loc)) rst
      end;

    fun strong_fert rst =
      let
        fun strong_fert_goal goal rst =
          givename strong_fertN (orr_list (map (fn s => apply_res s goal) (RippleCInfo.skeleton_names_of rst goal))) rst
      in
    (* map_then (fn g => (strong_fert_goal g)) rst *) 
        map_then (fn g => (strong_fert_goal g) try1_orelse (fert_critic g)) rst
      end;

    (* Weak Fertilisation by a single step of direct rewriting *)
    fun is_eq_term t = 
      is_some (Subst.move_to_concl_eq (Zipper.mktop t));
    fun subst_skel goal (skelnm,skel) rst= 
      (if is_eq_term skel then 
         let
           val gt = RstPP.goal_concl rst goal
     val z = Zipper.mktop gt
   in
     if is_eq_term gt then 
       orr_list [RTechnEnv.subst_in_lhs skelnm false goal, RTechnEnv.subst_in_rhs skelnm true goal]
           else
       (* try the skelequation both ways around *)
             orr_list [RTechnEnv.subst_eq skelnm false goal, RTechnEnv.subst_eq skelnm true goal]
   end
       else fail) rst;

    fun subst_skels goal skels =
      orr_list (map (subst_skel goal) skels);

    fun weak_fert rst = 
      let
        fun weak_fert_goal goal rst =
    givename weak_fertN (subst_skels goal (RippleCInfo.skeleton_namedterms_of rst goal)) rst; 
      in
        map_then weak_fert_goal rst
      end;

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Start Rippling                                                     *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (* given an reasoning state which is being use to explore, then we can *)
    (* setup rippling with the give skeleton terms and theorems.           *)
    val startr = 
      let 
        fun startr_goal goal rst = 
    let 
      val ppl = RState.get_pplan rst;
      (* val skels = PPlan.get_asmtrms ppl goal; *)
            val skels = PPlan.get_varified_lasmtrms ppl goal;
    in
        rst |> RState.set_rtechn NONE
        |> (givename (start_ripplingN goal)
         (RippleCInfo.start skels))
    end;
      in
        map_then startr_goal
      end;


    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Case-splitting                                                     *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


    (* solve non-rippling branches of if-statements using this             *)
    (* function. At the moment it requires simp to solve the goal          *)
    (* completely, otherwise it fails.                                     *)
    fun solve_by_simp rst =     
      Seq.map_filter (fn r => if (null (RState.get_goalnames r)) then (SOME r) else NONE) 
        (DTacRTechn.simp_no_asm_simp_changes_loc rst);

    fun simp_nonripples rst = 
      let 
        (* Do I want to use RippleCInfo.is_rippling or RippleCInfo.is_valid_ripple_state_goal ? *)
        val (ripples, nonripples) = RTechnEnv.split_goals (RippleCInfo.is_rippling rst) (RState.get_goalnames rst)
      in 
  (*Non non rippling steps*)
   if (null nonripples) then 
     Seq.single (dummy_rst (RstName.str "No non-ripples after split.") rst)
   else
     (*Keep states where simp succeded in solving the non-rippling goal*)
     ((RState.set_goalnames nonripples) fthen
       (solve_by_simp thenf (RState.set_goalnames ripples))) rst 
      end;

    (* update the ripple cinfo after applying a critic to do case-splitting *)
    fun update_critic_step old_skels rst = 
      RippleCInfo.update old_skels (RState.set_rtechn NONE rst);

    fun case_split split_tech goal rst =
      let 
        val old_skels = RippleCInfo.all_skels_of rst goal
  val rsts = (split_tech goal rst) :-> (RippleCInfo.update old_skels)
      in
  Seq.map (continue_with simp_nonripples) rsts
      end;

    (* Check if the goal the goal contains an if-or case statement that we need to deal with *) 
    fun applicable_critic_of rst goal = 
      if (SplitterRTechn.is_if rst goal) then 
  SOME (case_split SplitterRTechn.split_if_rtechn goal)
      else 
  case (SplitterRTechn.is_case rst goal) of
    (SOME caseinfo) => SOME (case_split SplitterRTechn.split_case_rtechn goal)
  | _ => NONE;

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Middle-out Stuff and Critics                                       *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

    fun update_midout_N rule =
      RstName.f (fn rst => Pretty.chunks 
                             [Pretty.block 
                                [Pretty.str ("Mid-out Ripple Step by rule: "^rule)], RippleCInfo.pretty_curgoals_skels rst])

    (* FIXME - give name properly and include the rulename etc *)
    fun update_midout_step goal old_skels mes_thld (rule_nm, rst) =
      (givename (update_midout_N rule_nm) (RippleCInfo.update_midout old_skels mes_thld)) (RState.set_rtechn NONE rst)

    fun poss_midout_steps mes_thld goal rst =
      let 
        val old_skels = RippleCInfo.all_skels_of rst goal
      in
        (MiddleOutRW.midout_rw goal rst) :-> (update_midout_step goal old_skels mes_thld)
      end;

    fun midout_ripple_steps mes_thld eager_fert_tech rst = 
      let
        fun steps_goal goal rst = 
    let  
      val possibles = 
              ((poss_midout_steps mes_thld goal) thenr (eager_fert_tech try1_orelse (midout_ripple_steps mes_thld eager_fert_tech))) rst  
    in
      if RippleCInfo.blocked_chk rst goal (Seq.list_of possibles) then 
        fail rst        
      else
        possibles
    end  
      in
        map_then steps_goal rst
      end;

    val apply_lemma_N  =
      RstName.f (fn rst => Pretty.chunks 
                             [Pretty.block 
                                [Pretty.str "Apply speculated lemma "], RippleCInfo.pretty_curgoals_skels rst])

    (* apply a schematic lemma. copute measure and embedding optimisticly, *)
    (* ie. ignore meta-variables and compute embedding for projections *)
    fun apply_lemma end_midout_r goal (*lemma_trm*) lemma_nm rst =
      let
        (*val (lemma_nm, ppl) = PPlan.new_topgoal ("spec_lemma_", lemma_trm) (RState.get_pplan rst) *)
  (* take worst mesure *)
        val mes_thld = List.last (Library.sort RippleCInfo.RippleSkel.RippleMeasure.ord (RippleCInfo.measures_of rst goal))

  fun apply lemma_nm goal rst = 
    let 
      val old_skels = RippleCInfo.all_skels_of rst goal
    in
      (RTechnEnv.subst_eq lemma_nm false goal rst)
      (*(DTacRTechn.subst_eq lemma_nm false goal rst) *)
      :->  (fn rst1 => (givename apply_lemma_N (RippleCInfo.update_midout old_skels mes_thld)) (RState.set_rtechn NONE rst1)) 
    end

    (* continue with mid-out ripple steps. The measure need to be at least one *)
          (* better than before, as applying the lemma would have had to improve mes.*)
  val rsts = Seq.map (continue_with (midout_ripple_steps mes_thld (end_midout_r lemma_nm))) (apply lemma_nm goal rst) 
      in
        rsts
      end;

    fun add_lemma end_midout_r goal lemma_trm rst =
      let
        val ppl0 = RState.get_pplan rst
  val (lemma_nm, ppl) = Prf.conj_term_in_cx  "spec_lemma_" lemma_trm (Prf.get_ndname_cxname ppl0 goal) ppl0
      in
        givename (RstName.pretty (Pretty.chunks [(Pretty.str "Adding speculated lemma: " ), Trm.pretty (PPlan.get_theory ppl) lemma_trm]))
  (* (RstName.str ("Adding speculated lemma: "^lemma_nm)) *)
        (fn rst' => Seq.single (continue_with (apply_lemma end_midout_r goal lemma_nm) rst')) (RState.set_pplan ppl rst)
      end;

    fun lemma_spec end_midout_r rst = 
      let
       fun lemma_spec_goal goal rst =
         let 
           (* the lemmas from each skeleton *)
           val skels = RippleCInfo.inst_skels_terms rst goal
     (* This is either a list [lhs_lemma, rhs_lemma] or a singelton list if the goal is not an equation *)
     val lemmas = LemmaSpec.lemmaspec skels goal rst
     (* take worst mesure *)
     val mes_thld = List.last (Library.sort RippleCInfo.RippleSkel.RippleMeasure.ord (RippleCInfo.measures_of rst goal))                                
     (* if goal is equation, get two schematic lemmas per skeleton, here apply one OR the other.*)
     val rtechs = orr_list (map (add_lemma end_midout_r goal) lemmas)
   in
           (* Apply the lemma for a skeleton OR another skel. *)
     rtechs rst
   end
      in
        map_then lemma_spec_goal rst
      end;

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Rippling Steps for reverse rippling                                *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    val startr_rev = 
      let 
        fun startr_goal goal rst = 
    let 
      val ppl = RState.get_pplan rst;
            (* val skels = PPlan.get_asmtrms ppl goal; *)
            val skels = PPlan.get_varified_lasmtrms ppl goal;
    in
      rst |> RState.set_rtechn NONE
          |> (givename (start_ripplingN goal) (RippleCInfo.start_rev skels))
    end;
      in
        map_then startr_goal
      end;

    fun update_step_rev dtac old_skels rst =
      (givename (update_stepN dtac) (RippleCInfo.update_rev old_skels)) (RState.set_rtechn NONE rst)

    fun possible_steps_rev goal rst = 
      let 
        val old_skels = RippleCInfo.all_skels_of rst goal
  val dtacs = RippleCInfo.applicable_dtacs_of rst goal
      in
  (apply_or_dtacs_to_g dtacs goal rst) :-> (fn (dtac,rst) => update_step_rev dtac old_skels rst)
      end

    fun steps_rev rst =
      let
        fun steps_goal goal rst =
    let
      val possibles = Seq.map (continue_with steps_rev) (possible_steps_rev goal rst)
    in
      possibles
    end
      in
  map_then steps_goal rst 
      end;

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Rippling Steps                                                     *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

    (* update the rippling state information *)
    fun update_step dtac old_skels rst = 
      (givename (update_stepN dtac) (RippleCInfo.update old_skels)) (RState.set_rtechn NONE rst)

    (* do a ripple valid steps using the wave rules in the wave rule DB.   *)
    (* When we get to a state which has a new best out measure, and no     *)
    (* following state has a better out measure, then we know rippling out *)
    (* is blocked. Similarly, for rippling in.                             *)
    fun possible_steps cont_tech goal rst =
      case (applicable_critic_of rst goal) of 
  (* NOTE: Critic might be a compound technique, so take care with continuations *)
        SOME critic =>(critic thenr cont_tech) rst                 
      | NONE =>
        let 
          val old_skels = RippleCInfo.all_skels_of rst goal
    val dtacs = RippleCInfo.applicable_dtacs_of rst goal
        in 
          let 
            val possibles = (apply_or_dtacs_to_g dtacs goal rst) :-> (fn (dtac,rst) => update_step dtac old_skels rst)
                            |> Seq.map (continue_with cont_tech)
          in
            if RippleCInfo.blocked_chk rst goal (Seq.list_of possibles) then 
        Seq.cons (dummy_rst (RstName.str ("end rippling, goal: " ^ goal)) rst) possibles
      else
        possibles
          end
        end;

    fun steps rst =
      let
        fun steps_goal goal rst =
    let
      (*remove possible if-statements, then continue with rippling or apply simp to non-rippling subgoals *)
      val cont_techn = (map_then steps_goal) 
      val possibles = possible_steps cont_techn goal rst (*Seq.map (continue_with cont_techn) *)
    in
            possibles
    end
      in
        map_then steps_goal rst 
      end;

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Simplify Base Case                                                 *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (* Simplify the base case *)
    val simplify_basecase = givename basecaseN DTacRTechn.simp_no_asm_simp_changes; 

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Induction and Rippling: no conjecturing                            *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    fun endr rst = 
      rstif (null o RState.get_goalnames) (dummy solved_by_ripplingN)      
  (split_then (RippleCInfo.success_chk rst) strong_fert
    (weak_fert try1_then (DTacRTechn.simp_noasm
            try1_orelse (dummy (RstName.str "Step case stuck"))))) rst;
    
    fun ripple_stepcase rst = 
      (refine stepcase_by_ripplingN (startr thenr steps thenr endr))
      rst 

    fun induct_and_ripple rst = 
      refine induct_and_rippleN (InductRTechn.induction simplify_basecase ripple_stepcase) rst; 

    fun induct_and_ripple_with_rule rule rst = 
      (refine induct_and_ripple_with_ruleN
        (InductRTechn.induction_with 
          (thm rule) simplify_basecase ripple_stepcase)) rst; 
    (* final rst is needed becasue of fun/val distinction *)


    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Induction and Rippling with Lemma Calc                             *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    fun conj_critic lemmatechn r = 
      r thenr (rstif RstPP.solved_focusgoals (dummy_str "Solved!")
        (map_then (ConjRTechn.prove_goal_by_lemma lemmatechn)));

    (* only with lemma calc *)
    fun endr_lemcalc rst = 
      rstif (null o RState.get_goalnames) (dummy solved_by_ripplingN)
        (split_then (RippleCInfo.success_chk rst) strong_fert (weak_fert 
          try1_then (DTacRTechn.simp_noasm try1_orelse                         
            (map_then (ConjRTechn.prove_goal_by_lemma induct_ripple_lemcalc))))) rst
    and ripple_stepcase_lemcalc rst = 
      (refine stepcase_by_ripplingN (startr thenr steps thenr endr_lemcalc)) rst
    and induct_ripple_lemcalc rst = 
      (refine induct_and_ripple_lemcalcN
        (InductRTechn.induction 
          (conj_critic induct_ripple_lemcalc simplify_basecase)        
            (ripple_stepcase_lemcalc))) rst;

    (* given explicit rule for first induction *)
    fun induct_ripple_lemcalc_with_rule rule = 
      refine induct_and_rippleN ((InductRTechn.induction_with (thm rule))
        (conj_critic induct_ripple_lemcalc simplify_basecase) (induct_ripple_lemcalc));   

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (*  Induction and Rippling with Lemma Speculation                      *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

    val weak_fert_then_calc =
      weak_fert thenr ((solve_or_nothing DTacRTechn.simp_noasm) try1_orelse                         
        (map_then (ConjRTechn.prove_goal_by_lemma induct_ripple_lemcalc)))

    (* Only want projections that keep the skeleton *)
    fun check_project old_skels goal rst =
      let 
        val goal_trm = RstPP.goal_concl rst goal
      in
  if (null (map (fn skel => EmbeddingLib.embed skel goal_trm) old_skels)) then
    Seq.empty
  else
    Seq.single (RState.set_rtechn NONE rst)
      end;

    fun weak_fert_of_projections goal rst = 
      let
        val old_skels_trms = map (snd o fst) (RippleCInfo.all_skels_of rst goal)
      in
        (LemmaSpec.expl_projections goal rst)
  :-> (check_project old_skels_trms goal)
  :-> strong_fert try1_orelse weak_fert
      end;

    (* Post middle-out rippling: explore projections and attempt weak-fertilisation.*)
    fun end_midout lemma_nm rst = 
        (* THINK: Might not want to project remaining meta-vars. These are really *)
        (* universally quantified things.                                         *)

  (* Right now: Only explore projections and then try weak                  *)
  (* fertilisation. Do not start proving any of the two lemmas (takes too   *)
        (* long).                                                                 *)
  let 
          fun some_counterex rs = 
            let 
              val non_counterex = map (fn g =>
                                         (if (CounterExCInfo.has_counterex g rs) then NONE else SOME g)) 
                                           (RState.get_goalnames rs)
            in
              null non_counterex
            end;                       
  in
          (map_then weak_fert_of_projections rst)   
  end;

    (* post_rippling: solve, or strong fertilise, or weak fert then calculation, *)
    (* orelse try speculation. *)
    fun endr_lemspec rst = 
      rstif (null o RState.get_goalnames) (dummy solved_by_ripplingN) 
        (split_then (RippleCInfo.success_chk rst) strong_fert                 
          (weak_fert_then_calc try1_orelse (lemma_spec end_midout))) rst;

    fun ripple_stepcase_lemspec rst = 
      (refine stepcase_by_ripplingN (startr thenr steps thenr endr_lemspec)) rst;

    fun induct_ripple_lemspec rst = 
      (refine induct_and_rippleN
        (InductRTechn.induction 
          (conj_critic induct_ripple_lemspec simplify_basecase)
            (ripple_stepcase_lemspec))) rst;

    fun induct_ripple_lemspec_with_rule rule = 
      refine induct_and_rippleN
        ((InductRTechn.induction_with (thm rule))
          (conj_critic induct_ripple_lemspec simplify_basecase)
            (ripple_stepcase_lemspec));   

  end; (* RTechnEnv local *) 
           
  end; (* struct *)
