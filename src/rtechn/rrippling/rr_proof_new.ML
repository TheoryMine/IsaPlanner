(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_proof_new.ML
    Author:     Dominic Mulligan, University of Edinburgh AND
                Lucas Dixon, University of Edinburgh
                dpm_edinburgh@yahoo.com
                lucasd@dai.ed.ac.uk
    Created:    10 Sept 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Test proof for relational rippling.
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


Trm.drop_var_args_flag := false;
quick_and_dirty := true;


val thry = (theory "Relations");
val gctxt = (Context.Theory thry);
val ctxt = (ProofContext.init thry);

local 
val thm = PureThy.get_thm thry;
in

(* require ordering of goals to be the same as ordering of anames in L *)
fun resol_fwd_multi_i abovegname L cname pp = 
    let 
      val ((new_cname, goals), pp) = Prf.lift_and_show_above cname (map fst L) abovegname pp;
      val fnames = (map snd L)
      val how_to_solve_goals = (fnames ~~ goals)

      fun apply_one_fact (f,g) (oldgoals,pp) = 
    Seq.map (fn (newgoals,pp2) => (newgoals @ oldgoals, pp2)) 
      (Prf.apply_resol_bck f g pp)

    in
      (new_cname, fold (Seq.maps o apply_one_fact) how_to_solve_goals (Seq.single ([],pp)))
    end;

fun resol_fwd_multi abovegname L cname pp = 
    let 
      val pp2 = Prf.start_meth [] pp
      val (new_cname, ppseq) = resol_fwd_multi_i abovegname L cname pp2
    in 
      Seq.map (fn (goals,pp3) => (new_cname,(goals,Prf.end_meth "res_fwd_multi" [new_cname] [] pp3 pp))) ppseq
    end;

(* 
   Forward reasons from a goal with a theorem, then resolves away any
   other extraneous assumptions of the theorem with other subgoals.
*)
(* Theorem name, goal to apply to, list of goalnames, goalname ctxt, proofplan *)
fun apply_thm_and_resolve_away t goal [] ctxtof pp =
      (pp |> Prf.apply_frule_thm (thm t) goal)
  | apply_thm_and_resolve_away t goal (l as (head::tail)) ctxtof pp =
      let
        val s = Seq.maps (fn (g, p) =>
          let
                              val assms = Prf.get_ndname_lasms p g
                              val comb = assms ~~ l
                            in
                              (p |> resol_fwd_multi ctxtof comb g)
                            end) (pp |> Prf.apply_frule_thm (thm t) goal)
      in
        Seq.map (fn ((new_ctxt, (x, (y, pp)))) => (new_ctxt, pp)) s
      end;

(*
fun split rst =
  let
    val exIdthm = DThm.mk (thm "exI")
    val conjIdthm = DThm.mk (thm "conjI")
    val _ = writeln "look here:"
    val _ = map writeln (RState.get_goalnames rst);
    open RTechnEnv;
  in
    ((apply_to_each_goal (apply_rule_dthm exIdthm)) thenr (apply_to_each_goal (apply_rule_dthm conjIdthm))) rst
  end;
*)


val pp = Prf.init ctxt;
val expr = Prf.read_top_term pp "!!r a b c. [| n (a::'a) c \\<in> r*** ; r a b |] ==> (EX d. n b d::'a \\<in> r*** & r c d)";
val CR_expr = Prf.read_top_term pp "!!r a b c. [| r (a::'a) b ; r a c |] ==> (EX v. r b v & r c v)";
val (g, pp) = Prf.conj_top_term "g" expr pp;
val rst = RState.init_from_pp pp;

val rtab = RelationTab.empty;
val instenv0 = InstEnv.init thry;

val (rst::L) = Seq.list_of (InductRTechn.just_induction_on_goal g rst);
val [base_case, step_case_1] = RState.get_goalnames rst;
val [IH_conc, Assm1, Assm2] = Prf.get_ndname_lasms (RState.get_pplan rst) step_case_1;
val [IH_assm_l, IH_assm_r] = Prf.get_ndname_lasms (RState.get_pplan rst) IH_conc;

val ((for_imp, pp)::L) = Seq.list_of (RState.get_pplan rst |> Prf.apply_frule_thm (thm "confluence_single_forward_imp") Assm1);
val (([step_case_2], pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "exE") for_imp step_case_1);
val [assm] = Prf.get_ndname_lasms pp step_case_2;

val ((ra2, pp)::L) = Seq.list_of (pp |> Prf.apply_frule_thm (thm "HOL.conjunct1") assm);
val ((ra1, pp)::L) = Seq.list_of (pp |> Prf.apply_frule_thm (thm "HOL.conjunct2") assm);

(* First set of embeddings: ra1 into Assm1 and ra2 into Assm2 *)
val rtab = RRippleLinkInfo.add_relational_link rtab (Prf.get_ndname_ctrm pp Assm2) Assm2;
val rtab = RRippleLinkInfo.add_relational_link rtab (Prf.get_ndname_ctrm pp ra2) ra2;

val [(instenv1, embedding1)] = Seq.list_of (RREmbeddingLib.embed rtab instenv0 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp ra1)) (Prf.get_ndname_ltrm pp Assm1));
val [(instenv2, embedding2)] = Seq.list_of (RREmbeddingLib.embed rtab instenv1 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp ra2)) (Prf.get_ndname_ltrm pp Assm2));

val [embedding1at] = RRipplingATerms.r_aterms_of_eterm embedding1;
val [embedding2at] = RRipplingATerms.r_aterms_of_eterm embedding2;

val mode_rtc3 = ModalityInfo.goal_mode_info_i ModalityInfo.empty (RRTrmUtil.num_args (Prf.get_ndname_ctrm pp ra1));
val mode_r = ModalityInfo.goal_mode_info_i ModalityInfo.empty (RRTrmUtil.num_args (Prf.get_ndname_ctrm pp ra2));

(* End first set of embeddings. *)

val (CR_conc, pp) = Prf.conj_top_term "CR_conc" CR_expr pp;
val [CR_asm1, CR_asm2] = (Prf.get_ndname_lasms pp CR_conc);

val ((new_CR, (conj2, ([], pp)))::L) = 
    Seq.list_of (pp |> resol_fwd_multi step_case_2 [(CR_asm1, ra2), (CR_asm2, Assm2)] CR_conc);

val (([new_CR], pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "exE") new_CR step_case_2);
val [assm] = Prf.get_ndname_lasms pp new_CR;
val ((cr2, pp)::L) = Seq.list_of (pp |> Prf.apply_frule_thm (thm "HOL.conjunct1") assm);
val ((cr1, pp)::L) = Seq.list_of (pp |> Prf.apply_frule_thm (thm "HOL.conjunct2") assm);

(* Second set of embeddings: ra1 into Assm1, cr2 and cr1 into Assm2 *)

val rtab = RRippleLinkInfo.add_relational_link rtab (Prf.get_ndname_ctrm pp cr1) cr1;
val rtab = RRippleLinkInfo.add_relational_link rtab (Prf.get_ndname_ctrm pp cr2) cr2;

val [(instenv3, embedding3)] = Seq.list_of (RREmbeddingLib.embed rtab instenv2 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp ra1)) (Prf.get_ndname_ltrm pp Assm1));
val [(instenv4, embedding4)] = Seq.list_of (RREmbeddingLib.embed rtab instenv3 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp cr1)) (Prf.get_ndname_ltrm pp Assm2));
val [(instenv5, embedding5)] = Seq.list_of (RREmbeddingLib.embed rtab instenv3 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp cr2)) (Prf.get_ndname_ltrm pp Assm2));

val [embedding3at] = RRipplingATerms.r_aterms_of_eterm embedding3;
val [embedding4at] = RRipplingATerms.r_aterms_of_eterm embedding4;
val [embedding5at] = RRipplingATerms.r_aterms_of_eterm embedding5;

val SOME(mode_rtc3) = ModalityInfo.update mode_rtc3 embedding1at embedding3at;
val SOME(mode_r) = ModalityInfo.update mode_r embedding2at embedding4at;
val SOME(mode_r) = ModalityInfo.update mode_r embedding2at embedding5at;

(* End second set of embeddings. *)

val [IH_assm_l, IH_assm_r] = Prf.get_ndname_lasms pp IH_conc;

val ((new_Goal, ([], ([], pp)))::L) = Seq.list_of (pp |> resol_fwd_multi new_CR [(IH_assm_l, ra1), (IH_assm_r, cr2)] IH_conc);
val (([step_case_3], pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "exE") new_Goal "exEg");
val [assm] = Prf.get_ndname_lasms pp step_case_3;
val ((cnc1, pp)::L) = Seq.list_of (pp |> Prf.apply_frule_thm (thm "HOL.conjunct1") assm);
val ((cnc2, pp)::L) = Seq.list_of (pp |> Prf.apply_frule_thm (thm "HOL.conjunct2") assm);

(* Third set of embeddings.  We've applied the IH, so new rtab and instenv, too. *)
val (([em31], pp')::L) = Seq.list_of (pp |> Prf.apply_rule_thm (thm "exI") step_case_3);
val (([em32, em33], pp')::L) = Seq.list_of (pp' |> Prf.apply_rule_thm (thm "conjI") em31);

(*
val rst = RState.init_from_pp pp;
val rst = RState.set_goalnames [step_case_3] rst;
val [rst] = Seq.list_of (split rst);
*)

val rtab = RRippleLinkInfo.add_relational_link RelationTab.empty (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' em33)) em33;
val rtab = RRippleLinkInfo.add_relational_link rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' cnc2)) cnc2;
val rtab = RRippleLinkInfo.add_relational_link rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' cr1)) cr1;
val instenv0 = InstEnv.init thry;
val mode_rtc3 = ModalityInfo.goal_mode_info_i ModalityInfo.empty (RRTrmUtil.num_args (Prf.get_ndname_ctrm pp ra1));
val mode_r = ModalityInfo.goal_mode_info_i ModalityInfo.empty (RRTrmUtil.num_args (Prf.get_ndname_ctrm pp ra2));

val [(instenv6, embedding6)] = Seq.list_of (RREmbeddingLib.embed rtab instenv0 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' em33)) (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' cnc2)));
val [(instenv7, embedding7)] = Seq.list_of (RREmbeddingLib.embed rtab instenv6 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' cnc1))
                                                                               (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' em32)));

val [embedding6at] = RRipplingATerms.r_aterms_of_eterm embedding6;
val [embedding7at] = RRipplingATerms.r_aterms_of_eterm embedding7;

val SOME(mode_r) = ModalityInfo.update mode_r embedding2at embedding6at;
val SOME(mode_rtc3) = ModalityInfo.update mode_r embedding1at embedding7at;

(* End third set of embeddings. *)

val ((lg, pp)::L) = Seq.list_of (pp |> apply_thm_and_resolve_away "rtc3.step" cnc1 [cr1] step_case_3);

(* Final set of embeddings. *)
val (([em41], pp')::L) = Seq.list_of (pp |> Prf.apply_rule_thm (thm "exI") step_case_3);
val (([em42, em43], pp')::L) = Seq.list_of (pp' |> Prf.apply_rule_thm (thm "conjI") em41);

val [(instenv8, embedding8)] = Seq.list_of (RREmbeddingLib.embed rtab instenv7 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' em42))
                                                                               (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' lg)));
val [(instenv9, embedding9)] = Seq.list_of (RREmbeddingLib.embed rtab instenv8 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' em43))
                                                                               (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp' cnc2)));

val [embedding8at] = RRipplingATerms.r_aterms_of_eterm embedding8;
val [embedding9at] = RRipplingATerms.r_aterms_of_eterm embedding9;

val SOME(mode_rtc3) = ModalityInfo.update mode_rtc3 embedding1at embedding8at;
val SOME(mode_r) = ModalityInfo.update mode_r embedding2at embedding9at;
(* End final set of embeddings. *)

val ((goal, pp)::L) = Seq.list_of (pp |> apply_thm_and_resolve_away "conjI" lg [cnc2] step_case_3);
val (([final], pp)::L) = Seq.list_of (pp |> Prf.apply_rule_thm (thm "exI") step_case_3);
val (([], pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck goal final);

end;

(* End of proof. *)
