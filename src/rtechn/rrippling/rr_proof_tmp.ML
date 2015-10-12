fun rename_vars (x $ y) = (rename_vars x) $ (rename_vars y)
  | rename_vars (Var ((n,i), x)) = Var(("z",i), x)
  | rename_vars x = x;

Trm.drop_var_args_flag := false;
quick_and_dirty := true;
val thry = the_context();
val pp = Prf.init thry;
val expr = Prf.read_top_term pp "!!a b c. [| n a c \<in> r*** ; r a b |] ==> (EX d. n b d \<in> r*** & r c d)";
val CR_expr = Prf.read_top_term pp "!!x y z. [| r x y ; r x z |] ==> (EX v. r y v & r z v)";
val (g, pp) = Prf.conj_top_term "g" expr pp;
val (CR_conc, pp) = Prf.conj_top_term "CR_conc" CR_expr pp;
val rst = RState.init_from_pp pp;
val (rst::L) = Seq.list_of (InductRTechn.just_induction_on_goal g rst);
val [base,step1] = RState.get_goalnames rst;

val rtab = RelationTab.empty;

(*val premeth_p = (RState.get_pplan rst);
val pp = Prf.start_meth [step1] (RState.get_pplan rst);*)

val [IH_conc, Assm1, Assm2] = Prf.get_ndname_lasms (RState.get_pplan rst) step1;
val [IH_assm_l, IH_assm_r] = Prf.get_ndname_lasms (RState.get_pplan rst) IH_conc;

val ((goal, goals), pp) = Prf.lift_and_show_above IH_conc [] step1 (RState.get_pplan rst);
val [IH_assm_l_new, IH_assm_r_new] = Prf.get_ndname_lasms pp goal;

(* Get an embedding of Assm1 into IH_assm_l and Assm2 into IH_assm_2 *)
val rtab = RRippleCInfo.add_relational_link rtab (Prf.get_ndname_ltrm pp Assm2) Assm2;
(* val rtab_s = RelationTab.to_string rtab; *)
val instenv0 = InstEnv.init (the_context ());

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp Assm1);
val mode_rtc3 = ModalityInfo.goal_mode_info_i ModalityInfo.empty (RRTrmUtil.num_args (Prf.get_ndname_ltrm pp Assm1));
val [(instenv1, embedding_1)] = PolyML.exception_trace (fn () => (Seq.list_of (RREmbeddingLib.embed rtab instenv0 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_l_new)) (Prf.get_ndname_ltrm pp Assm1))));
val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_1)));
val _ = writeln "";

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp Assm2);
val mode_r = ModalityInfo.goal_mode_info_i ModalityInfo.empty (RRTrmUtil.num_args (Prf.get_ndname_ltrm pp Assm2));
val [(instenv2, embedding_2)] = PolyML.exception_trace (fn () => (Seq.list_of (RREmbeddingLib.embed rtab instenv1 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_r_new)) (Prf.get_ndname_ltrm pp Assm2))));
val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_2)));
val _ = writeln "";
(* End embeddings. *)

val ((for1,pp)::L) = Seq.list_of (pp |> Prf.apply_frule_thm (thm "confluence_single_forward_imp") Assm1);
val (([step3],pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "exE") for1 step1);
val [exEAssm] = Prf.get_ndname_lasms pp step3;
val (([step4], pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "conjE") exEAssm step3);
val [ra2, ra1] = Prf.get_ndname_lasms pp step4;

(* Get an embedding of ra1 into IH_assm_l_new and ra2 and Assm2 into IH_assm_r_new *)
val rtab = RRippleCInfo.add_relational_link rtab (Prf.get_ndname_ltrm pp ra2) ra2;

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp ra1);
val [(instenv3, embedding_3)] = Seq.list_of (RREmbeddingLib.embed rtab instenv2 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_l_new)) (Prf.get_ndname_ltrm pp ra1));

(* Update our modality information. *)
val [em_1_at] = RRipplingATerms.r_aterms_of_eterm embedding_1
val [em_3_at] = RRipplingATerms.r_aterms_of_eterm embedding_3
val SOME(mode_rtc3) = ModalityInfo.update mode_rtc3 em_1_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_1_at)) em_3_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_3_at));

val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_3)));
val _ = writeln "";

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp Assm2);
val [(instenv4, embedding_4)] = Seq.list_of (RREmbeddingLib.embed rtab instenv3 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_r_new)) (Prf.get_ndname_ltrm pp Assm2));

(* Update our modality information. *)
val [em_2_at] = RRipplingATerms.r_aterms_of_eterm embedding_2
val [em_4_at] = RRipplingATerms.r_aterms_of_eterm embedding_4
val SOME(mode_r) = ModalityInfo.update mode_r em_2_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_2_at)) em_4_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_4_at));
val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_4)));
val _ = writeln "";

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp ra2);
val [(instenv5, embedding_5)] = Seq.list_of (RREmbeddingLib.embed rtab instenv4 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_r_new)) (Prf.get_ndname_ltrm pp ra2));

val [em_2_at] = RRipplingATerms.r_aterms_of_eterm embedding_2
val [em_5_at] = RRipplingATerms.r_aterms_of_eterm embedding_5
val SOME(mode_r) = ModalityInfo.update mode_r em_2_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_2_at)) em_5_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_5_at));

val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_5)));
val _ = writeln "";
(* End embeddings. *)

val (([crh1,crh2,step5],pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "exE") CR_conc step4);
val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck Assm2 crh1);
val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck ra2 crh2);
val [CRAssm] = Prf.get_ndname_lasms pp step5;
val (([step6],pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "conjE") CRAssm step5);
val [cr2,cr1] = Prf.get_ndname_lasms pp step6;

(* Get an embedding of ra1 into IH_assm_l_new and cr2 and cr1 into IH_assm_r_new *)
val rtab = RRippleCInfo.add_relational_link rtab (Prf.get_ndname_ltrm pp cr1) cr1;
val rtab = RRippleCInfo.add_relational_link rtab (Prf.get_ndname_ltrm pp cr2) cr2;
(* val rtab_s = RelationTab.to_string rtab; *)

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp ra1);
val [(instenv6, embedding_6)] = Seq.list_of (RREmbeddingLib.embed rtab instenv5 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_l_new)) (Prf.get_ndname_ltrm pp ra1));
val [em_1_at] = RRipplingATerms.r_aterms_of_eterm embedding_1;
val [em_6_at] = RRipplingATerms.r_aterms_of_eterm embedding_6;
val SOME(mode_rtc3) = ModalityInfo.update mode_rtc3 em_1_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_1_at)) em_6_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_6_at));

val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_6)));
val _ = writeln "";

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp cr2);
val [(instenv7, embedding_7)] = Seq.list_of (RREmbeddingLib.embed rtab instenv6 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_r_new)) (Prf.get_ndname_ltrm pp cr2));

val [em_2_at] = RRipplingATerms.r_aterms_of_eterm embedding_2;
val [em_7_at] = RRipplingATerms.r_aterms_of_eterm embedding_7;
val SOME(mode_r) = ModalityInfo.update mode_r em_2_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_2_at)) em_7_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_7_at));

val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_7)));
val _ = writeln "";

val _ = RRTrmUtil.print_term_info (Prf.get_ndname_ltrm pp cr1);
val [(instenv8, embedding_8)] = Seq.list_of (RREmbeddingLib.embed rtab instenv7 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_assm_r_new)) (Prf.get_ndname_ltrm pp cr1));

val [em_2_at] = RRipplingATerms.r_aterms_of_eterm embedding_2;
val [em_8_at] = RRipplingATerms.r_aterms_of_eterm embedding_8;
val SOME(mode_r) = ModalityInfo.update mode_r em_2_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_2_at)) em_8_at (RRTrmUtil.num_args (RRipplingATerms.inst_skel_term em_8_at));

val _ = map (fn x=> let val _ = map (TextIO.print) x in writeln "" end) (map (map (fn x => case x of RRipplingATerms.WFNone => "N" | RRipplingATerms.WFFunc => "F" | RRipplingATerms.WFRel => "R")) (map (RRipplingATerms.wave_fronts_at) (RRipplingATerms.r_aterms_of_eterm embedding_8)));
val _ = writeln "";
(* End embeddings. *)

(*val (g,pp) = Prf.end_meth "Forwards on the assumptions." [step6,cr2,cr1,IH_conc,CR_conc] [step1] pp premeth_p;
val premeth_p = pp;
val pp = Prf.start_meth [step6] pp;*)

val (([IH_conc_l_new, IH_conc_r_new, step7],pp)::L)  = Seq.list_of (pp |> Prf.apply_erule_thm (thm "exE") IH_conc step6);

(*val (g, pp) = Prf.end_meth "Application of inductive hypothesis." [crgoal1, step7] [step6] pp premeth_p;
val premeth_p = pp;
val pp = Prf.start_meth [step7, crgoal1] pp;*)

(*val (([rtc_stepl, rtc_stepr],pp)::L) = Seq.list_of (pp |> Prf.apply_rule_thm (thm "conjI") rtc_step);
val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck ra1 rtc_stepl);
val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck "conjEn" rtc_stepr);*)

val (([step8], pp)::L) = Seq.list_of (pp |> Prf.apply_rule_thm (thm "exI") step7);
val (([step9l, cnc2], pp)::L) = Seq.list_of (pp |> Prf.apply_rule_thm (thm "conjI") step8);

(* Get a fresh set of embeddings. *)
val rtab = RelationTab.empty;
val rtab = RRippleCInfo.add_relational_link rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp cnc2)) cnc2;

val instenv8 = InstEnv.init (the_context ());

(*
val [(instenv9, embedding_9)] = Seq.list_of (RREmbeddingLib.embed rtab instenv8 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_conc_r_new)) (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp cnc2)));
val [(instenv10, embedding_10)] = Seq.list_of (RREmbeddingLib.embed rtab instenv9 (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_conc_l_new)) (Prf.get_ndname_ctrm pp step9l)); *)
(* End embeddings. *)

val (([cnc1, cr2b], pp)::L) = Seq.list_of (pp |> Prf.apply_rule_thm (thm "rtc3.step") step9l);
val (([], pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck cr2 cr2b);

(* Get a fresh set of embeddings. *)
(*
val rtab = RRippleCInfo.add_relational_link rtab (Prf.get_ndname_ctrm pp cr2b) cr2b;
val rtab_s = RelationTab.to_string rtab;
val [(instenv11, embedding_11)] = Seq.list_of (RREmbeddingLib.embed rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_conc_l_new)) (Prf.get_ndname_ctrm pp cnc1));
val [(instenv12, embedding_12)] = Seq.list_of (RREmbeddingLib.embed rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_conc_r_new)) (Prf.get_ndname_ctrm pp cnc2));
val [(instenv13, embedding_13)] = Seq.list_of (RREmbeddingLib.embed rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_conc_r_new)) (Prf.get_ndname_ctrm pp cr2b));
*)
(* End embeddings. *)

val [cnc1_assm] = Prf.get_ndname_lasms pp cnc1;
val (([cnc2a], pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "conjE") cnc1_assm cnc1);
val [cnc2al, cnc2ar] = Prf.get_ndname_lasms pp cnc2a;

(* New embeddings. *)
(*
val rtab = RRippleCInfo.add_relational_link rtab (Prf.get_ndname_ctrm pp cnc2ar) cnc2ar;
val rtab_s = RelationTab.to_string rtab;
val [(instenv14, embedding_14)] = Seq.list_of (RREmbeddingLib.embed rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_conc_l_new)) (Prf.get_ndname_ctrm pp cnc2al));
val [(instenv15, embedding_15)] = Seq.list_of (RREmbeddingLib.embed rtab (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm pp IH_conc_r_new)) (Prf.get_ndname_ctrm pp cnc2ar));
*)
(* End embeddings. *)

(* val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck cnc2al cnc2a); *)
(* val [crassml, crassmr] = Prf.get_ndname_lasms pp crgoal1;
   val (([crl, crr], pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck CR_conc crgoal1);

val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck crassml crl);
val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck crassmr crr); *)

val (([cnc2b], pp)::L) = Seq.list_of (pp |> Prf.apply_erule_thm (thm "conjE") cnc1_assm cnc2);
val [cnc2bl, cnc2br] = Prf.get_ndname_lasms pp cnc2b;

raise ERROR "stop";

val (([], pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck cnc2br cnc2b);

val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck crh1 IH_conc_r_new);
val (([],pp)::L) = Seq.list_of (pp |> Prf.apply_resol_bck cnc1 cnc2a);

raise ERROR "stop";


(* val (g,pp) = Prf.end_meth "Backwards on the conclusions." [] [step7, crgoal1] pp premeth_p; *)
