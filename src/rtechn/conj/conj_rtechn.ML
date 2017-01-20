(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  DESCRIPTION:
    Reasoning techniques for the managing of proving lemmas, including
    conjecturing and notions of subspace. Corresponds to lemma
    calculation.
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

val g_conj_rtechn_debug_flag = Unsynchronized.ref true;

val g_counter_examples_flag = Unsynchronized.ref false;

signature CONJ_RTECHN =
sig
  exception conj_exp of string

  type appinfo

  val prove_goal_by_lemma : (PPlan.gname -> RState.rtechn) -> PPlan.gname -> RState.rtechn
  val prove_goal_by_lemma_w_delays : (PPlan.gname -> RState.rtechn) -> PPlan.gname -> RState.rtechn

  val conj_from_gname : RState.T -> PPlan.gname ->
                       (appinfo * (Trm.TrmParams.T * Term.term)) Seq.seq
  val prove_as_lemma_techn :
      PPlan.gname -> (PPlan.gname -> RState.rtechn) -> appinfo * Term.term -> RState.rtechn

  (* calc lemmas for unsolved goals and prove them using given techn; if proved, apply lemma. *)
  val lemcalc_unsolved : (PPlan.gname -> RTechn.T) -> RTechn.T

  val conj_critic : (PPlan.gname -> RTechn.T) -> (PPlan.gname -> RTechn.T)
                    -> PPlan.gname -> RTechn.T

end;


structure ConjRTechn
 : CONJ_RTECHN
= struct
  exception conj_exp of string
  type appinfo = LemmaConjLib.appinfo
  local open RTechnEnv; in

  (* make conjectures from a goal *)
  fun conj_from_gname rst gname =
      let
        val ptab = Cx.get_fixed_trm_ps (RstPP.get_cx rst gname);
        val sgterm = RstPP.goal_concl rst gname;
      in LemmaConjLib.conjs (RState.get_pplan rst) ptab sgterm end;

  (* apply a conjectured lemma to the goal if was conjectured to solve *)
  fun apply_lemmathm appinfo conj_name_thm g rst =
      RTechnEnv.apply_dtac_to_g
        (RTechnEnv.rule_dthm_dtac
           (LemmaConjLib.mk_dthm (RstPP.get_ctxt rst) appinfo conj_name_thm))
        g rst;

  (* side effect is to record the proof in conj DB cinfo *)
  fun note_proved_lemma conjname rst =
      let
        val conj_thm = (* make the theorem to store in the lemma db *)
            (Prf.mk_thm (RState.get_pplan rst) conjname)
              |> fst
              |> Thm.forall_elim_vars 0;
        val (absolute_conjname, rst2) =
              Conjdb_CtxtInfo.insert_proved_rst
                conjname (conj_thm, (conjname, (RState.get_pplan rst))) rst
      in ((absolute_conjname,conj_thm), rst2) end;

  fun note_and_apply_proved_lemma provedQ appinfo conjname g rst =
      let
        val _ = (* for debugging print out lemmas we are thinking about *)
            if !g_conj_rtechn_debug_flag then
            Pretty.writeln
            (Pretty.block [Pretty.str "Proved: ",
                           Pretty.str conjname,
                           Pretty.str ""
                          ])
            else ()
        val _ = (provedQ := true); (* set flag, so other branches know it's proved *)
        val (conj_name_thm,rst2) = note_proved_lemma conjname rst (* adds to conj DB *)
      in apply_lemmathm appinfo conj_name_thm g rst2 end; (* applys the lemma *)

  fun note_failed_lemma t rst =
      let val _ = (* for debugging print out lemmas we are thinking about *)
              if !g_conj_rtechn_debug_flag then
                    Pretty.writeln
                    (Pretty.block [Pretty.str "Failed to prove: ",
                                   Trm.pretty (RstPP.get_ctxt rst) t,
                                   Pretty.str ""])
              else ()
      (* we have failed, so make a note not to try again *)
      in (Conjdb_CtxtInfo.insert_failed_rst t rst; Seq.empty) end;

  datatype search_status =
           SearchStatus_Proved
         | SearchStatus_False;

  fun cut_if_proved provedref rst =
      if !provedref
      then
        case RState.get_rtechn rst
         of NONE => rst
          | SOME _ => RState.set_rtechn (SOME RTechn.fail) rst
      else rst;


  (* the technique of proving a lemma *)
  fun prove_as_lemma_techn g gr (appinfo, t) rst =
      (* Check if the new lemma has a counter-examle *)
      if (is_some (CounterExCInfo.timed_quickcheck_term
                     (RstPP.get_ctxt rst)
                     (CounterExCInfo.default_codegen_params, [])
                     (Trm.change_vars_to_fresh_frees t)
                     (Time.fromSeconds 1)))
      then note_failed_lemma t rst
      else if ConjStackCInfo.subsume_chk_rst rst t
      then Seq.empty
      else
        let
          (* make the new conjecture *)
          val (conjname,rst2) =
            rst |> ConjStackCInfo.add_term_rst t
                |> RstPP.new_conj_at_top ("lem_{"^g^"}", t)

          val _ = (* for debugging print out lemmas we are thinking about *)
              if !g_conj_rtechn_debug_flag then
                Pretty.writeln
                  (Pretty.block [Pretty.str "Conjecturing: ",
                                 Pretty.str conjname,
                                 Pretty.str " : \"",
                                 Trm.pretty (RstPP.get_ctxt rst) t,
                                 Pretty.str "\"."
                  ])
              else ()
          val provedQ = Unsynchronized.ref false;
        in
          (refine
             (RstName.block
                [RstName.str ("Proving goal " ^ g ^ " by a new lemma (name: " ^ conjname ^ "): "),
                 RstName.term t])
             (RTechnEnv.allfail_critic
                (note_failed_lemma t)
                (RTechn.map (cut_if_proved provedQ)
                            ((gr conjname)
                               thenr
                               (note_and_apply_proved_lemma
                                  provedQ appinfo conjname g))))
          ) rst2
        end;

  (* prove goal "g" by conjecturing it, or a unifyable generalisation
  of it, as a lemma using technique "r" in "rst". *)
  fun prove_goal_by_lemma gr g rst =
      Seq.maps
        (fn (appinfo, (ptab2,t)) =>
              let
                val (prfs,status) = Conjdb_CtxtInfo.lookup_rst rst t
              in case status of
                   ConjecturedbLib.ConjStatus_false _ => Seq.empty
                 | ConjecturedbLib.ConjStatus_failed => Seq.empty
                 | ConjecturedbLib.ConjStatus_in_progress =>
                   (* FIXME: register as delayed proof *)
                   raise conj_exp "not re-implemented at the moment"
                   (* the lookup function may actually have found a proof *)
                 | ConjecturedbLib.ConjStatus_unknown =>
                   ((try1_orelse_list (* prfs is list of proofs that might work *)
                       (map (fn (n,(th,_)) => apply_lemmathm appinfo (n,th) g)
                            prfs))  (* try applying them *)
                      try1_orelse
                      (* if none of the lemmas prove it, conjecture and prove it as a new lemma *)
                      (prove_as_lemma_techn g gr (appinfo, t)))
                     rst
              end)
        (conj_from_gname rst g);


  (* IMPROVE: make the version that delays if the proof of the lemma
  is in progress in a different branch of the search space *)
  val prove_goal_by_lemma_w_delays = prove_goal_by_lemma;

local open RTechnEnv; in

(* try to solve calculate unproved subgoals by calculating a lemma,
then, using "lemmatechn", prove the lemma and finally apply the proved
lemma to solve goal. Do this to each unsolved goal of "gr". If no
unsolve goals, dummy state "Solved!" *)
  fun lemcalc_unsolved lemmatechn =
      (rstif RstPP.solved_focusgoals
             (dummy_str "Solved!")
             (map_then (prove_goal_by_lemma lemmatechn)));
  end;

(* as above, but as a critic of a technique that takes a single goal
name; allows integration with technique it's a critic of; avoids extra
map_thens *)
fun conj_critic lemmatechn gr gname =
    (gr gname)
      thenr
      (rstif RstPP.solved_focusgoals
             (dummy_str "Solved!")
             (map_then (prove_goal_by_lemma lemmatechn)));

end; (* local *)
end;
