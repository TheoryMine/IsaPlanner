(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_techn.ML
    Author:     Dominic Mulligan, University of Edinburgh
                dpm_edinburgh@yahoo.com
    Created:    17th August, 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Relational rippling reasoning technique.  Based on the rippling
    reasoning technique maintained and written by Lucas Dixon and
    Moa Johansson.
    We disregard all critics and focus on implementation of the core
    heuristic.  Note: induction rule must be supplied by user.

*) 
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RRIPPLE_TECHN =
sig
    type fwdprf;
    val apply_induction : string -> RTechn.T;
    val lift_ih_into_ctxt : string -> string -> RState.T -> RState.T;
    val lift_ihs_of_goal : string -> RTechn.T;
    (* val lift_ihs : fwdprf -> RTechn.T; *)
    val lift_ihs : RTechn.T;
    val link_rels : string -> fwdprf -> RState.T -> (Term.term * PPlan.gname) list;
    val startr : Context.theory -> string -> fwdprf -> RTechn.T;
    val resol_fwd_multi : PPlan.gname -> (PPlan.gname * PPlan.gname) list ->
                          PPlan.gname -> DB_Prf.T -> (DB_Prf.gname * (DB_Prf.gname list * (DB_Prf.gname list * DB_Prf.T))) Seq.seq
    (* val resolve_assms : fwdprf -> RTechn.T; *)
    val resolve_assms : RTechn.T;
    val init_fwdprf : RState.T -> fwdprf;
    val update_fwdprf : fwdprf -> RState.T -> fwdprf;
    val induct_and_ripple : string -> RTechn.T;
end;

(* An explanation of the ordering of operations, so I don't get       *)
(* bamboozled:                                                        *)
(* (1) - Apply induction to goal.                                     *)
(* (2) - Lift the inductive hypothesis above the goal.  This allows   *)
(*       an initial embedding (this step isn't necessary in Isabelle  *)
(*       proof, c.f. IsaPlanner's handling of names in IH).           *)
(* (3) - Split conclusion of lifted IH by reasoning forward, then get *)
(*       embedding from this and facts.                               *)
(* (4) - Perform rewriting forward on facts.                          *)

functor RRippleTechnFUN (structure RRippleCInfo : RRIPPLE_CINFO) (* : RRIPPLE_TECHN *) =
struct
  local
        open RTechnEnv
    in
    
    type fwdprf = PPlan.gname list

      fun apply_induction goal rst =
          givename (RstName.str ("Applying induction to goal '" ^ goal ^ "'"))
                   (InductRTechn.just_induction_on_goal goal) rst;

      fun lift_ih_into_ctxt ih sc rst =
          let
              val ((gname, gnames), pp) = Prf.lift_and_show_above ih [] sc (RState.get_pplan rst)
              val rst' = RState.set_pplan pp rst
              val rst'' = RState.set_goalnames (gname::gnames) rst'
          in
              rst''
          end

      fun lift_ihs_of_goal goal rst =
          let
              val ih = IndPrf.get_ndname_indhyps (RState.get_pplan rst) goal
              val x = map (fn x => lift_ih_into_ctxt x goal rst) ih
          in
              Seq.of_list x
          end

(*
      fun lift_ihs fwd_prf rst =
        (apply_to_goals fwd_prf (map_then lift_ihs_of_goal)) rst
*)

      fun term_contains_indvar_assm indvar gname rst =
          let
              val trm = RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ltrm (RState.get_pplan rst) gname)
              val df = Term.term_frees trm
          in
              exists (fn x => case x of Free(x, z) => x=indvar | _ => false) df
          end

      fun term_contains_indvar_goal indvar gname rst =
          let
              val trm = RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm (RState.get_pplan rst) gname)
              val df = Term.term_frees trm
          in
              exists (fn x => case x of Free(x, z) => x=indvar | _ => false) df
          end

      fun link_rels indvar fwd_prf rst =
          let
              val ppl = RState.get_pplan rst
              val scs = filter (IndPrf.goal_is_stepcase ppl) fwd_prf
              val non_indhyps = maps (IndPrf.get_ndname_non_indhyps ppl) scs
              val non_indvar_hyps = filter (fn x => not (term_contains_indvar_assm indvar x rst)) non_indhyps
              val non_ivh_trms = map (fn x => (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ltrm ppl x), x)) non_indvar_hyps
              val non_scs = filter (not o (fn x => IndPrf.goal_is_stepcase ppl x)) fwd_prf
              val assms = maps (Prf.get_ndname_lasms ppl) non_scs
              val non_indvar_assms = filter (fn x => not (term_contains_indvar_goal indvar x rst)) assms
              val non_iva_trms = map (fn x => (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ctrm ppl x), x)) non_indvar_assms
          in
              distinct (op =) (non_iva_trms @ non_ivh_trms)
          end

      fun get_givens rst =
          let
              val ppl = RState.get_pplan rst
          in
              maps (Prf.get_ndname_lasms ppl) (IndPrf.get_open_non_stepcases ppl)
          end

      fun get_goals rst =
        let
          val ppl = RState.get_pplan rst
        in
          filter (fn x => not (IndPrf.assm_is_indhyp ppl x))
            (maps (Prf.get_ndname_lasms ppl) (IndPrf.get_open_stepcases ppl))
        end

      fun startr ctxt indvar fwd_prf rst =
          let
              val lrels = link_rels indvar fwd_prf rst
              val ppl = RState.get_pplan rst
              val instenv = InstEnv.init ctxt
              val givens = maps (Prf.get_ndname_lasms ppl) (filter (not o (fn x => IndPrf.goal_is_stepcase ppl x)) fwd_prf)
              val goals = filter (not o (fn x => IndPrf.assm_is_indhyp ppl x))
                                 (maps (Prf.get_ndname_lasms ppl) (filter (IndPrf.goal_is_stepcase ppl) fwd_prf))
              val gmis = map (fn x =>
                                 let
                                     val trm = (RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ltrm ppl x))
                                 in
                                     (RRTrmUtil.combinator_name trm, ModalityInfo.goal_mode_info_i ModalityInfo.empty (RRTrmUtil.num_args trm))
                                 end) goals
              val rtab = RRippleLinkInfo.add_relational_links RelationTab.empty lrels
              val skels = map (fn (x, y) => (x, RRTrmUtil.drop_meta_var_args y)) (map (fn x => (x, Prf.get_ndname_varified_ltrm ppl x)) givens);
          in
              RRippleCInfo.start gmis rtab instenv skels true fwd_prf rst
          end

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
          end

      fun resol_fwd_multi abovegname L cname pp = 
          let
              val pp2 = Prf.start_meth [] pp
              val (new_cname, ppseq) = resol_fwd_multi_i abovegname L cname pp2
          in 
              Seq.map (fn (goals,pp3) => (new_cname,(goals,Prf.end_meth "res_fwd_multi" [new_cname] [] pp3 pp))) ppseq
          end

(*      fun resolve_assms fwd_prf rst =
        let
          val ppl = RState.get_pplan rst
          val ctxts = filter (not o (fn x => IndPrf.goal_is_stepcase ppl x)) fwd_prf
          val abv = filter (IndPrf.goal_is_stepcase ppl) fwd_prf
          val ax = maps (Prf.get_ndname_lasms ppl) ctxts
          val bx = filter (not o (fn x => IndPrf.assm_is_indhyp ppl x)) (maps (Prf.get_ndname_lasms ppl) abv)
          val pairs1 = bx ~~ ax
          val pairs2 = abv ~~ ctxts
    val how_to_apply = (maps (fn (x,y) => map (fn z => (y, z, x)) pairs1) pairs2);
          val res = Seq.map (fn (a, (b, (c, d))) => RState.init_from_pp d)
                      (Seq.maps (fn (x, y, z) => resol_fwd_multi x [y] z ppl) (Seq.of_list (how_to_apply)))
          val _ = writeln "in resolve assm"
        in
          res
        end *)

      exception foo_exp of string;

      fun resolve_assms rst =
          let
              val _ = raise foo_exp "in resolve_assms"
              val ppl = RState.get_pplan rst
              val gnames = RState.get_goalnames rst
              val ctxts = filter (not o (fn x => IndPrf.goal_is_stepcase ppl x)) gnames
              val abv = filter (IndPrf.goal_is_stepcase ppl) gnames
              val ax = maps (Prf.get_ndname_lasms ppl) ctxts
              val bx = filter (not o (fn x => IndPrf.assm_is_indhyp ppl x)) (maps (Prf.get_ndname_lasms ppl) abv)
              val pairs1 = bx ~~ ax
              val pairs2 = abv ~~ ctxts
              val how_to_apply = (maps (fn (x,y) => map (fn z => (y, z, x)) pairs1) pairs2);
              val res = Seq.map (fn (a, (b, (c, d))) => RState.init_from_pp d)
                                (Seq.maps (fn (x, y, z) => resol_fwd_multi x [y] z ppl) (Seq.of_list (how_to_apply)))
          in
              res
          end

        fun apply_to_goals gnames rtech =
            rtech o RState.set_goalnames gnames;

        fun init_fwdprf rst =
            IndPrf.get_open_stepcases (RState.get_pplan rst)

        fun update_fwdprf fp rst =
            let
                val scs = RState.get_goalnames rst
            in
                fp @ scs
            end

        val simplify_basecase =
            let
                val simplifyN = RstName.str "Simplifying base case."
            in
                givename simplifyN (try_map_then DTacRTechn.simp_no_asm_simp_changes)
            end

        fun lift_ihs rst =
            let
                val liftN = RstName.str "Lifting inductive hypotheses."
                val _ = writeln "in lift_ihs"
            in
                givename liftN (try_map_then lift_ihs_of_goal) rst
            end

        fun resolve fwdprf rst =
            let
                val resolveN = RstName.str "Resolving goals."
                val _ = writeln "in resolve"
                val _ = map writeln fwdprf
            in
                (givename resolveN resolve_assms)
                    (RState.set_goalnames fwdprf rst)
            (* apply_to_goals fwdprf resolve_assms *)
            end

        fun rewrite_left fwdprf rst =
            let
                val rewriteN = RstName.str "Rewriting."
                val ppl = RState.get_pplan rst
                val ctxts = filter (fn x => IndPrf.goal_is_stepcase ppl x) fwdprf
                val ax = filter (not o (fn x => IndPrf.assm_is_indhyp ppl x)) (maps (Prf.get_ndname_lasms ppl) ctxts)
                val rst = RState.set_goalnames ax rst
                          
                fun rewrite_left_goal goal rst =
                    apply_or_dtacs_to_g (RRippleCInfo.applicable_dtacs_of rst goal) goal rst |>
                                        Seq.maps (fn (dt, rst) => Seq.single rst) (* update code in here *)
            in
                givename rewriteN (map_then rewrite_left_goal) rst
            end

        fun start_rippling fwdprf indvar rst =
            let
                val startN = RstName.str "Starting rippling."
            in
                rst |> RState.set_rtechn NONE |>
                    givename startN (startr (the_context ()) indvar fwdprf)
            end

        (* Lift IH's not right: returns empty sequence??? *)
        fun ripple_left fwdprf indvar rst =
            let
                val ripple_leftN = RstName.str "Rippling left hand side."
            in
                (lift_ihs thenr (resolve fwdprf) thenr (start_rippling fwdprf indvar) thenr (rewrite_left fwdprf)) rst
            end

        fun ripple_stepcase rst =
            (* strange behaviour with open gnames : if I record necessary gnames *)
            (* in a list for forward rewriting, all the steps collapse down into *)
            (* a single step - FIX THIS!                                         *)
            ripple_left ["ak", "aq"] rst

        fun induct_and_ripple indvar =
            try_map_then (fn x => InductRTechn.induction_on_goal x simplify_basecase (ripple_stepcase indvar))

(*
        (* This desperately needs changing! *)
        fun induct_and_ripple ctxt indvar rst =
          let
            (* after induction, ripple right hand side of any implications *)
            val induct = ((map_then apply_induction) rst)
            val fwd_prf = Seq.map init_fwdprf induct
            val pairs = (Seq.list_of fwd_prf) ~~ (Seq.list_of induct)
            val lift = map (fn (x, y) => lift_ihs x y) pairs
            val lifted = foldr (uncurry Seq.append) Seq.empty lift
            val pairs = (Seq.list_of fwd_prf) ~~ (Seq.list_of lifted)
            val fwd_prf = map (fn (x, y) => update_fwdprf x y) pairs
      val pairs = fwd_prf ~~ (Seq.list_of lifted)
            val resolve = map (fn (x, y) => resolve_assms x y) pairs
      val resolved = foldr (uncurry Seq.append) Seq.empty resolve
          in
            ((fn x => resolved) thenr (startr ctxt indvar fwd_prf)) rst
          end
*)
    end
  end
