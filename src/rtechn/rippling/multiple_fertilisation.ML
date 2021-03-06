functor MyBasicRippleRTechnFUN
          (structure RippleCInfo : BASIC_RIPPLE_CINFO
           structure ConjRTechn : CONJ_RTECHN)
(*         : BASIC_RIPPLE *)
= struct

(* prepare the skeleton, ie change object level "all's" and meta level
all's to schematic var representation. *)

(* IDEA: use records for autmatic type checking of results and for
passing back and taking information... this can capture state
transition requirements, such as needing explore to be true etc - this
would provide some compile-time code checking. *)

(* val prep_skeleton = Data.rulify o Drule.gen_all; *)
structure RippleCInfo = RippleCInfo;
local
  open RTechnEnv;
in

exception rippling_rtechn_exp of string;


(* Reasoning state pretty printing functions *)
val basecaseN =
    RstName.str "Solve the base case by simplification.";
val induct_and_rippleN =
    RstName.str "Solve using Induction and Rippling.";
val induct_and_ripple_with_ruleN =
    RstName.str "Solve using Induction (custom rule) and Rippling.";
val strong_fertN = RstName.str "Strong fertilisation";
val weak_fert_startN = RstName.str "Weak fertilisation";
val weak_fert_leftN = RstName.str "Weak fertilisation on left side of goal";
val weak_fert_rightN = RstName.str "Weak fertilisation on right side of goal";
fun start_ripplingN goal =
    RstName.chunks [RstName.str "Start Rippling with state: ",
                    (fn rst => RippleCInfo.pretty_skels rst goal)];
fun update_stepN dtac =
    RstName.f (fn rst => Pretty.chunks
                           [Pretty.block
                              [Pretty.str "Ripple Step by ",
                               DTac.pretty dtac (RState.get_ctxt rst)],
                            RippleCInfo.pretty_curgoals_skels rst]);
val solved_by_ripplingN =
    RstName.str "Rippling solves the goal directly";
val stepcase_by_ripplingN =
    RstName.str "Solve the step case using rippling.";


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Fertilisation                                                      *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Strong Fertilisation *)
fun strong_fert_goal goal rst =
    givename strong_fertN
             (orr_list (map (fn s => apply_res s goal)
                            (RippleCInfo.skeleton_names_of rst goal)))
             rst;

(* Weak Fertilisation by a single step of direct rewriting *)

fun is_eq_term t =
    is_some (Subst.move_to_concl_eq (Zipper.mktop t));


fun subst_in_lhs_until_fail skelnm goal rst =
    let
      val newseq = givename weak_fert_leftN (RTechnEnv.subst_in_lhs skelnm false goal) rst
      val no_more_ferts = (end_rst
                              (RstName.str ("end fertilisation on goal: " ^ goal))
                               rst |> RState.set_goalnames [goal] )
    in
      case Seq.pull newseq of
        NONE => Seq.single no_more_ferts
      | SOME _ => Seq.append (Seq.map (RState.set_rtechn
                                        (SOME (HTraceCInfo.thenify (map_then (subst_in_lhs_until_fail skelnm))))) newseq)
                             (Seq.single no_more_ferts)
    end ;


fun subst_in_rhs_until_fail skelnm goal rst =
    let
      val newseq = givename weak_fert_rightN (RTechnEnv.subst_in_rhs skelnm true goal) rst
      val no_more_ferts = (end_rst
                              (RstName.str ("end fertilisation on goal: " ^ goal))
                               rst |> RState.set_goalnames [goal] )
    in
      case Seq.pull newseq of
        NONE => Seq.single no_more_ferts
      | SOME _ => Seq.append (Seq.map (RState.set_rtechn
                                        (SOME (HTraceCInfo.thenify (map_then (subst_in_rhs_until_fail skelnm))))) newseq)
                             (Seq.single no_more_ferts)
    end;


fun subst_skel goal (skelnm,skel) rst =
    (if is_eq_term skel then
       let
         val gt = RstPP.goal_concl rst goal
         val z = Zipper.mktop gt
       in
         if is_eq_term gt then
           orr_list [subst_in_lhs_until_fail skelnm goal,
                     subst_in_rhs_until_fail skelnm goal]
         else
           (* try the skelequation both ways around *)
           orr_list [RTechnEnv.subst_eq skelnm false goal,
                     RTechnEnv.subst_eq skelnm true goal]
       end else fail) rst;


fun subst_skels goal skels = orr_list (map (subst_skel goal) skels);

(* FIXME: This is perhaps a bit hacky, but it had issues with
   returing reasoning states with no goalnames, or something otherwise.
   Also, maybe we don't always want to fertilise with all skels. *)
fun subst_skels2 goal [] rst = Seq.single (RState.set_goalnames [goal] rst)
  | subst_skels2 goal (skel1::skels) rst =
    (subst_skel goal skel1 rst)
      |> Seq.maps (fold_over_each_goal (fn g => subst_skels2 g skels));


fun weak_fert_skels_goal skels goal rst =
   subst_skels2 goal skels rst;

(*
fun nweak_fert_goal_skels skels goal rst =
  let val newseq = weak_fert_skels_goal skels goal rst
  in case Seq.pull newseq of
    NONE => Seq.single (RState.set_rtechn NONE rst)
  | SOME _ => Seq.map (RState.set_rtechn (SOME (map_then (nweak_fert_goal_skels skels)))) newseq
 end;
*)


fun weak_fert_goal goal rst =
   (refine weak_fert_startN
      (weak_fert_skels_goal (RippleCInfo.skeleton_namedterms_of rst goal) goal)) rst;

(*
val weak_fert_goal = weak_fert_twice_goal;
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Start Rippling                                                     *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* given an reasoning state which is being use to explore, then we can
setup rippling with the give skeleton terms and theorems. *)
fun startr_on_goal goal rst =
  let
    val skels = PPlan.get_varified_lasm_nctrms (RState.get_pplan rst) goal;
  in
    rst |> RState.set_rtechn NONE
        |> (givename (start_ripplingN goal)
                     (RippleCInfo.start skels ParamRGraph.empty goal))
  end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Rippling Steps                                                     *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* apply dtac and update the rippling state information *)
(* implicit arg: rst *)

fun filter_in_if_some_rippling_goal rst =
  let val gnames = RState.get_goalnames rst
      val ripple_gnames =
          filter (RippleCInfo.is_valid_ripple_state_goal rst) gnames
  in
    if null ripple_gnames then Seq.empty
    else Seq.single (RState.set_goalnames ripple_gnames rst)
  end;
(*
    if RippleCInfo.some_curgoal_is_ripple_valid rst
    then Seq.single rst
    else Seq.empty;
*)

fun make_ripple_goal_cinfos oldgoal newgoal rst =
  ((RState.set_goalnames [newgoal] rst)
     |> ((RippleCInfo.update oldgoal newgoal)
         try1_orelse
         (dummy_str "non-rippling-goal")
  ));

fun do_dtac_ripple_step dtac goal =
  givename (update_stepN dtac)
           ((apply_dtac_to_g dtac goal)
              thenfs
              (map_rstseqf (make_ripple_goal_cinfos goal))
              thenfs
              filter_in_if_some_rippling_goal
           );

(* do a valid ripple steps using the wave rules in the wave rule DB.
When we get to a state in which has no following state has a better
out measure, then we know rippling is blocked.  *)
fun rsteps_on_goal goal rst =
  let
    val possiblesL =
        (RippleCInfo.applicable_dtacseq_of rst goal)
          |> Seq.maps (fn dtac => ((do_dtac_ripple_step dtac goal)
                                    thenr (map_then rsteps_on_goal)) rst)
          |> Seq.list_of (* make sure we only evaluate the states once. *)
    val possibleSeq = Seq.of_list possiblesL
  in
    if RippleCInfo.blocked_chk rst goal possiblesL
    then
      Seq.cons (rst |> end_rst (RstName.str ("end rippling on goal: "
                                             ^ goal))
                    |> RState.set_goalnames [goal])
               possibleSeq
    else possibleSeq
  end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Simplify Base Case                                                 *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Simplify the base case *)
fun simplify_basecase g =
(*     givename basecaseN (DTacRTechn.simp_asm_full g);  *)
    givename basecaseN (DTacRTechn.simp_no_asm_simp_changes g);

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Induction and Rippling: no conjecturing                            *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
fun endr rst =
    rstif (null o RState.get_goalnames)
          (dummy solved_by_ripplingN)
          (split_then (RippleCInfo.success_chk rst)
                      (map_then strong_fert_goal)
                      ((map_then weak_fert_goal)
                         try1_then
                         ((map_then DTacRTechn.simp_noasm)
                            try1_orelse
                            (dummy (RstName.str "Step case stuck")))))
      rst;
fun ripple_stepcase goal rst =
    (refine stepcase_by_ripplingN
            ((startr_on_goal goal)
               thenr (rsteps_on_goal goal)
               thenr endr))
      rst;

fun induct_and_ripple g rst =
    (refine induct_and_rippleN
           (InductRTechn.induction_on_goal
              g
              (map_then simplify_basecase)
              (map_then ripple_stepcase)))
           rst;

fun induct_and_ripple_with_rule g rule rst =
    (refine induct_and_ripple_with_ruleN
           (InductRTechn.induction_on_goal_with
              g
              (ProofContext.get_thm (RState.get_ctxt rst) rule)
              (map_then simplify_basecase)
              (map_then ripple_stepcase)))
      rst;


end; (* RTechnEnv local *)
end; (* struct *)

structure MyRippleRTechn_flow = MyBasicRippleRTechnFUN(
  structure RippleCInfo = RippleCInfo_flow
  structure ConjRTechn = ConjRTechn);

structure MyRippleCaseSplit_flow = RippleCaseSplitRTechnFUN(
                            structure BasicRipple = MyRippleRTechn_flow);

structure MyRippling = RippleLemCalcFUN(
                          structure BasicRipple = MyRippleCaseSplit_flow);


(* Interface for rippling *)
fun my_rippling ctx goals =
    PPInterface.ipp_of_strings
      ctx (RTechnEnv.map_then MyRippling.induct_ripple_lemcalc) goals;

fun a_rippling_rst ctx goal =
    let
      val rsts_opt =
        PPInterface.init_rst_of_strings ctx [goal]
         |> RState.set_rtechn (SOME (RTechnEnv.map_then MyRippling.induct_ripple_lemcalc))
         |> GSearch.breadth_fs (fn rst => is_none (RState.get_rtechn rst)) RState.unfold
         |> Seq.filter RstPP.solved_all_chk
         |> Seq.pull;
       val rst_opt =
          case rsts_opt of
            NONE => RState.init @{context}
          | SOME (rst,altrsts) => rst
     in rst_opt end


(* Automatic rippling for one goal*)
fun a_rippling_one_goal ctx goal =
    let
      val prf_time = Unsynchronized.ref Time.zeroTime;
      val timer = Timer.startCPUTimer ()
      val rst_opt =
        PPInterface.init_rst_of_strings ctx [goal]
         |> RState.set_rtechn (SOME (RTechnEnv.map_then MyRippling.induct_ripple_lemcalc))
         |> GSearch.breadth_fs (fn rst => is_none (RState.get_rtechn rst)) RState.unfold
         |> Seq.filter RstPP.solved_all_chk
         |> Seq.pull;
      val _ = prf_time := !prf_time + (#usr (Timer.checkCPUTimer timer))

      val string_thrm_opt =
            case rst_opt of
              NONE => NONE
            | SOME (rst,altrsts) =>
              SOME ((*Pretty.str_of (PPlan.pretty (RState.get_pplan rst))*)
                  goal,
                  SynthPrfTools.name_thrm_from_rst "g1" rst)
      (* TODO: Extract relevant lemmas onece this has been fixed in IsaPlanner*)
        val lemmas = []
    in
      (string_thrm_opt, lemmas)
     (* (nw_thy, (prop_trm, rsts)) *)
      (*(nw_thy, (prop_trm, map (fn (thm, (gnm, rst)) => (thm,rst)) prfs)) *)
    end;


(* Type to annotate theorems depending on which of two proof strategies *)
datatype provedby = RippleWithMF of Thm.thm | Direct of Thm.thm


(* Timeout function for rippling *)
fun a_rippling_one_goal_timeout ctx goal =
    let
      val prf_time = Unsynchronized.ref Time.zeroTime;
      val timeout = Time.fromSeconds 10 (* 10 seconds per proof *)
      val ripple_res = Unsynchronized.ref NONE
      val timenow = Timer.startRealTimer();
      val nap = Time.fromReal 0.25;
      val ripple = Thread.fork (fn () =>
                                   ripple_res :=
                                  (SOME (a_rippling_one_goal ctx goal)), [])
      (* FIXME: even if ripping has timed out, we can still get the lemmas *)
      fun timeout_chk timer =
          if (Timer.checkRealTimer timer) >= timeout then
            let val _ = if (Thread.isActive ripple) then Thread.kill ripple else ()
                val _ = prf_time := !prf_time + timeout
            in (NONE, []) end

          else
            if (Thread.isActive ripple)
            then ((OS.Process.sleep nap); timeout_chk timer)
            else case !ripple_res
                  of NONE => (NONE, [])
                   | SOME (thm_opt, lemmas) =>
                     (thm_opt, lemmas)
    in
       timeout_chk timenow
    end;


(* Runs automatic rippling with timeout through the list, updating the context after each
 successful proof *)
fun one_step ctx [] openconjs = (ctx,openconjs)
  | one_step ctx (g::gs) openconjs =
    let
      val (thm_opt,lemmas) = a_rippling_one_goal_timeout ctx g
      val newctx_openconjs =
        case thm_opt
          of NONE => (ctx, g::openconjs)
           | SOME (by_str, thethm) => (SynthPrfTools.add_to_wrules thethm ctx, openconjs)
      val (newctx,newopenconjs) = newctx_openconjs
    in
      one_step newctx gs newopenconjs
    end;


(* Runs one_step many times, keeping the updated context *)
fun top_level ctx gs =
    let
      val (newctx,newgs) = one_step ctx gs []
    in
      if length gs = length newgs then newgs
      else top_level newctx newgs
    end;


(* Tries to one goal directly with a list of theorems *)
fun prove_directly_one ctx ann_thms goal =
    let
      fun annthms_to_thms [] thm_list = thm_list
        | annthms_to_thms ((_,x)::t) thm_list = annthms_to_thms t (x::thm_list)
      fun rule_thm_dtac1 th =
          DTac.mk (K (Pretty.str ("Resolution backward using thm " ^ (Thm.get_name_hint th))),
             GTacs.of_bckf (PPlan.apply_rule_thm th));
      fun prove_with_list_of_thms thms g =
          (RTechnEnv.orr_list (map (fn th => (RTechnEnv.apply_dtac (rule_thm_dtac1 th))) thms)) g
      val thms = annthms_to_thms ann_thms []
      val rtechn = prove_with_list_of_thms thms
      val rst_opt =
      PPInterface.init_rst_of_strings ctx [goal]
           |> RState.set_rtechn (SOME rtechn)
           |> GSearch.breadth_fs (fn rst => is_none (RState.get_rtechn rst)) RState.unfold
           |> Seq.filter RstPP.solved_all_chk
           |> Seq.pull;
      val string_thrm_opt =
          case rst_opt of
              NONE => NONE
            | SOME (rst,altrsts) =>
              SOME (goal, SynthPrfTools.name_thrm_from_rst "g1" rst)
    in
      string_thrm_opt
    end;


(* Tries to prove a list of goals with RIPPLING and DIRECTLY from a proven theorem. Returns a list
of new open conjectures and a list of annotated theorems *)
fun one_step_updt_ctx_end ctx provedconjs [] openconjs = (provedconjs,openconjs) (* when it has worked through the
                                                                      whole list it returns the
                                                                      updated context and the conjs
                                                                      that remain open*)
  | one_step_updt_ctx_end ctx provedconjs (g::gs) openconjs =
    let
      val ann_thm_opt =
          case prove_directly_one ctx provedconjs g
            of NONE => let val (x,_) = a_rippling_one_goal_timeout ctx g
                       in case x of
                          NONE => NONE
                        | SOME (_,thm_rmf) => SOME ("RipplingWithMF",thm_rmf)
                       end
             | SOME (_,thm_d) => SOME ("Directly",thm_d)
      val (newprovedconjs,newopenconjs) =  (* conjectures that weren't proved are added to the openconjs list and
                                the updated context list keeps up to date *)
        case ann_thm_opt
          of NONE => (provedconjs, g::openconjs)
           | SOME ann_thm => (ann_thm::provedconjs, openconjs)
    in
      one_step_updt_ctx_end ctx newprovedconjs gs newopenconjs (* if it hasn't gone through the whole list
                                                          it feeds itself the old and new contexts,
                                                          plus the rest of the goals and the updated
                                                          list of open conjs *)
    end;

(* Tries to prove a list of goals with RIPPLING from a proven theorem. Returns a list
of new open conjectures and a list of theorems *)
fun one_step_updt_ctx_end_jr ctx provedconjs [] openconjs = (provedconjs,openconjs) (* when it has worked through the
                                                                      whole list it returns the
                                                                      updated context and the conjs
                                                                      that remain open*)
  | one_step_updt_ctx_end_jr ctx provedconjs (g::gs) openconjs =
    let
      val ann_thm_opt =
          let val (x,_) = a_rippling_one_goal_timeout ctx g
               in case x of
                  NONE => NONE
                | SOME (_,thm_rmf) => SOME ("RipplingWithMF",thm_rmf)
               end
      val (newprovedconjs,newopenconjs) =  (* conjectures that weren't proved are added to the openconjs list and
                                the updated context list keeps up to date *)
        case ann_thm_opt
          of NONE => (provedconjs, g::openconjs)
           | SOME ann_thm => (ann_thm::provedconjs, openconjs)
    in
      one_step_updt_ctx_end_jr ctx newprovedconjs gs newopenconjs (* if it hasn't gone through the whole list
                                                          it feeds itself the old and new contexts,
                                                          plus the rest of the goals and the updated
                                                          list of open conjs *)
    end;

(*  Evaluation for a list of conjectures.
    Runs the list, updating the context at the end of every run.
    Returns three lists (open conjectures, proved by direct
    application of theorem, proved by rippling with multiple fertilisation) *)
fun top_level_updt_ctx_end ctx proved gs =
    let
      val (newproved, newgs) = one_step_updt_ctx_end ctx proved gs []
      fun add_ann_thms_to_ctx ctxt [] = ctxt
        | add_ann_thms_to_ctx ctxt (h::t) =
          let
            val (_,thm) = h
            val newctxt = SynthPrfTools.add_to_wrules thm ctxt
          in add_ann_thms_to_ctx newctxt t
          end;
      val newctx = add_ann_thms_to_ctx ctx newproved
    in
      if length gs = length newgs then (newgs,newproved)
      else top_level_updt_ctx_end newctx newproved newgs
    end;


(*  Evaluation for a list of conjectures.
    Runs the list, WITHOUT UPDATING THE CONTEXT.
    Returns three lists (open conjectures, proved by direct
    application of theorem, proved by rippling with multiple fertilisation) *)
fun top_level_no_updt_ctx ctx proved gs =
    let
      val (newproved, newgs) = one_step_updt_ctx_end ctx proved gs []
      val _ = TextIO.print("one cycle!")
    in
      if length gs = length newgs then (newgs,newproved)
      else top_level_no_updt_ctx ctx newproved newgs
    end;

