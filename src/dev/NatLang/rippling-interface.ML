(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Top level functions for Rippling with Multiple Fert                *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure RippleMultfertRTechn_flow = RippleMultfertRTechnFUN(
  structure RippleCInfo = RippleCInfo_flow
  structure ConjRTechn = ConjRTechn);


structure RippleMultfertLemCalc = RippleMultfertLemCalcFUN(
                              structure RippleMultfert = RippleMultfertRTechn_flow);


fun ipp_rst rst =
    Print_Mode.setmp [] (fn () => PPInterface.explore PPInterface.depth_fs_debug rst) ();
    
fun ipp_of_strings ctxt r goals =
    (PPInterface.init_rst_of_strings ctxt goals)
      |> RState.set_rtechn (SOME r)
      |> ipp_rst;

(* Automatic rippling, with RState.T as output *)
fun a_rippling_rst ctx goal = 
    let
      val rsts_opt = 
        PPInterface.init_rst_of_strings ctx [goal]
         |> RState.set_rtechn (SOME (RTechnEnv.map_then RippleMultfertLemCalc.induct_ripple_multfert_lemcalc))
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
         |> RState.set_rtechn 
             (SOME (RTechnEnv.map_then RippleMultfertLemCalc.induct_ripple_multfert_lemcalc))
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
           |> GSearch.depth_fs (fn rst => is_none (RState.get_rtechn rst)) RState.unfold 
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
