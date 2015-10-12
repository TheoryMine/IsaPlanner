(* Functions for proving synthesised conjecures. *)

structure SynthPrfTools =
struct



val thm_nm_tab = Unsynchronized.ref StrNTab.empty;
fun reset_thm_nm_tab () = thm_nm_tab := StrNTab.empty;

(* The time spent in proofs and counter examples *)
val prf_time = Unsynchronized.ref Time.zeroTime;
val counterex_time = Unsynchronized.ref Time.zeroTime;

(* ---------------------------------------------------------*)
(* --------------- Counter-example checking --------------- *)
(* ---------------------------------------------------------*)

(* Quickcheck parameters *)
(* CHECK: is this still needed? Quickcheck has undergone many updates... maybe need to 
   rewrite/experiment with new version of quickcheck *)
val quickcheck_params = SOME (Type("Int.int", []));

(* Counter-example checking *)
fun counter_ex_check ctxt trm =
    let 
      (* Change any Type-Variables to Frees *)
      val trm1 = Trm.change_vars_to_fresh_frees trm (*Type.legacy_freeze trm *)
    in 
      case (CounterExCInfo.quickcheck_term ctxt (quickcheck_params, []) trm1) of
        NONE => SOME trm | SOME cex => NONE
    end
    handle ERROR _ => SOME trm;

(* Counter-example checking with a counter that counts non-theorems *)
fun counter_ex_check_count  counter_ex_counter_ref ctxt trm0 =
    let 
      (* Change any Type-Variables to Frees *)
      val trm = Trm.change_vars_to_fresh_frees trm0 (*Type.legacy_freeze trm0 *)
      (* val _ = Trm.print ctxt trm *)
    in 
      case (CounterExCInfo.quickcheck_term ctxt (quickcheck_params, []) trm) of
      NONE => SOME trm0
      | SOME cex => 
        let val _ = counter_ex_counter_ref := (!counter_ex_counter_ref) +1 
        in NONE end
    end
    handle ERROR _ => SOME trm0;

fun timed_counter_ex_chk counter_ex_counter_ref ctxt trm0 =
    let 
      val timer = Timer.startCPUTimer ()
      val counter_ex = counter_ex_check_count counter_ex_counter_ref ctxt trm0
      val _ = counterex_time := !counterex_time + (#usr (Timer.checkCPUTimer timer))
    in counter_ex end;


(* ---------------------------------------------------------*)
(* ------------ Post-processing after proof --------------- *)
(* ---------------------------------------------------------*)

fun poss_add_Trueprop t = 
          let val _ = HOLogic.dest_Trueprop t in t end
          handle Term.TERM _ =>  HOLogic.mk_Trueprop t


(* Also add to lemmas proved, as these may crop up there too *)
fun add_to_wrules thm ctxt =
    let             
      (* Insert into lemma database *)
      (* Question: Why do we need this? Added to wrules already. *)
    (*  val (lem_gnm, rst') = 
          Conjdb_CtxtInfo.insert_proved_rst thm_nm 
                                        (conj_thm, 
                                         (gname, RState.get_pplan rst)) rst *)
      (* Insert into wave-rule database *)
      val (Context.Proof ctxt') = WRulesGCtxt.add_wrule_thm thm (Context.Proof ctxt)
    in ctxt'
      (* (nw_thy, (conj_thm, (gname, rst'))) *)
    end;

(* ---------------------------------------------------------*)
(* ---------- Prove things in IsaPlanner -------------------*)
(* ---------------------------------------------------------*)

(* Returns a names theorem of the given goalname, assumed to occur
in the rst *)
fun name_thrm_from_rst gname rst =
    let
      val (thm_nm, thm_tab) = StrNTab.new_name "synth_thm_a" 
                                               (!thm_nm_tab)  
      val conj_thm = RstPP.goal_thm rst gname
  (* Insert in theorem name-table (gives each therorem unique names) *)
      val _ = thm_nm_tab := StrNTab.update (thm_nm, conj_thm) thm_tab
    in    
      (Prf.mk_thm (RState.get_pplan rst) gname)
        |> fst
        |> Thm.forall_elim_vars 0
        |> Thm.put_name_hint thm_nm
    end;

(* start a new proof planning attempt on a synthesised conjecture. *)
fun just_ripple_conjecture ctxt prop_conj_term = 
    let
      (* Only need one proof *)
      fun cut_if_proved provedref rst = 
          if !provedref then RState.set_rtechn (SOME RTechn.fail) rst
          else rst
                            
      val rippling = RippleLemCalc.induct_ripple_lemcalc                     
      val (init_goal,pp) =  
          PPlan.conj_term_at_top ("g", prop_conj_term) (PPlan.init ctxt)
      val provedQ = Unsynchronized.ref false
      val rtechn = 
          RTechnEnv.thenf 
            ((RTechn.map (cut_if_proved provedQ) 
                         (rippling init_goal)), 
             (fn rst => let val _ = provedQ := true
                        in rst end))

      (* Timer for how long the proof takes *)
      val timer = Timer.startCPUTimer ()
      val rsts = 
          (RState.init_from_pp pp)
            |> RState.set_goalnames [init_goal]
            |> RState.set_rtechn (SOME rtechn)
            |> PPInterface.depth_fs
            |> Seq.filter RstPP.solved_all_chk
            |> Seq.list_of
      val _ = prf_time := !prf_time + (#usr (Timer.checkCPUTimer timer))

      val thrm_opt = 
          case rsts of 
            [] => NONE
          | (rst::alt_prfs) =>
            SOME ((*Pretty.str_of (PPlan.pretty (RState.get_pplan rst))*)
                "by rippling",
                name_thrm_from_rst init_goal rst)
    (* TODO: Extract relevant lemmas onece this has been fixed in IsaPlanner*)
      val lemmas = []  
    in
      (thrm_opt, lemmas)
     (* (nw_thy, (prop_trm, rsts)) *)
      (*(nw_thy, (prop_trm, map (fn (thm, (gnm, rst)) => (thm,rst)) prfs)) *)
    end;

(* If the conjecture is proved, immediately add as wave-rule *)
(*fun ripple_conj_add_wrules thy conj_term = 
    let
      val (thy2, conj, thm_opt, lemmas) = just_ripple_conjecture thy conj_term
      val nw_thy = case thm_opt of 
                     NONE => thy2
                   | SOME (prf_str,thm) => add_to_wrules thy2 thm
    in
      (nw_thy, (conj, thm_opt, lemmas))
    end;
*)

(* For automated testing. Makes sure rippling can't go on foreverby imposing timeout limit
   Returns a new theory and the conjecture term + a list of proofs (if any).  *)
(* FIXME! use Isabelle's Timeout.timout command, much simpler! and avoid evil Unsynchronized.references *)
fun ripple_timeout ctxt conj_term =
    let 
      val timeout = Time.fromSeconds 5 (* 5 seconds per proof *)
      val ripple_res = Unsynchronized.ref NONE 
      val timenow = Timer.startRealTimer();
      val nap = Time.fromReal 0.25;
      val ripple = Thread.fork (fn () => 
                                   ripple_res := 
                                   (SOME (just_ripple_conjecture ctxt conj_term)), [])
      (* FIXME: even if ripping has timed out, we can still get the lemmas *)
      fun timeout_chk timer = 
          if (Timer.checkRealTimer timer) >= timeout then 
            let val _ = Thread.kill ripple
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

(* Find a substitution with an existing theorem that results in a generalisation
   of the conjecture, then prove generalisation. *)
(*fun subst_gen_prove thy synth_thm_db conj_term =
    let 
      let  
        val prop_trm = poss_add_Trueprop (Type.freeze conj_term)
        val (init_goal,pp) =  
            PPlan.conj_term_at_top ("g", prop_trm) 
                                   (PPlan.init_from_thry thy)
        val init_rst = RState.init_from_pp nw_ppl
        val substs = Seq.list_of (WRules.eqrule_zipper_lookup 
                                               synth_thm_db pp init_goal (Zipper.mktop prop_t))

        val rsts = RTechnEnv.apply_or_dtacs_to_g subst_dtacs init_goal init_rst
*)

(* A technique for trying to prove theorems that need a generalisation,
   eg. rev l = qrev l [] given we have synthesised rev l @ m = qrev l m *)
fun subst_and_simp ctxt prop_trm gen_thm =
    let  
      val (init_goal,pp) =  
          PPlan.conj_term_at_top ("g", prop_trm) (PPlan.init ctxt)
    in
      Seq.maps (fn ((nw_g, all_gs), nw_ppl) =>
                   (RState.init_from_pp nw_ppl)
                     |> RState.set_goalnames all_gs
                     |> DTacRTechn.multi_simp_no_asm_simp_changes)
          (Subst.apply_thm gen_thm true init_goal pp)
    end;


end;
