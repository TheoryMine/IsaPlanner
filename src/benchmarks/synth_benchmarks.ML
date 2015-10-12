(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Code to run benchmarks for Synthesis.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

structure SynthBenchmarks =
struct

local structure Synthesis = ConstrSynthesis; in

(* Timers to add up time spent in each of synthesis, counter example
   checking and proving conjectures. *)
(*val synth_time = ref Time.zeroTime;
val prf_time = ref Time.zeroTime;
val counterex_time = ref Time.zeroTime;
*)
fun reset_timers() = 
    let val _ = Synthesis.synth_time := Time.zeroTime
        val _ = Synthesis.upd_constr_time := Time.zeroTime
        val _ = Synthesis.subsumpt_time := Time.zeroTime    
        val _ = SynthPrfTools.prf_time := Time.zeroTime
    in SynthPrfTools.counterex_time := Time.zeroTime end

fun prfs_to_str rsts =
    foldr (fn (rst, str) => 
              (RState.get_pplan rst)
                |> PPlan.pretty
                |> Pretty.string_of
                |> (fn s => s^"\n"^str)) "" rsts;
fun terms_to_str ctxt trms =
    foldr (fn (trm, str) =>
              (Trm.pretty ctxt trm)
                |> Pretty.string_of
                |> (fn s => s^"\n"^str)) "" trms;

fun stats_to_str (size, stats) =
    "Size "^(Int.toString size)^":\n"
    ^ "Theorems: "^(Int.toString (#theorems stats))^", "
    ^ "Conjectures: "^(Int.toString (#conjs stats))^"\n"
    ^ "False Conjs: "^(Int.toString (#false_conjs stats))^", "
    ^ "Subsumed: "^(Int.toString (#subsumed stats))^"\n"
    ^ "Synthesis time: "^(Time.toString (#synth_time stats))^", "
    ^ "Proof time: "^(Time.toString (#prf_time stats))^", "
    ^ "Counter example time: "^(Time.toString (#counterex_time stats))^"\n"
    ^ "Constraint update time: " ^(Time.toString (#update_time stats))^", "
    ^ "Subsumption checking time: "^(Time.toString (#subs_time stats))^"\n"
    ^ "Total time: "^ Time.toString ((#synth_time stats) + (#counterex_time stats)
                                     + (#update_time stats) + (#subs_time stats)
                                     + (#prf_time stats))
    ^ "\n";

fun result_string (thy, cinfo) (max_size, max_vars) (conjs, thrms) false_conjs tot_time =
    let 
      val ctxt = ProofContext.init thy
      val (ac_things, comm_thms) =  
          (map (fn (nm, cinfo) => 
                   if ((Constraints.Constant.dest nm) = "HOL.eq")
                   then ([], []) (* Exclude = as these thms are built in *)
                   else
                     let 
                       val assoc = Constraints.get_assoc_opt cinfo
                       val comm = Constraints.get_commute_opt cinfo
                       val com_defs = Constraints.get_commuted_defs cinfo
                     in 
                       ((map_filter I [assoc, comm]), com_defs)
                     end) 
               (Constraints.Constant.NTab.list_of cinfo))
            |> (fn thms => (flat (map fst thms), flat (map snd thms)))
      val line = "-----------------------\n"
    in
      "Theorems found:\n"
      ^ line 
      ^ (terms_to_str ctxt (map fst thrms))^"\n \n"
      ^ "AC-theorems found:\n"
      ^ line
      ^ (terms_to_str ctxt ac_things)^"\n \n"
      ^ "Commuted versions of defs:\n"
      ^ line
      ^ (terms_to_str ctxt comm_thms)^"\n \n"
      ^ "Conjectures found (not proved):\n"
      ^ line
      ^ (terms_to_str ctxt (map fst conjs))^"\n \n"
      ^ line
      ^ "Statistics for each size iteration:\n"
      ^ (foldl (fn ((i, stats), str) => 
                   (stats_to_str (i, stats))^"\n"^str)
               "" (!Synthesis.size_stats))
      ^ line
      ^ "Total number of false conjectures: "^(Int.toString false_conjs)^"\n"
      ^ "Time spent in synthesis: "^(Time.toString (!Synthesis.synth_time))
      ^ "\nTime spent updating constraints: "^(Time.toString (!Synthesis.upd_constr_time))
      ^ "\nTime spent subsumption checking: "^(Time.toString (!Synthesis.subsumpt_time)) 
      ^ "\nTime spent counter-example checking: "^(Time.toString (!SynthPrfTools.counterex_time))
      ^ "\nTime spent on proofs: "^(Time.toString (!SynthPrfTools.prf_time))
      ^"\nTotal time: "^(Time.toString tot_time)^"\n"
      ^ line
      ^ "\n \n \nProofs of theorems:\n"
      ^ line
      ^ (prfs_to_str (maps snd thrms))
    end;

fun partial_result_string (max_size, max_vars) thy = 
    let 
      val thrms = (StrNTab.list_of (!SynthPrfTools.thm_nm_tab))
                    |> map snd
                    |> map Thm.concl_of
      val conjs = (StrNTab.list_of (!Synthesis.conj_tab))
                    |> map snd

      val line = "-----------------------\n"
    in
      "Theorems found:\n"
      ^ line 
      ^ (terms_to_str (ProofContext.init thy) thrms)^"\n \n"
      ^ "Conjectures found (not proved):\n"
      ^ line
      ^ (terms_to_str (ProofContext.init thy) conjs)^"\n \n"
      ^ "Statistics for each size iteration up to exception:\n"
      ^ (foldl (fn ((i, stats), str) => 
                   (stats_to_str (i, stats))^"\n"^str)
               "" (!Synthesis.size_stats))
      ^ line
      ^ "Time spent in synthesis: "^(Time.toString (!Synthesis.synth_time))
      ^ "\nTime spent updating constraints: "^(Time.toString (!Synthesis.upd_constr_time))
      ^ "\nTime spent subsumption checking: "^(Time.toString (!Synthesis.subsumpt_time)) 
      ^ "\nTime spent counter-example checking: "^(Time.toString (!SynthPrfTools.counterex_time))
      ^ "\nTime spent on proofs: "^(Time.toString (!SynthPrfTools.prf_time))
      ^"\n"
      ^ line
    end;

fun result_loc thynm synth_opts (max_size, max_vars) =
    let 
      val path = "./benchmarks/synth_res/"^thynm^"/"
    in path ^thynm^"_"^synth_opts^"_"^(Int.toString max_size)^"_"^
       (Int.toString max_vars)^".txt"
    end;

fun write_result (cinfo, thy) (thy_nm, synth_opts) (max_size, max_vars) 
                 (conjs, thrms) false_conjs tot_time = 
    let 
      val outs = TextIO.openAppend(result_loc thy_nm synth_opts (max_size, max_vars)) 
    in 
      (TextIO.output (outs, result_string (thy, cinfo) (max_size, max_vars) 
                                          (conjs, thrms) false_conjs tot_time);
       TextIO.closeOut outs)
    end;

fun write_exception exp_str (min_size, max_size) max_vars thy (thy_nm, synth_opts) =
    let 
      val outs = TextIO.openAppend(result_loc thy_nm synth_opts (max_size, max_vars)) 
    in 
      (TextIO.output (outs, exp_str^" raised during synthesis! Writing partial results.\n" 
                            ^ (partial_result_string (max_size, max_vars) thy));
       TextIO.closeOut outs)
    end ;

(* Create directory to put results in then return true if we have
written the file, false if someone else has already started it. *) 
fun start_write_file thynm synth_opt_str (max_size, max_vars) =
    let
      fun safe_isDir s = 
          (OS.FileSys.isDir s) handle OS.SysErr _ => false;
      fun safe_mkDir s = 
          (if safe_isDir s then () else 
           OS.FileSys.mkDir s) handle OS.SysErr _ => ();
      val res_path = "./benchmarks/synth_res/"
      val thy_path = "./benchmarks/synth_res/"^thynm^"/"  
      val loc = thy_path ^thynm^"_"^synth_opt_str^"_"^(Int.toString max_size)^"_"^
       (Int.toString max_vars)^".txt";
      val _ = (safe_mkDir res_path; 
               safe_mkDir thy_path)
    in
      ((OS.FileSys.fileId loc; false) handle 
       OS.SysErr _ => (let val outs = TextIO.openOut loc in 
                         TextIO.output (outs,"Synthesis results for theory "^thynm^
                                             ", with maximum term-size "^
                                             (Int.toString max_size)^" and "^ 
                                             (Int.toString max_vars)^
                                             " different variables allowed. \n \n");
                       TextIO.closeOut outs; true end))
    end;


fun bmarks_of_thy_ac (min_size, max_size) max_vars thy = 
    let 
      val thy_nm = NameSpace.path_of (Sign.naming_of thy)
      val synth_opt_str = "ac"
    in
      if (start_write_file thy_nm synth_opt_str (max_size, max_vars)) 
      then
        let 
          val _ = reset_timers()
          val _ = SynthPrfTools.reset_thm_nm_tab ()
          val _ = Synthesis.reset_conj_tab ()
          val tot_timer = Timer.startCPUTimer () 
          val (cinfo, thy') = Constraints.mk_const_infos_ac thy
          val ((cinfo_tab2, thy2), (conjs, thrms)) =  
              Synthesis.synthesise_eq_terms (min_size, max_size) 
                                            max_vars thy' cinfo 
          val tot_time = (#usr (Timer.checkCPUTimer tot_timer))
        in
          write_result (cinfo_tab2, thy2) (thy_nm, synth_opt_str) 
                       (max_size, max_vars) (conjs, thrms) 
                       (!Synthesis.counter_ex_counter) tot_time
        end
      else () 
           
    end
    handle Interrupt => write_exception "Exception Interrupt (memory issue)" 
                                        (min_size, max_size) 
                                        max_vars thy
                                        (NameSpace.path_of (Sign.naming_of thy),"ac")
    handle _ => write_exception "Other exception (bug?)"
                                (min_size, max_size) 
                                max_vars thy
                                (NameSpace.path_of (Sign.naming_of thy),"ac");
(*
fun bmarks_of_thy_no_ac (min_size,max_size) max_vars thy = 
    let 
      val val _ = reset_timers()
    in
      bmarks_of_thy (min_size,max_size) max_vars 
                    (NameSpace.path_of (Sign.naming_of thy), "no_ac") 
                    (Constraints.mk_const_infos_no_ac thy, thy)
    end;
*)

end(* local *)
end
