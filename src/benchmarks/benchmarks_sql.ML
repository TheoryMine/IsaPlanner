(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./benchmarks.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Code to create and run benchmarks for IsaPlanner.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 


structure IsaPBenchmarksSql
= struct

type searchf = RState.T -> RState.T Seq.seq

datatype problem = 
         Problem of {theory : Context.theory, 
                     name : string, 
                     conjterm : Thm.cterm};

(* Reference variable to check if speculation has been applied *)
val spec_applied = ref false;
fun get_reset_spec _ = 
    let 
      val spec = !spec_applied
      val _ = spec_applied := false
    in
      if spec then "1" else "0"
    end;


fun name_of_problem (Problem rep) = #name rep;
val name_of_theory = NameSpace.path_of o (#naming) o Sign.rep_sg;
fun theory_of_problem (Problem rep) = #theory rep;
val theoryname_of_problem = name_of_theory o theory_of_problem;
fun termstr_of_problem (Problem rep) = 
    Pretty.string_of (Display.pretty_cterm (#conjterm rep));

fun mk_problem theory name cterm = 
    Problem {theory = theory,
             name = name,
             conjterm = cterm};

fun problem_of_strs theory (name, termstr) = 
    Problem 
      {theory = theory,
       name = name,
       conjterm =  Syntax.read_prop 
                     (ProofContext.set_mode ProofContext.mode_schematic 
                                            (ProofContext.init theory))
                     termstr
                     |> Thm.cterm_of theory};

fun mk_problems theory L = 
     map (fn (n,s) => problem_of_strs theory (n, s)) L;

fun initrst_of_problem (Problem rep) = 
    let val thy = Theory.copy (#theory rep)
    val (init_goal,pp) = 
          PPlan.conj_term_at_top (#name rep, Thm.term_of (#conjterm rep)) (PPlan.init_from_thry thy)
    in
       (RState.init_from_pp pp)
         |> RState.set_goalnames [init_goal]
    end;


fun result_loc tname p = 
    let 
      val name = name_of_problem p;
      val thyname = name_of_theory (theory_of_problem p);
      val techn_path = "./benchmarks/results/" ^ tname;
      val thy_path = techn_path ^ "/" ^ thyname;
    in thy_path ^ "/" ^ name ^ "_r.sql" end;


fun timeout_string maxt tname p = 
    "UPDATE isapres_results"
    ^ " SET timeout = 1"
    ^ ",  time = " ^ (Time.toString maxt)
    ^ " WHERE prob = '" ^ (name_of_problem p) ^ "' "
    ^ " and techn = '" ^ tname  ^ "' "
    ^ " and thry = '" ^ (theoryname_of_problem p) ^ "';\n"

fun write_timeout maxt tname p = 
    let val outs = TextIO.openAppend(result_loc tname p) in 
      (TextIO.output (outs, timeout_string maxt tname p);
       TextIO.closeOut outs)
    end;

fun result_string tname p NONE time spec = 
    "UPDATE isapres_results " 
    ^ " SET solved = 0" 
    ^ ",  time = " ^ (Time.toString time) ^ " "
    ^ ",  spec = " ^ spec ^ " "
    ^ " WHERE prob = '" ^ (name_of_problem p) ^ "' "
    ^ " and techn = '" ^ tname ^ "' "
    ^ " and thry = '" ^ (theoryname_of_problem p) ^ "';\n"
  | result_string tname p (SOME (rst', _)) time spec = 
    "UPDATE isapres_results SET " 
    ^ " solved = 1" 
    ^ ",  time = " ^ (Time.toString time) ^ " "
    ^ ",  spec = " ^ spec ^ " "
    ^ "  WHERE prob = '" ^ (name_of_problem p)  ^ "' "
    ^ " and techn = '" ^ tname  ^ "' "
    ^ " and thry = '" ^ (theoryname_of_problem p) ^ "';\n";

fun write_result tname p res time = 
    let val outs = TextIO.openAppend(result_loc tname p) in 
      (TextIO.output (outs, result_string tname p res time (get_reset_spec ()) );
       TextIO.closeOut outs)
    end;

(* ISSUE: do we reset the cached lemmas? *)
fun benchify_problem maxt srch (tname,r) p = 
    let 
      val _ = PolyML.fullGC ();
      val rst0 = (initrst_of_problem p) 
                   |> RState.set_rtechn (SOME (RTechnEnv.map_then r));
      val timer = Timer.startRealTimer();
      (*  val timer = Timer.startCPUTimer; *)

      val result = IsaThread.usr_timeout maxt (fn () => (Seq.pull (srch rst0)));

     (*  val cputimes = Timer.checkCPUTimer timer; *)
      val time = Timer.checkRealTimer timer;
    in
      case result of 
        NONE => write_timeout maxt tname p
      | SOME r => write_result tname p r time
    end;


(* output *)
fun sqlify_mk_result tname p = 
    "INSERT INTO isapres_results (prob, term, thry, techn, solved, time, timeout, exp, spec)" 
    ^ "\n  VALUES (" 
    ^ "'" ^ (name_of_problem p) ^ "', " 
    ^ "'" ^ (termstr_of_problem p) ^ "', " 
    ^ "'" ^ (name_of_theory (theory_of_problem p)) ^ "', " 
    ^ "'" ^ tname ^ "', "
    ^ "0, " (* start as unsolved *)
    ^ "0.0, " (* no time *)
    ^ "0, " (* no timeout *)
    ^ "0, " (* no exp *)
    ^ "0  " (* no speculation *)
    ^ "); \n";

(* return true if we have written the file, false if someone else has
already started it. *)
fun start_write_file tname p = 
    let
      fun safe_isDir s = 
          (OS.FileSys.isDir s) handle OS.SysErr _ => false;
      fun safe_mkDir s = 
          (if safe_isDir s then () else 
           OS.FileSys.mkDir s) handle OS.SysErr _ => ();
      val name = name_of_problem p;
      val thyname = name_of_theory (theory_of_problem p);
      val techn_path = "./benchmarks/results/" ^ tname;
      val thy_path = techn_path ^ "/" ^ thyname;
      val loc = thy_path ^ "/" ^ name ^ "_r.sql";
      val _ = (safe_mkDir techn_path; 
               safe_mkDir thy_path)
    in
      ((OS.FileSys.fileId loc; false) handle 
       OS.SysErr _ => (let val outs = TextIO.openOut loc in 
                         TextIO.output (outs, sqlify_mk_result tname p); 
                       TextIO.closeOut outs; true end))
    end;


fun write_results_of_problems maxt srch (tname,r) L = 
    map (fn p => 
            if start_write_file tname p then 
              benchify_problem maxt srch (tname,r) p
            else ())
        L;

fun benchmark_problems t srch (tname,r) L = 
    write_results_of_problems t srch (tname,r) L;

end;



(* 
fun points_of_seq maxt globaltimer points s = 
    let val curtime = #usr (Timer.checkCPUTimer globaltimer) in
      if Time.<= (maxt,curtime) then 
        (points, TimeoutResult)
      else
        (case usr_timeout maxt (fn _ => Seq.pull s) of 
           (t, NONE) => (points, TimeoutResult)
         | (t, SOME (NONE)) => (points, EndResults t)
         | (t, SOME (SOME (h,s2))) => 
           let val usedt = #usr (Timer.checkCPUTimer(globaltimer)) in
             points_of_seq maxt globaltimer (h::points) s2
           end)
    end;
fun sqlify_result tname r = 
    let val p = problem_of_result r;
        val sucs = sucs_of_result r;
        val unsolved = List.null sucs;
    in
      "INSERT INTO isapres_results (prob, thry, techn, solved, time, timeout, exp)" 
      ^ "\n  VALUES ('" ^ (name_of_problem p) ^ "', '" 
      ^ (name_of_theory (theory_of_problem p)) ^ "', " 
      ^ "'" ^ tname ^ "', "
      ^ (if unsolved then "0, " else "1, ")
      ^ (case resultend_of_result r of 
           EndResults t => 
           (case sucs of [] => (Time.toString t) 
                               ^ ", 0, 0"
                       | (h::t) => (Time.toString (time_of_point h))
                                   ^ ", 0, 0")
         | TimeoutResult => "0, 1, 0"
         | ExpResult => "0, 0, 1")
      ^ "); \n"
    end;
*)
