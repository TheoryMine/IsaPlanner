
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
signature ISAP_BENCHMARK_DATA = 
sig
  type T
  val init : RState.T -> T 
  val pretty : T -> Pretty.T
  val update : RState.T option -> T
end;

signature ISAP_BENCHMARKS =
sig
  type resultT
  type pointT
  type problemT
  type searchf = RState.T -> RState.T Seq.seq
       
  val benchmark_problems :
      searchf -> RTechn.T -> problemT list -> unit
  val one_benchmark_problems :
      searchf -> RTechn.T -> problemT list -> unit
  val pretty_one_benchmark_problems :
      searchf -> RTechn.T -> problemT list -> Pretty.T
  val results_of_problems :
      searchf -> RTechn.T -> problemT list -> resultT list
  val result_of_pp :
      searchf -> RTechn.T -> problemT -> resultT
  val one_result_of_pp :
      searchf -> RTechn.T -> problemT -> resultT

  val mk_problem :
      Context.theory -> string -> Thm.cterm -> problemT
  val mk_problems :
      string -> (string * string) list -> problemT list
  val problem_of_strs :
      Context.theory -> string * string -> problemT
  val rst_of_problem : problemT -> RState.T   
  val name_of_problem : problemT -> string

  val minimal_pretty_of_result : resultT -> Pretty.T
  val pretty_of_point : pointT -> Pretty.T
  val pretty_results : resultT list -> Pretty.T
  val print_results : resultT list -> unit                    
end;

functor IsaPBenchmarksFUN
(structure Stats : ISAP_BENCHMARK_DATA) 
(* : ISAP_BENCHMARKS *)
= struct


(* fun f with usr time timeout maxt *)
(* fun usr_timeout maxt f =
let
  
    val result = Process.channel()

    val killThread = Process.console(fn () => Process.send(result, f()))

    val finalResult = Process.channel()
    val timer = Timer.startCPUTimer();
    fun sleep () = 
        let val t = (#usr (Timer.checkCPUTimer timer))
          val tsub = Time.-(maxt, t)
        in
          if Time.<= (tsub, Time.fromSeconds 1)
          then if Time.<= (tsub, Time.zeroTime) then t
               else (OS.Process.sleep tsub; sleep())
          else (OS.Process.sleep (Time.fromSeconds 1); sleep())
        end;
in
    Process.choice(fn () => (let val t = sleep (); in 
                               (Process.send(finalResult, (t, NONE));
                                killThread()) end),
                   fn () => let val r = Process.receive result 
                            in Process.send(finalResult, 
                         ((#usr (Timer.checkCPUTimer timer)), SOME r)) end);
    Process.receive finalResult
end;
*)

fun usr_timeout maxt f = IsaThread.usr_timeout;
(* 
    let 
      val return_mutex = Mutex.mutex ();
      val wait_for_return_mutex = Mutex.mutex ();
      val _  = Mutex.lock wait_for_return_mutex;
      val return_value = ref NONE;
      val working_thread = 
          Thread.fork ((fn () => let val v = f();
                                     val _ = Mutex.lock return_mutex;
                                     val _ = return_value := SOME v;
                                     val _ = Mutex.unlock wait_for_return_mutex;
                                 in Thread.exit () end), []);
      val sleeping_thread = 
          Thread.fork ((fn () => (OS.Process.sleep (Time.fromSeconds maxt);
                                  Mutex.lock return_mutex;
                                  Mutex.unlock wait_for_return_mutex;
                                  Thread.exit ())), []);
      fun try_kill thread = 
          ((Thread.kill thread) handle Thread _ => ());
    in 
      (Mutex.lock wait_for_return_mutex; 
       try_kill working_thread; 
       try_kill sleeping_thread; 
       (!return_value))
    end;
*)
(* *)


val nds_count = ref 0;

type searchf = RState.T -> RState.T Seq.seq

datatype problem = 
         Problem of {theory : Context.theory, 
                     name : string, 
                     conjterm : Thm.cterm};

fun name_of_problem (Problem rep) = #name rep;
val name_of_theory = NameSpace.path_of o (#naming) o Sign.rep_sg;
fun theory_of_problem (Problem rep) = #theory rep;

fun mk_problem theory name cterm = 
    Problem {theory = theory,
             name = name,
             conjterm = cterm};

fun problem_of_strs theory (name, termstr) = 
    Problem 
      {theory = theory,
       name = name,
       conjterm = Syntax.read_prop 
                    (ProofContext.set_mode ProofContext.mode_schematic 
                                           (ProofContext.init theory))
                    termstr
                    |> Thm.cterm_of theory};
    
fun initrst_of_problem (Problem rep) = 
    let val thy = Theory.copy (#theory rep)
    val (init_goal,pp) = 
          PPlan.conj_term_at_top (#name rep, Thm.term_of (#conjterm rep)) (PPlan.init_from_thry thy)
    in
       (RState.init_from_pp pp)
         |> RState.set_goalnames [init_goal]
    end;

datatype point = 
         Point of {time : Time.time,
                   nodes : int,
                   stats : Stats.T};

fun time_of_point (Point rep) = #time rep;
fun stats_of_point (Point rep) = #stats rep;
fun nodes_of_point (Point rep) = #nodes rep;

datatype resultend = 
         EndResults of Time.time
       | ExpResult
       | TimeoutResult;

datatype result = 
         Result of { problem : problem,
                     stats : Stats.T,
                     successes : point list,
                     resultend : resultend };

fun problem_of_result (Result rep) = #problem rep;
fun stats_of_result (Result rep) = #stats rep;
fun sucs_of_result (Result rep) = #successes rep;
fun resultend_of_result (Result rep) = #resultend rep;

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

(* FIXME: allow results to give some success and also an exception *)
fun result_of_pp maxt srch r p = 
    let 
      val rst0 = (initrst_of_problem p) 
                   |> RState.set_rtechn (SOME (RTechnEnv.map_then r));
      fun mk_point gtimer rstopt = 
          Point {time = #usr (Timer.checkCPUTimer gtimer),
                 nodes = (! nds_count),
                 stats = (Stats.update rstopt)};
      val _ = (nds_count := 0);
      val globaltimer = Timer.startCPUTimer();
      val res_seq = srch rst0;
      val startstats = Stats.init rst0;

      val (points,endres) = 
          (points_of_seq maxt globaltimer []
                         (Seq.map (fn rst => mk_point globaltimer (SOME rst)) 
                                  res_seq)
           handle _ => ([],ExpResult));
    in
      Result {problem = p, stats = startstats, 
              successes = points, resultend = endres}
    end;

fun mk_problems theory L = 
     map (fn (n,s) => problem_of_strs theory (n, s)) L;

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

fun start_write_file tname problem = 
    let
      fun safe_isDir s = 
          (OS.FileSys.isDir s) handle OS.SysErr _ => false;
      val name = name_of_problem problem;
      val thyname = name_of_theory (theory_of_problem problem);
      (* loc is relative to IsaPlanner src *)
      val loc = "./benchmarks/results/" ^ tname ^ "_" 
                ^ thyname ^ "_" ^ name ^ "_r.sql";
    in
      ((OS.FileSys.fileId loc; NONE) handle 
       OS.SysErr _ => SOME (TextIO.openOut loc))
    end;

fun write_results_of_problems t srch (tname,r) L = 
    map (fn p => 
            case start_write_file tname p 
             of NONE => ()
              | SOME outs => 
                (TextIO.output (outs, sqlify_result tname
                                        (result_of_pp t srch r p)); 
                 TextIO.closeOut outs))
        L;

fun benchmark_problems t srch (tname,r) L = 
    write_results_of_problems t srch (tname,r) L;

end;

structure NoStats_IsaPBenchmarksData =
struct
type T = unit
fun init x = ();
fun pretty x = (Pretty.str "");
fun update x = ();
end;

structure IsaPBenchmarks = 
IsaPBenchmarksFUN(structure Stats = NoStats_IsaPBenchmarksData);



(*
fun pretty_of_point (Point rep) = 
    Pretty.block [Pretty.str "[",
                  Pretty.str "; ", Pretty.str "Nodes: ", 
                  Pretty.str (string_of_int (#nodes rep)),
                  Pretty.str "; Time: ", Pretty.str (Time.toString (#time rep)), 
                  Pretty.str "]"];

fun minimal_pretty_of_result (ExpResult p) = 
    Pretty.str ("** exception ** : " ^ (name_of_problem p))
  | minimal_pretty_of_result (Result rep) = 
    case #successes rep of 
      [] => Pretty.block [Pretty.str "-- failed --: ",
                          Pretty.str (name_of_problem (#problem rep)),
                          pretty_of_point (#finalpoint rep)]
    | (suc1 :: sucs) => 
      Pretty.block [Pretty.str "++ proved ++(",
                    Pretty.str (string_of_int (length (#successes rep))),
                    Pretty.str "): ",
                    Pretty.str (name_of_problem (#problem rep)),
                    pretty_of_point suc1, 
                    Pretty.str "\n            ended search: ", 
                    pretty_of_point (#finalpoint rep)];


fun pretty_results Rs = Pretty.chunks (map minimal_pretty_of_result Rs);
val print_results = Pretty.writeln o pretty_results
*)
