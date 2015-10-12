(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./benchmarks_timeout.ML
    Author:     Lucas Dixon,Moa Johansson, University of Edinburgh
                lucasd@dai.ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Code to create and run benchmarks for IsaPlanner. 
    Supports timeouts and writes the results to file in the directory
    /benchmarks/Results/<givenPath>/<problem-name>.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
signature BMARK_TIMEOUT 
= sig
  datatype problemT =
           problem of
           {name: string, path: string, theory: Theory.theory,
            conjterm: Thm.cterm}
  type pointT
  type resultT

  val nds_count : int ref
  val print_point : pointT -> string
  val print_point_pp : pointT -> string
  val print_result : resultT -> string

  val mk_problems :
      string (* extra post-theory path *)
      -> string (* theory *)
      -> (string * string) list (* problem name and statement *)
      -> problemT list
  val problem_of_strs : 
      string (* extra post-theory path *)
      -> string (* theory *)
      -> string * string (* problem name and statement *)
      -> problemT

  val do_split :
      int (* timout in seconds *)
      -> (RState.T -> RState.T Seq.seq) (* searchf *)
      -> RTechn.T -> problemT -> unit
  val result_of_pp :
      (RState.T -> RState.T Seq.seq) (* searchf *)
      -> RTechn.T -> problemT -> unit -> unit
  val results_of_problems :
      int (* timout in seconds *)
      -> (RState.T -> RState.T Seq.seq) ->
      RTechn.T -> problemT list -> unit

  val benchmark_problems :
      int (* timout in seconds *)
      -> (RState.T -> RState.T Seq.seq)  (* searchf *)
      -> RTechn.T 
      -> problemT list 
      -> unit

  val benchmark : 
      int (* timout in seconds *)
      -> (RState.T -> RState.T Seq.seq) (* searchf *)
      -> RTechn.T (* technique to use *)
      -> string (* additional sub path name *)
      -> string (* thoery *)
      -> (string * string) list (* problem names and strings *)
      -> unit

  val rst_of_problem : problemT -> RState.T
  val name_of_problem : problemT -> string

  val write_exp_result : exn -> problemT -> unit
  val write_results : resultT -> problemT -> unit
  val write_sol : problemT -> pointT -> unit
  val write_timeout : problemT -> bool -> unit
end;


functor BMarkTimeOutFUN
(structure Stats :ISAP_BENCHMARK_DATA)
: BMARK_TIMEOUT
= struct
   
datatype problemT = 
         problem of {theory : Theory.theory, 
                     name : string, 
                     conjterm : Thm.cterm,
                    path : string}
datatype pointT = 
         point of {time : string,
                   nodes : int,
                   stats : Stats.T};

datatype resultT = 
         result of {problem : problemT,
                    start : Stats.T,
                    successes : pointT list,
                    finalpoint : pointT}
       | exp_result of problemT;

val nds_count = ref 0;

fun name_of_problem (problem rep) = #name rep;

fun safe_isDir s = 
    (OS.FileSys.isDir s) handle OS.SysErr _ => false;

fun problem_of_strs path thyname (name, termstr) = 
    let 
      (* loc is relative to IsaPlanner src *)
      val thy_path = "./benchmarks/results/" ^ thyname;
      val user_path =  thy_path ^ "/" ^ path ^ "/";
      val _ = 
          (if (safe_isDir thy_path) then 
            if (safe_isDir user_path) then ()
            else OS.FileSys.mkDir user_path
          else (OS.FileSys.mkDir thy_path; OS.FileSys.mkDir user_path))
               handle OS.SysErr _ => 
                      raise ERROR_MESSAGE ("Problem creating directory for results: " ^ user_path);

      val loc = user_path ^ name;
      val outstr = TextIO.openOut loc;
      val _ = (TextIO.output (outstr, "<Name>"^name^"</Name>\n"
                                      ^"<Conj>"^termstr^"</Conj>\n"
                                      ^"<Theory>"^thyname^"</Theory>\n"); 
               TextIO.closeOut outstr)
      val theory = (theory thyname)
    in
      problem 
        {theory = theory,
         name = name,
         conjterm = (Goals.read_cterm (Theory.sign_of theory) 
                                      (termstr, propT)),
         path = loc }
    end;

fun rst_of_problem (problem rep) = 
    let val thy = Theory.copy (#theory rep)
    in IsarPP.init_rst_i thy (#name rep, Thm.term_of (#conjterm rep)) end;

fun print_point_pp (point rep) = 
    "<Solution>\n"
    (*"<Nodes>"^(string_of_int (#nodes rep))^"</Nodes> \n"*)
    ^" <Time>"^(#time rep)^"</Time> \n"
    ^" <PPlan>"^Pretty.string_of(Stats.pretty(#stats rep))^"</PPlan>\n</Solution>\n";

fun print_point (point rep) = 
    (*"<Nodes>"^(string_of_int (#nodes rep))^"</Nodes> \n"*)
    "<Time>"^(#time rep)^"</Time> \n";

fun print_result (result rep) = 
    case #successes rep of 
      [] => 
      "<Result> \n"
      ^"<Status>Fail</Status>\n"                                            
      ^"<Ended>\n"^ (print_point(#finalpoint rep)) ^"</Ended> \n"
      ^"</Result> \n"
    | (suc1 :: sucs) => 
      "<Result> \n"
      ^"<Status>Proved</Status> \n"
      ^"<NumSol>"^(string_of_int (length (#successes rep)))^"</NumSol> \n"
      ^"<FirstSol>\n"^(print_point suc1)^"</FirstSol> \n"
      ^"<Ended>\n"^(print_point(#finalpoint rep))^"</Ended> \n"
      ^"</Result> \n";

fun write_sol (problem p) (point rep) =
    let val outstr = TextIO.openAppend (#path p) in
         (TextIO.output (outstr, (print_point_pp (point rep))); 
          TextIO.closeOut outstr) end;

fun write_results (result res) (problem p)=
    let val outstr = TextIO.openAppend (#path p) in
         (TextIO.output (outstr, (print_result (result res))); 
          TextIO.closeOut outstr) end;

fun write_exp_result expn (problem p) =
    let val outstr = TextIO.openAppend (#path p) in
      (TextIO.output (outstr, "<Result>\n" 
                              ^"<Status>Exception: "^(exnMessage expn)
                              ^"</Status> \n</Result>\n"); 
       TextIO.closeOut outstr) end;

fun write_timeout (problem p) timed_out =
    if timed_out then
      let val outstr = TextIO.openAppend (#path p) in
        (TextIO.output (outstr, "<Result> \n"
                                  ^"<Status>TimedOut</Status>\n"
                                  ^"</Result>\n"); 
         TextIO.closeOut outstr)  end
    else () (*Do nothing*)


fun result_of_pp srch r p () = 
    (let 
      val rst0 = (rst_of_problem p) 
                   |> RTechnEnv.init
                   |> RState.set_rtechn (SOME r);
      fun mk_point t rstopt = 
          let val pt = point {time = endTiming t,
                             nodes = (! nds_count),
                             stats = (Stats.update rstopt)}
          in 
            case rstopt of 
              NONE => pt
            | SOME rst => let val _ = (write_sol p pt) in pt end 
          end;

      val t = (nds_count := 0; startTiming())
      val res_seq = srch rst0;
      val start = Stats.init rst0;
      val points = Seq.list_of (* Note forced evaluation *)
                (Seq.map (fn rst => mk_point t (SOME rst)) res_seq); 
      val endpoint = mk_point t NONE;
    in
       write_results (result {problem = p, start = start, 
               successes = points, finalpoint = endpoint}) p
    end; exit(1))
    handle expn => (write_exp_result expn p; exit(1));

fun do_split i srch r p =
    Thread.split (Thread.mk_real_timer (write_timeout p) 
                                  (Time.fromReal (Real.fromInt i))) 
                 (result_of_pp srch r p)

fun results_of_problems i srch r L = 
    (map (do_split i srch r) L; ());

fun benchmark_problems i srch r L = 
      (results_of_problems i srch r L);

fun mk_problems path thyname L = 
     map (fn (n,s) => problem_of_strs path thyname (n, s)) L;

fun benchmark i srch r path thy L = 
      (Context.context (theory thy);
       benchmark_problems i srch r (mk_problems path thy L));

end;


structure PPlan_IsaPBenchmarksData :> ISAP_BENCHMARK_DATA =
struct
type T = PPlan.T option;
fun init x = NONE;

fun update rstopt =
    case rstopt of
      NONE => NONE
    | SOME rst => SOME (RState.get_pplan rst);

fun pretty stats = 
     case stats of
       NONE => Pretty.str ""
     | SOME plan => PPlan.pretty plan;
end;

structure BMarkTimeOut = BMarkTimeOutFUN(structure Stats = PPlan_IsaPBenchmarksData);
