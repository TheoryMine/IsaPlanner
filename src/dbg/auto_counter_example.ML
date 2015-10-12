(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      dbg/auto_counter_example.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    created:    30 Jun 2005                                            *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

(* DESCRIPTION: A demo file showing how counter examples can be
entered and used with an autopmatic tactic, that combines quickcheck
and auto as well as some classical reasoning. 

The idea is that another program might generate this file (filling in
the problem name and problem term) and execute Isabelle in a batch
mode with this file to get some results. 

Note: will fail if the output files already exist.

from IsaPlanner/src/ run with something like: 

isabelle -e "use \"dbg/auto_counter_example.ML\";" HOL_IsaP

 *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

(*------------- Setup -------------*)
Trm.drop_var_args_flag := false;

(* create a new theory using IsaP and Main *)
val thry = Theory.begin_theory "test" [theory "Main", theory "IsaP"];
ML_Context.set_context (SOME (Context.Theory thry));

(* make a new empty proof plan/reasoning state *)
val init_rst = RState.init_from_thy (the_context());

(*------------- Problem setup -------------*)
val problem_name = "C0";
val problem_term = 
    PPlan.read_prop
      (RState.get_pplan init_rst) 
      "(((pv_i >= 0) & (pv_i <= (length pv_a))) --> (((pv_i ~= (length pv_a)) = True) --> (ALL x. ((pv_i >= 0) & ((pv_i < (length pv_a)) & (((pv_i >= 0) & (pv_i < (length pv_a))) & (ALL i. ((i = (pv_i + 1)) --> (i = z & (i >= 0) & (i <= (length pv_a)))))))))))";

val counter_ex_filename = "./isap_" ^ problem_name ^ ".cex.txt";
val proof_plan_filename = "./isap_" ^ problem_name ^ ".ppl.txt";


(*------------- Make state from problem -------------*)
val rst = 
    init_rst |> (RstPP.add_new_conj (problem_name, problem_term))
             |> RState.set_rtechn (SOME QCheckAutoRTechn.quickcheck_and_auto);

(*------------- Do proof planning -------------*)
val [final_rst] = Seq.list_of (RState.search (MSearch.depthfs()) rst);

(*------------- functions to write output -------------*)
(* output utility function *)
exception file_exists_exp of string;

fun write_result filename result_str = 
    let
      val loc = filename;
      (* make sure does not already exist *)
      val outs = ((OS.FileSys.fileId loc; raise file_exists_exp loc)
                  handle OS.SysErr _ => (TextIO.openOut loc))
    in (TextIO.output (outs, result_str); TextIO.closeOut outs) end;

fun write_pplan_and_cex rst = 
    let val _ = (* proof plan *)
            write_result proof_plan_filename 
                         (Pretty.string_of (RState.pretty final_rst));
        val _ = (* counter example file *) 
            (case QCheckAutoRTechn.get_bad_goals final_rst of 
               [] => write_result counter_ex_filename "No counter example found. "
             | l => write_result 
                      counter_ex_filename 
                       ((Pretty.string_of o Pretty.chunks)
                         (map (fn g => 
                                  Pretty.chunks 
                                    [Pretty.block 
                                       [Pretty.str "* Counter Example for goal: ", 
                                        Pretty.str g],
                                     CounterExCInfo.pretty_rst g final_rst])
                              l)));
    in writeln "write_pplan_and_cex: Completed." end;

(*------------- Actually write result to file -------------*)
(write_pplan_and_cex final_rst) 
handle _ => 
       (writeln "Failed to write output: maybe file's already exit?"; 
        OS.Process.exit OS.Process.failure);

(*------------- exit -------------*)
OS.Process.exit OS.Process.success;
