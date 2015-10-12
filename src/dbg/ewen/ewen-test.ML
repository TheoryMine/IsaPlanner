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
      "(?F (0 :: nat) (pv_i :: nat) (pv_a :: nat)) --> (ALL x. (?F x pv_i pv_a))";

(*------------- Make state from problem -------------*)
val rst = 
    init_rst |> (RstPP.add_new_conj (problem_name, problem_term));

val ienv = (PPlan.get_ienv (RState.get_pplan rst));
val [(v,vtyp)] = InstEnv.uninst_vars_of ienv;
(* Trm.Var.NTab.dest (snd (Trm.dest_vtab (PPlan.get_vars (RState.get_pplan rst)))); *)


val v_inst = 
    PPlan.read_term (RState.get_pplan rst)
                    "(% (x:: nat) (y:: nat) (z :: nat). x < y & z = 0)";
val ienv = ienv |> InstEnv.add_var_inst (v,(vtyp,v_inst));
val rst2 = RstPP.inst ienv rst;

InstEnv.print (Prf.get_theory (RState.get_pplan rst)) ienv;

val rst = rst |> RState.set_rtechn (SOME QCheckAutoRTechn.quickcheck_and_auto);

(*------------- Do proof planning -------------*)
val [final_rst] = Seq.list_of (RState.search (MSearch.depthfs()) rst);

(*------------- Write out proof plan -------------*)

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

(* write_pplan_and_cex final_rst; *)

(* OS.Process.exit 1; *)
