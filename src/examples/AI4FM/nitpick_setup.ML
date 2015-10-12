(* Nitpick setup *) 
structure NitpickSetup =
struct

fun set_timout params timeout = 
   {cards_assigns = #cards_assigns params,
     maxes_assigns = #maxes_assigns params,
     iters_assigns = #iters_assigns params,
     bitss = #bitss params,
     bisim_depths = #bisim_depths params,
     boxes = #boxes params,
     finitizes = #finitizes params,
     monos = #monos params,
     stds = #stds params,
     wfs = #wfs params,
     sat_solver = #sat_solver params,
     blocking = #blocking params,
     falsify = #falsify params,
     debug = #debug params,
     verbose = #verbose params,
     overlord = #overlord params,
     user_axioms = #user_axioms params,
     assms = #assms params,
     whacks = #whacks params,
     merge_type_vars = #merge_type_vars params,
     binary_ints = #binary_ints params,
     destroy_constrs = #destroy_constrs params,
     specialize = #specialize params,
     star_linear_preds = #star_linear_preds params,
     total_consts = #total_consts params,
     needs = #needs params,
     peephole_optim = #peephole_optim params,
     datatype_sym_break = #datatype_sym_break params,
     kodkod_sym_break = #kodkod_sym_break params,
     timeout = SOME (Time.fromSeconds timeout),
     tac_timeout = #tac_timeout params,
     max_threads = 1,
     show_datatypes = #show_datatypes params,
     show_skolems = #show_skolems params,
     show_consts = #show_consts params,
     evals = #evals params,
     formats = #formats params,
     atomss = #atomss params,
     max_potential = #max_potential params,
     max_genuine = #max_genuine params,
     check_potential = #check_potential params,
     check_genuine = #check_genuine params,
     batch_size = #batch_size params,
     expect = #expect params}

val exp_string = "Exception"

fun nitpick_fun ctxt thy timeout conj =
  let      
     val state = Proof.theorem NONE (K I) [[(conj, [])]] ctxt
     val params = set_timout (Nitpick_Isar.default_params thy []) timeout
    val (response, _) =  
         Nitpick.pick_nits_in_subgoal state params Nitpick.Normal 1 0
         handle Exn.Interrupt => (exp_string,state)
  in
    if (response=Nitpick.noneN orelse response=Nitpick.unknownN orelse response=exp_string) 
    then SOME(response,conj) else NONE
  end

fun filter_nitpick ctxt thy conjs =
    map_filter (nitpick_fun ctxt thy 10) conjs;

fun print_nitpick_results ctxt thy conjs =
    map (fn (response, conj) => 
            Pretty.writeln (Pretty.block [Pretty.str "(",
                                           Pretty.str response,
                                          Pretty.str ", ",
                                           Trm.pretty ctxt conj,
                                           Pretty.str ")"] ))
        (filter_nitpick ctxt thy conjs);

fun term_to_str ctxt trm =
              (Trm.pretty ctxt trm)
                |> Pretty.string_of;

fun stupid_complicated_to_string t ctxt = Print_Mode.setmp [] (fn () => Syntax.string_of_term ctxt t) ();


fun nitpick_results_to_file exp_nm ctxt thy conjs = 
    let 
      val (exp_conjs, tested_conjs) = 
          List.partition (fn (r,c) => r=exp_string) (filter_nitpick ctxt thy conjs)
      val res_string = 
         List.foldl (fn ((response, conj), res) => 
                        res ^ "(" ^ response ^  ", " ^ 
                        (stupid_complicated_to_string conj ctxt) ^ ") \n") 
                    "" (tested_conjs @ exp_conjs);
      val path = "./results/"^exp_nm^".txt";
      val outs = TextIO.openAppend path
    in
      (TextIO.output (outs, res_string); TextIO.closeOut outs)
    end;
end;    
