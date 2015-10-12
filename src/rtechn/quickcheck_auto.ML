(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/quickcheck_auto.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    created:    30 Jun 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    quick check followed by auto

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

signature QCHECK_AUTO_RTECHN =
sig
    val deselect_bad_goals : RState.T -> RState.T
    val get_bad_goals : RState.T -> PPlan.gname list
    val quickcheck : RTechn.T
    val quickcheck_and_auto : RTechn.T
    val quickcheck_curgoals : RState.T -> RState.T
    val quickcheck_curgoals_concl : RState.T -> RState.T
end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure QCheckAutoRTechn
: QCHECK_AUTO_RTECHN
= struct local open RTechnEnv; in

(* state function that checks which goals have counter examples *)
fun quickcheck_curgoals rst = 
    RstPP.fold_cur_goals' CounterExCInfo.quickcheck rst rst;

(*Moa: Check the goals, but does not include assumptions *)
fun quickcheck_curgoals_concl rst = 
     RstPP.fold_cur_goals' CounterExCInfo.quickcheck_concl rst rst;  
                               
(* the goals that have counter examples *)
fun get_bad_goals rst = 
    fold (fn x => fn y => x @ y) 
         (map (fn g => if CounterExCInfo.has_counterex g rst 
                       then [g] else []) 
              (RState.get_goalnames rst))
         [];

(* technique that checks which goals have counter examples *)
val quickcheck = 
    let 
      fun prettyf rst =  (* FIXME: buugy print *)
          let 
            val _ = writeln "computing quickcheck name";
            val bad_goals = get_bad_goals rst in
            case bad_goals of
              [] => Pretty.str "No counter examples found"
            | l => Pretty.block 
                [Pretty.chunks 
                   [Pretty.str "Counter examples found to: ",
                    Pretty.list "[" "]" (map Pretty.str l)]]
          end;
    in ofstep (RstName.f prettyf) quickcheck_curgoals end;




(* state function that deselects goals which have counter examples *)
fun deselect_bad_goals rst = 
    let 
      val bad_goals = get_bad_goals rst
    in RState.update_goalnames 
         (* subtract first from second *)
         (fn l => Library.subtract (op =) bad_goals l) 
         rst
    end;

(* apply r to the non-bad (counter example containing) goals *)
fun to_true_goals r rst = 
    let 
      val bad_goals = get_bad_goals rst
      val good_goals = 
          Library.subtract (op =) bad_goals
                           (RState.get_goalnames rst)
    in 
      (RState.set_goalnames good_goals rst)
        |> (r thenf (RState.add_goalnames bad_goals))
    end;

(* quick check then auto the goals which do not have counterexamples *)
val quickcheck_and_auto = 
    refine (RstName.str "quickcheck and then auto")
           (DTacRTechn.multi_safe 
              thenr quickcheck 
              thenr (to_true_goals DTacRTechn.multi_auto));

end; end; (* local; struct *)
