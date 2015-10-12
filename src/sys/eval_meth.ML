(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/eval_meth
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    1 Jun 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    The isar method stuff for the eval tactic that applies
    (conditional) equality rules exhustively, from bottom-left to
    right-top (ML style, call by value).

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature EVAL_METH = 
sig

end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure EvalMeth =
struct

val defaultN = "default"; (* the name of the default evalnet *)
val evalattrN = "eval"; (* keyword for method and attribute *)
val evalmethN = "eval"; (* keyword for method and attribute *)
val onlyN = "only"; (* option for using only a set of rules in the net *)
val onceN = "once"; (* option to eveluation only once *)
val nthN = "nth"; (* option to evaluate the nth application (once) *)
val inN = "in"; (* keyword for selecting which rulenet to use *)

(* val default_order = EvalOrders.bl_ru;
   val default_rnet = ThmEvalNet.new (defaultN, default_order); *)

val add_rule_to_thy = EvalThyInfo.add_rule_to_thy;
val del_rule_from_thy = EvalThyInfo.del_rule_from_thy;

val add_rule_to_ctxt = EvalThyInfo.add_rule_to_ctxt;
val del_rule_from_ctxt = EvalThyInfo.del_rule_from_ctxt;

(* fun default_rnet_of_ctxt ctxt = 
    EvalThyInfo.lookup_rnet_from_ctxt (defaultN,ctxt); *)

(* syntax *)
fun add_evalrule_syntax f = 
    Args.$$$ "addto" -- Args.name 
             >> (fn (_,n) => f n);

fun del_evalrule_syntax f = 
     Args.$$$ "delfrom" -- Args.name
              >> (fn (_,n) => f n);

fun eval_add_del_args addf delf x = Attrib.syntax
  (Scan.lift (add_evalrule_syntax addf || del_evalrule_syntax delf)) x;

val ruleattr = 
    (eval_add_del_args add_rule_to_thy del_rule_from_thy,
     eval_add_del_args add_rule_to_ctxt del_rule_from_ctxt);


(* tactics *)
(* _tac: implicit: rulenet i th *)
(* _ctxt_tac: implicit: i th *)
(* val backtrack_tac = EvalTac.eval;
fun backtrack_ctxt_tac ctxt = backtrack_tac (rules_of_context ctxt); *)

val nobacktrack_tac = EvalTac.eval_no_backtrack;
val once_tac = EvalTac.eval_once;
(* make the chosen evaluation tactic ignore conditions, as the user
   will want to solve these themselves *)
val nth_tac = K EvalTac.eval_once_nth (K Tactical.all_tac);

fun SOLVE_SUBGOAL tac th = 
    let val subgoals1 = Thm.nprems_of th 
      val ths = (tac th)
    in Seq.filter (fn th2 => Thm.nprems_of th2 < subgoals1) ths end;

(* Isar Method 
where do facts and prems come from? "from"'s and "using"'s, or as args?  

     val _ = (writeln "\nonly: "; 
               (case onlys_opt of NONE => print "NONE" | (SOME x) => (print "SOME "; print x)); 
               writeln "\nadds: "; 
               print adds;
               writeln "\ndels: ";
               print dels) 
*)
fun meth ((netname, ctac), (onlys_opt, (adds,dels))) ctxt =
    let
      val ctxtnet = EvalThyInfo.lookup_rnet_from_ctxt (netname, ctxt)
      val net = 
          (case onlys_opt 
            of NONE => ctxtnet
             | SOME onlyrules => 
               foldr ThmEvalNet.insert (ThmEvalNet.empty_copy ctxtnet) onlyrules)
      val net' =  foldr ThmEvalNet.delete (foldr ThmEvalNet.insert net adds)
                        dels
      val simp_tac = 
          (fn i => SOLVE_SUBGOAL (Simplifier.asm_full_simp_tac 
                                    (Simplifier.get_local_simpset ctxt) i))
    in
      Method.METHOD
        (fn facts =>
            HEADGOAL (Method.insert_tac facts
                                        (* THEN' ObjectLogic.atomize_tac *)
                                        THEN' (ctac net' simp_tac)))
    end;

(* options for the tactic *)
val options =
    (Args.parens (Args.$$$ inN |-- Args.name)) -- 
    (Args.parens (Args.$$$ nthN -- Args.colon -- Args.nat) >> 
                 (fn (x,y) => nth_tac y) ||
     Args.parens (Args.$$$ onceN) >> K once_tac ||
     Scan.succeed nobacktrack_tac);

val rule_effects = 
    Scan.option ((Scan.lift (Args.$$$ onlyN -- Args.colon)) |-- Attrib.local_thms) --
    ((Scan.optional ((Scan.lift (Args.add -- Args.colon)) |-- Attrib.local_thms) []) -- 
    (Scan.optional ((Scan.lift (Args.del -- Args.colon)) |-- Attrib.local_thms) []));

(* method syntax *)
fun meth_syntax meth src ctxt =
    meth (snd (Method.syntax ((Scan.lift options) -- rule_effects) src ctxt)) 
         ctxt;

(* setup rippling method and attributes *)
val setup = 
    [Attrib.add_attributes
       [(evalattrN, ruleattr, "declaration of a eval rule")],

     Method.add_method (evalmethN, meth_syntax meth, "Evaluation")];


(** outer syntax **)
(* val print_rulesP =
  OuterSyntax.improper_command "print_eval_rules" "print the currently used evaluation rules"
    OuterSyntax.Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o 
                   (Toplevel.keep
      (Toplevel.node_case GlobalData.print 
                          (LocalData.print o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [print_rulesP];
*)


end;
