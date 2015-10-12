(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/casesplit_tac
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    1 Sep 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A Tactic to perform case splits

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* the signature of an instance of the RW step tactic *)
signature CASESPLIT_TAC = 
sig

val casesplit_tac : string -> int -> Tactical.tactic;
val casesplit_meth : string -> Proof.method

val setup : (Theory.theory -> Theory.theory) list

val casesplit_dmeth : string -> DMethod.T
end;


structure CaseSplitTac
: CASESPLIT_TAC
= struct


val casesplit_tac = CaseSplit.casesplit_name;


fun casesplit_meth s =
    Method.METHOD 
      (fn facts =>
          HEADGOAL (Method.insert_tac facts
                                      THEN' ObjectLogic.atomize_tac
                                      THEN' (casesplit_tac s)));

fun meth_syntax m src ctxt = 
    m (snd (Method.syntax (Scan.lift Args.name) src ctxt));

val setup = 
    [Method.add_method ("casesplit", meth_syntax casesplit_meth, 
                        "IsaPlanner Case splitting")]; 



(* Adding stuff to make a DMethod without knowing what I'm doing...*)

val name = "Case-split critic";
datatype T =  string; 


fun prettyf s ctxt = Pretty.str ("Case-split on " ^ s);

fun textf s ctxt =
    Method.Basic (fn contx => (casesplit_meth s));

  structure I = 
    DMethodInstFUN(
      structure K = 
      struct
        type T = string;
        val name = name;
        val textf = textf;
        val prettyf = prettyf;
      end)

fun casesplit_dmeth s = I.dmeth_of s;

end;
