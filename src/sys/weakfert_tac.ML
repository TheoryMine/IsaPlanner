(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/weakfert_tac.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    18 Aug 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A Tactic to perform weak fertilisation
*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure WeakFertTac =
struct

fun weak_fert_tac_aux rwtac giventhms i th  = 
    let val (prems, goalth, exp) = IsaND.fixes_and_assumes i th in 
      (rwtac (giventhms @ prems) 1 goalth
       :-> Method.insert_tac prems 1
       :-> IsaND.export_back exp)
        |> (Seq.map Thm.strip_shyps)
    end;

val weak_fert_tac = weak_fert_tac_aux EQSubstTac.eqsubst_tac;

(* inthms are the given arguments in Isar, and treated as eqstep with
   the first one, then the second etc *)
fun weakfert_meth_aux tac inthms = 
    Method.METHOD 
      (fn facts => case inthms of 
                     [] => HEADGOAL (tac facts)
                   | (_::_) =>  HEADGOAL (tac inthms THEN' Method.insert_tac facts));

val weakfert_meth = weakfert_meth_aux weak_fert_tac;

val setup = 
    [Method.add_method ("wfert", Method.thms_args weakfert_meth, "Weak fertilisation from left to right (optional given theorems).") ];


end;
