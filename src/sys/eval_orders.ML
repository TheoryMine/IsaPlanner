
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/eval_orders.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Modified:   15 Oct 2004
    Created:    16 Jun 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

   Evaluation orders for use with eval nets. These are focus term
   pasring tools that define an ordering on the application of a match
   function to a focus term

   This file simply contains wrappers from the eval orders defined in 
   "IsaFTerm.ML".

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature EVAL_ORDERS = 
sig 

  val valid_bl_ur : ThmEvalNet.evalord
  val valid_bl_ru : ThmEvalNet.evalord
  
  val all_bl_ur : ThmEvalNet.evalord
  val all_bl_ru : ThmEvalNet.evalord

  val setup : (theory -> theory) list

end;

structure EvalOrders : EVAL_ORDERS = 
struct 

val valid_bl_ru = ThmEvalNet.mk_evalord ("valid_bl_ru",
                                   IsaFTerm.search_valid_bl_ru_f);
val valid_bl_ur = ThmEvalNet.mk_evalord ("valid_bl_ur",
                                   IsaFTerm.search_valid_bl_ur_f);
val all_bl_ru = ThmEvalNet.mk_evalord ("all_bl_ru",
                                   IsaFTerm.search_all_bl_ru_f);
val all_bl_ur = ThmEvalNet.mk_evalord ("all_bl_ur",
                                   IsaFTerm.search_all_bl_ur_f);

val setup = 
    [EvalThyInfo.add_eord_to_thy valid_bl_ur,
     EvalThyInfo.add_eord_to_thy valid_bl_ru,
     EvalThyInfo.add_eord_to_thy all_bl_ur,
     EvalThyInfo.add_eord_to_thy all_bl_ru];

end;
