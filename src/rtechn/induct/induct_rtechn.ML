(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/induct_rtechn.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    created:    30 Jun 2005
    modified:   Moa - 14 Jun 2006: changed to use new proof environment
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Techniques for induction

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 


signature INDUCT_RTECHN =
sig
  val inductable_things_in_term 
      : Context.theory -> Term.term -> (string * Term.typ) list
  val inductable_things_of 
      : PPlan.gname -> RState.T -> (string * Term.typ) list

  val just_induction_on_goal : PPlan.gname -> RTechn.T;
  val just_induction_on_goal_with : Thm.thm -> PPlan.gname -> RTechn.T;

  val base_then_step : 
      RTechn.T -> (*Base case techn*)
      RTechn.T -> (*Step case techn*)
      RTechn.T

  val induction_on_goal : 
      PPlan.gname -> 
      RTechn.T -> (*Base case techn*)
      RTechn.T -> (*Step case techn*)
      RTechn.T

  val induction_on_goal_with : 
      PPlan.gname -> 
      Thm.thm -> (*Induction rule *)
      RTechn.T -> (*Base case techn*)
      RTechn.T -> (*Step case techn*)
      RTechn.T
end;


structure InductRTechn
= struct

local
open RTechnEnv;
in

(* gets names/types of possible induction vars *)
fun inductable_things_of g rst = 
    let 
      val pp = RState.get_pplan rst
      val thy = PPlan.get_theory pp
      val gt = Prf.get_ndname_ctrm pp g
    in InductDTac.inductable_things_in_term thy gt end;

(* just do the induction scheme application, no more. *)
fun just_induction_on_goal g rst = 
    let 
      val (ithings,_) = inductable_things_of g rst;
      val dts = map (fn i => InductDTac.induct [i]) 
                    (map fst ithings);
    in Seq.map snd (apply_or_dtacs_to_g dts g rst) end;

(* use an induction rule *)
fun just_induction_on_goal_with g rule rst = 
    let
      val prev_asms = RstPP.asms_of_goal rst g
      val (indthings, _) = inductable_things_of g rst
      val dts = 
            map (fn (i,_) => InductDTac.induct_rule [rule] [i])
                indthings
    in Seq.map snd (apply_or_dtacs_to_g dts g rst) end;

(*Apply base-case technique to all goals without 
  asumptions/inductive hypothesis, step-techn to other goals*)
fun base_then_step base_r step_r prev_asms rst = 
    split_then
      (not o PPlan.has_new_asm (RState.get_pplan rst) prev_asms)
      (solve_or_fail base_r) (solve_or_fail step_r) rst;

(* induction followed by base and step case techniques *)
fun induction_on_goal g base_r step_r rst= 
    (*Check if we have any assumptions before we start induction*)
      let 
        val prev_asms = RstPP.lasms_of_goal rst g
      in
        ((just_induction_on_goal g)
          thenr
          (base_then_step base_r step_r prev_asms)) rst
      end;

fun induction_on_goal_with g rule base_r step_r rst = 
    (*Check if we have any assumptions before we start induction*)
      let 
        val prev_asms = 
            distinct (op =) (maps (RstPP.asms_of_goal rst) 
                                  (RState.get_goalnames rst))
      in
        ((just_induction_on_goal_with g rule)
           thenr
          (base_then_step base_r step_r prev_asms)) rst
      end;

end; (* local *)
 
end;
