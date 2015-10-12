(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/ripple_tac.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    18 Feb 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A Tactic to perform rippling (using IsaPlanner)

    FIXME: if there are no wave rules then no exploration is done -
    this wrongly introduces a single new subgoal - fix this! -- look
    into this - for some reason there is a meta varaible
    introduced... odd.

    Actually this is a big problem... -- doesn't happen with Nats, 
    only lists.
*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RIPPLE_TAC = 
sig

val rippling_modifiers : 
    (Args.T list -> (Method.modifier * Args.T list)) list

val ripple_skel_syntax : 
    ProofContext.context * Args.T list ->
    (Term.term list * Thm.thm list) * (ProofContext.context * Args.T list)

val ripple_tac_i : Proof.context -> Term.term list * Thm.thm list 
                   -> int -> Tactical.tactic;
val ripple_tac : Term.term list * Thm.thm list 
                 -> int -> Tactical.tactic;

val ripple_meth : Term.term list * Thm.thm list 
                  -> Proof.context -> Proof.method

val setup : (Theory.theory -> Theory.theory) list

end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
functor RippleTacFun (R : RIPPLING_RTECHN) 
: RIPPLE_TAC 
= struct

(* make a rst from a technique and a goal (thm) *)
fun init_ctxt_rst ctxt techn i th = 
    let 
      val gterm = Library.nth_elem (i - 1, prems_of th)
    in
      (IsarPP.init_rst_from_ctxt_i ctxt gterm)
        |> RTechnEnv.init
        |> RState.set_rtechn (SOME (techn ctxt))
    end;

(* apply rippling in proof planning as a tactic, exporting result to
   context ctxt, and adding wavethms as wave rules locally. *)
fun ripple_tac_i ctxt skels i gthm = 
    let 
      fun rtechn ctxt = R.just_ripple skels
      val searchf = (GSearch.depth_fs (Library.is_none o RState.get_rtechn)
                                     RState.unfold)
    in 
      Seq.map 
        RstPP.export_thm
        (searchf (init_ctxt_rst ctxt rtechn i gthm))
    end;

(* this must be a function, (not a val) else the context will be wrong *)
fun ripple_tac skels i gthm = 
    ripple_tac_i ((Proof.context_of o Proof.init 
                   o ProofContext.init o the_context)())
                 skels i gthm;


(* FIXME: add conditional rippling usinhg the facts to validate 
   the conditions *)
(* FIXME: should have an extra thing to allow: by (rippling skeleton:
   ... ) ie to explicitly give the skeletons, currently, we'll just take
   the first hypothesis and use the ripple tac *)
(* the method takes the more wave rule theorems as arguments *)

fun ripple_meth skelts ctxt =
    Method.METHOD
      (fn facts =>
          HEADGOAL (Method.insert_tac facts
                    THEN' (ripple_tac_i ctxt skelts)));


val onlyN = "only";

(* modifiers for the rippling tactic *)
val rippling_modifiers =
 [Args.add -- Args.colon >> K (I, RippleThyInfo.wrule_add_local),
  Args.del -- Args.colon >> K (I, RippleThyInfo.wrule_del_local),
  Args.$$$ onlyN -- Args.colon >> K 
           (RippleThyInfo.map_local_wrules RippleWRulesDB.clear_wrules, 
            RippleThyInfo.wrule_add_local)]


(* Note: sectioned_args first element is pre-stuff, and second is
soemthing that is gievn options plus theorem names. *)

(*
val ripplemeth_syntax =
    Method.sectioned_args ((Scan.lift (Args.$$$ "skel" -- Args.colon)) 
                             |-- Attrib.local_thms)
                          rippling_modifiers
                          ripple_meth;
*)

val ripple_skel_syntax = 
    ((Scan.optional 
        ((Scan.lift (Args.$$$ "skelts" -- Args.colon)) 
           |-- (Args.and_list1 Args.local_term))
        []) --
            (Scan.optional 
               ((Scan.lift (Args.$$$ "skels" -- Args.colon)) 
                  |-- (Args.and_list1 Attrib.local_thm))
               []));

val ripplemeth_syntax =
    Method.sectioned_args ripple_skel_syntax 
                          rippling_modifiers
                          ripple_meth;


(* val rippling_parser = 
    Method.sectioned_args 
      (Args.bang_facts -- Scan.lift rippling_options) 
      rippling_modifiers ripple_meth;  *)
(* Method.thms_ctxt_args *)

(* setup rippling method and attributes *)
val setup = 
    [Method.add_method ("rippling", ripplemeth_syntax, "Rippling")];

end;

structure RippleTac = RippleTacFun(RippleRTechn_dsum);
