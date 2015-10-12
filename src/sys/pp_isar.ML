(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/pp_isar.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    13 Sep 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Isar language element wrapper for performing proof planning

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure PPIsar = 
struct 

fun init_rst techn pst = 
    (RState.init_with_pp_from_ctxt 
       (Proof.context_of pst) (IsarPP.init_from_pst pst))
      |> RState.set_rtechn (SOME techn)
      |> RTechnEnv.init;

fun pptac_aux searchf rtechn pst = 
    Seq.map (PPlan.top_pst_of o RState.get_pplan) 
            (searchf (init_rst rtechn pst));

val ppdfs = pptac_aux (GSearch.depth_fs (is_none o RState.get_rtechn) RState.unfold) o DTechn.techn_of;

val ipp = pptac_aux 
            (fn rst => let val rst' = (PPInterface.ipp_rst rst) in 
                         if Library.is_none (RState.get_rtechn rst' ) then 
                           Seq.single rst' else Seq.empty end) 
          o DTechn.techn_of;

(* syntax to read declarative technique *)
fun pp_step_cmd ppf ((s, argsL),pos) pst = 
    let 
      val ctxt = Proof.context_of pst
      val dtechnsytx = TechnThyInfo.lookup_from_ctxt (s, ctxt)
      val (dm, _) = TechnThyInfo.technsyntax_of dtechnsytx (ctxt, argsL)
    in ppf dm pst end;

(* add syntax for proof planning as a direct element of the Isar langauge *)
val pptop_syntax =
  OuterSyntax.command 
    "pp" (* syntax of command *)
    "proof planing using the given technique"  (* description *)
    (OuterKeyword.tag "pp" OuterKeyword.prf_script) (* unique id? *)
    (OuterParse.position (OuterParse.xname -- OuterParse.arguments) 
                         >> (Toplevel.print oo (Toplevel.proof o ProofHistory.applys o (pp_step_cmd ppdfs))));

val ipptop_syntax =
  OuterSyntax.command 
    "ipp" (* syntax of command *)
    "interactive proof planing using the given technique"  (* description *)
    (OuterKeyword.tag "ipp" OuterKeyword.prf_script) (* unique id? *)
    (OuterParse.position (OuterParse.xname -- OuterParse.arguments) 
                         >> (Toplevel.print oo (Toplevel.proof o ProofHistory.applys o (pp_step_cmd ipp))));

val _ = OuterSyntax.add_parsers [pptop_syntax, ipptop_syntax];

end;
