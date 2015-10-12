(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      Pure/IsaPlanner/isand.ML
    ID:    $Id: gap_tac.ML 2575 2010-06-26 13:17:40Z lucasd $
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Updated:    26 Apr 2005
    Date:       6 Aug 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Tactic to inserting gaps We fix vars and tvars, and assume all
    frees to be proved universally. IDEA: add a logic specific bit to
    allow schematic vars to be exitentially quantified.
*)

signature GAPTAC = 
sig
    structure I : DMETHOD_INST where type T = DTechn.T option
    val gap_of_sugoal : int -> Thm.thm -> Thm.cterm * Thm.thm
    val gap_of_term : Sign.sg -> Term.term -> Thm.cterm * Thm.thm

    (* generic things for declarative methods *)
    val meth : DTechn.T option -> Proof.context -> Proof.method (* redudent *)
    val dmeth : DTechn.T option -> DMethod.T
    val setup : (Theory.theory -> Theory.theory) list
    val syntax : Method.src -> Proof.context -> Proof.method (* dmeth? *)
    val tac : int -> Thm.thm -> Thm.thm Seq.seq
end;


structure GapTac 
 : GAPTAC
= struct

(* TOOLS *)

(* Note: unsafe if we have are in a context with more frees than are
in t; i.e. only safe for "t ==> t" style isar goals, else we may get
accidental name capture. *)
(* returns a pair: cterm and thm *)
fun gap_of_term thry t = 
    let 
      val typv_namings = 
          map (fn ((x,s),y) => (x,TFree y))
              (IsaND.fix_tvars_to_tfrees_in_terms [] [t]);
      val t2 = Term.subst_TVars typv_namings t;
      val termv_namings = 
          map (fn ((ix,ty),y) => (ix,Free y)) 
              (IsaND.fix_vars_to_frees_in_terms [] [t2]);
      val t3 = Term.subst_vars ([],termv_namings) t2;
      val frees = map Term.dest_Free (Term.term_frees t3);
      val tfrees = Term.term_tfrees t3;
    in IsaND.assume_allified thry ([],frees) t3 end;

fun gap_of_sugoal i th = 
    gap_of_term (Thm.theory_of_thm th) 
                (List.nth (Thm.prems_of th, i - 1));

(* TACTIC *)
fun tac i th = rtac (snd (gap_of_sugoal i th)) i th;

(* METHOD *)
fun meth dtechnopt ctxt = 
    Method.METHOD (fn facts => 
                       (SkipProof.cheat_tac (ProofContext.theory_of ctxt)));
(* FIXME: below causes errors with extra hidden hyps in Isar - 
we need to throw Isar out and use a better proof representation: gproof.ML *)
(* Method.METHOD (fn facts => ALLGOALS tac); *)

(* SYNTAX *)
fun syntax src ctxt = 
    meth (TechnThyInfo.opt_dtechn_ctxt_syntax src ctxt) ctxt;

(* THEORY SETUP *)
val setup = 
    [Method.add_method ("gap", 
                        syntax, 
                        "An Proof Planning Gap")];

(* DECLARATIVE METHOD *)
structure I = 
DMethodInstFUN(
  structure K = 
  struct
    type T = DTechn.T option;
    val name = "gap";
    fun textf d ctxt = Method.Basic (meth d);
    fun prettyf dtopt ctxt = 
        Pretty.block 
          ([Pretty.str "gap"] @ 
           (case dtopt 
             of SOME dt => 
                [Pretty.str " ",
                 Pretty.enclose 
                   "(" ")" [DTechn.pretty_of dt ctxt]]
              | NONE => []));
  end)

val dmeth = I.dmeth_of;

end;