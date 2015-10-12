(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/skip_meth.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    21 Dec 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A Tactic to skip the proof (uses tactic provded by sorry - 
    skip_proof.ML)

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* the signature of an instance of the RW step tactic *)
signature SKIP_METH = 
sig
val cheat_tac' : Proof.context -> Tactical.tactic
val meth : Proof.context -> Proof.method
val setup : (Context.theory -> Context.theory) list
end;


structure SkipMeth
: SKIP_METH
= struct

val cheat_tac' = SkipProof.cheat_tac o ProofContext.theory_of;

val meth = Method.SIMPLE_METHOD o cheat_tac';

val setup = 
    [Method.add_method ("skip", Method.ctxt_args meth, "Skip the proof - method version of sorry")];

end;
