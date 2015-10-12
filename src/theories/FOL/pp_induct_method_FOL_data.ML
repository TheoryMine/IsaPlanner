(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/pp_induct_method_FOL_data.ML
    Author:     Markus Wenzel, TU Muenchen
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Edited:     13 July 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

data for HOL logic for my induction tactic.

*)

(* To be moved to the theory *)
structure PPInductMethod = PPInductMethodFun(
struct
    val spec = (Goals.thm "FOL.spec")
    fun spec_tac v i = 
        res_inst_tac [("x",v)] 
                     (RWTools.rename_thm_bvars [("x",v)] spec) i;

    val unspec = (Goals.thm "FOL.allI")
    fun unspec_tac v i = rtac unspec i;

    val dest_concls = HOLogic.dest_concls;
    val cases_default = Goals.thm "case_split";
    val local_impI = Goals.thm "induct_impliesI";
    val conjI = Goals.thm "conjI";
    val atomize = Goals.thms "induct_atomize";
    val rulify1 = Goals.thms "induct_rulify1";
    val rulify2 = Goals.thms "induct_rulify2";
    val localize = [Thm.symmetric (Goals.thm "induct_implies_def")];
end
);