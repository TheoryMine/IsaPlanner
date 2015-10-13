(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      libs/lemma_conj_ZF_data.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Date:       22 July 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Logic dependent data for the conjecturing library
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

structure FOL_LemmaConjData : LEMMA_CONJ_DATA = 
struct

fun rw_term_sides (((Const(@{const_name FOL.eq}, ty)) $ l) $ r) = SOME (l, r)
  | rw_term_sides (((Const(@{const_name FOL.iff}, ty)) $ l) $ r) = SOME (l, r)
  | rw_term_sides (((Const(@{const_name FOL.implies}, ty)) $ l) $ r) = SOME (r, l)
  | rw_term_sides (((c as Const(@{const_name Pure.imp}, ty)) $ l) $ r) = SOME (r, l)
  | rw_term_sides _ = NONE;

val mk_imp = FOLogic.mk_imp;
val mk_Trueprop = FOLogic.mk_Trueprop;
val dest_Trueprop = FOLogic.dest_Trueprop;

end;
structure LemmaConjLib = LemmaConjLibFUN(FOL_LemmaConjData);
