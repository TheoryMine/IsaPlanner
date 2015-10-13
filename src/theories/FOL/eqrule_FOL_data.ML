(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/eqrule_FOL_data.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    18 Feb 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:
    Data for equality rules in the logic
*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure ZF_EqRuleData : EQRULE_DATA =
struct

fun mk_eq th = case concl_of th of
        Const(@{const_name Pure.eq},_)$_$_       => Some (th)
    |   _$(Const(@{const_name FOL.iff},_)$_$_) => Some (th RS iff_reflection)
    |   _$(Const(@{const_name HOL.eq},_)$_$_) => Some (th RS eq_reflection)
    |   _ => None;

val tranformation_pairs =
  [(@{const_name HOL.implies}, [mp]), (@{const_name HOL.conj}, [conjunct1,conjunct2]),
   (@{const_name HOL.All}, [spec]), (@{const_name HOL.True}, []), (@{const_name HOL.False}, [])];

(*
val mk_atomize:      (string * thm list) list -> thm -> thm list
looks too specific to move it somewhere else
*)
fun mk_atomize pairs =
  let fun atoms th =
        (case Thm.concl_of th of
           Const(@{const_name HOL.Trueprop},_) $ p =>
             (case Term.head_of p of
                Const(a,_) =>
                  (case Library.assoc(pairs,a) of
                     Some(rls) => flat (map atoms ([th] RL rls))
                   | None => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

val prep_meta_eq = 
    (mapfilter  
       mk_eq
       o (mk_atomize tranformation_pairs)
       o Drule.gen_all 
       o zero_var_indexes)

end;
structure EqRuleData = ZF_EqRuleData;

structure EQSubstTac = 
  EQSubstTacFUN(structure EqRuleData = EqRuleData);