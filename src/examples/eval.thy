theory eval
imports Main IsaP
begin

lemma "[|  ?P; ~ ~ ~ ~ ~ (False) |] ==> G"
apply safe
done
apply safe

thm Nat.split

thm ssubst 
lemmas ssubst_bool = ssubst[of _ _ "%x. x"]


lemmas foo =  Nat.split[THEN ssubst_bool]

ML {* 

Seq.list_of (Safe_tac (thm "foo"));

*}

thm subst;
thm ssubst;

text{* This is a simple example of creating an evaluation set for
performing CNF conversion of formulae. The first part of this file
contains some simple definitions. *}

thm de_Morgan_disj
thm de_Morgan_conj
thm not_ex
thm not_all
thm iff_conv_conj_imp
thm imp_conv_disj

thm not_imp
thm not_iff
thm not_imp

ML {*
val cnf_eval_setup = 
  [EvalThyInfo.add_rnet_to_thy (ThmEvalNet.new("CNF", EvalOrders.bl_ru))];
*}

setup cnf_eval_setup

text{* The following ML can be used to examine the evaluations sets: *}

ML {*  EvalThyInfo.print_from_thy (the_context());  *}

text{* Initially, evaluation sets are empty. Rules can be added to
them using the "eval" attribute, as follows: *}

lemmas myrules [eval addto CNF] = 
  de_Morgan_disj de_Morgan_conj 
  not_ex not_all not_not
  iff_conv_conj_imp imp_conv_disj 
  disj_assoc conj_assoc
  disj_conj_distribL disj_conj_distribR

text{* We can now re-examine the evaluation sets to see the rules added: *}

ML {*  EvalThyInfo.print_from_thy (the_context());  *}

lemma "a = (b :: bool)"
apply (eval (in CNF))
oops

lemma "\<not> (\<forall> x. P x = ((Q x) :: bool))"
apply (eval (in CNF))
oops

end;
