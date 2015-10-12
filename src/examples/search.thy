header{* A Theory Search as Used by IsaPlanner *}

theory search = Main:

section{* A Search Strategy *}

text {* Initial version using a triple -- I changed to using a record
as this allow snice access to the fields, and more closely reflects
the ML. *}

datatype ('n, 'a) sstrat_dt = 
     sstrat_dt "'a \<times> ('n list \<Rightarrow> 'a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> ('n \<times> 'a) option)"

consts dfs_dt :: "('n, 'n list) sstrat_dt"
defs 
dfs_dt_def: 
  "dfs_dt == sstrat_dt ([], (\<lambda> ns a. ns @ a),
                 (\<lambda> a. case a of [] \<Rightarrow> None | (h#t) \<Rightarrow> Some(h,t)))";

text {* Easier to read and manipulate using a record. Note we cannot
use the field empty, as this causes some kind of nasty conflict with
some other theory. It seems that there is aproblem with overloading
constants from a previous theory in the use of records. *}

record ('n, 'a) sstrat = 
  agenda :: "'a" 
  addf :: "'n list \<Rightarrow> 'a \<Rightarrow> 'a"
  popf :: "'a \<Rightarrow> ('n \<times> 'a) option"

consts depthfs :: "('n, 'n list) sstrat"
defs
depthfs_def: 
  "depthfs == 
    \<lparr> agenda = [], 
      addf = (\<lambda> ns a. ns @ a),
      popf = (\<lambda> a. case a of [] \<Rightarrow> None | (h#t) \<Rightarrow> Some(h,t)) \<rparr>";

text {* A record to hold the state of search *}

record ('n, 'a) onesearch = 
  onegf :: "('n \<Rightarrow> bool)"
  onexf :: "('n \<Rightarrow> 'n list)"
  oneagenda :: "'a" 
  oneadd :: "'n list \<Rightarrow> 'a \<Rightarrow> 'a"
  onepop :: "'a \<Rightarrow> ('n \<times> 'a) option"

text {* A function to step through a single search strategy. *}

consts one_search_step :: 
  "('n, 'a) onesearch \<Rightarrow> ((('n option) \<times> ('n, 'a) onesearch) option)"
defs 
  one_search_step_def: 
  "one_search_step == (\<lambda> s. 
    case ((onepop s) (oneagenda s))
      of None \<Rightarrow> None
       | (Some (n,a)) \<Rightarrow> Some (if (onegf s n) then (Some n) else None, 
                               s \<lparr> oneagenda := a \<rparr> ))"

text {* Note: to actually search we need a possibly infinite number of
unfoldings of the serach. This means that to actually perform search
requires a tactic. This is exactly what we want as we can still reason
about search and the contents of the search space within Isabelle. A
logic of terminating functions pushes evaluation of non-termination to
the level of a tactic. But proofs are still within the logic, you just
have to specify a counter. Of course this essentially makes all
non-terminating functions equivalent. If you want to reason about
streams I need to think more about it, or use one of the other
extensions of HOL. *}

consts onesearch_sol_in_n :: "('n, 'a) onesearch \<Rightarrow> nat \<Rightarrow> bool"
primrec
onesearch_has_sol_0:  "onesearch_sol_in_n s 0 = False"
onesearch_has_sol_Suc: 
"onesearch_sol_in_n s (Suc n) =
  (case (one_search_step s) 
    of None \<Rightarrow> False 
     | (Some (nopt, s2)) \<Rightarrow> (case nopt of (Some x) \<Rightarrow> True
                                       | None \<Rightarrow> onesearch_sol_in_n s2 n))"

consts onesearch_has_sol :: "('n, 'a) onesearch \<Rightarrow> bool"
defs 
onesearch_has_sol_def: 
"onesearch_has_sol == \<lambda> s. (\<forall> n. (onesearch_sol_in_n s n))"
  
text {* Note that we need to use an exttra option in order for
Isabelle to accept that the type is not empty. The first function is
the add nodes function and the second one is the pop node
function. Together these abstractly define a search strategy. *}


datatype 'a seq = seq "unit \<Rightarrow> ('a  * 'a seq) option"

consts 
  seqf_of :: "'a seq \<Rightarrow> unit \<Rightarrow> ('a  * 'a seq) option"
primrec 
  "seqf_of (seq f) = f"

text {* Note, we have to use recdef as primrec and def don't allow
this def, as they consider that it may be dangerours. *}

text {* Sequence of infinite zeros *}

consts 
  seq0_aux :: "unit \<Rightarrow> ('a  * 'a seq) option"
recdef seq0_aux "measure size"
  "seq0_aux () = Some (0 :: nat, seq seq0_aux)"
constdefs seq0 :: "nat seq"
seq0_def: "seq0 == seq seq0_aux"

text {* Sequence of increasing nats *}

consts 
  seqN_aux :: "nat * unit \<Rightarrow> ('a  * 'a seq) option"
recdef seqN_aux "measure (size o snd)"
  seqN_aux: "seqN_aux (n, ()) = Some (n, seq (curry seqN_aux (Suc n)))"
constdefs seqN :: "nat seq"
seqN_def: "seqN == seq (curry seqN_aux 0)"

thm seqN_aux_def

text {* Now back to my search trees *}

consts getInl :: "'a + 'b \<Rightarrow> 'a"
consts getInr :: "'a + 'b \<Rightarrow> 'b"
defs 
getInl_def: "getInl == sum_case (\<lambda> x. x) (\<lambda> x. arbitrary)"
getInr_def: "getInr == sum_case (\<lambda> x. arbitrary) (\<lambda> x. x)"

datatype 'n search_st = 
search_st "('n list \<Rightarrow> 'n search_st option) 
           \<times> (unit \<Rightarrow> ('n \<times> 'n search_st) option)"

text {* Note the use of an extra unit in order to allow termination -
ie claim that the function recurses on unit -- the problem is that I
want lazy, mutual recursive functions. Mutual recurssion in thi way
does not support lasyness, as this requires that the recursion is
applied to less arguments, and we wan't do this becasue *}

consts addpop_ :: 
  "((('n, 'a) sstrat) \<Rightarrow> 'n list \<Rightarrow> (('n search_st) option)) 
     + (('n, 'a) sstrat \<Rightarrow> unit \<Rightarrow> (('n \<times> 'n search_st) option))
       \<Rightarrow> (('n search_st) option) + (('n \<times> 'n search_st) option)"

term "wfrec"
term "wfrec (measure (sum_case (size o getInl) (size o getInr)))"
ML {* set show_types; *}
lemma not_all_lengths_are_equal: "(\<forall> n2 n. length n2 < length n) = False"
proof 
  assume a[rule_format]: "\<forall> (n2 :: 'a list) (n :: 'b list). length n2 < length n"
  {fix h :: 'a and t :: "'a list"
(*   from a have "length (h # t) < length []" by rule  *)
   note a[of "(h # t)" "[] :: 'b list"]}
  thus "False" by simp
next 
  assume "False"
  thus "\<forall>(n2\<Colon>'a list) n\<Colon>'b list. length n2 < length n" by rule
qed

recdef (permissive) addpop_ "measure (sum_case (size o snd) (size))"
  "addpop_ (Inl (s, nds)) = 
     (\<lambda> a2. Inl (Some (search_st (\<lambda> nds. getInl (addpop_ (Inl (s \<lparr> agenda := a2 \<rparr>, nds))), 
                             \<lambda> u. getInr (addpop_ (Inr (s \<lparr> agenda := a2 \<rparr>)))))))
            ((addf s) nds (agenda s))"
  "addpop_ (Inr (s)) = 
    (case ((popf s) (agenda s))
       of None \<Rightarrow> Inr None
        | Some (n, a2) \<Rightarrow> 
          Inr (Some (n, search_st (\<lambda> nds. getInl (addpop_ (Inl (s \<lparr> agenda := a2 \<rparr>, nds))), 
                              \<lambda> u. getInr (addpop_ (Inr (s \<lparr> agenda := a2 \<rparr>)))))))"

consts 
  st_add_nodes :: 
    "(('n, 'a) sstrat)
     \<Rightarrow> 'n list 
     \<Rightarrow> (('n search_st) option)"
  st_pop_node  :: 
    "('n, 'a) sstrat
     \<Rightarrow> unit
     \<Rightarrow> (('n \<times> 'n search_st) option)"
defs
 st_pop_node_def:
  "st_pop_node == wfrec {} (\<lambda> st_pop_node s u.
    (case ((popf s) (agenda s))
       of None \<Rightarrow> None
        | Some (n, a2) \<Rightarrow> Some (n, search_st (st_add_nodes (s \<lparr> agenda := a2 \<rparr>), 
                                              st_pop_node (s \<lparr> agenda := a2 \<rparr>)))))"
st_add_node_def:
   "st_add_nodes == wfrec {} (\<lambda> st_add_nodes s nds.
     ((\<lambda> a2. Some (search_st (st_add_nodes (s \<lparr> agenda := a2 \<rparr>), 
                              st_pop_node (s \<lparr> agenda := a2 \<rparr>))))
            ((addf s) nds (agenda s))))"


thm st_pop_node_def

consts 
  st_add_nodes :: 
    "(('n, 'a) sstrat * unit)
     \<Rightarrow> 'n list 
     \<Rightarrow> (('n search_st) option)"
  st_pop_node  :: 
    "(('n, 'a) sstrat * unit)
     \<Rightarrow> (('n \<times> 'n search_st) option)"

thm lfp_unfold
term lfp
term wfrec


defer_recdef st_pop_node
  "st_pop_node (s, ()) =
    (case ((popf s) (agenda s))
       of None \<Rightarrow> None
        | Some (n, a2) \<Rightarrow> Some (n, search_st (st_add_nodes (s \<lparr> agenda := a2 \<rparr>, ()), 
                                              curry st_pop_node (s \<lparr> agenda := a2 \<rparr>))))"
defer_recdef st_add_nodes
  "st_add_nodes (s,()) = 
     (\<lambda> nds.
     ((\<lambda> a2. Some (search_st (st_add_nodes (s \<lparr> agenda := a2 \<rparr>, ()), 
                              curry st_pop_node (s \<lparr> agenda := a2 \<rparr>)))) 
            ((addf s) nds (agenda s))))"

term 
"measure (size o snd)"


record  

consts 
  st_add_nodes :: 
    "('n list \<Rightarrow> 'a \<Rightarrow> 'a) 
     \<Rightarrow> ('a \<Rightarrow> ('n \<times> 'a) option) 
     \<Rightarrow> 'a 
     \<Rightarrow> unit
     \<Rightarrow> 'n list 
     \<Rightarrow> (('n search_st) option)"
  st_pop_node  :: 
    "('n list \<Rightarrow> 'a \<Rightarrow> 'a) 
     \<Rightarrow> ('a \<Rightarrow> ('n \<times> 'a) option) 
     \<Rightarrow> 'a 
     \<Rightarrow> unit 
     \<Rightarrow> (('n \<times> 'n search_st) option)"

recdef st_pop_node "measure "
  "st_pop_node == \<lambda> addf popf a u. 
    (case (popf a) 
       of None \<Rightarrow> None
        | Some (n, a2) \<Rightarrow> Some (n, search_st (st_add_nodes addf popf a2, 
                                              st_pop_node addf popf a2)))"
  "st_add_nodes addf popf a nds = 
     (\<lambda> a2. Some (search_st (st_add_nodes addf popf a2, st_pop_node addf popf a2))) 
            (addf nds a)"
  "st_pop_node addf popf a u = None"

term 
"
     (case (popf a) 
       of None \<Rightarrow> None
        | Some (n, a2) \<Rightarrow> Some (n, search_st (st_add_nodes addf popf a2, 
                                              st_pop_node addf popf a2)))"



term

(* would be nice to have recrods within the datatype package, thus allowing 
   recursive records. You can probably currently do this by hand,
   making a polymorphic record and instantiating with with the
   datatype within the datatype definition. *)

record 'n search_st = 
  addnds_st :: "'n list \<Rightarrow> 'n search_st"
  popnd_st :: "unit \<Rightarrow> ('n \<times> 'n search_st) option"

types search_st = "('n list \<Rightarrow> 'n search_st) \<times> (unit \<Rightarrow> ('n \<times> 'n search_st) option)"


end;
