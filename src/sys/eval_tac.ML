(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/eval_tac.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    1 Jun 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    The eval tactic applies (conditional) equality rules exhustively,
    from bottom-left to right-top (ML style, call by value).

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* test with: 

use_thy "sys/ind_test";
*)

(* match lhs against part of t, look for matches starting at the left, then moving up(and right only) and when reaching the top, move onto the next leaf *)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature EVAL_TAC = 
sig

(* note the int -> tactic argument is the conditions solver *)

val eval_once : ThmEvalNet.rulenet -> (int -> Tactical.tactic) -> 
                int -> Tactical.tactic
val eval_once_nth : int -> ThmEvalNet.rulenet -> (int -> Tactical.tactic) -> 
                int -> Tactical.tactic
val eval : ThmEvalNet.rulenet -> (int -> Tactical.tactic) -> 
                int -> Tactical.tactic
val eval_no_backtrack : ThmEvalNet.rulenet -> (int -> Tactical.tactic) -> 
                int -> Tactical.tactic

val unfold_nth : (Thm.thm list * int) -> int -> Tactical.tactic

end;



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure EvalTac : EVAL_TAC =
struct



fun solve_conditions_tac tac i 0 thm = Seq.single thm
  | solve_conditions_tac tac i n thm = 
    ((tac i) THEN (solve_conditions_tac tac i (n - 1))) thm;

(* try to solve conditions by assumption *)
(* fun solve_conditions_by_asm i 0 thm = Seq.single thm
  | solve_conditions_by_asm i n thm = 
    Seq.map Thm.strip_shyps 
            ((((assume_tac i) ORELSE (defer_tac i))
                THEN (solve_conditions_by_asm i (n - 1))) thm);

THEN (solve_conditions_by_asm i (Thm.nprems_of rule)))
*)


(* rewrite using a match *)
fun do_subst_in_concl dfd_tac i th substinfo (ThmEvalNet.RuleNet.match rep) =
    let
      val rule = (#data rep) 
      val nprems0 = Thm.nprems_of th
    in
      (EQSubstTac.apply_subst_in_concl 
         i th substinfo rule (#insts rep, #faketyps rep, 
                              #typs rep, #absterm rep)) 
      :-> (fn th' => solve_conditions_tac 
                       dfd_tac i ((Thm.nprems_of th') - nprems0) th')
    end;


(* IMPROVE: make more efficient avoiding fixing alls each time etc - we
can do such operations only once at the start of rewriting, then
simply repreat rewriting, cleaning up once at the end. *)
fun mk_concl_rw_seq rnet dfd_tac i gth = 
    let val (substinfo, srchinfo) = 
            EQSubstTac.prep_concl_subst i gth;
    in (ThmEvalNet.find_fcterm_unifiers srchinfo rnet) :-> do_subst_in_concl dfd_tac i gth substinfo end;

val mk_rw_seq = mk_concl_rw_seq;


(* evaluation functions *)
fun eval_once net dfd_tac i th = mk_rw_seq net dfd_tac i th;

(* unfold the nth occurance of rule *)
fun eval_once_nth nth net dfd_tac i th = 
      IsaPLib.NTH nth (fn x => mk_rw_seq net dfd_tac i x) th;

(* FIXME: cleanup to optiomise for tsig and matches *)
fun eval net dfd_tac i th = 
      Seq.flat (Seq.map (Seq.TRY (eval net dfd_tac i)) 
                        (mk_rw_seq net dfd_tac i th));

(* FIXME: cleanup to optiomise for tsig and matches *)
fun eval_no_backtrack net dfd_tac i th = 
      case Seq.pull (mk_rw_seq net dfd_tac i th) of
        NONE => Seq.single th
      | SOME (th', _) => eval_no_backtrack net dfd_tac i th';

(* unfold the nth occurance of a single rule -- unused I think *)
fun unfold_nth (rules, nth) i th = 
    let 
      val small_eval_net = 
          ThmEvalNet.new ("foo_net",EvalOrders.valid_bl_ru)
      val net = foldr ThmEvalNet.insert small_eval_net rules
    in
      IsaPLib.NTH nth (eval_once net (K Tactical.all_tac) i) th
    end;

end; (* functor *)


(* testing: 
(* *)
fun asm_mk t = (assume (cterm_of (Theory.sign_of (the_context())) t)); 
fun asm_read s =  
    (assume (read_cterm (Theory.sign_of (Context.the_context())) (s,propT))); 

val myrule = asm_read "(A :: 'a => 'c) X == B";
val (lhs,rhs) = Logic.dest_equals (Logic.strip_imp_concl (Thm.prop_of myrule));

Goal "R (A X) P A (% x. A x)";
val t = Thm.concl_of (topthm());

val fts = IsaFTerm.leaf_seq_of_fcterm (IsaFTerm.fcterm_of_term t);

val tsig = Sign.tsig_of (Thm.sign_of_thm (topthm()));
val matches = Seq.flat (Seq.map (mateches_up_from_leaf tsig lhs) fts);

Seq.list_of (Seq.map (TermLib.string_of_term o snd) matches);



term_of_fcterm

*)
