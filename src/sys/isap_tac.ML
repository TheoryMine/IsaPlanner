(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/isap_tac.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    18 Feb 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Auxillary tactics and thm tools used by IsaPlanner
*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature ISAP_TAC = 
sig

  (* general exception *)
  exception isap_tac_exp of string

  (* introspection *)
  val frees_of_thm : Thm.thm -> Term.term list
  val find_free_typ : (string * Term.typ) list -> string -> Term.typ
  val lookup_free_typs : string list -> Thm.thm -> (string * Term.typ) list

  (* assertion of properties *)
  val assert_unique_free_names : string list -> Thm.thm -> Thm.thm

  (* changing variable representation *)
  val frees_to_alls : (string * Term.typ) list -> Thm.thm -> Thm.thm
  val named_frees_to_alls : string list -> Thm.thm -> Thm.thm

  val vars_to_frees : ((string * int) * Term.typ) list -> Thm.thm -> Thm.thm
  val vars_to_frees_unsafe : ((string * int) * Term.typ) list -> Thm.thm -> Thm.thm
  val vars_to_alls : ((string * int) * Term.typ) list -> Thm.thm -> Thm.thm

  
  (* renaming tactics *)
  val rename_frees : (string * string) list -> Thm.thm -> Thm.thm

  (* give a theorem which is the sgi ==> sgi, where sgi is the subgoal i. *)
  val unhidehyps_sg_of : Thm.thm -> int -> Thm.thm 
  val unhidehyps_thm_of : Thm.thm -> Thm.thm 

end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure IsaPTac : ISAP_TAC= 
struct 

exception isap_tac_exp of string;

(* all used frees in the theorem, including those in the hidden
   assumptions (the thm hyps). *)
(* Thm.thm -> Term.term list *)
val frees_of_thm = (OldTerm.term_frees o prop_of o implies_intr_hyps);

(* given the frees in (string, typ) form, find the type of the free named n *)
(* (string * Term.typ) list -> string -> string * Term.typ *)
fun find_free_typ frees n = 
    case Library.find_first (fn x => fst x = n) frees of 
      NONE => raise isap_tac_exp ("lookup_free_typs: free " ^ n ^ 
                                  "does not exist in term")
    | SOME (n,ty) => ty;

(* lookup the the types of the names from free variabls in the term *)
(* string list -> Thm.thm -> (string * Term.typ) list *)
fun lookup_free_typs names th = 
    let val frees = (map Term.dest_Free (frees_of_thm th))
    in map (fn n => (n, find_free_typ frees n)) names end;

(* convert frees to meta level univ quantifierd varaibles. Note this 
   will raise an exception if the free variable occurs inside the thm 
   hyps *)
(* (string * Term.typ) list -> Thm.thm -> Thm.thm *)
fun frees_to_alls fvs th =                             
    forall_intr_list (map ((Thm.cterm_of (Thm.theory_of_thm th)) o Free) fvs) th;

(* given just the free's name convert it to a meta univ quantified variable *)
(* string list -> Thm.thm -> Thm.thm *)
fun named_frees_to_alls fvs th =
    let val frees = map dest_Free ((OldTerm.term_frees o prop_of) th)
    in frees_to_alls (map (fn n => (n, find_free_typ frees n)) fvs) th end;

(* asserts that the names are not used by any free variables in the term *)
(*  string list -> Thm.thm -> Thm.thm *)
fun assert_unique_free_names names th = 
    let 
      val frees = map (fst o Term.dest_Free) (frees_of_thm th)
    in
      case Library.find_first (fn n => n mem frees) names of 
            NONE => th
          | (SOME n2) => raise isap_tac_exp 
            ("assert_unique_free_names: " ^ n2 
             ^ " already exists as a free variable in thm")
    end;

fun mk_var_to_free_subst ctermify ((n,0),ty) = 
    (ctermify (Var((n,0),ty)), ctermify (Free(n,ty)))
  | mk_var_to_free_subst ctermify ((n,i),ty) = 
    (ctermify (Var((n,i),ty)), ctermify (Free(n ^ (string_of_int i),ty)));

(* Safe version, checks that introduced free variables have a unique
   name *)
(* ((string * int) * Term.typ) list -> Thm.thm -> Thm.thm *)
fun vars_to_frees vs th = 
    let 
      val freenames = map (fst o Term.dest_Free) (frees_of_thm th)
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
      val insts = map (mk_var_to_free_subst ctermify) vs
    in
      th |> assert_unique_free_names freenames
         |> Thm.instantiate ([], insts)
    end;

(* unsafe version, introduced variables may conflict with an existing
   free variable *)
(* ((string * int) * Term.typ) list -> Thm.thm -> Thm.thm *)
fun vars_to_frees_unsafe vs th = 
    let 
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
      val insts = map (mk_var_to_free_subst ctermify) vs 
    in
      Thm.instantiate ([], insts) th
    end;


(* change the vars given to be quantified by alls *)
(* ((string * int) * Term.typ) list -> Thm.thm -> Thm.thm *)
fun vars_to_alls vs th = 
    let 
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
      val insts = map (ctermify o Var) vs 
    in
      Drule.forall_intr_list insts th
    end;



(* convert meta level univ quantified vars into schematic variables *)
(* 
fun alls_to_vars vs th = forall_elim_list 
fun alls_to_frees fvs th = forall_elim_list 
fun frees_to_vars th = forall_elim_list
*)


(* Renames frees in a thm by first exporting the frees to meta level
   univerally quantified variables, and then instantiating them again. *)
(* Notes: frees must not occur in a thm's hidden hyps *)
(*  (string * string) list -> Thm.thm -> Thm.thm  *)
fun rename_frees namechanges th = 
    let 
      val frees = (map Term.dest_Free (frees_of_thm th))
      val typed_name_changes = 
          map (fn (n1,n2) => let val ty = find_free_typ frees n1 in
                               ((n1,ty),(n2,ty)) end)
              namechanges
      val (fromfrees, tofrees) = Library.split_list typed_name_changes
      val alls_thm = frees_to_alls fromfrees th
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
    in 
      forall_elim_list (map (ctermify o Free) tofrees) alls_thm
    end;


(* Creates a version of the theorem "th" that doesn't have the
previous hidden hyps. Instead it assumes a version of the goal/th with
meta vars replaced by meta level universally quantified vars. *) 
(* This is way of being able to assume thms with meta vars, by
assuming that the vars are meta level universally quantified
varaiables. *)

(* assumes that "th" has been zero_var_indexes. *)
(* for a thm of the form: 
Given thm: "[| ... SGi ?v; ... |] ==> G"
Results in thm:  "SGi ?v"  [!!v. SGi v]
*)
fun unhidehyps_sg_of th i = 
    let 
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
      val sgt = List.nth (Thm.prems_of th, i - 1)
      val vars = (OldTerm.term_vars sgt)
      val vars_ix = map Term.dest_Var vars 
      fun abs (a as ((n,i), ty), t) = 
          Abs(n, ty, abstract_over (Var a,t))
      val sgt' = foldr abs sgt vars_ix
      val ctvars = map ctermify vars
    in
       forall_elim_list ctvars (Thm.assume (ctermify sgt'))
    end;


(* assumes that "th" has been zero_var_indexes. *)
(* 
Given thm: "A ?v; ==> C ?v"
Results in thm:  "A ?v; ==> C ?v"  [!!v. A v ==> C v]
*)
fun unhidehyps_thm_of th = 
    let 
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
      val t = prop_of th
      val vars = (OldTerm.term_vars t)
      val vars_ix = map Term.dest_Var vars 
      fun abs (a as ((n,i), ty), t) = 
          Abs(n, ty, abstract_over (Var a,t))
      val t' = foldr abs t vars_ix
      val ctvars = map ctermify vars
    in
       forall_elim_list ctvars (Thm.assume (ctermify t'))
    end;


end; (* struct *)
