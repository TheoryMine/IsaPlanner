(* conj_subsume.ML *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Title:      rtechn/conj/conj_subsume.ML
    Author:     Lucas Dixon, University of Edinburgh
                ldixon@inf.ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  DESCRIPTION:

    A stack of conjectures made so far, to allow loop avoidence by checking
    when we make a new conjecture against those previously made.

    We use the subsume to mean our own custom subsumtion
    check: this is a combination of an embedding-check and a
    not-containing-a-new-constant check.
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature CONJ_SUBSUME =
sig

  (* the conjecture stack type *)
  type T

  val empty : T

  val add_term : Term.term -> T -> T

  val term_contains : Term.term -> Term.term -> bool
  val subsume_chk : T ->  Term.term -> bool

  val pretty : Proof.context -> T -> Pretty.T
end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure ConjSubsume
: CONJ_SUBSUME
= struct

structure StrInttab = Table(
  type key = string * int
  val ord = prod_ord fast_string_ord int_ord);

(* first term contains the second in some name convertable
   way. Assumes the terms are in eta-long, beta-short form *)
fun term_contains1 (Bs, FVs) (Abs(s,ty,t)) (Abs(s2,ty2,t2)) =
      if ty = ty2 then
        term_contains1 ((SOME(s,s2,ty)::Bs), FVs) t t2
      else Seq.empty

  | term_contains1 T t1 (Abs(s2,ty2,t2)) = Seq.empty

  | term_contains1 (Bs, FVs) (Abs(s,ty,t)) t2 =
    term_contains1 (NONE::Bs, FVs) t t2

  | term_contains1 T (ah $ at) (bh $ bt) =
    Seq.append (term_contains1 T ah (bh $ bt))
    (Seq.append (term_contains1 T at (bh $ bt))
                (Seq.maps (fn inT => (term_contains1 inT at bt))
                          (term_contains1 T ah bh)))

  | term_contains1 T a (bh $ bt) = Seq.empty

  | term_contains1 T (ah $ at) b =
    Seq.append (term_contains1 T ah b) (term_contains1 T at b)

  | term_contains1 T a b =
    let
      (* check to see if, w.r.t. the variable mapping, two terms are leaf
         terms and are mapped to each other. Note constants are only mapped
         to the same constant. *)
      fun same_leaf_check (T as (Bs,FVs)) (Bound i) (Bound j) =
          let
            fun aux_chk (i1,i2) [] = false
              | aux_chk (0,0) ((SOME _) :: bnds) = true
              | aux_chk (i1,0) (NONE :: bnds) = false
              | aux_chk (i1,i2) ((SOME _) :: bnds) =
                aux_chk (i1 - 1,i2 - 1) bnds
              | aux_chk (i1,i2) (NONE :: bnds) =
                aux_chk (i1,i2 - 1) bnds
          in
            if (aux_chk (i,j) Bs) then Seq.single T
            else Seq.empty
          end
        | same_leaf_check (T as (Bs,(Fs,Vs)))
                          (a as (Free (an,aty)))
                          (b as (Free (bn,bty))) =
          (case Symtab.lookup Fs an of
             SOME b2n => if bn = b2n then Seq.single T
                         else Seq.empty (* conflict of var name *)
           | NONE => Seq.single (Bs,(Symtab.update (an, bn) Fs,Vs)))
        | same_leaf_check (T as (Bs,(Fs,Vs)))
                          (a as (Var (an,aty)))
                          (b as (Var (bn,bty))) =
          if an = bn then Seq.single T else Seq.empty
(*           (case bterm_from an Vs of
             SOME b2n => if bn = b2n then [T]
                         else []
           | NONE => [(Bs,(Fs,(an,bn)::Vs))])  *)
        | same_leaf_check T (a as (Const _)) (b as (Const _)) =
          if a = b then Seq.single T else Seq.empty
        | same_leaf_check T _ _ = Seq.empty
    in
      same_leaf_check T a b
    end;

(* wrapper for term_contains1: checks if the term "a" contains in
some embedded way, (w.r.t. name -convertable) the term "b" *)
fun term_contains a b =
    case Seq.pull (term_contains1 ([],(Symtab.empty,StrInttab.empty)) a b) of
      SOME _ => true
    | NONE => false;

(* we store lots of extra that we derive from the term to avoid
having to repreat the work, but essentially everything is derived
from the term.  *)
type el = { term : Term.term, (* the term *)
            consts : TermConstLib.T, (* the constsants in term *)
            subsf : Term.term -> bool (* quick subsumes check *)
          }
type T = el list;

fun term_of_el (rep : el) = #term rep;

val empty = [] : T;

(* pretty priting, mostly for debugging *)
fun pretty_elem_term ctxt elem =
    Trm.pretty ctxt (term_of_el elem);

(* a simple function to pair with each element of a list, a number *)
fun number_list i [] = []
  | number_list i (h::t) =
    (i,h)::(number_list (i+1) t)

fun pretty ctxt cs =
    Pretty.chunks
    ([Pretty.str "Conjecture Stack:",
      Pretty.str "["] @
     (map (fn (i,c) =>
              Pretty.block
                [(Pretty.str o string_of_int) i,
                 (Pretty.str " : "),
                 ((Pretty.indent 4) o pretty_elem_term ctxt) c])
          (number_list 0 cs)) @
     [Pretty.str "]"]);

(* add a term to the conjecture stack, note doesn't do a subsume
check first, so we can end up adding redudent things -- be
careful.*)
fun add_term t cs =
    let
      val consts = TermConstLib.consts_of t
      val consts_subf = (TermConstLib.extra_const_from_term_chk consts)
      fun subsumef t2 =
          (not (consts_subf t2)) andalso term_contains t2 t
    in
      {term = t,
       consts = consts,
       subsf = subsumef} :: cs
    end;

(* check if a term in the stack subsumes the given term *)
fun subsume_chk cs t =
    let
      fun subsume_chk_aux [] t = false
        | subsume_chk_aux ((rep::cs) : T) t =
          ((#subsf rep) t) orelse (subsume_chk_aux cs t);
    in
      subsume_chk_aux cs t
    end;

end;

