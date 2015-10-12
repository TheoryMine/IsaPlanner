(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/dctxtattr.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    14 Oct 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Generic extensible declarative Isar Attributes for Theorems
    (Attributes are mappings of the form: ('a, thm) -> ('a, thm))

    examples include Isar's [symetric] and [simp]
    Note symetric modifies the theorem only and simp the simpset only. 
    You can also modify both. 
*)

(* declarative, but extensible attributes, which include their context
(theory or proof.context *)
signature DCTXTATTR =
sig
type 'a T; (* type of declarative attributes *)
type 'a attrthm; (* type of a theorem with dattrs *)

val kind_of : 'a T -> SafeObject.kind (* unique kind of an attribute *)

(* pretty printing dattrs *)
val stringf_of : 'a T -> 'a -> string
val prettyf_of: 'a T -> 'a -> Pretty.T

(* attribute function we are a declarative representation of *)
val attrf_of : 'a T -> 'a Thm.attribute

(* used in the functor for making new kinds of declarartive thy attrib *)
val mk_getdataf :
    SafeObject.kind -> (SafeObject.T -> 'd) -> 'a T -> 'd option

(* make a declarative attribute object *)
val mk_dattr :
       ('a -> 'b -> Pretty.T)  (* prettyf *)
       * ('a -> 'b Thm.attribute) (* attrib f *)
       * ('a -> 'a -> bool) (* equality for objects *)
       * (SafeObject.T -> 'a) (* decoding function *)
       * ('a -> SafeObject.kind * SafeObject.T) (* encoding function  *)
       -> 'a (* data *)
       -> 'b T (* the new declarative attribute object *)

(* make a declarative attributed theorem from a list of declarative
   attributes *)
val mk_attrthm : 'a T list -> ('a * Thm.thm) -> 'a attrthm;

(* equaility based on name and dattrs *)
val attrthm_eq : ('a attrthm) * ('a attrthm) -> bool
(* name of initial theorem *)
val name_of_attrthm : ('a attrthm) -> string;
val sign_of_attrthm : ('a attrthm) -> Sign.sg;
(* parseable pretty print *)
val pretty_of_attrthm : 'a attrthm -> Pretty.T; 
(* return final result first and stages of application *)
val appl_of_attrthm : 'a attrthm -> ('a * Thm.thm)
                                    * (('a T * ('a * Thm.thm)) list);
(* get the resulting attributed theorem *)
val thm_of_attrthm : 'a attrthm -> Thm.thm;
(* initial values for attributed theorem *)
val init_of_attrthm : 'a attrthm -> ('a * Thm.thm);

end;


structure DCtxtAttr 
 :> DCTXTATTR 
= struct 

exception dattr_unnamed_thm_exp of string;

(* Note: the object data has already been given to the attrf and pretty
functions. Any modification of the data must be done through a
mechanism that updates the pretty and attrf functions appropriatly *)
datatype 'a T = dattr of { kind : SafeObject.kind, (* get the unique kind object *)
              data : SafeObject.T, (* data for this kind of attribute *)
              eq : 'a T -> bool, (* equality check with another dattr *)
              prettyf : 'a -> Pretty.T, (* pretty print this attribute *)
              attrf : 'a Thm.attribute }; (* the attribute function *)

fun kind_of (dattr rep) = #kind rep;
fun eq_of (dattr rep) = #eq rep;
fun prettyf_of (dattr rep) ctxt = (#prettyf rep) ctxt;
(* implicit attribute kind type *)
fun stringf_of da = Pretty.string_of o prettyf_of da;
fun attrf_of (dattr rep) = #attrf rep;
fun data_of (dattr rep) = #data rep;

(* create a function to get the data *)
fun mk_getdataf k decf (dattr rep) = 
    if SafeObject.eq_kind (k, #kind rep) then SOME (decf (#data rep)) 
    else NONE;
(* note: requires that kind uniquely specified data type, else we get a runtime exp *)
fun mk_eqf (kind,eqf,decf) da = 
    SafeObject.eq_kind (kind_of da, kind) andalso 
    eqf (decf (data_of da));

(* function to make a generic thy attrb, we place the data in the pretty
and attr function directly. This is not a problem as anything that
edits the data must update the prettyf and attrf also. *)
fun mk_dattr (prettyf, attrf, eqf, decf, encf) (d : 'b) = 
    let 
      val (kind, generic_d) = encf d
    in
      dattr {kind = kind, 
       data = generic_d, 
       eq = mk_eqf (kind,eqf d,decf),
       prettyf = prettyf d, 
       attrf = attrf d
      } : ('a T)
    end;


(* type for an attributed theorem in Isar, using declarative attributes *)
(* FIXME: make attribute kind data dependent on 'a as a function! *)
datatype 'a attrthm = attrthm of
                { attrv : 'a, (* initial attribute value *)
                  thm : Thm.thm, (* initial (named) theorem *) 
                  appl : ('a * Thm.thm)  (* stages of application *)
                         * (('a T * ('a * Thm.thm)) list), 
                  pretty : Pretty.T }; (* pretty type that can be re-parsed *)


fun apply_attrs [] (v,th) L = ((v,th), L)
  | apply_attrs (attr::dattrs) (v,th) L = 
    apply_attrs dattrs (attrf_of attr (v,th)) ((attr,(v,th)) :: L);

fun mk_attrthm dattrs (vthm as (v,th)) = 
     let 
       val thmname = Thm.name_of_thm th
       val _ = if thmname = "" then 
                 raise dattr_unnamed_thm_exp "mk_attrthm: cannot make a declarative attribute of an unnamed theorem."
               else ()
       val (appl as ((lastv,lastth), dattrL)) = 
           apply_attrs dattrs vthm [] in 
       attrthm {attrv = v,
                thm = th,
                appl = appl,
                pretty = Pretty.block
                           [Pretty.str (Thm.name_of_thm th),
                            Pretty.list "[" "]" 
                                        (map (fn (da, (v,thm)) => 
                                                 (prettyf_of da v)) 
                                             dattrL)]}
     end;

fun pretty_of_attrthm (attrthm d) = (#pretty d);
fun appl_of_attrthm (attrthm d) = (#appl d);
fun init_of_attrthm (attrthm d) = (#attrv d, #thm d);
fun thm_of_attrthm (attrthm d) = snd (fst (#appl d));
fun dattrs_of_attrthm dthm = (map fst o snd o appl_of_attrthm) dthm;
fun name_of_attrthm dthm = (Thm.name_of_thm o snd o init_of_attrthm) dthm;
fun sign_of_attrthm dthm = (Thm.sign_of_thm o snd o init_of_attrthm) dthm;

(* equality for lists of declarative attributes - must have the same
   number and they must be the same *)
fun attrs_eq [] [] = true
  | attrs_eq (h :: t) (h2 :: t2) = 
    eq_of h h2 andalso attrs_eq t t2
  | attrs_eq _ _ = false;

(* declarative attributed theorems are checked for equality using
their names and the kinds of attributes that are applied. Note: maybe
we should use the stricter Thm.eq rather than names...? *)
fun attrthm_eq (dthm1, dthm2) = 
    name_of_attrthm dthm1 = name_of_attrthm dthm2 andalso 
    attrs_eq (dattrs_of_attrthm dthm1) (dattrs_of_attrthm dthm2);

end;
