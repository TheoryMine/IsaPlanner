(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/dattr.ML
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

(* declarative, but extensible attributes *)
signature DATTR =
sig
type 'a T; (* type of declarative attributes *)
type 'a attrthm; (* type of a theorem with dattrs *)

val kind_of : 'a T -> Object.kind (* unique kind of an attribute *)

(* pretty printing dattrs *)
val stringf_of : 'a T -> 'a -> string
val prettyf_of: 'a T -> 'a -> Pretty.T

(* attribute function we are a declarative representation of *)
val attrf_of : 'a T -> 'a Thm.attribute

(* used in the functor for making new kinds of declarartive thy attrib *)
val mk_getdataf :
    Object.kind -> (Object.T -> 'd) -> 'a T -> 'd option

(* make a declarative attribute object *)
val mk_dattr :
       ('a -> 'b -> Pretty.T) *  (* prettyf *)
       ('a -> 'b Thm.attribute) * (* attrib f *)
       ('a -> Object.kind * Object.T) -> (* encoding function  *)
       'a -> (* data *)
       'b T (* the new declarative attribute object *)

(* make a declarative attributed theorem from a list of declarative
   attributes *)
val mk_attrthm : 'a T list -> ('a * Thm.thm) -> 'a attrthm;

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


structure DAttr :> DATTR = 
struct 

exception dattr_unnamed_thm_exp of string;

(* Note: the object data has already been given to the attrf and pretty
functions. Any modification of the data must be done through a
mechanism that updates the pretty and attrf functions appropriatly *)
type 'a T = { kind : Object.kind, (* get the unique kind object *)
              data : Object.T, (* data for this kind of attribute *)
              prettyf : 'a -> Pretty.T, (* pretty print this attribute *)
              attrf : 'a Thm.attribute }; (* the attribute function *)

fun kind_of {kind, ...} = kind;
fun prettyf_of {prettyf, ...} ctxt = prettyf ctxt;
(* implicit attribute kind type *)
fun stringf_of dattr = Pretty.string_of o prettyf_of dattr;
fun attrf_of {attrf, ...} = attrf;
(* create a function to get the data *)
fun mk_getdataf k decf {kind, data, ... } = 
    if Object.eq_kind (k, kind) then SOME (decf data) 
    else NONE;

(* function to make a generic thy attrb, we place the data in the pretty
and attr function directly. This is not a problem as anything that
edits the data must update the prettyf and attrf also. *)
fun mk_dattr (prettyf, attrf, encf) (d : 'b) = 
    let 
      val (kind, generic_d) = encf d
    in
      {kind = kind, 
       data = generic_d, 
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
                                        (map (fn (dattr, (v,thm)) => 
                                                 (prettyf_of dattr v)) 
                                             dattrL)]}
     end;

fun pretty_of_attrthm (attrthm d) = (#pretty d);
fun appl_of_attrthm (attrthm d) = (#appl d);
fun init_of_attrthm (attrthm d) = (#attrv d, #thm d);
fun thm_of_attrthm (attrthm d) = snd (fst (#appl d));

end;


(* the kind of a declarative attribute must have these things... *)
signature DATTR_KIND =
sig

type attrv
type T

val attrf : T -> attrv Thm.attribute
val prettyf : T -> attrv -> Pretty.T
val name : string

end;


(* to get an instance of a declarative attribute kind *)
signature DATTR_INST =
sig

type attrv
type T

val kind : Object.kind

val dattr_of : T ->  attrv DAttr.T
val data_of : attrv DAttr.T -> T option

end;


functor DAttrInstFUN (structure K : DATTR_KIND)
        : DATTR_INST = 
struct

val kind = Object.kind K.name;

type attrv = K.attrv;
type T = K.T;

local 
  exception Data of T;
  fun decf (Data x) = x
  fun encf d = (kind, Data d)
in

(* implicit extra arg: DThyAttr.T *)
val data_of = DAttr.mk_getdataf kind decf;

(* implicit extra arg: T *)
val dattr_of = DAttr.mk_dattr (K.prettyf, K.attrf,encf);

end; (* local *)

end; (* DAttrInstFUN *)