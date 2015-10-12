(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/basics/prf_morph_net.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Modified:   9 Apr 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A net of terms for unifictaion and matching with functions that
    manipulate the proof plan.

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature PRF_MORPH_DATA = 
sig

type T 

val pat_of : T -> Term.term
val ienv_of : T -> InstEnv.T
val prff : T -> Prf.T -> Prf.gname -> Zipper.T 
           -> ((Prf.gname list (* new derived facts *)
                * Prf.gname list) (* new subgoals *)
               * Prf.T) Seq.seq
val eq : T * T -> bool
val pretty : Proof.context -> T -> Pretty.T

end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature PRF_MORPH_NET = 
sig

structure MData : PRF_MORPH_DATA

type T

val empty : T
val insert : MData.T * T -> T
val delete : MData.T * T -> T
val merge : T * T -> T
val pretty : Proof.context -> T -> Pretty.T
val print : Proof.context -> T -> unit
val dest : T -> MData.T list

(* matching and unification to find manipulations in the net. *)
val matchings :
    T (* using this morph net *)
    -> Prf.T  (* in this prf *)
    -> Prf.gname -> Zipper.T (* result and ziper in it *)
    -> MData.T Seq.seq 

val unifyings :
    T -> Prf.T -> Prf.gname -> Zipper.T 
    -> MData.T Seq.seq

val apply_matchings :
    T (* using this morph net *)
    -> Prf.T  (* in this prf *)
    -> Prf.gname -> Zipper.T (* result and ziper in it *)
    -> (MData.T * 
        ((Prf.gname list 
          * Prf.gname list) 
         * Prf.T)) Seq.seq 

val apply_unifyings :
    T -> Prf.T -> Prf.gname -> Zipper.T 
    -> (MData.T * 
        ((Prf.gname list 
          * Prf.gname list) 
         * Prf.T)) Seq.seq

end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
functor PrfMorphNetFUN (MData : PRF_MORPH_DATA)
   : PRF_MORPH_NET
= struct

(* evaldata is the kind of data held in the eval net *)
structure MData = MData; 

type T = MData.T Net.net;

val eq = MData.eq;

(* basic operations *)
fun insert (k, net) = 
    let val t = MData.pat_of k in 
      Net.insert_term eq (t, k) net 
      handle Net.INSERT => 
             (* when the same thing is inserted twice, do nothing but warn user *)   
             (tracing "WARNING: you tried to insert the same thing twice!"; net)
    end;
fun delete (k, net) = 
    let val t = MData.pat_of k in Net.delete_term eq  (t, k) net end;
val empty = Net.empty : T;
fun merge (n1, n2) = Net.merge eq (n1,n2);
(* dest: implicit Net.net, gives back MData.T list *)
val dest = Net.entries;

(* pretty printing *)
fun pretty ctxt = Pretty.chunks o map (MData.pretty ctxt) o dest;
val print = Pretty.writeln oo pretty;


(* find possibly matching/unifying morphisms 
   and try to apply them at this point in the zipper. *)
fun matchings net prf n z = 
    Seq.filter (fn d => case Seq.pull (MData.prff d prf n z) 
                         of NONE => false
                          | SOME _ => true)
               (Seq.of_list (Net.match_term net (Zipper.trm z)));

fun apply_matchings net prf n z = 
  Seq.maps (fn d => Seq.map (pair d) (MData.prff d prf n z))
           (Seq.of_list (Net.match_term net (Zipper.trm z)));

fun unifyings net prf n z = 
    Seq.filter (fn d => case Seq.pull (MData.prff d prf n z) 
                         of NONE => false
                          | SOME _ => true)
               (Seq.of_list (Net.unify_term net (Zipper.trm z)));

fun apply_unifyings net prf n z = 
  Seq.maps (fn d => Seq.map (pair d) (MData.prff d prf n z))
           (Seq.of_list (Net.unify_term net (Zipper.trm z)));


end; (* functor *)
