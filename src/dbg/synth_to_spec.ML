(* ------------- EXAMPLE SET 1 ------------- *)
(*   stuff in Main   *)
print_depth 100;
structure Synthesis = ConstrSynthesis;

(* synthesis of "?x = ?y" *)
val thy = Theory.begin_theory "test" [theory "Main", theory "IsaP"];
val (cs, thy) = Constraints.mk_const_infos_ac thy; 
val _ = Constraints.Constant.NTab.print (K (Pretty.str "...")) cs;
val rst0 = RstPP.init thy;

(* ------------- EXAMPLE 1.1 ------------- *)
(*  "?x = ?y" *)

(* create initial constant info for synthesis *)
val t = RstPP.read_top_term rst0 ("?x = ?y");

(* initial synthesis setup *)
val s0 = Synthesis.init_any_sterm thy cs 14 4;
val _ = Synthesis.print_sterm s0;

(* synthesised things... *)
val l = Seq.list_of (Synthesis.synthesise_upto_given_term 
                       thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0);
val it = length l;
val _ = map Synthesis.print_sterm l;


(* ------------- EXAMPLE 1.2 ------------- *)
(*  "x = y" <= FAILS: cannot have fresh var on rhs of eq 
    Synthesis.VarAllowed.is_hole_in_lhs restricts this. 
*)

(* create initial constant info for synthesis *)
val t = RstPP.read_top_term rst0 ("x = ?y");

(* initial synthesis setup *)
val s0 = Synthesis.init_any_sterm thy cs 3 4;
val _ = Synthesis.print_sterm s0;
val (SOME s) = Synthesis.update_as_instance_of_term thy t s0;

(* instantiate to make "?h1 = ?h2" *)
val Synthesis.ProgressSynth ss = Synthesis.synthesise_1step thy Synthesis.VarAllowed.is_hole_in_lhs cs s;
val [s] = Seq.list_of ss;
val (SOME s) = Synthesis.update_as_instance_of_term thy t s;

(* instantiate to make "a = ?h2" *)
val Synthesis.ProgressSynth ss = Synthesis.synthesise_1step thy Synthesis.VarAllowed.is_hole_in_lhs cs s;
val [s] = Seq.list_of ss;
val (SOME s) = Synthesis.update_as_instance_of_term thy t s;

(* instantiate to make "a = b" *)
val Synthesis.ProgressSynth ss = Synthesis.synthesise_1step thy Synthesis.VarAllowed.is_hole_in_lhs cs s;
val [] = Seq.list_of ss;
(* Synthesis stops *)


(* ------------- EXAMPLE 1.3 ------------- *)
(*  "?x = ?y" *)

(* create initial constant info for synthesis *)
val t = RstPP.read_top_term rst0 ("x = ?y");

(* initial synthesis setup *)
val s0 = Synthesis.init_any_sterm thy cs 3 4;
val _ = Synthesis.print_sterm s0;

(* synthesised things... *)
val [s2] = Seq.list_of (Synthesis.synthesise_upto_given_term 
                       thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0);
val _ = Synthesis.print_sterm s2;

(* Note: fails is you try to synth a larger size term... *)
val s0 = Synthesis.init_any_sterm thy cs 14 4;
val [] = Seq.list_of (Synthesis.synthesise_upto_given_term 
                       thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0);


(* ------------- EXAMPLE SET 2 ------------- *)
(*  on fold theory with no type vars... *)
use_thy "benchmarks/synth_theories/List_fold2";
val thy = theory "List_fold2"; 
val (cs, thy) = Constraints.mk_const_infos_ac thy; 
val _ = Constraints.Constant.NTab.print (K (Pretty.str "...")) cs;
val rst0 = RstPP.init thy;
val s0 = Synthesis.init_any_sterm thy cs 14 4;

val t = RstPP.read_top_term rst0 "foldl ?f (foldl ?f ?a ?l) ?l2 = foldl ?f ?a (?l @ ?l2)";

val [st] = (Seq.list_of (Synthesis.synthesise_upto_given_term
                          thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0));

Synthesis.print_sterm st;

(* BUG HERE: *)
(* should give back singleton! but gives back empty list *)

val t = RstPP.read_top_term rst0 "foldl f (foldl f a l) l2 = foldl f a (l @ l2)";
val [st] = (Seq.list_of (Synthesis.synthesise_upto_given_term
                          thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0));

val _ = (Seq.list_of (Synthesis.dbg_synthesise_upto_given_term 
                        thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0));

Synthesis.print_sterm st;





(* BUG HERE: *)
val t = RstPP.read_top_term rst0 "foldl f (foldl f a l) ?l2 = foldl f a (l @ ?l2)";

(* should give back singleton! but gives back empty list *)
val [st] = (Seq.list_of (Synthesis.synthesise_upto_given_term
                          thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0));

Synthesis.print_sterm st;



(* some generic theory generation... *)

(* Generate the one theorem you find before the big one about fold,
    get a new constant-info. *)
val ((cs,thy), _) = Synthesis.synth_w_stats (3,7) 3 thy cs;

(* Run again on size 14. This takes a while unless you do that filtering thing because it's lots of things to counter-example check *)
val ((cs,thy), _) = Synthesis.synth_w_stats (3,15) 4 thy cs; 
