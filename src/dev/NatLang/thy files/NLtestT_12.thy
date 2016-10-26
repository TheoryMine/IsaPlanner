theory T_12
imports IsaP 
uses "../myrippling.ML" "../nlproof.ML"
begin

datatype "T_12" =  "C_24" "Nat.nat"  | "C_23" "T_12" "HOL.bool"  
declare nat.inject[wrule]

fun f_4 :: "T_12 => nat => nat" where
  "f_4 (C_24 a) b = Suc (Suc (Suc (Suc b)))"
| "f_4 (C_23 a b) c = Suc (f_4 a (f_4 a c))"

declare f_4.simps[wrule]

ML{* val rst = my_rippling @{context} ["f_4 a (f_4 b c) = f_4 b (f_4 a c)"] *}

ML{* val k = NLProof.nlproof_init rst;
 NLProof.print k *}
ML{* val htr0 = rst |> RState.get_cinfo 
                    |> HTraceCInfo.I.get_from_cinfo *}
ML{* val htr1 =  htr0 |> HTraceCInfo.get_from_trace  *}
ML{* val htr = htr1 |> fst |> hd *}
ML{* val k1 = NLProof.toggle_expandability [0] k;
NLProof.print k1*}
ML{* val k2 = NLProof.toggle_expandability [0,3] k1;
NLProof.print k2*}
ML{* val k3 = NLProof.toggle_expandability [0,3,2] k2;
NLProof.print k3*}





















































































































































































































































































































































































































































































































































































































































ML{* val k = NLProof.nlproof_init full_prf tree;
 NLProof.print k *}
ML{* val k1 = NLProof.toggle_expandability [0] k;
NLProof.print k1*}
ML{* val k2 = NLProof.toggle_expandability [0,3] k1;
NLProof.print k2*}
ML{* val k3 = NLProof.toggle_expandability [0,3,2] k2;
NLProof.print k3*}
ML{* val k4 = NLProof.toggle_expandability [0,2,0] k3;
NLProof.print k4*}
ML{* val k5 = NLProof.toggle_expandability [0,2,0,3] k4;
NLProof.print k5*}
ML{* val k6 = NLProof.toggle_expandability [0,2,0,3,2] k5;
NLProof.print k6*}


ML{* val k2 = NLProof.toggle_expandability [0,3] k1;
NLProof.print k2*}
ML{* val k3 = NLProof.toggle_expandability [0,3,2] k2;
NLProof.print k3*}
ML{* val k1 = NLProof.expand_all k;
NLProof.print k1*}
ML{* val k2 = NLProof.expand_all k1;
NLProof.print k2*}
ML{* val k3 = NLProof.expand_all k2;
NLProof.print k3*}
ML{* val kr = NLProof.expand_recursively k;
NLProof.print kr *}

ML{* val collapsed02 = NLProof.collapse_branch [0,2] k *}
ML{* val _ = NLProof.print collapsed02 *}
ML{* val pb02 = NLProof.expand_branch [0,2] collapsed02
val _ = NLProof.print pb02
*}
ML{* val pb03 = NLProof.expand_branch [0,2,1] pb02
val _ = NLProof.print pb03
*}

ML{* val high = NLProof.nlproof_init_highest k;
val _ = NLProof.print high
*}
ML{* val lup = NLProof.expand_all high;
val _ = NLProof.print lup
*}
ML{* val lup2 = NLProof.expand_all lup;
val _ = NLProof.print lup2
*}
ML{* val lup3 = NLProof.expand_all lup2;
NLProof.print lup3
*}

ML{*
local open HTraceCInfo in


fun change_rst_names_in_tree (Tree ((i,rst),ch)) =
  let 
    val name = RstName.str "Cool name"
    val rtech = RState.get_rtechn rst
    val new_rtech = case rtech of NONE => NONE | SOME x => SOME (RTechnComb.givename name x)
    val new_rst = RState.set_rtechn new_rtech rst
    val _ = PolyML.print (DescripCInfo.string_of_rst new_rst)
  in (Tree ((i,new_rst),map change_rst_names_in_tree ch))
  end

fun change_rst_names_in_trace (Trace (tl,x)) = Trace (map change_rst_names_in_tree tl,x)

val new_htrace = change_rst_names_in_trace htrace

end;
 *}

ML{* val _ = Pretty.writeln (HTraceCInfo.pretty new_htrace) *}
ML{* val tree = let val (x::t,_) = (HTraceCInfo.get_from_trace new_htrace) in x end *}
ML{* val from_tree = HTraceCInfo.get_from_tree tree *}
ML{* val rst = let val ((_,x),_) = from_tree in x end*}
ML{* DescripCInfo.string_of_rst rst *}



ML{*
 (* open conjectures for function: f_4*)
"f_4 a (f_4 b 0) = f_4 b (f_4 a 0)",
"f_4 a (f_4 b c) = f_4 b (f_4 a c)",
"f_4 a (Suc (Suc 0)) = Suc (f_4 a (Suc 0))",
"f_4 a (Suc (Suc 0)) = Suc (Suc (f_4 a 0))",
"f_4 a (Suc (Suc b)) = Suc (f_4 a (Suc b))",
"f_4 a (Suc (Suc b)) = Suc (Suc (f_4 a b))",
"Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))",
"Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))",
"Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))",
"Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))",
"f_4 a (Suc 0) = Suc (f_4 a 0)",
"f_4 a (Suc b) = Suc (f_4 a b)",
"Suc (f_4 a 0) = f_4 a (Suc 0)",
"Suc (f_4 a b) = f_4 a (Suc b)"
val (openconjs, theorems) = top_level_no_updt_ctx @{context} [] conjectures;
*}

ML{*
fun pretty_thm ctxt thm =
  Syntax.pretty_term ctxt (prop_of thm);

fun printlist [] = ()
  | printlist (h::t) =
    let
      val _ = TextIO.print(h ^ "\n")
  in printlist t
  end;

fun printlist_annthms [] = ()
  | printlist_annthms (h::t) =
    let
      val (ann,thm) = h
      val _ = PolyML.print(ann ^ "-> " ^ (Display.string_of_thm @{context} thm))
      val _ = TextIO.print("\n")
  in printlist_annthms t
  end;

TextIO.print("Conjectures:\n");
printlist conjectures;
TextIO.print("\n\n");

TextIO.print("New open conjectures:\n");
printlist openconjs;
TextIO.print("\n\n");

TextIO.print("Proved:\n");
printlist_annthms theorems;
TextIO.print("\n\n");

TextIO.print("lenght of openconjs:" ^ Int.toString(length conjectures) ^ "\n");
TextIO.print("lenght of newopenconjs: " ^ Int.toString(length openconjs) ^ "\n");
TextIO.print("lenght of proved conjectures: " ^ Int.toString(length theorems) ^ "\n");
*}

end