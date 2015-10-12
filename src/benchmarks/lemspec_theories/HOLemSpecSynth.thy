theory HOLemSpecSynth
imports Main IsaP
begin
declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.inject[wrule]

declare List.append.simps[wrule]
declare List.rev.simps[wrule]
declare List.map.simps[wrule]
declare List.concat.simps[wrule]
declare foldl_Nil[wrule]
declare foldl_Cons[wrule]

consts maps :: "('a => 'b list) => 'a list => 'b list"
primrec
  maps_nil[wrule]: "maps f [] = []" 
  maps_cons[wrule]: "maps f (h#t) = (f h) @ (maps f t)"


consts len :: "'a list => nat"   ("len _" [500] 500)
primrec 
  len_nil[wrule]:     "len [] = 0"
  len_cons[wrule]:    "len (h # t) = Suc (len t)"

consts rotate :: "nat \<Rightarrow> 'a list => 'a list"
primrec
  rot_zero[wrule]:  "rotate 0 l = l"
  rot_suc[wrule]:   "rotate (Suc n) l = (case l of (h#t) => rotate n (t@[h])
                                                  | [] => [])" 

consts even :: "nat \<Rightarrow> bool" ("even _" [520] 520)
recdef even "measure size"
  even_0[wrule]:"even 0 = True"
  even_not_S_0[wrule]: "even (Suc 0) = False"
  even_S_S[wrule]:     "even (Suc (Suc n)) = even n"

fun lesseq :: "nat => nat => bool" (infix "leq" 520)
where
  less_eq_0: "(0::nat) leq y = True" |
  less_eq_Suc:  "(Suc x) leq y = (case y of 0 => False | Suc z => (x leq z))"
declare less_eq_0[wrule]
declare less_eq_Suc[wrule]
(*
lemma plus_Suc2[wrule]: "x + Suc y =Suc(x + y)"
by rippling
*)

lemma leq_plus_suc[simp,wrule]: "x leq Suc(y+x) = True"
by rippling

ML{*
fun rippling goals =
  Print_Mode.setmp []
  (fn () => PPInterface.ipp_of_strings @{theory} 
    (RTechnEnv.map_then RippleLemCalc.induct_ripple_lemcalc) goals) ();

val myrst = rippling ["x leq (y+x)"];
*}

ML{*
val plus = @{term "op + :: nat => nat => nat"};

val constinfo = ConstInfo.init_const_infos_for 
      [Term.dest_Const @{term "lesseq"}, Term.dest_Const plus] (* function constants *)
      (map (fst o Term.dest_Type) ([@{typ "nat"}, @{typ "bool"}])) (* datatype names *)
      [] (* theorems *)
      @{theory};

val((cinfo, thy), (conjs, thrms)) = Synthesis.synth_w_stats (3, 8) 2 @{theory} constinfo;
*}
ML{*
(*
val (lemma,rstlist) = List.nth (thrms,8);
map RState.print rstlist;
*)
*}
(*
lemma plus_Suc2[wrule]: "x + Suc y =Suc(x + y)"
by rippling
*)
(*
lemma leq_plus_suc[wrule]: "x leq Suc(y+x) = True"
by rippling
*)
(*lemma leq_lemma[wrule]: "Suc z leq (aa + Suc z) = z leq Suc (aa + z)"
sorry
*)

lemma leq_plus[wrule]: "x leq (y+x)"

lemma rev_app[wrule]: "rev (a @ b) = (rev b) @ (rev a)"
by rippling
lemma rev_app_sngl[wrule]: "rev( l @ [h]) = h # (rev l)"
by rippling


lemma map_rev[wrule]: "map f (rev l) = rev(map f l)"
by rippling

lemma app_assoc[wrule]: "(x @ y) @ z = x @ (y @z)"
by rippling


(*lemma len_rev[wrule]: "len(rev a) = len a"
sorry
lemma rev_app_rev[wrule]: "rev(a @ (rev b)) = b @ (rev a)"
sorry
lemma len_map[wrule]: "len(map a b) = len b"
sorry
lemma map_maps[simp,wrule]: "concat(map f l) = maps f l"
sorry
*)




end;
