theory QRELind3
imports Main
begin


(* to simplify - need a min in adequacy proof *)

(*
type_synonym X = bool
*)
typedecl X

section "Partition"

type_synonym xpset = "X set set"

definition
  is_total :: "xpset => bool"
where
  "is_total p \<equiv> \<Union>p = UNIV"

definition
 is_disj
where
 "is_disj ss \<equiv> (\<forall> s1 s2. s1 \<in> ss \<and> s2 \<in> ss \<longrightarrow> s1 = s2 \<or> s1 \<inter> s2 = {})"

definition
  Part :: "xpset => bool"
where
  "Part p \<equiv> {} \<notin> p \<and> is_disj p \<and> is_total p"

subsection "Example theory and operator lemmas"

lemma Pempty: "Part p ==> {} \<notin> p"
oops

lemma LO1: "Part {e. \<exists> x. e = {x}}"
oops

definition
  merge :: "xpset \<Rightarrow> (X set => bool) \<Rightarrow> xpset"
where
 "merge p t == {s \<in> p. \<not>(t s)} \<union> {\<Union>{s \<in> p. (t s)}}"



lemma L02: assumes h1: "Part p"
    and h2: "\<exists> s \<in> p. t s"
    and h3: "p' = merge p t"
shows "Part p'"
oops
   
subsection "Specification"

definition
  pTEST :: "X => X => xpset => bool => bool"
where
 "pTEST e1 e2 p r \<equiv> (r = (\<exists> s \<in> p . {e1,e2} \<subseteq> s))"

definition
  pEQUATE :: "X => X => xpset => xpset"
where
 "pEQUATE e1 e2 p \<equiv> {s \<in> p. e1 \<notin> s \<and> e2 \<notin> s} \<union> {\<Union>{s \<in> p. e1 \<in> s \<or> e2 \<in> s}}"

lemma L03: "Part p \<Longrightarrow> \<exists> p'. Part p' \<and> pEQUATE e1 e2 p = p'"
oops

lemma L04: "Part p \<Longrightarrow> pTEST e1 e2 p r \<Longrightarrow> e1 = e2 \<Longrightarrow> r"
oops

lemma L05: "Part p \<Longrightarrow> p = {e. \<exists> x. e = {x}} \<Longrightarrow> pTEST e2 e1 p r \<Longrightarrow> r \<Longrightarrow> e1 = e2"
oops

lemma L06: "Part p \<Longrightarrow>  pTEST e1 e2 p ra \<Longrightarrow> pTEST e2 e1 p rb \<Longrightarrow> ra = rb"
oops

lemma L07: "Part p \<Longrightarrow>  pTEST e1 e2 p ra \<Longrightarrow> pTEST e2 e3 p rb \<Longrightarrow> pTEST e1 e3 p rc \<Longrightarrow> ra \<and> rb ==> rc"
oops


lemma L08:
 assumes h1: "Part p"
  and h2: "Part p'"
  and h3: "pTEST e1 e2 p r"
  and h4: "pEQUATE e1 e2 p = p'"
  shows "\<not>r \<or> p'=p"
oops

lemma L09: "Part p ==> Part p' ==> pTEST e1 e2 p ra \<Longrightarrow> pEQUATE e1 e2 p = p' \<Longrightarrow> pTEST e1 e2 p' rb \<Longrightarrow> ra \<Longrightarrow> rb"
oops

section "Forest"

type_synonym xmap = "(X * X) set"

definition 
 functional :: "xmap => bool"
where
 "functional m \<equiv> (\<forall>x \<in> Domain m. \<exists>!y. (x,y) \<in> m)"

definition 
 rngrestr :: "xmap => X set => xmap" (infix "|>" 35)
where 
 "R |> A \<equiv> {r. r \<in> R \<and> snd r \<in> A}" 

definition 
 xapp :: "xmap \<Rightarrow> X => X" (infixl "$$" 51)
where 
 "xapp f x \<equiv> THE y. (x,y) \<in> f"

inductive
 Forest :: "xmap => bool"
where
  base[simp] : "Forest {}"
| step[intro]: "\<lbrakk>Forest m; e1 \<notin> Domain m; e2 \<notin> Domain m \<union> {e1}\<rbrakk> \<Longrightarrow> Forest (m \<union> {(e1,e2)})"

definition 
  roots :: "xmap \<Rightarrow> X set"
where
  "roots m = UNIV - Domain m"

function (domintros)
  root :: "X \<Rightarrow> xmap => X"
where
  "root x f = (if x \<in> roots f then x else root (f $$ x) f)"
 by auto

(*
lemma sorry1: "Forest f \<Longrightarrow> root_dom(x,f)" sorry
lemmas root_simps = root.psimps[OF sorry1]

*)
lemma  "Forest f ==> root e f \<in> roots f"
oops

lemma Forest_root_roots[intro]: "Forest f ==> root e f \<in> roots f"
oops

definition
 collapse :: "xmap => xmap"
where
 "collapse f = {(e,root e f) | e. e : UNIV}"

(* pre: r : roots(f) -- maybe use function instead? *)
definition 
 collect :: "X => xmap => X set"
where
 "collect r f \<equiv> {e. root e f = r}"
(*
lemma [code]: "Forest f = True" sorry
lemma [code]: "root x f = (if x \<in> roots f then x else root (f $$ x) f)" sorry
*)
lemma L10: "Forest f \<Longrightarrow> x = root a f" 
oops

lemma L10: "\<lbrakk> Forest f; {r1,r2} \<subseteq> roots f; r1 \<noteq> r2; f' = f \<union> {(r1,r2)}\<rbrakk> \<Longrightarrow> Forest f'" 
oops

lemma L11: "Forest f \<Longrightarrow> (collapse f) $$ e = root e f"
oops

lemma L12: "Forest f \<Longrightarrow> r \<in> roots f \<Longrightarrow> collect r f = Domain (collapse f |> {r})"
oops

lemma G1: "Forest f \<Longrightarrow> root x f = root (root x f) f"
oops

lemma G2: "Forest f ==> root x f = e \<Longrightarrow> x : collect (root e f) f"
oops

lemma G3: "Forest f ==> root x f = e \<Longrightarrow> e : collect (root x f) f"
oops

lemma L13: "Forest f \<Longrightarrow> e \<in> collect (root e f) f"
oops

lemma G4: "Forest f ==> {r1,r2} \<subseteq> roots f ==> r1 \<noteq> r2 \<Longrightarrow> root r1 f \<noteq> root r2 f"
oops

lemma G5: "r1 : roots f ==> r2 : roots f ==> roots (f \<union> {(r1, r2)}) = roots f - {r1}"
oops

lemma union_coll_dist: "{e. P e} \<union> {e. Q e} = {e. P e \<or> Q e}"
 by auto

(* should be simpler! *)
lemma L14: "\<lbrakk> Forest f; {r,r1,r2} \<subseteq> roots f; r1 \<noteq> r2; r \<noteq> r1; r \<noteq> r2\<rbrakk> \<Longrightarrow> collect r (f \<union> {(r1,r2)}) = collect r f "
oops

lemma L16: "\<lbrakk> Forest f; {r1,r2} \<subseteq> roots f; r1 \<noteq> r2\<rbrakk> \<Longrightarrow> collect r1 f \<inter> collect r2 f = {}"
oops

lemma L17: "\<lbrakk> Forest f; {r,r1,r2} \<subseteq> roots f; r1 \<noteq> r2; r \<noteq> r1; r \<noteq> r2\<rbrakk> \<Longrightarrow>
  Domain (collapse (f \<union> {(r1,r2)}) |> {r}) = Domain (collapse f |> {r})"
oops

lemma L18a: "\<lbrakk> Forest f; {r1,r2} \<subseteq> roots f; r1 \<noteq> r2\<rbrakk> \<Longrightarrow> 
  (collapse (f \<union> {(r1,r2)}) |> {r2}) =  (collapse f |> {r1,r2})"
oops


lemma L18: "\<lbrakk> Forest f; {r1,r2} \<subseteq> roots f; r1 \<noteq> r2\<rbrakk> \<Longrightarrow> 
  Domain (collapse (f \<union> {(r1,r2)}) |> {r2}) = Domain (collapse f |> {r1,r2})"
 oops

lemma L19: "Forest f \<Longrightarrow> r = root e f \<longleftrightarrow> e \<in> Domain (collapse f |> {r})"
oops

subsection "Specification"

definition
  fTEST :: "X => X => xmap => bool"
where
 "fTEST e1 e2 f \<equiv> root e1 f = root e2 f" 

definition
  fEQUATE :: "X => X => xmap => xmap"
where
  "fEQUATE e1 e2 f \<equiv> (if root e1 f = root e2 f then f else f \<union> {(root e1 f,root e2 f)})"

subsection "refinement"

lemma Part_finite: "Part p \<Longrightarrow> finite p"
 oops
 
definition
  retr_Part :: "xmap => xpset"
where
 "retr_Part f \<equiv> {collect r f | r. r \<in> roots f}"

lemma L20: "Part p \<Longrightarrow> (\<exists> f. Forest f \<and> retr_Part f = p)"
oops

subsubsection "Justifying the operations"

(* could prove that Forest f0 !! *)
lemma Forest_empty: "Forest {}"
oops

lemma L21: "Forest f0 \<Longrightarrow> f0 = {} \<Longrightarrow> retr_Part f0 = {e. \<exists> x. e = {x}}"
oops

lemma L22: " Forest f \<Longrightarrow> (\<exists> s. s \<in> retr_Part(f) \<and> e1 \<in> s \<and> e2 \<in> s) \<longleftrightarrow> root e1 f = root e2 f"
oops

lemma "Forest f ==> x = root e f \<Longrightarrow> x : roots f"
oops

lemma G7: "r1 \<noteq> r2 ==> r1 : roots f ==> r2 : roots f ==> roots (f \<union> {(r1, r2)}) = {r2} \<union> (roots f - {r2,r1})"
oops


lemma L23: "\<lbrakk> Forest f; Part p; p = retr_Part f; r1 = root e1 f; r2 = root e2 f; r1 \<noteq> r2 \<rbrakk> \<Longrightarrow> 
  retr_Part (f \<union> {(r1,r2)}) = {s \<in> p. e1 \<notin> s \<and> e2 \<notin> s} \<union> {\<Union>{s \<in> p. e1 \<in> s \<or> e2 \<in> s}}"
oops

end