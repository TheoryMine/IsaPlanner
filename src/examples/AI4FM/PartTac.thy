theory PartTac
imports Main 
begin

typedecl X

axiomatization
  X_fin
where
  X_fin: "finite (A::X set)"

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

inductive
 PPart :: "xpset => bool"
where
  base[simp] : "PPart {e. \<exists> x. e = {x}}"
| step[intro]: "\<lbrakk>PPart ({s,t} \<union> ss); s \<notin> ss; t \<notin> ss; ss' = {s \<union> t} \<union> ss \<rbrakk> \<Longrightarrow> PPart ss'"

lemma PPart_el_fin: "PPart p ==> x \<in> p ==> finite x"
 by (rule X_fin)

-- "erule PPart induct withouth auto"
ML{*
fun clarsimp_or_blast_all ctxt =
  (fn n => (CHANGED (clarsimp_tac ctxt n)) ORELSE (blast_tac ctxt n))
 |> REPEAT_SOME;

val erule_PPart_ind = Tactic.eresolve_tac [@{thm PPart.induct}] 1;

fun PPart_ind_clarsimp_blast_tac ctxt =
  erule_PPart_ind THEN (clarsimp_or_blast_all ctxt);
*}

lemma PPart_disj: "PPart p \<Longrightarrow> is_disj p"
 unfolding is_disj_def
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma PPempty1 [rule_format,intro]: "PPart p ==> s \<in> p \<longrightarrow> s \<noteq> {}"
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma PPart_has_el: "PPart p \<Longrightarrow> \<exists> s. s \<in> p"
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma PPart_total: "PPart p \<Longrightarrow> is_total p"
 unfolding is_total_def
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma PPart_al_elsub: "PPart p \<Longrightarrow> \<forall> e. \<exists> s \<in> p. e \<in> s"
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma PPempty: "PPart p ==> {} \<notin> p"
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma PPart_Part: "PPart p ==> Part p"
 unfolding Part_def
 by (blast intro!: PPempty PPart_disj PPart_total) (* note: intro: doesn't work *)

lemma PPs3_l1: "{s,t,u} \<union> ss = {s,t} \<union> ({u} \<union> ss)"
 by blast

lemma PPart_union_not_mem: "PPart ss \<Longrightarrow> s \<noteq> t \<Longrightarrow> s \<in> ss \<Longrightarrow> t \<in> ss \<Longrightarrow> (s \<union> t) \<notin> ss"
apply (frule PPart_disj)
unfolding is_disj_def
apply clarify
apply (subgoal_tac "s \<union> t \<noteq> s")
apply (auto dest: PPempty1) (* since in assumption? *)
done

lemma assumes h1: "PPart ({s,t,u} \<union> ss)"
  and h2: "s \<notin> ss"
  and h3: "t \<notin> ss" 
  and h4: "u \<notin> ss"
 shows "PPart ({s \<union> t \<union> u} \<union> ss)"
proof (case_tac "u = s \<or> u = t")
 assume a1: "u = s \<or> u = t"
 thus ?thesis
 proof (case_tac "u=s")
   assume a1': "u = s"
   from a1' have g1: "{s \<union> t \<union> u} = {s \<union> t}" by blast
   from a1' have "{s,t,u} = {s,t}" by blast
   with h1 have h1': "PPart ({s,t} \<union> ss)" by auto
   have "PPart ({s \<union> t} \<union> ss)"
    apply (rule PPart.step)
   using h1' h2 h3 by auto
   thus ?thesis by (subst g1)
  next   
   assume "u \<noteq> s"
   with a1 have a1': "u = t" by simp
   from a1' have g1: "{s \<union> t \<union> u} = {s \<union> t}" by blast
   from a1' have "{s,t,u} = {s,t}" by blast
   with h1 have h1': "PPart ({s,t} \<union> ss)" by auto
   have "PPart ({s \<union> t} \<union> ss)"
    apply (rule PPart.step)
    using h1' h2 h3 by auto
   thus ?thesis by (subst g1)
  qed
 next
  assume a1: "\<not> (u = s \<or> u = t)"
  hence a1a: "u \<noteq> s" and a1b: "u \<noteq> t" by auto
  have g1: "{s,t,u} \<union> ss = {s,t} \<union> ({u} \<union> ss)" by blast
  from h1 have h1': "PPart ({s,t} \<union> ({u} \<union> ss))" 
   by (subst g1[symmetric])
  have g1: "PPart ({s \<union> t} \<union> ({u} \<union> ss))"
   apply (rule PPart.step)
   apply (rule h1')
   using h2 a1a apply simp
   using h3 a1b apply simp
   apply (rule refl)
   done
  have g2l1: "{s \<union> t, u} \<union> ss = {s \<union> t} \<union> ({u} \<union> ss)" by blast
  from g1 have g2: "PPart ({s \<union> t, u} \<union> ss)"
   by (subst g2l1)
  have g3:"s \<union> t \<notin> ss"
  proof (case_tac "s=t")
    assume "s=t"
    with h2 show ?thesis by force
  next
   assume a1: "s \<noteq> t"
   have g3':"s \<union> t \<notin> {s,t,u} \<union> ss"
     apply (rule  PPart_union_not_mem)
     apply (rule h1)
     apply (rule a1)
     by auto
   thus ?thesis by simp
  qed
  show ?thesis
   apply (rule PPart.step)
   apply (rule g2)
   defer 1
   apply (rule h4)
   apply (rule refl)
   apply (rule g3)
   done
qed

definition
  merge :: "xpset \<Rightarrow> (X set => bool) \<Rightarrow> xpset"
where
 "merge p t == {s \<in> p. \<not>(t s)} \<union> {\<Union>{s \<in> p. (t s)}}"


subsection "Example theory and operator lemmas"

lemma LO1: "PPart {e. \<exists> x. e = {x}}"
  by auto

subsection "Specification"

definition
  pTEST :: "X => X => xpset => bool"
where
 "pTEST e1 e2 p \<equiv> (\<exists> s \<in> p . {e1,e2} \<subseteq> s)"

definition
  pEQUATE :: "X => X => xpset => xpset"
where
 "pEQUATE e1 e2 p \<equiv> {s \<in> p. e1 \<notin> s \<and> e2 \<notin> s} \<union> {\<Union>{s \<in> p. e1 \<in> s \<or> e2 \<in> s}}"

lemma L03: "PPart p \<Longrightarrow> \<exists> p'. PPart p' \<and> pEQUATE e1 e2 p = p'"
 unfolding pEQUATE_def
 apply (rule exI)
 apply (rule conjI)
 prefer 2
 apply (rule refl)
 (* case_tac e1 and e2 are in the same  *) 
 apply (subgoal_tac "\<exists> s. s \<in> p \<and> e1 \<in> s")
 apply (subgoal_tac "\<exists> s. s \<in> p \<and>e2 \<in> s")
 apply (elim exE conjE)
 defer 1
 apply (blast dest: PPart_al_elsub)
 apply (blast dest: PPart_al_elsub)
 apply (subgoal_tac "{s \<union> sa} \<union> (p - {s,sa}) = ({s \<in> p. e1 \<notin> s \<and> e2 \<notin> s} \<union> {\<Union>{s \<in> p. e1 \<in> s \<or> e2 \<in> s}})")
 apply (rule_tac s = "{s \<union> sa} \<union> (p - {s,sa})" and t = "({s \<in> p. e1 \<notin> s \<and> e2 \<notin> s} \<union> {\<Union>{s \<in> p. e1 \<in> s \<or> e2 \<in> s}})" in subst)
 apply simp
 apply (rule PPart.step)
 prefer 4
 apply (rule refl)
 prefer 2
 apply simp
 prefer 2
 apply simp
 apply (subgoal_tac "{s, sa} \<union> (p - {s, sa}) = p")
 prefer 2
 apply blast
 apply simp
 apply (frule PPart_disj)
 unfolding is_disj_def
 apply auto
 done

(* does not terminate! *)
lemma L04[rule_format]: "PPart p \<Longrightarrow> pTEST e1 e2 p = r \<longrightarrow> (e1 = e2) \<longrightarrow> r"
 unfolding pTEST_def 
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma  "PPart p \<Longrightarrow> e1=e2 \<longrightarrow>  pTEST e1 e2 p"
 unfolding pTEST_def 
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma L05[rule_format]: "PPart p \<Longrightarrow> p = {e. \<exists> x. e = {x}} \<longrightarrow> pTEST e2 e1 p \<longrightarrow> e1 = e2"
 unfolding pTEST_def
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma L06[rule_format]: "PPart p \<Longrightarrow> pTEST e1 e2 p = pTEST e2 e1 p"
 unfolding pTEST_def
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done

lemma L07: "PPart p \<Longrightarrow> pTEST e1 e2 p --> pTEST e2 e3 p --> pTEST e1 e3 p"
 apply (drule PPart_Part)
 unfolding pTEST_def Part_def is_disj_def is_total_def
 by auto

(* required to stop auto looping below *)
lemma L08_la: "sa \<in> p \<Longrightarrow> {\<Union>{s \<in> p. s = sa}} = {sa}"
 apply auto
 done

lemma L08:
 assumes h1: "PPart p"
  (* and h2: "PPart p'" *) (* not required *)
  and h3: "pTEST e1 e2 p = r"
  and h4: "pEQUATE e1 e2 p = p'"
  shows "\<not>r \<or> p'=p"
proof (cases "r")
  assume "\<not> r" thus ?thesis by blast
next
  assume a1: "r"
  with h3 have "(\<exists> s \<in> p . {e1,e2} \<subseteq> s)"
   unfolding pTEST_def by simp
  then obtain sa where g1: "{e1,e2} \<subseteq> sa" and g2: "sa \<in> p" by auto
  from h1[THEN PPart_disj] g2 have g3: "(\<forall> sb \<in> p. sa = sb \<or> sa \<inter> sb = {})"
   unfolding  is_disj_def by auto
  have g4: "\<forall> s \<in> p. e1 \<notin> s \<and> e2 \<notin> s \<longleftrightarrow> s \<noteq> sa"
   apply (rule ballI)
   using g1 g2 g3
   by auto
  have g5: "\<forall> s \<in> p. e1 \<in> s \<or> e2 \<in> s \<longleftrightarrow> s = sa"
   apply (rule ballI)
   using g1 g2 g3
   by auto
  from h4 g3 have g6: "p' = {s \<in> p. e1 \<notin> s \<and> e2 \<notin> s} \<union> {\<Union>{s \<in> p. e1 \<in> s \<or> e2 \<in> s}}"
   unfolding pEQUATE_def by blast
  with g4 g5 have "p' = {s \<in> p. s \<noteq> sa} \<union> {\<Union>{s \<in> p. s = sa}}"
   by blast
  hence  "p' = {s \<in> p. s \<noteq> sa} \<union> {sa}"
   apply (subst (asm) L08_la)
   by (auto simp add: g2)
  with g2 have "p' = p" by auto
  thus ?thesis by simp
qed

lemma L09: "PPart p ==> PPart p' ==> pTEST e1 e2 p \<Longrightarrow> pEQUATE e1 e2 p = p' \<Longrightarrow> pTEST e1 e2 p'"
 unfolding pTEST_def pEQUATE_def Part_def is_disj_def is_total_def
 apply (tactic "PPart_ind_clarsimp_blast_tac @{context}")
 done





ML{*
(*
try_proof_tout @{context} @{term "PPart p ==> pTEST e1 e2 p = ra --> pEQUATE e1 e2 p = p' --> pTEST e1 e2 p' = rb --> ra --> rb"};
try_proof_tout @{context} @{term "PPart p'  \<Longrightarrow> pEQUATE e1 e2 p = p' \<Longrightarrow> pTEST e1 e2 p' \<Longrightarrow> ra \<Longrightarrow> rb"};
try_proof_tout @{context} @{term "PPart p \<Longrightarrow> \<exists> p'. PPart p' \<and> pEQUATE e1 e2 p = p'"};
try_proof_tout @{context} @{term "PPart p ==> s \<in> p \<longrightarrow> s \<noteq> {}"};
*)
*}


end