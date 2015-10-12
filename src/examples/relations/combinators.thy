theory combinators
imports Nominal
begin

abbreviation
  sublst :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "sublst xs ys \<equiv> \<forall>a. a \<in> set xs \<longrightarrow> a \<in> set ys"

lemma tl_sublst:
  assumes h:"sublst (x#xs) ys"
  shows "sublst xs ys"
  using h by auto

atom_decl par    -- " names of assumptions "

lemma par_fresh_commutes:
  fixes x y :: par
  assumes h:"x\<sharp>y"
  shows     "y\<sharp>x"
proof -
  from h fresh_atm have "x ~= y" by simp
  from this have "y ~= x" by auto
  from this fresh_atm show ?thesis by simp
qed

types ap = nat   -- " atomic propositions "
constdefs
  A0 :: ap
  "A0 == 0"
  A1 :: ap
  "A1 == 1"

-- "types (propositions) "
nominal_datatype tp = Atm ap
                    | Arr tp tp  (infixr "\<rightarrow>" 200)

lemma tp_perm[simp]:
  fixes pi ::"par prm" and A ::"tp"
  shows "pi\<bullet>A = A"
by (induct A rule: tp.weak_induct, simp_all add: perm_nat_def)

lemma tp_fresh[simp]:
  fixes x ::"par" and A ::"tp"
  shows "x\<sharp>A"
by (induct A rule: tp.weak_induct, simp_all add: fresh_nat)


-- " unary substitution for atomic types "
consts
  sbst :: "tp \<Rightarrow> ap \<Rightarrow> tp \<Rightarrow> tp"  ("_[_;=_]" 75)
nominal_primrec
  "(Atm P)[Q;=C] = (if P = Q then C else (Atm P))"
  "(A \<rightarrow> B)[Q;=C] = (A[Q;=C]) \<rightarrow> (B[Q;=C])"
by auto

-- " simultaneous substitution for atomic types "
consts
  assoc_def :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b \<Rightarrow> 'b"
primrec
  "assoc_def a [] d = d"       (* lookup fails; return default *)
  "assoc_def a (cb#l) d = (if a = fst cb then (snd cb)
                                         else (assoc_def a l d))"

consts
  sbsts :: "tp \<Rightarrow> (ap * tp) list \<Rightarrow> tp"  ("_[;_]" 100 )
nominal_primrec
  "(Atm P)[;rho] = assoc_def P rho (Atm P)"
  "(P \<rightarrow> Q)[;rho] = (P[;rho]) \<rightarrow> (Q[;rho])"
by auto

-- " contexts of assumptions "
types cxt = "(par * tp) list"

lemma fresh_for_cxt:
  fixes p :: par
  shows "p \<sharp> (G::cxt) == p \<sharp> (map fst G)"
proof (induct G, simp add: fresh_list_nil)
  case (Cons aa GG)
  have j:"p \<sharp> GG \<equiv> p \<sharp> map fst GG" by fact
  have j1:"p \<sharp> aa == p \<sharp> (fst aa)"
    using fresh_prod[of p "fst aa" "snd aa"] tp_fresh[of p "snd aa"]
    by (subst surjective_pairing[of aa], force)
  show "p \<sharp> (aa # GG) \<equiv> p \<sharp> map fst (aa # GG)"
    by (simp add: fresh_list_cons fresh_prod j1 j)
qed

inductive valid :: "cxt \<Rightarrow> bool"
  where
  vNil[simp,intro!]: "valid []"
| vCons[simp,intro]: "\<lbrakk>valid G; (fst pA)\<sharp>G\<rbrakk>\<Longrightarrow> valid (pA#G)"

inductive_cases vCons_inv: "valid (pA#G)"

lemma valid_tl:
  assumes h:"valid (pA#G)"
  shows "valid G"
using valid.cases[OF h] by auto

lemma valid_head_fresh:
  assumes h:"valid (pA#G)"
  shows "(fst pA)\<sharp>G"
by (rule vCons_inv[of pA], auto simp add: h)

lemma valid_split:
  assumes h:"valid (G1 @ G2)"
  shows "valid G1 \<and> valid G2"
  using h
proof (induct G1, simp)
  case (Cons aa GG1)
  have ih:"valid (GG1 @ G2) \<Longrightarrow> valid GG1 \<and> valid G2" 
    and j2:"valid ((aa # GG1) @ G2)"
    by fact+
  hence m0:"valid (aa#(GG1@G2))" by auto
  hence "valid (GG1 @ G2)" and k0:"(fst aa)\<sharp>(GG1@G2)"
    using valid_tl[OF m0] valid_head_fresh[OF m0] by auto
  hence k1:"valid GG1" and k2:"valid G2" using ih by auto
  from k0 fresh_list_append have k3:"(fst aa)\<sharp>GG1" by force
  have "valid (aa # GG1)" by (rule vCons[OF k1 k3])
  thus "valid (aa # GG1) \<and> valid G2" using k2 by simp
qed

lemma valid_apart:
  assumes h: "valid ((aA)#G)"
  shows "(fst aA)\<sharp>G"
  using valid.cases [OF h] by auto

lemma valid_mem_fresh:
  assumes h:"valid (G1@pA#G2)"
  shows "(fst pA)\<sharp>G1 \<and> (fst pA)\<sharp>G2"
proof -
  from valid_split[OF h] valid_head_fresh
  have pG2:"(fst pA)\<sharp>G2" by auto
  from h have h1:"valid ((G1@[pA])@G2)" by auto
  hence "valid (G1@[pA])" using valid_split[OF h1] by auto
  hence "(fst pA)\<sharp>G1"
  proof (induct G1, simp add: fresh_list_nil)
    case (Cons aa GG1)
    have ih:"valid (GG1 @ [pA]) \<Longrightarrow> (fst pA) \<sharp> GG1"
      and j2:"valid ((aa # GG1) @ [pA])" by fact+
    from j2 have j3:"valid (aa # (GG1 @ [pA]))" by auto
    have k1:"(fst pA) \<sharp> GG1" using ih[OF valid_tl[OF j3]] .
    have j4:"(fst aa) \<sharp> (GG1 @ [pA])"
      using valid_head_fresh[OF j3] .
    hence "(fst aa) \<sharp> (fst pA)"
      using fresh_list_append[of "fst aa" GG1 "[pA]"]
            fresh_list_cons[of "fst aa" "pA" "[]"]
            fresh_prod[of "fst aa" "fst pA" "snd pA"] by force
    hence k2:"(fst pA) \<sharp> (fst aa)" using par_fresh_commutes by auto
    have  k3:"(fst pA) \<sharp> (snd aa)" by simp
    have "(fst pA) \<sharp> aa"
      by (subst surjective_pairing[of aa],
          auto simp only: k2 k3 fresh_prod[of "fst pA"])
    thus "(fst pA) \<sharp> (aa # GG1)"
      using fresh_list_cons[of "fst pA" aa] k1 by auto
  qed
  thus ?thesis using pG2 by auto
qed

lemma valid_strengthen:
  assumes h:"valid (G1@(pA#G2))"
  shows "valid (G1@G2)"
  using h
proof (induct G1)
  case Nil
  hence j1:"valid (pA#G2)" by auto
  have "valid G2" using valid_tl[OF j1] .
  thus ?case by auto
next
  case (Cons aa GG1)
  have ih:"valid (GG1 @ pA # G2) \<Longrightarrow> valid (GG1 @ G2)"
    and j1:"valid ((aa # GG1) @ pA # G2)" by fact+
  from j1 have j2:"valid (aa # (GG1 @ (pA # G2)))" by auto
  hence "valid (GG1 @ (pA # G2))" by (rule valid_tl)
  hence k1:"valid (GG1 @ G2)" using ih by auto
  from fresh_list_append[of "fst aa" GG1 "pA#G2"]
    valid_head_fresh[OF j2]
    fresh_list_cons[of "fst aa" pA G2]
  have "fst aa \<sharp> GG1" and "fst aa \<sharp> G2" by auto
  thus "valid ((aa # GG1) @ G2)"
    using vCons[OF k1, of aa]
      fresh_list_append[of "fst aa" GG1 G2] by auto
qed

(*<*)
(*
-- " substitution preserves validity "
lemma sbst_pres_valid:
  assumes h:"valid G"
  shows "valid (map (%(p,C). (p,C[Q;=B])) G)"
  using h
proof (induct, simp)
  case (vCons GG pp AA)
  have j1:"valid (map (\<lambda>(p, C). (p, C[Q;=B])) GG)" and j2:"pp \<sharp> GG"
    by fact+
  show "valid (map (\<lambda>(p, C). (p, C[Q;=B])) ((pp, AA) # GG))"
  proof (simp, rule combinators.vCons[OF j1])
    show "pp \<sharp> map (\<lambda>(p, C). (p, C[Q;=B])) GG"
    proof (induct GG, simp add: fresh_list_nil)
qed
*) 

-- " simultaneous substitution preserves validity"
(*
lemma sbsts_pres_valid:
  assumes h:"valid G"
  shows "valid (map (%(p,C). (p,C[;rho])) G)"
  using h
proof (induct, simp)
  case (vCons GG pp AA)
  have j1:"valid (map (\<lambda>(p, C). (p, C[;rho])) GG)" and j2:"pp \<sharp> GG"
    by fact+
  show "valid (map (\<lambda>(p, C). (p, C[;rho])) ((pp, AA) # GG))"
  proof (simp, rule combinators.vCons[OF j1])
    show "pp \<sharp> map (\<lambda>(p, C). (p, C[;rho])) GG"
    proof (induct GG, simp add: fresh_list_nil fresh_for_cxt)

qed
*)
(*>*)

-- " proof terms "
nominal_datatype trm = k | s | Asm par | app trm trm (infixl "^" 50)

-- " typing judgement "
inductive typg :: "cxt \<Rightarrow> trm \<Rightarrow> tp \<Rightarrow> bool"  ("_ \<turnstile> _ : _" 50)
  where
  dAsm[simp,intro!]: "\<lbrakk>valid G; (p,A) \<in> set G\<rbrakk> \<Longrightarrow> G \<turnstile> (Asm p) : A"
| dK[simp,intro!]: "valid G \<Longrightarrow> G \<turnstile> k : A \<rightarrow> B \<rightarrow> A"
| dS[simp,intro!]: "valid G \<Longrightarrow> G \<turnstile> s : (A \<rightarrow> B \<rightarrow> C) \<rightarrow> (A \<rightarrow> B) \<rightarrow> A \<rightarrow> C"
| dMP[intro!]: "\<lbrakk>G \<turnstile> f : A \<rightarrow> B; G \<turnstile> a : A\<rbrakk>\<Longrightarrow> G \<turnstile> f^a : B"

inductive_cases dK_inv: "G \<turnstile> k : X"
inductive_cases dS_inv: "G \<turnstile> s : X"
inductive_cases dMP_inv: "G \<turnstile> f^a : X"
inductive_cases Atm_inv: "G \<turnstile> a : Atm x"

thm dMP_inv
thm trm.inject

-- " fix weak inversion rules "
lemma dMP_inv:
  assumes h1:"G \<turnstile> f^a : X"
  and h2:"!!A. \<lbrakk>G \<turnstile> f : A \<rightarrow> X; G \<turnstile> a : A\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (rule dMP_inv[OF h1])
  fix fa A aa
  assume j1:"(f ^ a) = (fa ^ aa)"
    and j2:"G \<turnstile> fa : A \<rightarrow> X" and j3:"G \<turnstile> aa : A"
  from j1 trm.inject(2) have j4:"f = fa" "a = aa" by auto
  show P by (rule h2[unfolded j4, OF j2 j3])
qed

lemma typg_valid:
  assumes h:"G \<turnstile> a : A"
  shows "valid G"
  using h
by (induct, auto)

lemma dK_inv1: assumes h:"G \<turnstile> k : A \<rightarrow> B \<rightarrow> C" shows "A = C"
by (rule dK_inv[OF h], simp add: tp.inject)

lemma dS_inv1:
  assumes h:"G \<turnstile> s : X \<rightarrow> Y \<rightarrow> Z \<rightarrow> W"
  shows "\<exists> A B C. X = A \<rightarrow> B \<rightarrow> C \<and> Y = A \<rightarrow> B \<and> Z = A \<and> W = C"
by (rule dS_inv[OF h], simp add: tp.inject)

lemma dS_inv2:
  assumes h:"Gam \<turnstile> s : (A \<rightarrow> B \<rightarrow> C) \<rightarrow> (D \<rightarrow> E) \<rightarrow> F \<rightarrow> G"
  shows "A = D \<and> B = E \<and> A = F \<and> C = G"
by (rule dS_inv[OF h], simp add: tp.inject)

lemma K_shape:
  assumes h:"G \<turnstile> k : A"
  shows "\<exists> X Y. A = X \<rightarrow> Y \<rightarrow> X"
by (rule dK_inv[OF h], blast)

lemma S_shape:
  assumes h:"G \<turnstile> s : A"
  shows "\<exists> X Y Z. A = (X \<rightarrow> Y \<rightarrow> Z) \<rightarrow> (X \<rightarrow> Y) \<rightarrow> X \<rightarrow> Z"
by (rule dS_inv[OF h], blast)

lemma typg_weak:
  assumes h:"G \<turnstile> a : A" "sublst G H" "valid H"
  shows "H \<turnstile> a : A"
  using h by (induct, auto)


lemma typg_strengthen:
  assumes h:"H \<turnstile> a : A" "H = G1@(p,B)#G2" "p\<sharp>a"
  shows "G1@G2 \<turnstile> a : A"
  using h
proof (induct)
  case (dAsm GG pp AA)
  hence j1:"valid (G1 @ (p,B) # G2)"
    and j2:"(pp, AA) \<in> set (G1 @ (p,B) # G2)"
    and j3:"p \<sharp> Asm pp" by auto
  from j3 trm.fresh(3) fresh_atm have l1:"p ~= pp" by auto
  have k1:"valid (G1 @ G2)" using valid_strengthen[OF j1] .
  from j2 set_append have "(pp,AA) \<in> set G1 \<or> (pp,AA) \<in> set ((p,B) # G2)"
    by auto
  hence k2:"(pp,AA) \<in> set (G1 @ G2)"
  proof (rule, force)
    assume l2:"(pp,AA) \<in> set ((p,B) # G2)"
    thus ?thesis using l1 by force
  qed
  show "G1 @ G2 \<turnstile> Asm pp : AA" by(rule combinators.dAsm[OF k1 k2])
next
  case (dK GG AA BB)
  hence "valid (G1 @ (p,B)#G2)" by auto
  hence k1:"valid (G1 @ G2)" using valid_strengthen by simp
  show "G1 @ G2 \<turnstile> k : AA \<rightarrow> BB \<rightarrow> AA" by (rule combinators.dK[OF k1])
next
  case (dS GG AA BB CC)
  hence "valid (G1 @ (p,B)#G2)" by auto
  hence k1:"valid (G1 @ G2)" using valid_strengthen by simp
  show "G1 @ G2 \<turnstile> s : (AA \<rightarrow> BB \<rightarrow> CC) \<rightarrow> (AA \<rightarrow> BB) \<rightarrow> AA \<rightarrow> CC"
    by (rule combinators.dS[OF k1])
next
  case (dMP GG ff AA BB aa)
  hence ih1:"p \<sharp> ff \<Longrightarrow> G1 @ G2 \<turnstile> ff : AA \<rightarrow> BB"
    and ih2:"p \<sharp> aa \<Longrightarrow> G1 @ G2 \<turnstile> aa : AA"
    and j3:"p \<sharp> (ff ^ aa)"
    by auto
  from j3 trm.fresh have j4:"p \<sharp> ff" "p \<sharp> aa" by auto
  from ih1 j4 have k1:"G1 @ G2 \<turnstile> ff : AA \<rightarrow> BB" by simp
  from ih2 j4 have k2:"G1 @ G2 \<turnstile> aa : AA" by simp
  show "G1 @ G2 \<turnstile> ff ^ aa : BB" by (rule combinators.dMP[OF k1 k2])
qed

(*<*)
(*
-- " substitution preserves typing"
lemma sbst_pres_typg:
  assumes h:"G \<turnstile> a : A"
  shows "(map (%(p,C). (p,C[Q;=B])) G) \<turnstile> a : A[Q;=B]"
  using h
proof (induct)

lemma sbsts_pres_typg:
  assumes h:"\<turnstile> a : A"
  shows "\<turnstile> a : (A[;rho])"
  using h
by (induct, auto)

lemma typg_poly:
  assumes h1:"\<turnstile> a : A" and h2:"\<turnstile> a : B"
  shows "\<exists>rho. B = A[;rho]"
  using h1 h2
proof (induct)
  case (dK AA BB)
  have j:"\<turnstile> k : B" by fact
  from K_shape[OF j] obtain X and Y where j1:"B = X \<rightarrow> Y \<rightarrow> X" by auto
  let ?rho = "(AA,X)#(BB,Y)#[]"
  have j2:"(X \<rightarrow> Y \<rightarrow> X) = ((AA \<rightarrow> BB \<rightarrow> AA)[;(?rho)])" proof simp
  show "\<exists>rho. B = (AA \<rightarrow> BB \<rightarrow> AA)[;rho]"
  proof (subst j1)
    assume p:"
    using K_shape[OF j] proof (auto)
\<dots>
qed
*)
(*>*)

-- "reduction relation on terms"
inductive red :: "trm \<Rightarrow> trm \<Rightarrow> bool"  ("_ \<guillemotright> _" 40)
  where
  rK[simp,intro!]: "k^a^b \<guillemotright> a"
| rS[simp,intro!]: "s^a^b^c \<guillemotright> a^c^(b^c)"
| rMPl[intro]: "a \<guillemotright> a' \<Longrightarrow> a^b \<guillemotright> a'^b"
| rMPr[intro]: "a \<guillemotright> a' \<Longrightarrow> b^a \<guillemotright> b^a'"

inductive_cases rK_inv: "k^a^b \<guillemotright> x"

-- "reduction preserves typing"
lemma subjRed:
  assumes h:"a \<guillemotright> b" "G \<turnstile> a : A"
  shows "G \<turnstile> b : A"
  using h
proof (induct arbitrary: A)    -- " needs the arbitrary A "
  -- " two inductive cases first: rippling may help "
  case (rMPl a1 a2 bb X)
  have j1:"a1 \<guillemotright> a2" and j2:"!!X. G \<turnstile> a1 : X \<Longrightarrow> G \<turnstile> a2 : X"
    and j3:"G \<turnstile> a1 ^ bb : X"
    by fact+
  show "G \<turnstile> a2 ^ bb : X"
  proof (rule dMP_inv[OF j3])
    fix ff Y aa assume p1:"G \<turnstile> a1 : Y \<rightarrow> X" and p2:"G \<turnstile> bb : Y"
    from j2[OF p1] have P1:"G \<turnstile> a2 : Y \<rightarrow> X" .
    show ?thesis using dMP[OF P1 p2] .
  qed
next
  case (rMPr a1 a2 bb X)
  have j1:"a1 \<guillemotright> a2" and j2:"!!X. G \<turnstile> a1 : X \<Longrightarrow> G \<turnstile> a2 : X"
    and j3:"G \<turnstile> bb ^ a1 : X"
    by fact+
  show "G \<turnstile> bb ^ a2 : X"
  proof (rule dMP_inv[OF j3])
    fix Y assume p1:"G \<turnstile> bb : Y \<rightarrow> X" and p2:"G \<turnstile> a1 : Y"
    from j2[OF p2] have P2:"G \<turnstile> a2 : Y" .
    show ?thesis using dMP[OF p1 P2] .
  qed
next   -- " I guess rippling can't help with the base cases "
  case (rK aa bb Y)
  have j:"G \<turnstile> k ^ aa ^ bb : Y" by fact
  show "G \<turnstile> aa : Y"
  proof (rule dMP_inv[OF j])
    fix AA  assume p:"G \<turnstile> k ^ aa : AA \<rightarrow> Y"
    show ?thesis
    proof (rule dMP_inv[OF p])
      fix BB assume q1:"G \<turnstile> k : BB \<rightarrow> AA \<rightarrow> Y" and q2:"G \<turnstile> aa : BB"
      show ?thesis using dK_inv1[OF q1] q2 by simp
    qed
  qed
next
  case (rS aa bb cc W)
  have j:"G \<turnstile> s ^ aa ^ bb ^ cc : W" by fact
  show "G \<turnstile> aa ^ cc ^ (bb ^ cc) : W"
  proof (rule dMP_inv[OF j])
    fix AA assume p1:"G \<turnstile> s ^ aa ^ bb : AA \<rightarrow> W" and p2:"G \<turnstile> cc : AA"
    show ?thesis
    proof (rule dMP_inv[OF p1])
      fix BB assume q1:"G \<turnstile> s ^ aa : BB \<rightarrow> AA \<rightarrow> W" and q2:"G \<turnstile> bb : BB"
      show ?thesis
      proof (rule dMP_inv[OF q1])
	fix CC assume r1:"G \<turnstile> s : CC \<rightarrow> BB \<rightarrow> AA \<rightarrow> W" and r2:"G \<turnstile> aa : CC"
	from dS_inv1[OF r1] obtain X and Y and Z 
	  where eqs:"CC = X \<rightarrow> Y \<rightarrow> Z" "BB = X \<rightarrow> Y" "AA = X" "W = Z"
	  by auto
	from r2 eqs have R2:"G \<turnstile> aa : X \<rightarrow> Y \<rightarrow> Z" by simp
	from q2 eqs have Q2:"G \<turnstile> bb : X \<rightarrow> Y" by simp
	from p2 eqs have P2:"G \<turnstile> cc : X" by simp
	show ?thesis using eqs R2 Q2 P2 by auto
      qed
    qed
  qed
qed

inductive fitch :: "cxt \<Rightarrow> trm \<Rightarrow> tp \<Rightarrow> bool"  ("_ \<parallel>- _ : _" 50)
  where
  fAsm[simp,intro!]: "((p,A)#G) \<parallel>- x : X \<Longrightarrow> ((p,A)#G) \<parallel>- (Asm p) : A"
| fweak[simp,intro!]: "\<lbrakk>G \<parallel>- a : A; p\<sharp>G\<rbrakk>\<Longrightarrow> ((p,B)#G) \<parallel>- a : A"
| fK[simp,intro!]: "Nil \<parallel>- k : A \<rightarrow> B\<rightarrow> A"
| fS[simp,intro!]: "Nil \<parallel>- s : (A \<rightarrow> B \<rightarrow> C) \<rightarrow> (A \<rightarrow> B) \<rightarrow> A \<rightarrow> C"
| fMP[intro!]: "\<lbrakk>G \<parallel>- f : A \<rightarrow> B; G \<parallel>- a : A\<rbrakk>\<Longrightarrow> G \<parallel>- f^a : B"

inductive_cases fK_inv: "G \<parallel>- k : X"
inductive_cases fS_inv: "G \<parallel>- s : X"
inductive_cases fMP_inv: "G \<parallel>- f^a : X"
inductive_cases fAtm_inv: "G \<parallel>- a : Atm x"

lemma valid_fitch:
  assumes h:"valid G"
  shows "\<exists> x X. G \<parallel>- x : X"
  using h
by (induct, force, force)

lemma fitch_valid:
  assumes h:"\<exists> x X. G \<parallel>- x : X"
  shows "valid G"
proof -
  from h obtain x X where j:"G \<parallel>- x : X" by auto
  thus ?thesis by (induct, auto)
qed

lemma fitch_typg:
  assumes h:"G \<parallel>- a : A"
  shows "G \<turnstile> a : A"
  using h
proof (induct)
  case (fAsm pp AA GG xx XX)
  have j2:"(pp, AA) # GG \<turnstile> xx : XX"
    by fact
  from typg_valid[OF j2] have k:"valid ((pp, AA) # GG)" .
  show "(pp,AA)#GG \<turnstile> Asm pp : AA" by (rule dAsm, simp_all add: k)
next
  case (fweak GG aa AA pp BB)
  have j2:"GG \<turnstile> aa : AA" and j3:"pp \<sharp> GG"
    by fact+
  from typg_valid[OF j2] have k:"valid GG" .
  show "(pp, BB) # GG \<turnstile> aa : AA"
  by (rule typg_weak[OF j2], force, rule vCons[OF k], simp add: j3)
next
  case (fK AA BB)
  show "[] \<turnstile> k : AA \<rightarrow> BB \<rightarrow> AA"
    by (rule dK, simp)
next
  case (fS AA BB CC)
  show "[] \<turnstile> s : (AA \<rightarrow> BB \<rightarrow> CC) \<rightarrow> (AA \<rightarrow> BB) \<rightarrow> AA \<rightarrow> CC"
    by (rule dS, simp)
next
  case (fMP GG ff AA BB aa)
  have ih1:"GG \<turnstile> ff : AA \<rightarrow> BB"
    and ih2:"GG \<turnstile> aa : AA"
    by fact+
  show "GG \<turnstile> ff ^ aa : BB"
    by (rule dMP[OF ih1 ih2])
qed
(*<*)
(* 
lemma fitch_lookup:
  assumes h:"(p,A) \<in> set G" and j:"G \<parallel>- x : X"
  shows "G \<parallel>- (Asm p) : A"
proof -
  from in_set_conv_decomp[of "(p,A)" G] h
  obtain G1 G2 where j1:"G = G1 @ (p,A)#G2" by auto
  show ?thesis proof (subst j1)

  hence "valid ((p,A)#G2)"
    using valid_Tl[of G1 "(p,A)#G2"] fitch_valid[OF j] by auto
  show ?thesis proof (subst j1)


qed


lemma typg_fitch:
  assumes h:"G \<turnstile> a : A"
  shows "G \<parallel>- a : A"
  using h
proof (induct)
  case (dAsm GG pp AA)
  have j1:"valid GG" and j2:"(pp, AA) \<in> set GG" by fact+
  show "GG \<parallel>- Asm pp : AA" using j2
  proof (induct GG, force)

  case (dK GG AA BB)
  have j:"valid GG" by fact
  show "GG \<parallel>- k : AA \<rightarrow> BB \<rightarrow> AA"
*)

end;
(*>*)