theory combinators
imports Main
begin

typedecl ap      (* atomic propositions *)

(** types (propositions) **)
datatype tp = Atm ap 
            | Arr tp tp  (infixr "\<rightarrow>" 100)

(** unary substitution for atomic types **)
consts
  sbst :: "tp \<Rightarrow> ap \<Rightarrow> tp \<Rightarrow> tp"  ("_[_;=_]" 75)
primrec
  "(Atm P)[Q;=A] = (if P = Q then A else (Atm P))"
  "(A \<rightarrow> B)[Q;=C] = (A[Q;=C]) \<rightarrow> (B[Q;=C])"

(** simultaneous substitution for atomic types **)
consts
  assoc_def :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b \<Rightarrow> 'b"
primrec
  "assoc_def a [] d = d"       (* lookup fails; return default *)
  "assoc_def a (cb#l) d = (if a = fst cb then (snd cb)
                                         else (assoc_def a l d))"

consts
  sbsts :: "tp \<Rightarrow> (ap * tp) list \<Rightarrow> tp"  ("_[;_]" 100 )
primrec
  "(Atm P)[;rho] = assoc_def P rho (Atm P)"
  "(P \<rightarrow> Q)[;rho] = (P[;rho]) \<rightarrow> (Q[;rho])"

(** proof terms **)
datatype trm = k | s | app trm trm (infixl "^" 50)

(** typing judgement **)
inductive typg :: "trm \<Rightarrow> tp \<Rightarrow> bool"  ("\<turnstile> _ : _" 50)
  where
  dK[simp,intro!]: "\<turnstile> k : A \<rightarrow> B \<rightarrow> A"
| dS[simp,intro!]: "\<turnstile> s : (A \<rightarrow> B \<rightarrow> C) \<rightarrow> (A \<rightarrow> B) \<rightarrow> A \<rightarrow> C"
| dMP[intro!]: "\<lbrakk>\<turnstile> f : A \<rightarrow> B; \<turnstile> a : A\<rbrakk>\<Longrightarrow> \<turnstile> f^a : B"

inductive_cases dK_inv: "\<turnstile> k : X"
inductive_cases dS_inv: "\<turnstile> s : X"
inductive_cases dMP_inv: "\<turnstile> f^a : X"
inductive_cases Atm_inv: "\<turnstile> a : Atm x"

lemma dK_inv1: assumes h:"\<turnstile> k : A \<rightarrow> B \<rightarrow> C" shows "A = C"
by (rule dK_inv[OF h], force)

lemma dS_inv1:
  assumes h:"\<turnstile> s : X \<rightarrow> Y \<rightarrow> Z \<rightarrow> W"
  shows "\<exists> A B C. X = A \<rightarrow> B \<rightarrow> C \<and> Y = A \<rightarrow> B \<and> Z = A \<and> W = C"
by (rule dS_inv[OF h], force)

lemma dS_inv2:
  assumes h:"\<turnstile> s : (A \<rightarrow> B \<rightarrow> C) \<rightarrow> (D \<rightarrow> E) \<rightarrow> F \<rightarrow> G"
  shows "A = D \<and> B = E \<and> A = F \<and> C = G"
by (rule dS_inv[OF h], force)

lemma K_shape:
  assumes h:"\<turnstile> k : A"
  shows "\<exists> X Y. A = X \<rightarrow> Y \<rightarrow> X"
by (rule dK_inv[OF h], simp)

lemma S_shape:
  assumes h:"\<turnstile> s : A"
  shows "\<exists> X Y Z. A = (X \<rightarrow> Y \<rightarrow> Z) \<rightarrow> (X \<rightarrow> Y) \<rightarrow> X \<rightarrow> Z"
by (rule dS_inv[OF h], simp)

(** substitution preserves typing **)
lemma sbst_pres_typg:
  assumes h:"\<turnstile> a : A"
  shows "\<turnstile> a : A[Q;=B]"
  using h
by (induct, auto)

lemma sbsts_pres_typg:
  assumes h:"\<turnstile> a : A"
  shows "\<turnstile> a : (A[;rho])"
  using h
by (induct, auto)


(** reduction relation on terms **)
inductive red :: "trm \<Rightarrow> trm \<Rightarrow> bool"  ("_ \<guillemotright> _" 40)
  where
  rK[simp,intro!]: "k^a^b \<guillemotright> a"
| rS[simp,intro!]: "s^a^b^c \<guillemotright> a^c^(b^c)"
| rMPl[intro]: "a \<guillemotright> a' \<Longrightarrow> a^b \<guillemotright> a'^b"
| rMPr[intro]: "a \<guillemotright> a' \<Longrightarrow> b^a \<guillemotright> b^a'"

inductive_cases rK_inv: "k^a^b \<guillemotright> x"

(* reduction preserves typing *)
lemma subjRed:
  assumes h:"a \<guillemotright> b" "\<turnstile> a : A"
  shows "\<turnstile> b : A"
  using h
proof (induct arbitrary: A)    (** needs the arbitrary A **)
  (** two inductive cases first: rippling may help **)
  case (rMPl a1 a2 bb X)
  have j1:"a1 \<guillemotright> a2" and j2:"!!X. \<turnstile> a1 : X \<Longrightarrow> \<turnstile> a2 : X"
    and j3:"\<turnstile> a1 ^ bb : X"
    by fact+
  show "\<turnstile> a2 ^ bb : X"
  proof (rule dMP_inv[OF j3])
    fix Y assume p1:"\<turnstile> a1 : Y \<rightarrow> X" and p2:"\<turnstile> bb : Y"
    from j2[OF p1] have P1:"\<turnstile> a2 : Y \<rightarrow> X" .
    show ?thesis using dMP[OF P1 p2] .
  qed
next
  case (rMPr a1 a2 bb X)
  have j1:"a1 \<guillemotright> a2" and j2:"!!X. \<turnstile> a1 : X \<Longrightarrow> \<turnstile> a2 : X"
    and j3:"\<turnstile> bb ^ a1 : X"
    by fact+
  show "\<turnstile> bb ^ a2 : X"
  proof (rule dMP_inv[OF j3])
    fix Y assume p1:"\<turnstile> bb : Y \<rightarrow> X" and p2:"\<turnstile> a1 : Y"
    from j2[OF p2] have P2:"\<turnstile> a2 : Y" .
    show ?thesis using dMP[OF p1 P2] .
  qed
next   (** I guess rippling can't help with the base cases **)
  case (rK aa bb Y)
  have j:"\<turnstile> k ^ aa ^ bb : Y" by fact
  show "\<turnstile> aa : Y"
  proof (rule dMP_inv[OF j])
    fix AA  assume p:"\<turnstile> k ^ aa : AA \<rightarrow> Y"
    show ?thesis
    proof (rule dMP_inv[OF p])
      fix BB assume q1:"\<turnstile> k : BB \<rightarrow> AA \<rightarrow> Y" and q2:"\<turnstile> aa : BB"
      show ?thesis using dK_inv1[OF q1] q2 by simp
    qed
  qed
next
  case (rS aa bb cc W)
  have j:"\<turnstile> s ^ aa ^ bb ^ cc : W" by fact
  show "\<turnstile> aa ^ cc ^ (bb ^ cc) : W"
  proof (rule dMP_inv[OF j])
    fix AA assume p1:"\<turnstile> s ^ aa ^ bb : AA \<rightarrow> W" and p2:"\<turnstile> cc : AA"
    show ?thesis
    proof (rule dMP_inv[OF p1])
      fix BB assume q1:"\<turnstile> s ^ aa : BB \<rightarrow> AA \<rightarrow> W" and q2:"\<turnstile> bb : BB"
      show ?thesis
      proof (rule dMP_inv[OF q1])
	      fix CC assume r1:"\<turnstile> s : CC \<rightarrow> BB \<rightarrow> AA \<rightarrow> W" and r2:"\<turnstile> aa : CC"
	      from dS_inv1[OF r1] obtain X and Y and Z 
	        where eqs:"CC = X \<rightarrow> Y \<rightarrow> Z" "BB = X \<rightarrow> Y" "AA = X" "W = Z"
	        by auto
	      from r2 eqs have R2:"\<turnstile> aa : X \<rightarrow> Y \<rightarrow> Z" by simp
	      from q2 eqs have Q2:"\<turnstile> bb : X \<rightarrow> Y" by simp
	      from p2 eqs have P2:"\<turnstile> cc : X" by simp
	      show ?thesis using eqs R2 Q2 P2 by auto
      qed
    qed
  qed
qed



end;