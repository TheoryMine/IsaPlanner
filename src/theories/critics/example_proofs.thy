header{* The Domains of Peano Arithmetic and Lists *}

theory example_proofs = PreList + HOL_IsaP:

section{* Peano Arithmetic *}

datatype N = zero  ("0\<^isub>N")
           | suc N ("suc\<^isub>N _" [500] 500)
syntax
  "_suc"     :: "N => N" ("suc _" [500] 500)
translations
  "0" == "0\<^isub>N"
  "suc x" == "suc\<^isub>N x"

declare N.inject[wrule]

consts add :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "+\<^isub>N" 510)
translations "x + y" == "x +\<^isub>N y" 
primrec 
  add_0[wrule]    :  "(0 + y) = y"
  add_suc[wrule]  :  "suc x + y = suc (x + y)"

consts mult :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "*\<^isub>N" 510)
translations "x * y" == "x *\<^isub>N y" 
primrec 
  mult_0[wrule]    :  "(0 * y) = 0"
  mult_suc[wrule]  :  "(suc x) * y = y + (x * y)"

consts exp :: "[N, N] => N" (infixr "exp" 515)
translations "op ^" == "op exp"
primrec
  exp_0[wrule]   : "x ^ 0 = suc 0"
  exp_suc[wrule] : "x ^ (suc y) = x * (x ^ y)"

consts less :: "[N, N] => bool" (infix "less" 520)
translations "op <" == "op less"
primrec
  less_0[wrule]   : "x < 0 = False"
  less_suc[wrule] : "x < (suc y) = (case x of 0 => True | suc z => z < y)"

consts sumto :: "[ N, N \<Rightarrow> N] => N" ("sumto _ _" [520, 520] 520)
primrec
  sumto_0[wrule]   : "sumto 0 f = f 0"
  sumto_Suc[wrule] : "sumto (suc n) f = (f (suc n)) + (sumto n f)"



section{* Lists *}

datatype  'a List = nil ("[]") 
                 | cons "'a" "'a List"      (infixr "#" 490)
syntax
  "@list"     :: "args => 'a List"                          ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

declare List.inject[wrule]

consts len :: "'a List \<Rightarrow> N"   ("len _" [500] 500)
primrec 
  len_nil[wrule]:     "len [] = 0"
  len_cons[wrule]:    "len (h # t) = suc (len t)"

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 500)
primrec 
  append_0[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"

consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [510] 510)
primrec 
  rev_nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ [h]"

consts qrev :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" ("qrev _ _" [510,510] 510)
primrec 
  qrev_nil[wrule]:  "qrev [] l = l"
  qrev_cons[wrule]: "qrev (h # t) l = qrev t (h # l)"

consts rot :: "N \<times> 'a List \<Rightarrow> 'a List"   ("rot _" [505] 505)
recdef rot "measure (size o fst)"
  rot_0[wrule]:   "rot (0, l) = l"
  rot_nil[wrule]: "rot (n, []) = []"
  rot_suc[wrule]: "rot (suc n, h # t) = rot (n, t @ [h])"


consts map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a List \<Rightarrow> 'b List)"  ("map _ _" [510] 510)
primrec
  map_nil[wrule]:  "map f []     = []"
  map_cons[wrule]: "map f (x#xs) = f(x)#map f xs"

consts zip :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"   ("zip _ _" [505] 505)
primrec
  zip_nil[wrule]:  "zip [] ys = ys"
  zip_cons[wrule]: "zip (x # xs) ys = 
    (case ys of [] \<Rightarrow> x # xs | (y # ys) \<Rightarrow> x # y # (zip xs ys))"

consts zip2 :: "'a List \<times> 'a List \<Rightarrow> 'a List"   ("zip2 _" [505] 505)
recdef zip2  "measure (size o fst)" 
  zip2_nil1[wrule]: "zip2 ([], ys) = ys"
  zip2_nil2[wrule]: "zip2 (xs, []) = xs"
  zip2_cons[wrule]: "zip2 (x#xs, y#ys) = x # y # (zip2(xs,ys))"


section{* Equivalence of Reverse and Quick Reverse *}

lemma assoc_append: "x @ y @ z = x @ (y @ z)" 
by (induct x, simp_all)

lemma append_rev_qrev: "(rev x) @ l = qrev x l"
proof (ppinduct x)
  fix l show "rev [] @ l = qrev [] l" by simp
next 
  fix a L l'
  assume ih: "\<forall>l. rev L @ l = qrev L l"
  have "qrev L ([a] @ l') = qrev L (a # l')"
    by simp
  hence "rev L @ ([a] @ l') = qrev L (a # l')"
    -- "Weak fertilisation"
    by (eqstep ih)
  hence "rev L @ [a] @ l' = qrev L (a # l')"
    -- "Weak fertilisation Critic on lhs"
    by (eqstep assoc_append)
  thus "rev (a # L) @ l' = qrev (a # L) l'" 
    by (rippling skelthms: ih)
qed


lemma append_rev_qrev: "(rev x) @ l = qrev x l"
apply (ppinduct x)
apply simp
apply (rippling)
apply (wfert)
oops

lemma append_nil2: "l = l @ []" by (induct l, simp_all)

text {* accidental error: trying to prove a non-theorem: *}
lemma qrev_xs_ys: "qrev xs ys = ys @ (qrev xs [])"
proof (ppinduct xs)
  fix ys
  show "qrev [] ys = ys @ (qrev [] [])" by (simp add: append_nil2)
next
  fix a L ys
  assume IH: "\<forall>ys. qrev L ys = ys @ qrev L [] "
  show "qrev (a # L) ys = ys @ qrev (a # L) []" 
    apply (rippling skelthms: IH)
    apply (eqstep IH)
oops
lemma qrev_xs_ys_fert_lemma: "(a # ys) @ qrev L [] = ys @ qrev (a # L) []"
proof (ppinduct L)
  fix ys a
  show "(a # ys) @ qrev [] [] = ys @ qrev [a] []"
    apply simp
oops -- {* now I see that its not a theorem and that I made an error *}


text {* Corrected version of above *}
lemma qrev_xs_ys_fert_lemma: 
  "qrev L [] @ (a # ys) = qrev (a # L) [] @ ys"
proof (ppinduct "L")
  fix ys a 
  show "qrev [] [] @ (a # ys) = qrev [a] [] @ ys" by simp
next 
  fix a L ys aa
  assume IH: "\<forall>ys a. qrev L [] @ (a # ys) = qrev (a # L) [] @ ys"
  show "qrev (a # L) [] @ (aa # ys) = qrev (aa # a # L) [] @ ys"
    apply (rippling skelthms: IH) back back
 -- {* fixme: caching should make only once answer - and we should 
       prune failures i.e. the first result *}
 -- {* here I'm stuck but have an idea to prove a new thm *}
oops

lemma qrev_xs_ys: "qrev xs ys = (qrev xs []) @ ys"
proof (ppinduct xs)
  fix ys
  show "qrev [] ys = (qrev [] []) @ ys" by simp 
next
  fix a L ys
  assume IH: "\<forall>ys. qrev L ys = qrev L [] @ ys"
  show "qrev (a # L) ys = qrev (a # L) [] @ ys" 
    apply (rippling skelthms: IH) back 
    apply (eqstep IH) -- {* need lemma:  *}
    oops 


lemma qrev_xs_ys: "qrev xs (zs @ ys) = (qrev xs zs) @ ys"
proof (ppinduct xs)
  fix zs ys
  show "qrev [] (zs @ ys) = (qrev [] zs) @ ys" by simp 
next
  fix a L ys zs
  assume IH: "\<forall>zs ys. qrev L (zs @ ys) = qrev L zs @ ys"
  show "qrev (a # L) (zs @ ys) = qrev (a # L) zs @ ys" 
    apply (rippling skelthms: IH) back back back back back  -- {* back back *}
    apply (eqstep IH) -- {* need lemma:  *}
    apply rule
    done
qed

term "%x. f x"

lemma qrev_qrev_id: "qrev (qrev xs []) [] = xs"
proof (ppinduct xs)
  show "qrev qrev [] [] [] = []" by simp
next
  fix a L
  assume IH: "qrev qrev L [] [] = L"
  show "qrev qrev (a # L) [] [] = a # L" 
    apply (rippling skelthms: IH) back
oops


theorem rev_qrev: "rev x = qrev x []"
proof (induct x)
  show "rev [] = qrev [] []" by simp
next 
  fix a L
  assume ih: "rev L = qrev L []"
  have "rev L @ [a] = qrev L [a]"
    -- "Generalisation critic to introduce a new sink"
    by (eqstep append_rev_qrev, simp)
  thus "rev (a # L) = qrev (a # L) []"
    by (rippling skelthms: ih, eqstep qrev_cons)
qed

text {* Note the final proof will actually be different from the above
  - which shows how it was found. In particular, the theorem is proved
  to be an "instance" of the generalisation lemma: *}

lemma append_nil2: "l = l @ []" by (induct l, simp_all)

theorem rev_qrev: "rev x = qrev x []"
proof - 
  have lhs: "rev x = rev x @ []" 
    -- "Conjecture with subterm generalisation"
    by (rule append_nil2)
  have rhs: "qrev x [] = qrev x []" by (rule refl)
  show ?thesis by (eqstep lhs, eqstep rhs, rule append_rev_qrev)
qed


section{* Strange Reverse Append Combination *}

lemma append_nil2: "l = l @ []" by (induct l, simp_all)

lemma assoc_append: "x @ y @ z = x @ (y @ z)" 
by (induct x, simp_all)

lemma append_single_cons: "(z @ [a]) @ L = z @ (a # L)"
by (ppinduct z, simp_all)

theorem rev_rev_append: "rev (rev t @ l) = rev l @ t"
proof (ppinduct t)
  fix l 
  have "rev l = rev l @ []" 
    -- "Conjecture with subterm generalisation"
    by (rule append_nil2)
  thus "rev (rev [] @ l) = rev l @ []" by (simp)
next 
  fix a L l' 
  assume ih: "\<forall>l. rev (rev L @ l) = rev l @ L"
  have "(rev l' @ [a]) @ L = rev l' @ (a # L)" 
    -- "Conjecture with subterm generalisation"
    by (eqstep append_single_cons, rule) 
  hence "rev ([a] @ l') @ L = rev l' @ (a # L)" 
    by simp
  hence "rev (rev L @ ([a] @ l')) = rev l' @ (a # L)" 
    -- "Weak fertilisation"
    by (eqstep ih)
  hence "rev (rev L @ [a] @ l') = rev l' @ (a # L)" 
    -- "Weak fertilisation critic on lhs"
    by (eqstep assoc_append) 
  thus "rev (rev (a # L) @ l') = rev l' @ (a # L)"
    by (rippling skelthms: ih)
qed

text {* Note, in the above proof, the role of @{text "simp"} after
  weak fertilisation! If this is not done then the resulting
  conjecture is the same as a weak fertilisation critic - but
  eventually leads (I think) to the same conjecture *}

text {* Note: This theorem is actually a trivial consequence of:
  @{term "rev (rev x) = x"} and @{term "rev (a @ b) = rev b @ rev a"}
  *}

axioms revrev: "rev (rev x) = x"
axioms rev_append_distr: "rev (a @ b) = rev b @ rev a"
theorem "rev (rev t @ l) = rev l @ t" 
by (simp add: revrev rev_append_distr)


section{* Rotate Length *}

lemma append_nil2: "l = l @ [] " by (induct l, simp_all)

lemma assoc_append: "x @ y @ z = x @ (y @ z)" 
by (induct x, simp_all)

lemma append_single_cons: "(z @ [a]) @ L = z @ (a # L)"
by (ppinduct z, simp_all)

lemma rot_append: "rot (len l, l @ k) = k @ l"
proof (ppinduct l)
  fix k 
  have "k = k @ []" 
    -- "Conjecture from subgoal"
    by (rule append_nil2)
  thus "rot (len [], [] @ k) = k @ []" by (simp)
next
  fix a L k'
  assume ih: "\<forall>k. rot (len L, L @ k) = k @ L"
  have "k' @ [a] @ L = k' @ (a # L)"
    -- "Conjecture from subgoal"
    by (rule append_single_cons)
  hence "rot (len L, L @ (k' @ [a])) = k' @ (a # L)"
    -- "Weak fertilisation"
    by (eqstep ih)
  hence "rot (len L, L @ k' @ [a]) = k' @ (a # L)"
    -- "Weak fertilisation critic on the lhs" 
    by (eqstep assoc_append)
  thus "rot (len (a # L), (a # L) @ k') = k' @ (a # L)"
    by (rippling skelthms: ih)
qed


theorem rot_len: "rot (len l, l) = l"
proof (induct l)
  case nil show ?case by simp
next
  fix a L
  assume ih: "rot (len L, L) = L"
  have "rot (len L, L @ [a]) = a # L"
    -- "Generalisation critic to introduce a new sink"
    by (eqstep rot_append, simp)
  thus "rot (len (a # L), a # L) = a # L"
    by (rippling skelthms: ih, eqstep rot_suc)
qed

text {* Note the final proof will actually be different from the above
  - which shows how it was found. In particular, the theorem is proved
  to be an
 "instance" of the generalisation lemma: *}

theorem rot_len: "rot (len l, l) = l"
proof - 
  have lhs: "rot (len l, l) = rot (len l, l @ [])" 
    -- "Conjecture from subgoal"
    by (eqstep append_nil2, rule refl)
  have rhs: "l = [] @ l" by simp
  show ?thesis by (eqstep lhs, eqstep rhs, rule rot_append)
qed

text {* Question: While the above is what was done in Ireland's work,
  it actually seems easier, given that we are
  almost there, to simply finish off the inductive proof, although it
  does not really express the kind of reasoning being used.  *}


section{* Zip *}

lemma [simp]:"(0 = len x) = (x = [])" by (cases "x", simp_all)
lemma [simp]:"(len x = 0) = (x = [])" by (cases "x", simp_all)

theorem "len a = len x \<and> len b = len y \<Longrightarrow> 
  zip (a @ b) (x @ y) = (zip a x) @ (zip b y)"
proof (ppinduct a)
  fix y x b :: "'a List"
  assume "len [] = len x \<and> len b = len y"
  thus "zip ([] @ b) (x @ y) = ( zip [] x) @ (zip b y)"
    by simp
next
  fix a :: "'a" 
  fix List y x b :: "'a List"
  assume IH: "\<forall>y x b.
           len List = len x \<and> len b = len y \<longrightarrow>
           zip (List @ b) (x @ y) = (zip List x) @ (zip b y)"
  assume "len (a # List) = len x \<and> len b = len y"
  from IH 
  show "zip ((a # List) @ b) (x @ y) = (zip (a # List) x) @ (zip b y)"
    oops
(*    apply rippling -- raises a "LIST hd" exception!  *)

end;
