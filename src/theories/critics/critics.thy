theory critics = PreList + HOL_IsaP :
section {* The Datatype Definitions *}

ML {* set quick_and_dirty; *}

text {* We use Isabelle's recursive datatype package to define natural
numbers and lists.  *}

datatype N = NZero  ("0\<^isub>N")
           | NSuc N ("S\<^isub>N _" [500] 500)
syntax
  "_S"     :: "N => N" ("S _" [500] 500)
translations
  "0" == "0\<^isub>N"
  "S x" == "S\<^isub>N x"

declare N.inject[impwrule]

text {* These syntax translation allow the use of @{text "0"} and
@{text "S"} while avoiding conflicts with Isabelle's internal theory of
natural numbers. *}

datatype 'a List = Nil ("[]") 
                 | Cons "'a" "'a List"      (infixr "#" 490)
syntax
  "@list"     :: "args => 'a List"                          ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

(* declare List.inject[wrule] *)

text {* The above syntax translation(s) for lists allows us to use @{text
"#"} as an infix symbol for @{text "Cons"} and to abbreviate @{text "x
# y # z # []))"} as @{text "[x,y,z]"}. *}


section {* Functions Definitions *}

text {* Given these definitions we can now define the usual functions. *}

consts NAdd :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "+\<^isub>N" 510)
translations "x + y" == "x +\<^isub>N y" 
primrec 
  NAdd_0[wrule]: "0 + n = n"
  NAdd_S[wrule]: "S m + n = S (m + n)"

consts NMult :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "*\<^isub>N" 510)
translations "x * y" == "x *\<^isub>N y" 
primrec 
  NMult_0[wrule]: "0 * n = 0"
  NMult_S[wrule]: "(S m) * n = n + (m * n)"

consts NExp :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "^\<^isub>N" 515)
translations "x ^ y" == "x ^\<^isub>N y" 
primrec 
  NExp_0[wrule]: "n ^ 0 = S 0"
  NExp_S[wrule]: "m ^ (S n) = n * (m ^ n)"

consts NEven :: "N \<Rightarrow> bool" ("even _" [520] 520)
recdef NEven "measure size"
  NEven_0[wrule]:       "even 0 = True"
  NEven_not_S_0[wrule]: "even (S 0) = False"
  NEven_S_S[wrule]:     "even (S S n) = even n"

consts len :: "'a List \<Rightarrow> N"   ("len _" [500] 500)
primrec 
  len_Nil[wrule]:     "len [] = 0"
  len_Cons[wrule]:    "len (h # t) = S (len t)"

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 500)
primrec 
  append_0[wrule]      : "[] @ l = l"
  append_Cons[wrule]   : "(h # t) @ l = h # (t @ l)"

consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [510] 510)
primrec 
  rev_Nil[wrule]: "rev [] = []"
  rev_Cons[wrule]: "rev (h # t) = rev t @ [h]"

consts qrev :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" ("qrev _ _" [510,510] 510)
primrec 
  qrev_Nil[wrule]:  "qrev [] l = l"
  qrev_Cons[wrule]: "qrev (h # t) l = qrev t (h # l)"

consts rot :: "N \<times> 'a List \<Rightarrow> 'a List"   ("rot _" [505] 505)
recdef rot "measure (size o fst)"
  rot_0[wrule]:   "rot (0, l) = l"
  rot_Nil[wrule]: "rot (n, []) = []"
  rot_S[wrule]:   "rot (S n, h # t) = rot (n, t @ [h])"

text {* intersting remark: the simplification theorems are not what
you would expect! @{term "rot (0, l) = l"} becomes two theorems for
each case of "l". Presumably, we should automatically construct the
more general version and drop the other two? *}

consts zip :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"   ("zip _ _" [505] 505)
primrec
  zip_Nil[wrule]:  "zip [] ys = ys"
  zip_Cons[wrule]: "zip (x # xs) ys = 
    (case ys of [] \<Rightarrow> x # xs | (y # ys) \<Rightarrow> x # y # (zip xs ys))"

consts zip2 :: "'a List \<times> 'a List \<Rightarrow> 'a List"   ("zip2 _" [505] 505)
recdef zip2 "measure (size o fst)"
  zip2_Nil1[wrule]: "zip2 ([], ys) = ys"
  zip2_Nil2[wrule]: "zip2 (xs, []) = xs"
  zip2_Cons[wrule]: "zip2 (x#xs, y#ys) = x # y # (zip2(xs,ys))"


section {* Induction Rules *}

text {* Isabelle automatically generates induction rules for recursive
  datatypes and recursive functions.  The name of the induction rule
  is the datatype/function name concatenated onto ``.induct''. For
  example, the following induction rules have been automatically
  derived from the above definitions:

\subsubsection*{@{text "N.induct"}}
@{thm [display] N.induct}

\subsubsection*{@{text "List.induct"}}
@{thm [display] List.induct}

\subsubsection*{@{text "rot.induct"}}
@{thm [display] rot.induct}

\subsubsection*{@{text "NEven.induct"}}
@{thm [display] NEven.induct}

The default rule used by Isabelle's induction tactic is the one
associated with the definition of the data type.
*}

(*<*)
section {* Proofs *}

subsection {* Reverse *}

(*
ML {* RippleTac.print_wrules_of_theory (the_context()); *}
ML {* trace_rippling := true; *}
ML {* set show_types; *}
*)

declare arg_cong[impwrule]

lemma append_Nil2: "l @ [] = l"
proof (induct l)
  show "[] @ [] = []" by simp
next
  fix a l
  assume indhyp: "l @ [] = l"
  thus "(a # l) @ [] = a # l" by (rippling skel: indhyp)
qed

lemma rev_app_single: "rev (l @ [a]) = a # rev l" 
proof (induct l)
  show "rev ([] @ [a]) = a # rev []" by simp
next
  fix b l 
  assume a: "rev (l @ [a]) = a # rev l"
  thus "rev ((b # l) @ [a]) = a # rev (b # l)" by simp
qed

theorem revrev: "rev rev x = x"
proof (induct x)
  show "rev rev [] = []" by simp
next 
  fix a l
  assume indhyp: "rev rev l = l"
  show "rev rev (a # l) = a # l" 
    by (simp add: rev_app_single)
qed



subsection {* Nats *}

theorem N_add0_right: "x + 0 = x" by (induct "x", simp_all)
theorem N_addS_right: "x + (S y) = S(x + y)" by (induct "x", simp_all)

subsection {* Length *}

theorem [rule_format]: "ALL y. len (zip x y) = len x + len y"
apply (induct x)
apply simp
apply simp
apply clarify
apply (case_tac "y")
apply (simp add: N_add0_right)
apply (simp add: N_addS_right)
done

theorem "len x = 0 \<Longrightarrow> x = []"
apply (cases "x")
apply simp
apply simp
done

subsection {* Zip and Length *}

theorem "ALL b x y. ((len x = len a) & (len y = len b) --> 
         (zip (a @ b) (x @ y)) = ((zip a x) @ (zip b y)))"
apply (induct a)
(* base case *)
  apply clarify
  apply simp
  apply (case_tac "x")
  apply simp
  apply simp
(* step case *)
  apply clarify
  apply (case_tac "x")
  apply simp
  apply simp
done

theorem "((len x = len a) & (len y = len b) --> 
         (zip (a @ b) (x @ y)) = ((zip a x) @ (zip b y)))"
thm zip2.induct
apply (induct "x" "a" rule: zip2.induct)
(* base case *)
  apply (clarify, simp)+
done
(*>*)

theorem "[| len x = len a; len y = len b |] ==> 
         (zip (a @ b) (x @ y)) = ((zip a x) @ (zip b y))"
apply (ppinduct x)
oops


section {* Rippling and Induction with Proof Critics *}

text {*
\begin{center}
\scalebox{0.50}{\includegraphics{images/ripple_techn.eps}}
\end{center}
%\begin{figure}[ht]
%  \centering\scalebox{0.50}{\includegraphics{images/ripple_techn.eps}}}
%  \caption{The complete rippling and induction technique with
%    placeholders for critics}
%\end{figure}
*}

section {* Rotate and Length *}



theorem rot_len: "rot(len l, l) = l"
proof(induct "l" rule: rot.induct) 
  show "rot (0, []) = []" by simp
next
  fix y z 
  show "rot (0, y # z) = y # z" by simp
next
  fix w 
  show "rot (S w, []) = []" by simp
next
  fix n h t
  assume ih: "rot (n, t @ [h]) = t @ [h]"
  show "rot (S n, h # t) = h # t"
    apply (simp add: ih)
    oops

text {* Observe that induction scheme @{text "rot.induct"} does not
result in a conlcusion in which the induction hypothesis embeds. Also:
this induction scheme is of little use without a lemma that relates
the induction hypothesis result to the amount the list is rotated. *}


theorem rot_len: "rot(len l, l) = l"
proof(induct l)
  show "rot (len [], []) = []" by simp
next
  fix a L 
  assume ih: "rot (len L, L) = L" 
  have "rot (S len L, a # L) = a # L" 
    sorry 
  thus "rot (len (a # L), a # L) = a # L" 
    by (rippling skel: ih)
qed

text {* At this point Weak fertilisation is possible. Weak
fertilisation can be applied to every occurance of @{term "L"}, using
the induction hyopthesis from right to left. Heuristic: We are only
interested in redexes on the side from which we rewrite the induction
hypothesis. So, as we are rewriting with the induction hypotheis from
right to left, we only condier redexes on the rhs of the induction
conclusion. This leaves a single possible weak fertilisation,
resulting in the proof script: *}

theorem rot_len: "rot(len l, l) = l"
proof(induct l)
  show "rot (len [], []) = []" by simp
next
  fix a L 
  assume ih: "rot (len L, L) = L" 
  have "rot (S len L, a # L) = a # rot (len L, L)" 
    sorry
  hence "rot (S len L, a # L) = a # L" 
    by (eqstep_sym ih)
  thus "rot (len (a # L), a # L) = a # L" 
    by (rippling skel: ih)
qed

text {* From this point the normal thing to do is to simplify the
resulting goal, generalise common subterms (but avoiding the
separation of free variables). This results in the following proof
script: *}

theorem rot_len: "rot(len l, l) = l"
proof(induct l)
  show "rot (len [], []) = []" by simp
next
  fix a L 
  assume ih: "rot (len L, L) = L" 
  have "rot (len L, L @ [a]) = a # rot (len L, L)" 
    sorry
  hence "rot (S len L, a # L) = a # rot (len L, L)" 
    by simp
  hence "rot (S len L, a # L) = a # L" 
    by (eqstep_sym ih)
  thus "rot (len (a # L), a # L) = a # L" 
    by (rippling skel: ih)
qed

text {* IsaPlanner would now try and prove this goal as a new lemma,
doing indiction on @{term "L"}, rippling then becomes blocked at the
following point: *}

lemma "rot (len l, l @ [a]) = a # rot (len l, l)"
proof (induct "l")
  show "rot (len [], [] @ [a]) = a # rot (len [], [])" 
    by simp
next
  fix b L
  assume ih: "rot (len L, L @ [a]) =  a # rot (len L, L)" 
  have "rot (S len L, b # L @ [a]) = a # rot (S len L, b # L)" 
    sorry
  thus "rot (len (b # L), (b # L) @ [a]) = a # rot (len (b # L), b # L)"
    by (rippling skel: ih)
qed

text {* Rippling has become blocked at this point (before
  fertilisation). The generalisation critic is only applies if
  rippling failed and weak fertilisation doesn't lead to a solution.
  Generalisation should be applied to the goal {\em before} weak
  fertilisation. That goes back to the goal: 

  @{term "rot (S len L, a # L) = a # L"}

  The generalisation critic looks for a rule that is
  applicable, but was not applied because no sink exists below the
  wavefront. @{text "rot_S"} is such a rule. Applying it would result in
  following goal:

  @{term "rot (len L, L @ [a]) = a # L"}
  
  From this failed ripple step we construct a generalisation
  conjecture. This is done by manipulating the skeleton at the
  location of the wavefront(s) that we were hoping to rippling inwards.
  A schematic variable (a meta variable) is introduced to
  stands for a subterm involving the wavefront. This is applied to the
  original wave hole and a new
  variable that will be universally quantified to create a sink.
  
  One interesting question is: what is the type of the sink?
  Presumably we want this decision to be left as late as possible.
  
  We introduce schematic variables to replace each wave front. The
  introduced schematic variable is dependent
  on the current wave hole and the newly introduced sink variable. In
  our example this becomes:

  @{text "rot (len l, ?F l k) = ?G l k"}

  The contraint on this is that it must prove the original problem: 
*}

lemma "rot (len l, ?F l k) = ?G l k \<Longrightarrow> 
  rot (len l, l) = l" sorry

text {* Generally we assume that it is the base case for "k" that
provides us with a solution for the original problem, in particular: *}

lemma "rot (len l, ?F l []) = rot (len l, l) \<and> 
       ?G l [] = l" sorry

text {* However, if we don't know what the type of "k" is then this
decision must be left to a later point. For now we will switch to the
proof and instantiation of the main conjecture, which proceeds as
before, by induction on @{term "l"}. The idea is that we should be
able to ripple to the same point as we got stuck earlier, but this
time take an additional step and (partially) instantiate the meta
variables. For its part, the base case introduces an additional
contraint as can be seen from the following proof script: *}

lemma "\<exists> F G. ALL k. rot (len l, F l k) = G l k"
proof (induct l)
  have "\<exists>F G. \<forall>k. rot (0, F [] k) = G [] k" sorry
  thus "\<exists>F G. \<forall>k. rot (len [], F [] k) = G [] k" by simp
next
  fix a L
  assume ih: "\<exists>F G. \<forall>k. rot (len L, F L k) = G L k"
  have "\<exists> Ft Fh G. \<forall>k. rot (len L, (Ft (a # L) k) @ [Fh (a # L) k]) 
    = G (a # L) k" sorry
    -- {* @{term "F (a # L) k = (Fh (a # L) k) # (Ft (a # L) k)"} *}
  hence "\<exists>F G. \<forall>k. rot (S len L, F (a # L) k) = G (a # L) k" 
    sorry -- {* @{text "apply (rule exI)+  apply (eqstep rot_S) apply (rule exE)+"} *}
  thus "\<exists>F G. \<forall>k. rot (len (a # L), F (a # L) k) = G (a # L) k" 
    by (eqstep len_Cons)
qed


text {* This is where the higher order case now differs significantly
from the first order case: We cannot contrain the instantiation of Ft
and Fh, as they may yet beta reduce to something that embeds and
reduces the measure. Some restructions *can* be imposed: embedding
must always be possible, and measure must always be decreasing. 

Furthermore, in the higher order case {\em every} rewrite rule can be
applied in the body of F. We observe that we are only interested in
those that do not rewrite within F, as any other would break skeleton
preservation (F is part of the skeleton, and so we cannot rewrite it
along!).

Oberve that in the above proof script, F was partially instantiated! 
In particulat to: @{term "F (a # L) k = (Fh (a # L) k) # (Ft (a # L)
k)"} 

The embedding contraint forces the modified part of the skeleton
@{term "F L k"} to embed into the new conclusion 
@{term "(Ft (a # L) k) @ [Fh (a # L) k]"}.

Another question is: why don't we solve the base case eagerly, for
example by, instantiating F to first projection, and G to the lhs.  Of
course such a result will fail on the step case, but the question is
how should we avoid this part of the search space.

 Returning to the actualy problem, there are now two subproblems, 
rippling to satify:

@{term "F (a # L) k = (Fh (a # L) k) # (Ft (a # L) k)"}

and rippling to ripple inwards from 

@{term "(Ft (a # L) k) @ [Fh (a # L) k]"}

Ireland's proof critics use have to be given two lemmas: 

@{term "(a @ b) @ c = a @ (b @ c)"}
@{term "(a @ [b]) @ c = a @ (b # c)"}

These, with the object level wave fronts can be used to finish
instantiating @{term "F"} by rippling the wave fronts inwards. In the
higher order wsetting this does not work as we don't have object level
wave fronts to guide us. Generally, in the higher order setting meta
variables cannot stand for wave fronts as there instantiation may beta
reduce to something that doesn't have any wave fronts. We could
perhaps impose further restriction on the instantiation of meta
variables to ensure that they don't do this. 

It is a little unclear to me how Irelands unification algorithm works,
as I don't see any way for the @{term "[Fh (a # L) k]"} to be unified
with @{term "[a]"}. To do this would require further rewriting. 

However, we would like to avoid the user having to supply these
lemmas, and instead allow our proof mechansim to conjecture them. 

Instead of continuing rippling, as is done in Irelands method, we
first try to solve, by rippling:

@{term "F (a # L) k = (Fh (a # L) k) # (Ft (a # L) k)"}

In fact, we search fro a rule with the same leading constant as our
rhs. In the above case, the @{text "addend_Cons"} rule has the correct
leading constant, and can be used to instantiate the lhs directly,
doing this also instantiates the rhs of what we are looking for. I'm
not sure what happens if several rewriting steps are needed. This key
step in instantiating @{term "F"} to @{term "op @"} allows the proof to
continue. Note that the instantiation and use of the @{text
"addend_Cons"} rule automatically breaks down the @{term "(a # L)"}
that were in the rhs of the above schematic problem. 

We then get stuck at with the goal: 

@{term "rot (len L, (L @ k) @ [a]) = G (a # L) k"}

Lemma speculation will try to find a rule that ripples inward:

@{term "(L @ k) @ [a] = L @ (F l k a)"}

This is easily solve as the base case provides a valid instantiation
for @{term "F"} of @{term "% l k a. k @ [a]"}. 

Having instantiated @{term "F"} we can also again return to the base
case in order to try and instantiate @{term "G"}.

This results in the base case condition of:
@{term "G [] k = k"}. 

However making this generally the 2nd projection fails on the step case. 

The step case condition comes from the step case: 

@{term "rot (len L, L @ (k @ [a])) = G (a # L) k"}

which is weak-fertilised on the left, to give: 

@{term "G L (k @ [a]) = G (a # L) k"} 

Question: why not try to instantiate G to the lhs? Failed part of the
search space?

In Irelands critics, a lemma is given that will directly instantiate
@{term "G"}. However, we would like to synethsis G directly. 

This can be done by keeping in mind the contraints and (embedding and
initial generalisation), and starting a new inductive proof. Induction
on k leads to the goal: 

@{term "G L ((h # k) @ [a]) = G (a # L) (h # k)"} 

when this is maximally ripples out w.r.t the introduced shecmatics we get: 

@{term "G L (h # (k @ [a])) = G (a # L) (h # k)"} 

We now look for a wave rule in which our wave front and hole embeds
and which will ripple the wave front outwards, instantiating G
also. Again the @{text "addend_Cons"} rule is found. This instanitates
G to the appen operation but with the arguemnts switched. This in turn
leads to a successfull ripple proof, and solves everything! 

*}

(*<*)


ML {* reset show_types *}


lemma "?G l (h # (k @ [a])) = (h # (k @ [a])) @ ?k" 
apply (rule refl)
oops

ML {* reset show_types *}

lemma "(l @ k) @ [a] = l @ (F k l a)"
proof (induct l)
  have "k @ [a] = F k [] a" sorry
  thus "[] @ k @ [a] = [] @ F k [] a" by simp
next 
  fix aa List
  assume "List @ k @ [a] = List @ F k List a" 
  show "(aa # List) @ k @ [a] = (aa # List) @ F k (aa # List) a" sorry
qed


text {* Interestingly, if we object-level universally quantify the
"a", and use simplificastion instead of rippling, we do get a weak
fertalisation opportunity, but it is of no heolp. This has simply
unfolded another case, but got us nowhere better. The following
illustrates this: *}

lemma "ALL a. rot (len l, l @ [a]) = a # rot (len l, l)"
proof (induct "l")
  show "ALL a. rot (len [], [] @ [a]) = a # rot (len [], [])" 
    by simp
next
  fix b L
  assume ih[rule_format]: 
    "ALL a. rot (len L, L @ [a]) = a # rot (len L, L)"
  show "\<forall>aa. rot (len (b # L), (b # L) @ [aa]) = 
    aa # rot (len (b # L), b # L)"
  proof (rule allI)
    fix aa
    have "rot (len L, L @ [aa] @ [b]) = 
      aa # b # rot (len L, L)" sorry
    hence "rot (len L, L @ [aa] @ [b]) = 
      aa # rot (len L, L @ [b])" by (eqstep ih)
    thus "rot (len (b # L), (b # L) @ [aa]) = 
      aa # rot (len (b # L), b # L)" by simp
  qed
qed

text {* I'm curious, would ACL2 loop at this point? IsaPlanner would
terminate our goal embeds into the subgoal and no new constants are
introduced. I suspect that the use of the embedding as a loop
avoidence strategy is a very useful tool. *}

theorem rot_len: "rot(len l, l) = l"
proof(rule N.induct[of _ "len l"])
oops

(*
subsection {* Zip2 and Length *}

theorem "\<lbrakk>len a = len x; len b = len y\<rbrakk> 
     \<Longrightarrow> zip2 (a @ b, x @ y) = (zip2 (a, x)) @ (zip2 (b,y))"
proof (rule zip2.induct)
sorry
*)

end;
(*>*)
