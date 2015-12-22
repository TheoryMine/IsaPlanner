theory "shankar-challenge"
imports "../IsaP" Main
begin

-- "Remove old syntax, we don't want to confuse ourselves with 
    the existing theories and end up just doing theorem lookup"
no_notation Groups.zero ("0")
no_notation Groups.plus (infixl "+" 65)

-- "Redefine numbers to avoid using Isabelle's and thus avoid existing lemmas" 
datatype N = Nzero  ("0")
           | Nsuc N ("suc _" [100] 100)
declare N.inject[wrule]

-- "Define addition"
fun add :: "N => N => N" (infixr "+" 70)
where
  add_0    [wrule]:  "0 + y = y"
| add_suc  [wrule]:  "(suc x) + y = suc (x + y)"

-- "Define another version of addition"
fun add' :: "N => N => N" (infixr "+`" 70)
where
  add'_0    [wrule]:  "0 +` y = y"
| add'_suc  [wrule]:  "(suc x) +` y = x +` (suc y)"

-- "See the wave-rules saved in the context"
ML {* WRulesGCtxt.print @{context}; *}

-- "Setup the interactive proof-tracer to trace an autoamtic 
    proof using rippling and lemma calculation"
ML {*
fun prove_by_rippling goalstrs = 
  Print_Mode.setmp []
    (fn () => PPInterface.ipp_of_strings @{theory} 
                (RTechnEnv.map_then RippleLemCalc.induct_ripple_lemcalc) 
                goalstrs)
    ();
*}

-- "Prove Shankar's challenge: the problem that he gives his students 
    and usually stumps them"
ML {* val myrst = prove_by_rippling ["x + y = x +` y"]; *}

-- "One of the proofs that was found (the first one). 
    [Timing: Finding all 4 proofs takes negliable time (effectively instant)]"
text {*
\begin{verb}
+[1] Solve using Induction, Rippling and Lemma Calculation....
  -[1] on goals:[i, j] Induction on: x 
  -[1] Solve the base case by simplification.
  -[1] Solved!
  +[1] Solve the step case using rippling....
    -[1] Start Rippling with state: 
         Skeleton Measures:
         (1) measures for skeleton: k: {
         (a) Pressure: 8;  Avgflow: 1
         }
         Embeddings: {embWF (suc embWH z) + embSVar ?ab aa =
                      embWF (suc embWH z) +` embSVar ?ab aa}
    -[1] on goals:[l] Ripple Step by suc ?x +` ?y == ?x +` suc ?y
                      Skeleton Measures:
                      (1) measures for skeleton: k: {
                      (b) Pressure: 4;  Avgflow: 0
                      }
                      Embeddings: {embWF (suc embWH z) + embSVar ?ab aa =
                                   z +` embSVar ?ab (suc aa)}
    -[1] on goals:[l] Ripple Step by suc ?x +` ?y == ?x +` suc ?y
                      Skeleton Measures:
                      (1) measures for skeleton: k: {
                      (b) Pressure: 4;  Avgflow: 0
                      }
                      Embeddings: {embWF (suc embWH z) + embSVar ?ab aa =
                                   z +` embSVar ?ab (suc aa)}
    -[1] on goals:[m] Ripple Step by suc ?x + ?y == suc (?x + ?y)
                      Skeleton Measures:
                      (1) measures for skeleton: k: {
                      (c) Pressure: 1;  Avgflow: 1
                      }
                      Embeddings: {embWF (suc embWH (z + embSVar ?ab aa)) =
                                   z +` embSVar ?ab (suc aa)}
    -[1] on goals:[n] Weak fertilisation
    +[1] Proving goal n by a new lemma: q +` suc r = suc (q +` r)...
      -[1] Proving goal n by a new lemma: q +` suc r = suc (q +` r)
      +[1] Solve using Induction, Rippling and Lemma Calculation....
        -[1] Solve using Induction, Rippling and Lemma Calculation.
        -[1] on goals:[o, p] Induction on: q 
        -[1] Solve the base case by simplification.
        -[1] Solved!
        +[1] Solve the step case using rippling....
          -[1] Start Rippling with state: 
               Skeleton Measures:
               (1) measures for skeleton: q: {
               (a) Pressure: 9;  Avgflow: 1
               }
               Embeddings: {embWF (suc embWH s) +` suc embSVar ?u t =
                            suc (embWF (suc embWH s) +` embSVar ?u t)}
          -[1] on goals:[r] Ripple Step by suc ?x +` ?y == ?x +` suc ?y
                            Skeleton Measures:
                            (1) measures for skeleton: q: {
                            (b) Pressure: 4;  Avgflow: 0
                            }
                            Embeddings: {embWF (suc embWH s) +`
   suc embSVar ?u t =
   suc (s +` embSVar ?u (suc t))}
          -[1] on goals:[r] Ripple Step by suc ?x +` ?y == ?x +` suc ?y
                            Skeleton Measures:
                            (1) measures for skeleton: q: {
                            (b) Pressure: 4;  Avgflow: 0
                            }
                            Embeddings: {embWF (suc embWH s) +`
   suc embSVar ?u t =
   suc (s +` embSVar ?u (suc t))}
          -[1] on goals:[s] Ripple Step by suc ?x +` ?y == ?x +` suc ?y
                            Skeleton Measures:
                            (2) measures for skeleton: q: {
                            (c) Pressure: 0;  Avgflow: 0
                            (d) Pressure: 1;  Avgflow: 1
                            }
                            Embeddings: {s +` suc embSVar ?u (suc t) =
   suc (s +` embSVar ?u (suc t)),
    s +` embWF (suc embWH (suc embSVar ?u t)) =
    suc (s +` embSVar ?u (suc t))}
          -[1] Strong fertilisation
      -[1] Resolution backward using dthm lem_a[symmetric]

Proof:
  ------------------------------------------------------------------
   {{ALL x : N, y : N.
     (g1): "x + y = x +` y"
     [by_meth (Induction on: x ) to: i, j]
     
     {ALL z : N.
      (i): "0 + z = 0 +` z"
      [by_meth (simp (no_asm_simp))]}
     
     {ALL z : N, aa : N.
      {ALL ab. (k): "z + ab = z +` ab"}
      |- 
      (j): "suc z + aa = suc z +` aa"
      [by_meth (subst_w_thm: quicktest.add'_suc) to: l]
      
      (l): "suc z + aa = z +` suc aa"
      [by_meth (subst_w_thm: quicktest.add_suc) to: m]
      
      (m): "suc (z + aa) = z +` suc aa"
      [by_meth (subst k) to: n]
      
      (n): "suc (z +` aa) = z +` suc aa"
      [by_meth (rule lem_a[symmetric])]}}
    
    {ALL q : N, r : N.
     (lem_a): "q +` suc r = suc (q +` r)"
     [by_meth (Induction on: q ) to: o, p]
     
     {ALL s : N.
      (o): "0 +` suc s = suc (0 +` s)"
      [by_meth (simp (no_asm_simp))]}
     
     {ALL s : N, t : N.
      {ALL u. (q): "s +` suc u = suc (s +` u)"}
      |- 
      (p): "suc s +` suc t = suc (suc s +` t)"
      [by_meth (subst_w_thm: quicktest.add'_suc) to: r]
      
      (r): "suc s +` suc t = suc (s +` suc t)"
      [by_meth (subst_w_thm: quicktest.add'_suc) to: s]
      
      (s): "s +` suc suc t = suc (s +` suc t)"
      [by q]}}}
  ------------------------------------------------------------------
\end{verb}
*}

end