theory quicktest 
imports IsaP
begin

-- {* Remove other notation to avoid syntax clashes *}
no_notation Groups.zero ("0")
no_notation Groups.plus (infixl "+" 65)
no_notation Groups.times (infixl "*" 70)
no_notation Power.power_class.power (infixr "^" 80)

-- {* Define a natural number datatype *}
datatype N = Nzero  ("0")
           | Nsuc N ("suc _" [100] 100)
print_theorems
-- {* Declare the injectivity rule for the datatype as a wave rule *}
declare N.inject[wrule]

-- {* Define addition for our datatype N *}
fun add :: "N => N => N" (infixr "+" 70)
where
  add_0    :  "(0 + y) = (y)"
| add_suc  :  "suc x + y = suc (x + y)"

-- {* Declare the auto-generated simplication rules to be wave rules *}
declare add.simps[wrule]

-- {* Print the wave rules in the context; just to see what the above did *}
ML {* WRulesGCtxt.print @{context}; *}

-- {* Define subtraction *}
(* TODO: use nice notation *)
fun minus :: "N => N => N"
where
  minus_0    :  "(minus 0 y) = 0"
| minus_suc  :  "(minus (suc x) y) = 
  (case y of (0) => x| (suc y2) => minus x y)"
declare minus.simps[wrule]

-- {* Define multiplication *}
fun mult :: "N => N => N" (infixl "*" 75)
where 
  mult_0    :  "(0 * y) = 0"
| mult_suc  :  "(suc x) * y = y + (x * y)"
declare mult.simps[wrule]

-- {* Define Exponentiation *}
fun exp :: "N => N => N"            (infixr "^" 80)
where
  exp_0   : "x ^ 0 = suc 0"
| exp_suc : "x ^ (suc y) = x * (x ^ y)"
declare exp.simps[wrule]

section {* Examples *}

-- "This line sets the tests to use the simple theory of Peano
    arithmetic without any lemmas proved."

ML {* val thry = @{theory}; *}

-- "ML function to automatically prove goals in Peano arithematic using
    with Rippling and Lemma Calculation "
ML {*
fun a_rippling goals = 
  PPInterface.init_rst_of_strings @{context} goals
   |> RState.set_rtechn (SOME (RTechnEnv.map_then RippleLemCalc.induct_ripple_lemcalc))
   |> GSearch.depth_fs (fn rst => is_none (RState.get_rtechn rst)) RState.unfold
   |> Seq.pull;
*}

-- "Things that can be automatically proved."

ML {* val SOME(myrst,morersts) = a_rippling ["a + b = b + (a::N)"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["a + 0 = (a::N)"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["suc (n + p) = n + suc p"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["a ^ (b + (c :: N)) = a ^ b * a ^ c"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["a + (b + c) = ((a::N) + b) + c"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["(n :: N) * p + q * p = (n + q) * p"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["a * (b * c) = ((a::N) * b) * c"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["a * b = ((b::N) * a)"]; *}
ML {* val SOME(myrst,morersts) = a_rippling ["a ^ (b + (c :: N)) = a ^ b * a ^ c"]; *}

-- "Example of doing a proof automatically"
ML {* val SOME(myrst,morersts) = a_rippling ["a + b = b + (a::N)"]; *}

-- "An example that the technique fails for. This is due to failing to 
    find the needed generalisation"
ML {* val NONE = a_rippling ["a ^ (b ^ (c :: N)) = a ^ (b * c)"]; *}
ML {* val NONE = a_rippling ["x + suc x = suc(x + x)"]; *}

-- "Note: for debugging, it is very useful to trace exceptions... Note: turn on debugging 
    in Isabelle settings menu."
(* PolyML.exception_trace (fn () =>  CODE_GOES_HERE  ); *)


section {* Examples using Simplification and Lemma Calculation *}

-- "Use the technique described in the CADE'03 IsaPlanner paper. "
ML {* 
fun ind_and_simp goals =
  PPInterface.init_rst_of_strings @{context} goals
   |> RState.set_rtechn (SOME (RTechnEnv.map_then InductAndSimp.induct_and_simp))
   |> GSearch.depth_fs (fn rst => is_none (RState.get_rtechn rst)) RState.unfold
   |> Seq.pull;
*}

ML {* val SOME(myrst,more) = ind_and_simp ["a + 0 = (a::N)"]; *}
ML {* val SOME(myrst,more) = ind_and_simp ["a + b = b + (a::N)"]; *}

(*The below two seem to be non termninating due to diverging or the same lemmas being calculated over and over. *)
(* 
ML {* val myrst = ind_and_simp ["a * b = ((b::N) * a)"]; *} 
ML {* val myrst = ind_and_simp ["a ^ (b + (c :: N)) = a ^ b * a ^ c"]; *}
*)

end