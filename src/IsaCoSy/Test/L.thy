theory L
imports IsaP

begin

datatype L =
  nil ("[]")
 | cons "nat" "L" (infixr "#" 65)

syntax
  -- {* list Enumeration *}
  "_L" :: "args => L"    ("[(_)]")

declare L.inject[impwrule]


primrec
  Append :: "L => L => L" (infixr ":" 65) where
    Append_nil[wrule]:"[] : ys = ys"
  | Append_cons[wrule]: "(x#xs) : ys = x # (xs : ys)"

primrec Rev :: "L => L" where
   Rev_nil[wrule]:  "Rev [] = []"
  | Rev_cons[wrule]: "Rev (x # xs) = (Rev xs) : (x#[])"

primrec Qrev :: "L => L \<Rightarrow> L" where
  Qrev_nil[wrule] : "Qrev [] a = a"
  | Qrev_cons[wrule] : "Qrev (x#xs) a = Qrev xs (x#a)"
  
ML{*


val def_thms = [@{thm "Append_nil"}, @{thm "Append_cons"}, 
                @{thm "Rev_nil"}, @{thm "Rev_cons"},
                @{thm "Qrev_nil"}, @{thm "Qrev_cons"}]

val cparams = ConstraintParams.empty @{context}
        |> ConstraintParams.add_eq @{context}
        |> ConstraintParams.add_datatype @{context} @{typ "L"}
        |> ConstraintParams.add_consts_of_string_names @{context}["L.Append", "L.Rev", "L.Qrev"]
        |> ConstraintParams.add_thms @{context} def_thms;
*}


ML{*

val (init_ctxt, init_cparams) = 
  ConstraintParams.add_ac_properties_of_const @{context}
                  ("L.Append",@{typ "L => L => L"}) 
                   @{thms "Append.simps"} cparams;

TheoryConstraints.print init_ctxt (TheoryConstraints.init init_ctxt init_cparams);
*}

ML{*
 val (nw_cparams, nw_ctxt) = 
   SynthInterface.thm_synth
  SynthInterface.rippling_prover 
  SynthInterface.quickcheck 
  SynthInterface.wave_rule_config
  SynthInterface.var_allowed_in_lhs
  {max_size = 5, min_size = 1, max_vars = 3, max_nesting= SOME 2} 
  (SynthNames.ConstantName.mk "HOL.eq") (init_cparams, init_ctxt)

*}
ML{*
SynthInterface.print_thms (nw_cparams, nw_ctxt);
*}
ML{*
val output = SynthOutput.Ctxt.get nw_ctxt;
map (Trm.print nw_ctxt) (SynthOutput.get_conjs output);
*}
end
