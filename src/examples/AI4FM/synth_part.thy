theory synth_part
imports PartTac HOL_IsaP IsaCoSy
uses "synth_setup.ML" "nitpick_setup.ML"

begin
ML {* use "PartExperiment.ML"; *}

ML{*
val setmem1 = Thm.term_of @{cpat "Set.member :: X set => (X set set) => bool"}
val emptyset1 = Thm.term_of @{cpat "Orderings.bot_class.bot :: X set => bool"}
val setmem2 = Thm.term_of @{cpat "Set.member :: X => (X set) => bool"}
val emptyset2 = Thm.term_of @{cpat "Orderings.bot_class.bot :: X => bool"}

val ((eq,eqty),eqair) = (Term.dest_Const @{term "HOL.eq"},2);
*}
ML{*
val ctxt = @{context};

(* Working on X set sets, restricting polymorphic functions member and {} *)
val consts1 =  [(@{term "pEQUATE"},3), (@{term "pTEST"}, 3), (@{term "HOL.implies"}, 2), 
  (@{term "HOL.Not"}, 1), (setmem1, 2), (emptyset1,0)]
  |> map (fn (c,airity)  => (Term.dest_Const c, airity));

(* Working on X sets *)
val consts2 =  [(@{term "pEQUATE"},3), (@{term "pTEST"}, 3), (@{term "HOL.implies"}, 2), 
  (@{term "HOL.Not"}, 1), (setmem2, 2), (emptyset2,0)]
  |> map (fn (c,airity)  => (Term.dest_Const c, airity))

val airities = SynthNames.Constant.NTab.of_list (map (fn ((cnm,ty), airity) => 
                                                      (SynthNames.Constant.mk cnm,airity)) 
                                                (((eq,eqty),eqair)::(consts1)))


(* We add some constraints:*)
val constr_terms = [Trm.change_frees_to_fresh_vars @{term "HOL.implies (HOL.Not x) (HOL.Not y)"},
                    Trm.change_frees_to_fresh_vars @{term "HOL.Not (HOL.implies x y)"},
                    Trm.change_frees_to_fresh_vars @{term "HOL.eq (HOL.Not x) (HOL.Not y)"},
                    Trm.change_frees_to_fresh_vars @{term "HOL.Not(HOL.Not x)"},
                    Trm.change_frees_to_fresh_vars @{term "HOL.implies (HOL.implies x y) z"},
                    Trm.change_frees_to_fresh_vars @{term "HOL.implies x (HOL.implies y (HOL.implies z (HOL.implies u v)))"},
                    Trm.change_frees_to_fresh_vars @{term "HOL.Not (HOL.eq x y)"} (* Don't want ineqaulities right now *)

];

(* Add equality so its used during synthesis *)
fun myaddeq ctxt = ConstraintParams.add_termrws ctxt 
                   ThyConstraintParams.termrws_for_eq o ConstraintParams.add_consts 
                   ThyConstraintParams.consts_for_eq;

(* Compute parameters for IsaCoSy, given our constants and constraints, with = as top level symbol, and = not allowed anywhere else *)
val topeqparams1 = 
  ConstraintParams.empty
  |> ThyConstraintParams.add_eq ctxt 
  |> ((ConstraintParams.add_consts o map fst) consts1)
  |> (ConstraintParams.add_arb_terms ctxt constr_terms);

val topeqparams2 = 
  ConstraintParams.empty
  |> ThyConstraintParams.add_eq ctxt 
  |> ((ConstraintParams.add_consts o map fst) consts2)
  |> (ConstraintParams.add_arb_terms ctxt constr_terms);

val imp_params = 
ConstraintParams.empty
  |> myaddeq ctxt
  |> ((ConstraintParams.add_consts o map fst) consts1)
  |> (ConstraintParams.add_arb_terms ctxt constr_terms);
*}

ML{*
fun myprove ctxt tac t = Goal.prove_global (ProofContext.theory_of ctxt) [] [] t (fn {context, ...} => tac context);

fun unf_PPart_ind_clarsimp_blast_tac ctxt = 
  (unfold_tac [@{thm "pTEST_def"}, @{thm "pEQUATE_def"}, @{thm "Part_def"}, @{thm "is_disj_def"}, @{thm "is_total_def"}](Simplifier.simpset_of ctxt))
  THEN
  (PPart_ind_clarsimp_blast_tac ctxt);


fun PPart_ind_prove ctxt = myprove ctxt unf_PPart_ind_clarsimp_blast_tac;
fun try_proof ctxt t = SOME ("erule PPart then (clarsimp | blast)+", PPart_ind_prove ctxt t) handle _ => NONE;

fun prove_w_timeout secs f (ctxt:Proof.context) (t:Term.term) =
    let 
      val timeout = Time.fromSeconds secs
      val res = Unsynchronized.ref NONE
      val timenow = Timer.startRealTimer();
      val nap = Time.fromReal 0.25;
      val prove = Thread.fork (fn () => res := f ctxt t,[])
      fun timeout_chk timer = 
          if (Timer.checkRealTimer timer) >= timeout then 
            let val _ = Thread.kill prove
            in NONE end
          else
            if (Thread.isActive prove)
            then ((OS.Process.sleep nap); timeout_chk timer)
            else !res 
    in
       timeout_chk timenow  
    end;

fun try_proof_tout ctxt t = (prove_w_timeout 5 try_proof ctxt t, ([]:(string * Thm.thm) list));
*}


ML{*
val cex_checker = SynthInterface.CExFinder(PartExperiment.add_asm_and_nitpick);
val prover =  SynthInterface.Prover(try_proof_tout);
val not_bool_in_lhs = SynthInterface.VarAllowedFun(SynthSetup.not_bool_in_lhs);
val no_bool_vars = SynthInterface.VarAllowedFun(SynthSetup.not_bool_hole);

*}
ML{*
(* Synthesise some implications *)
 val (imp_cparams, imp_ctxt) = 
(* PolyML.exception_trace (fn () => *) 
SynthSetup.thm_synth 
  prover
  cex_checker
  SynthSetup.ai4fm_part_config 
  no_bool_vars
  {max_size = 10, min_size = 3, max_vars = 3, max_nesting= SOME 2} 
  (Constant.mk "HOL.implies") airities (imp_params,@{context})

; 

*}
ML{*
val imp_thms = SynthOutput.get_thms (SynthOutput.Ctxt.get imp_ctxt);
 map (Trm.print imp_ctxt) (map (Thm.full_prop_of o snd) imp_thms);
*}
ML{*
val imp_conjs = map (Trm.print imp_ctxt) (SynthOutput.get_conjs (SynthOutput.Ctxt.get imp_ctxt));
*}
ML{*
(* Synthesise some equalities *)
val (eq_cparams, eq_ctxt) = 
(* PolyML.exception_trace (fn () => *)
SynthSetup.thm_synth 
  prover
  cex_checker
  SynthSetup.ai4fm_part_config 
  not_bool_in_lhs
  {max_size = 12, min_size = 3, max_vars = 3, max_nesting= SOME 2} 
  (Constant.mk "HOL.eq") airities (topeqparams1,@{context})
; 

*}
ML {*

val net = SynthOutput.get_thm_net (SynthOutput.Ctxt.get eq_ctxt);
val stuff = Net.entries net;
 map (Trm.print eq_ctxt) (map (Thm.full_prop_of o snd) stuff);
*}
ML {*
val eq_thms = SynthOutput.get_thms (SynthOutput.Ctxt.get eq_ctxt);

 val eq_conjs = map (Trm.print eq_ctxt) (SynthOutput.get_conjs (SynthOutput.Ctxt.get eq_ctxt));

(* val thms = map (Trm.print eq_ctxt) (map (Thm.full_prop_of o snd) eq_thms); 

val all = map (Trm.print eq_ctxt) (SynthOutput.get_all (SynthOutput.Ctxt.get eq_ctxt));
*)
*}
end;

