(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      gproof/isa_dtacs.ML
    Author:     Moa Johansson, University of Edinburgh
    Date:       15 June 2006       
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

   Some declarative tactics for IsaPlanner *)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
structure IsaDTac =
struct

  (* + simplify assumptions with each other *)
  fun simp_asm_full ctxt = 
      DTac.mk_from_isa_tac_local 
        (K (Pretty.str "simp"),
         Simplifier.asm_full_simp_tac ctxt 1);

val HOL_thy = @{theory "HOL"};
val HOL_simps_ctxt = Proof_Context.init_global HOL_thy;

  (* ignore assumptions *)
  fun simp_only thm =  
      DTac.mk_from_isa_tac_local
        (K (Pretty.str ("simp only: " ^ (Thm.get_name_hint thm))), 
         (Simplifier.simp_tac (Simplifier.addsimps (HOL_simps_ctxt,[thm])) 1));

  (* ignore assumptions *)
  fun simp_no_asm simpset =  
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "simp (no_asm)"), 
         Simplifier.simp_tac simpset 1);

  (* As above but only return 'new' goals, ie. fails insted of giving back a
     copy of the original goal *)
  fun simp_no_asm_changes simpset =
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "simp (no_asm_changes)"), 
         CHANGED (Simplifier.simp_tac simpset 1));

  (* ? simplify, but don't use assumptions *)
  fun simp_no_asm_use simpset =  
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "simp (no_asm_use)"), 
         Simplifier.full_simp_tac simpset 1);

  (* ? *)
  fun simp_asm_lr simpset = 
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "simp (asm_lr)"), 
         Simplifier.asm_lr_simp_tac simpset 1);

(* ? use, but don't simplify assumptions.*)
  fun simp_no_asm_simp simpset = 
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "simp (no_asm_simp)"), 
         Simplifier.asm_simp_tac simpset 1);

  (* ? use, but don't simplify assumptions. only suceed if tactic can 
   produce some new goal. *)
  fun simp_no_asm_simp_changes simpset = 
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "simp (no_asm_simp)"), 
         CHANGED (Simplifier.asm_simp_tac simpset 1));

  fun auto ctxt = 
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "auto"), (Clasimp.auto_tac ctxt));

  fun safe ctxt = 
      DTac.mk_from_isa_tac_local
        (K (Pretty.str "safe"), Classical.safe_tac ctxt);

end;
