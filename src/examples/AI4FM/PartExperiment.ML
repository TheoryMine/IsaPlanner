structure PartExperiment =
struct

val arrow = Const (@{const_name Pure.imp}, @{typ"prop => prop => prop"})
val trueprop = Const (@{const_name "HOL.Trueprop"}, @{typ "bool => prop"})
val partition = Const(@{const_name "PartTac.PPart"}, @{typ "xpset => bool"}) 

fun set_ppart_asm concl (pparnm,ptyp) =
      arrow $ (trueprop $ (partition $ Free (pparnm, ptyp))) $ concl;

fun get_part_frees t = 
    let 
	      val part_arg_typ = @{typ "xpset"};
	      val parts = filter (fn (free,typ) => Trm.typ_name_eq part_arg_typ typ)
	                         (Trm.frees_of t)   
	    in 
	      case parts of [] => NONE | [p] => SOME (set_ppart_asm t p) | _ => NONE 
	    end;

fun add_asm_and_nitpick ctxt trm =
    case (get_part_frees trm) of 
      SOME t2 => 
      (case (NitpickSetup.nitpick_fun ctxt (ProofContext.theory_of ctxt) 10 t2) of
         SOME(resp,conj) => SOME conj | NONE => NONE)
    | NONE => NONE;
    
end;
