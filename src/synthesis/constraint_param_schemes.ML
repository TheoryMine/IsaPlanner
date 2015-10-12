  (* Title : constraint_param_schemes.ML                                
     Author: Moa Johansson                                              
     Description: 
     Simple schemes for synthesis of associativity and commutativty
     properties of functions. Can be used as a pre-procedding step
     prior to term-synthesis in IsaCoSy, as these properties produce
     useful constraints.                                                *)
(* ---------------------------------------------------------------------*)

signature CONSTRAINT_PARAM_SCHEMES =
sig 
  (* Main function, returns AC-theorems found by schemes *)           
  val synth_ac_thrms : Proof.context -> string * typ -> Thm.thm list -> (string * thm) list

  val synth_commute : Proof.context -> string * typ -> Trm.T list -> (string * thm) list
  val synth_assoc : Proof.context -> string * typ -> (string * thm) list
  val commuted_defs : Proof.context -> string -> Trm.T list -> (string * thm) list

  (* Schemes for associativity and commutativity *)
  val commute_template : string * typ -> term option
  val assoc_template : string * typ -> term option
end

structure ConstraintParamSchemes : CONSTRAINT_PARAM_SCHEMES
= struct 

  (* Build a conjecture about commutativity for constant "cname" *)
  fun commute_template (cname, ty) =
      let 
        val (argtyps,_) = Term.strip_type ty 
      in  
        case argtyps of
          [arg_ty1,arg_ty2] => 
          if (arg_ty1 = arg_ty2)
          then
            let
              val arg1 = Trm.mk_free ("x",arg_ty1)
              val arg2 = Trm.mk_free ("y",arg_ty1)
            in
              SOME
              ((HOLogic.mk_eq (Const(cname,ty)$arg1$arg2,
                               Const(cname,ty)$arg2$arg1))
                 |> HOLogic.mk_Trueprop)
            end
          else NONE
        | _ => NONE
      end;
  
  (* Build a conjecture about associativity for constant "cname" *)
  fun assoc_template (cname, ty) = 
      let 
        val (argtyps,_) = Term.strip_type ty 
      in  
        case argtyps of
          [arg_ty1,arg_ty2] => 
          if (arg_ty1 = arg_ty2)
          then
            let
              val arg1 = Trm.mk_free ("x",arg_ty1)
              val arg2 = Trm.mk_free ("y",arg_ty1)
              val arg3 = Trm.mk_free ("z",arg_ty1)
              val lhs = Const(cname,ty)$(Const(cname,ty)$arg1$arg2)$arg3
              val rhs = Const(cname,ty)$arg1$(Const(cname,ty)$arg2$arg3)
            in
              SOME
                ((HOLogic.mk_eq (lhs,rhs))
                 |> HOLogic.mk_Trueprop)
            end
          else NONE
        | _ => NONE
      end; 
  


  (* -------------------------------------------------------- *)
  (* Try to figure out if a function is associative and/or 
     commutative before starting synthesis  *)
  (* -------------------------------------------------------- *)
  (* IMPROVE: can we directly use schemes here? 
     Thought recustion easier, it flips all occurences of the 
     function. Actually, should it do this, or only in LHS?
  *)

  (* We believe 'const-nm' to be a commutative fucntion. 
  Try and build a commuted version of the functions defs *)
  
  fun commute_args_of_const const_nm z = 
      case Zipper.trm z 
       of t1$t2 =>  
          (case (Term.strip_comb (t1$t2)) of   
            ((Const(cnm2,ty)), [arg1,arg2]) => 
            (* The commutative function we're looking at:*)
            if (cnm2 = const_nm) 
            then
              let
                val swapped_arg1 = 
                    commute_args_of_const const_nm (Zipper.mktop arg1)
                val swapped_arg2 = 
                    commute_args_of_const const_nm (Zipper.mktop arg2)
              in  
                (Const(const_nm, ty)$swapped_arg2$swapped_arg1)
              end
              (* Some other function, don't commute it's args *)
            else Term.list_comb (Const(cnm2,ty), 
                                 map ((commute_args_of_const const_nm) o 
                                      Zipper.mktop) [arg1,arg2])
          | (hdtrm,args) =>
            Term.list_comb (hdtrm, 
                            map ((commute_args_of_const const_nm) o 
                                 Zipper.mktop) args)
          )
        | Term.Abs _ => commute_args_of_const const_nm (Zipper.move_down_abs z)
        | _ => Zipper.top_trm z; (* Vars, Frees *)
  
  
  (* Speculate that commuted versions of definitions are potentially
  interesting/useful thms.*)

  (* IMPROVE: work from theorems and reason forward?  
     
     IMPROVE: maybe this can be removed? Flaminia's commutativity
     subsumption makes this redundent.  
     Moa: I disagree: Perhaps they aren't interesting to sell for TM,
     but they may be useful simp- and wave-rules. Recall that simp
     can't use commutativity. *)

  fun commuted_defs ctxt const_nm def_eqs = 
      let
        val com_defs = def_eqs
                         |> map Zipper.mktop
                         |> map (commute_args_of_const const_nm)
                         |> map (Trm.change_vars_to_fresh_frees) 
                         |> map_filter (SynthPrfTools.counter_ex_check ctxt) 
        val cdef_prfs = 
            map (SynthPrfTools.ripple_timeout ctxt) com_defs

         (* Just give back the one theorem (the list rep. alt proofs) *)
      in
         map_filter (fn (thm_opt, lemmas) => 
                        case thm_opt of SOME(prf,thm) => SOME (prf,thm) | NONE => NONE) 
                    cdef_prfs
      end       

  (* Try synthesising and proving associativity *)
  fun synth_assoc ctxt (const_name, ty)  = 
      case (assoc_template (const_name, ty)) of
        SOME assoc_trm => 
        if (is_some (SynthPrfTools.counter_ex_check ctxt assoc_trm)) then
          let 
            val cand_prf = 
                (*SynthPrfTools.ripple_conjecture *)
                SynthPrfTools.ripple_timeout ctxt assoc_trm
          in
            case cand_prf of 
              (NONE,_) => []
              | (SOME (prf,thm), _) => 
              let val _ = tracing (const_name^ " is associative.")
              in [(prf,thm)] end
          end
        else []
      | NONE => []
  
  (* Try synthesising and proving commutativity *)
  fun synth_commute ctxt (const_name, ty) def_eqs = 
      case (commute_template (const_name, ty)) of
        SOME commute_trm => 
        if (is_some (SynthPrfTools.counter_ex_check ctxt commute_trm)) then
          let 
          val cand_prf = 
              (*SynthPrfTools.ripple_conjecture*)
              SynthPrfTools.ripple_timeout ctxt commute_trm
          in 
            case cand_prf of 
              (NONE,_) => []
            | (SOME (prf,thm), _) =>
              let 
                val _ =  tracing (const_name ^ " is commutative.") 
                val commuted_def_thrms = commuted_defs ctxt const_name def_eqs
              in
              ((prf,thm)::commuted_def_thrms)
              end
          end
        else []
      | NONE => [];


(* Scheme-based synthesis of AC-theorems. Also commutes function defs, if 
   the function turn out to be commutative. These are useful for rippling. *)
fun synth_ac_thrms ctxt (fun_nm,typ) def_thms = 
    (synth_assoc ctxt (fun_nm, typ)) @ 
    (synth_commute ctxt (fun_nm,typ) (map Thm.concl_of def_thms));


end (* struct *)
