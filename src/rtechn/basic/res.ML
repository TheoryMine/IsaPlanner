(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      res.ML
    Author:     Moa Johansson, University of Edinburgh
                moa.johansson@ed.ac.uk
    
*)


(* Resolution with a theorem restricted to not allow top-level
meta-variables to throw away their arguments. *) 

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)



structure Res =

struct

(* Restricted resulution, if there is a top-level 
meta-variable, it is not allowed to throw away its
arguments *)

(* Get the arguments to the thing in the bottom left of this
zipper. Ignore free variables (comes from lifting operation) *)
fun right_branches z rs =
    case (Zipper.omove_down_right z) of
       SOME z' => if (Term.is_Free (Zipper.trm z')) then 
                   right_branches (Zipper.move_down_left z) rs
                 else right_branches (Zipper.move_down_left z) (z'::rs)
    | NONE => rs;


fun find_matches (n,ty) ppl rule_strms goal_subtrm =
    let      
      val thry = Prf.get_theory ppl
      val ienv = Prf.get_ienv ppl                           

      fun try_match g_strm_zip r_strm_zip = 
            if MyUnify.unifies (ienv, 
                               [(Zipper.trm r_strm_zip, Zipper.trm g_strm_zip)]) 
            then
                MetaVarLib.inst_mvar (n,ty) (Zipper.move_up r_strm_zip) g_strm_zip ppl
            else NONE;
    
    in
       Seq.map_filter (try_match goal_subtrm) (Seq.of_list rule_strms)        
    end;


fun try_dest_Trueprop (Const("HOL.Trueprop", _) $ T) = T
    | try_dest_Trueprop T = T;

(* Function for searching zipper which doesn't include terms involving Bounds if we're under a lambda
  as doing this might cause illegal attempts of unification.*)
(*fun sf_above_lam_td_lr z = 
    case Zipper.trm z 
     of Zipper.C.D.Trm.$ _ => [Zipper.Here z, Zipper.LookIn (Zipper.move_down_left z),
                    Zipper.LookIn (Zipper.move_down_right z)]
(* FIXME: Do go below lambdas if subterm doesn't contain the Bound variable *)
      | Zipper.C.D.Trm.Abs _ =>  [Zipper.Here z] (* don't go below lambda *)
      | _ => [Zipper.Here z] 
     
*)

(* Restricted version of resolution that won't allow top-level meta-vars
to throw away their arguments *)
fun restr_res thm goal ppl0 = 
    let
      val ppl = Prf.start_meth [goal] ppl0 
   
      (* make zipper of concl, move below Trueprop *)
      val (rule_nm,ppl2) = Prf.insert_thm thm ppl

      (* lift into same context as goal *)
      val ((lifted_rulenm,lifed_asms),ppl3) = 
          Prf.lift_and_show_above rule_nm [] goal ppl2

      val rule_z = Zipper.mktop (try_dest_Trueprop 
                                (Prf.get_ndname_ctrm ppl3 lifted_rulenm))                    

      (* if there is a top-level meta-var it needs inst first *)
      val pot_var = Term.head_of (Zipper.trm rule_z)
    in
      case pot_var of (Var (n,ty)) => 
        let 
          val goal_z = Zipper.mktop (try_dest_Trueprop 
                                    (Prf.get_ndname_ctrm ppl3 goal))               

          (* Arguments to top-level Var, ie. subterms we'd like to match goal *)
          (* Only want args that are proper subterms, not variables from
              lifting operation, this is done in right_branches. *)
          val rule_subtrms = right_branches rule_z []

          val goal_subtrms = ZipperSearch.all_td_lr goal_z
                             |> Seq.filter (null o Term.loose_bnos o Zipper.trm)
                            (*Zipper.lzy_search sf_above_lam_td_lr goal_z *)
          val ppls = Seq.maps (find_matches (n,ty) ppl3 rule_subtrms) goal_subtrms 
          val results = Seq.maps (fn pplan => 
                         PPlan.apply_res_bck 
                         lifted_rulenm goal pplan) ppls
                              
        in  
          Seq.map (fn (gs,nw_pplan) => 
                  Prf.end_meth  
                  ("Restricted resultion with "^ Thm.get_name_hint thm)
                   gs (* facts that are derived in subprf *)
                   [goal] (* goal list that are refined in subprf *)
                   nw_pplan (* subprf which you have applied start_meth and then more operations to. *)
                   ppl0 (* prf before you applied start_meth *)
                  ) results 

        end
      | _ => Seq.empty
        (*normal res, this doesn't work because you get a type error*)
      (*PPlan.apply_res_bck lifted_rulenm goal ppl3*)
    end;




end;
