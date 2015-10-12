

(* ----------------------------------------------------------------*)
(* Induction in the precence of meta-variables.                    *)
(* ----------------------------------------------------------------*)
signature INDUCT_MVAR =
sig
val apply_induct_mvar_dtac :
       (string * Term.typ) *        (* Induction variable name and type *)
       (string * Term.typ) list ->  (* Variables to be turned into sinks *)
       Prf.gname -> RTechn.T

val induction_on_goal : Prf.gname -> RTechn.T
val induction_on_goal2 : Prf.gname ->  RTechn.T -> (*Base case techn*)
                                       RTechn.T -> (*Step case techn*)
                                       RTechn.T

val inst_mvar_ind_scheme : 
               Var.name * Term.typ -> (* Name and type of meta-variable *)
                Zipper.T ->     (* Zipper of term with meta-variable. *)                
                Zipper.T ->      (* Zipper used to instantiate meta-variable *)
                Zipper.T list ->  (* Other occurences of the subterm that 
                                   appears in the instantiating zipper *)  
                (string * Term.typ) list -> (* the sinks *)
                Prf.T ->          (* Current proof-plan *)
                Prf.T option      (* SOME pplan if successful instantiation found *)
end

functor IndMvarFUN(D : DATATYPE_IND_SCHEMES) =
struct

(* Instantiation of the meta-varaiable in the conclusion of the
induction scheme. Induction is on the varaible where 'src_zip' is
located. The list 'occs' are zippers for other locations of that
variable. 'othervars' are the variables that are non-induction
variables, that will be universally quantified and turned into sinks.*)

fun inst_mvar_ind_scheme (n,ty) targ_zip src_zip occs othervars ppl =
    let                  
      val (argtyps,finaltyp) = Term.strip_type ty
      val i = MetaVarLib.n_args_right targ_zip 
      val src_typ = Term.type_of1 ((Zipper.ty_ctxt src_zip), (Zipper.trm src_zip))
      val thry = Prf.get_theory ppl
      val herety = List.nth (argtyps, length argtyps - i - 1) 
      val ppl2opt = Prf.unify_typs [(herety,src_typ)] ppl
             
      (* Follow same ctxt as in occ_zip and replace that part with trm in inst_zip *)                      
      fun set_term trm occ_zip inst_zip = 
          Zipper.zipto (Zipper.ctxt occ_zip) (Zipper.goto_top inst_zip)
          |> Zipper.set_trm trm
          |> Zipper.goto_top;

     (* fun freevar_to_bound var_zips (index, z) = 
           let val heretrm = Bound (index)
           in
              (index +1, fold (set_term heretrm) var_zips z)
           end; *)

      fun allify (name,typ) t = HOLogic.mk_all (name,typ,t);                               
    in
     (case ppl2opt of NONE => NONE
                     | SOME ppl2 =>
                     let
                     val heretrm = Bound (i + length (Zipper.ty_ctxt src_zip) + 
                                              length othervars)
                     val inst_z0 = Zipper.set_trm heretrm src_zip
                     (* Replace any other occurences by heretrm *)
                     val inst_t1  = fold (set_term heretrm) occs inst_z0
                                   |> Zipper.top_trm

                     (*val inst_t0 = fold freevar_to_bound othervar_zips 
                                        (length (Zipper.ty_ctxt src_zip), inst_z1)
         
                                   |> Zipper.top_trm o snd; *)

                     val inst_t = fold allify othervars inst_t1          

                     (* Might have found unifier for something in the src_typ so instantiate *) 
                     val top_src_typ = InstEnv.inst_typ_tvars (Prf.get_ienv ppl2) 
                                               (Term.type_of (Zipper.top_trm src_zip))
                     in 
                       (case (Prf.unify_typs [(finaltyp, top_src_typ)] ppl2)
                           of NONE => NONE
                            | SOME ppl3 =>                              
                              let
                                val var_inst = InstEnv.inst_trm 
                                                 (Prf.get_ienv ppl3)
                                                 (Term.list_abs (map (pair "") argtyps, inst_t))
                                val typ_inst = InstEnv.inst_typ_tvars (Prf.get_ienv ppl3) ty
                              in
                                SOME(Prf.inst_prf (InstEnv.add_var_inst (n, (typ_inst, var_inst)) 
                                                                        (InstEnv.init thry)) ppl3)
                                
                              end)
                       end)
     
    end; 





(* Unify all occurences of the subterm in the goal that matches some argument to the
   meta-variable (here this subterm is a variable we're doing induction on. *)
fun find_matches (n,ty) ppl rule_strms goal_subtrm other_occs othervars =
    let      
      val thry = Prf.get_theory ppl
      val ienv = Prf.get_ienv ppl                           

      fun try_match g_strm_zip r_strm_zip =
       
            if MyUnify.unifies thry (ienv, 
                               [(Zipper.trm r_strm_zip, Zipper.trm g_strm_zip)]) 
            then
                inst_mvar_ind_scheme (n,ty) (Zipper.move_up r_strm_zip) 
                                              g_strm_zip other_occs othervars ppl                     
            else NONE;
    
    in
       Seq.map_filter (try_match goal_subtrm) (Seq.of_list rule_strms)        
    end;

val spec_thm = thm "HOL.spec";
val allI_thm = thm "allI";

(* Essentially resolution with the induction scheme, which has a conclusion of the form ?P(?x).
   We unify the x with our induction variable and instantiate ?P.*)
fun apply_induction_on_var ((indvar_nm,typ),othervars) goal ppl0  = 
    let
      val ppl = Prf.start_meth [goal] ppl0 
      val (typ_nm,_) = Term.dest_Type typ
      
      val datatype_stuff  = D.lookup (Prf.get_theory ppl) typ_nm
      val ind_scheme = D.default_ind_thm (the datatype_stuff)

      (* make zipper of concl, move below Trueprop *)
      val (rule_nm,ppl2) = Prf.insert_thm ind_scheme ppl

      (* lift into same context as goal *)
      val ((lifted_rulenm,lifted_asms),ppl3) = 
          Prf.lift_and_show_above rule_nm [] goal ppl2

      val rule_z = Zipper.mktop (Res.try_dest_Trueprop 
                   (Prf.get_ndname_ctrm ppl3 lifted_rulenm))                    
      (* if there is a top-level meta-var it needs inst first *)
      val pot_var = Term.head_of (Zipper.trm rule_z)
    in
      case pot_var of (Var (n,ty)) => 
        let 
          val goal_z = Zipper.mktop (Res.try_dest_Trueprop 
                                    (Prf.get_ndname_ctrm ppl3 goal))               

          (* Arguments to top-level Var, ie. subterms we'd like to match goal *)
          (* Only want args that are proper subterms, not variables from
              lifting operation, this is done in right_branches. *)
          val rule_subtrms = Res.right_branches rule_z []

          (* Only interested in occurences of the variable 'var_nm' that we want to induct on *)
          val goal_leaves = Seq.list_of (ZipperSearch.leaves_lr goal_z)
          val goal_subtrms = filter (fn z => case (Zipper.trm z) of
                                             Free(free_n,free_t) => free_n=indvar_nm
                                             | _ => false) 
                                    goal_leaves;

          val ppls = find_matches (n,ty) ppl3 rule_subtrms 
                                  (hd goal_subtrms) (tl goal_subtrms) othervars


          (* After forall-ing sinks need to lift to meta-forall to get match *)
          val ppls2 = Seq.maps (fn pplan => 
                               Prf.apply_frule_thm spec_thm lifted_rulenm pplan) 
                               ppls

          (* Apply our induction scheme *)
          val results = Seq.maps (fn (mod_ind_scheme,pplan) => 
                                     PPlan.apply_res_bck mod_ind_scheme goal pplan)
                                     ppls2

        in 
           Seq.map (fn (gs,nw_pplan) => 
                    Prf.end_meth  
                   ("Induction on: "^indvar_nm)
                   gs (* facts that are derived in subprf *)
                   [goal] (* goal list that are refined in subprf *)
                   nw_pplan (* subprf which you have applied start_meth and then more operations to. *)
                   ppl0 (* prf before you applied start_meth *)
                  ) results
        end
      | _ => Seq.empty
      
    end;

(* the dtac *)
fun induct_mvar_dtac ((n,ty),othervars) = 
          DTac.mk (Pretty.str ("Induction on: "^n),
           GTacs.of_bckf (apply_induction_on_var ((n,ty), othervars)));

(* othervars must be changed to universally quantified variables and we must replace all occurences of var*)
fun apply_induct_mvar_dtac ((n,ty),othervars) =
    RTechnEnv.apply_dtac_to_g (induct_mvar_dtac ((n,ty), othervars));

fun induction_on_goal goal rst =
  let
      val thry = RstPP.get_theory rst
      val gt = Prf.get_ndname_ctrm (RState.get_pplan rst) goal
      val (ithings, non_ithings) = InductDTac.inductable_things_in_term thry gt

     (* make a list of pairs of (induction-variable, variables-to-become-sinks) *)
      fun vars_and_sinks [] vars = vars
        | vars_and_sinks (ithing::rest) vars = 
                 vars_and_sinks rest ((ithing, non_ithings @ rest @ (map fst vars)) :: vars);

      val ind_vars = vars_and_sinks ithings []   
     
  in
      (RTechnEnv.orr_list (map (fn v => apply_induct_mvar_dtac v goal) ind_vars)) rst
      |> Seq.maps (RTechnEnv.map_rstseqf (RTechnEnv.apply_rule_dthm (DThm.mk allI_thm)))
  end;

(* cheat and make meta-vars to frees and send to isabelle *)
fun induction_on_goal2 base_r step_r goal rst =
    let
       val ppl = RState.get_pplan rst
       val goalt = Prf.get_ndname_ctrm ppl goal
    in
      if (null (Term.term_vars goalt)) then 
         InductRTechn.induction_on_goal goal base_r step_r rst 
      else (* Change meta-variables to fresh Frees *)
          let val ((ptab',tmp_var_nms), goalt') =
              Trm.foldmap_trm_vars 
              (fn  (ptab,nw_ns) => fn (((var_nm,i), var_ty), t) =>
                           let 
                             val (nw_n, nw_ptab) = Trm.TrmParams.add1 (var_nm,var_ty) ptab
                           in ((nw_ptab, nw_n::nw_ns), Trm.mk_free(nw_n,var_ty)) 
                           end)
               ((Trm.ptab_of goalt),[]) goalt
               
               val rsts' = Seq.map (fn pplan => RState.set_pplan pplan rst)
                                   (Prf.unify [(goalt,goalt')] ppl)
          in 
               Seq.maps (fn rst => InductRTechn.just_induction_on_goal 
                        goal rst) rsts'
    (*        |> Seq.maps (fn rst => 
                        ((InductRTechn.just_induction_on_goal 
                        goal base_r step_r)
                        thenr
                        (reset_mvars tmp_var_nms)
                        thenr
                        (base_then_step base_r step_r)) rst) *)
          end
    end;


end; (*struct*)

structure IndMvar = IndMvarFUN(HOLDatatypeIndScheme);

(*
Need to disable the check for meta-variables in ipp, otherwise can't test.
use "rtechn/induct/ind_mvar_rtechn.ML";
use_thy "examples/critics_isabelleWS07";
Trm.drop_var_args_flag := false;
val rst = PPInterface.ipp (IndMvar.induction_on_goal "g") ("g", "rev (?F l t) (l :: 'a List) = rev t");
val rst = PPInterface.ipp (IndMvar.induction_on_goal "g") ("g", "! l. rev (?F l t) (l :: 'a List) = rev t");
val rst = PPInterface.ipp (InductRTechn.induction_on_goal "g" RTechn.dummy RTechn.dummy ) ("g", "rev (?F l t) (l :: 'a List) = rev t");

Prf.get_ndname_ltrm;
BUG???:

 val ppl = RState.get_pplan rst;
 val ppls = Prf.apply_resol_bck "spef" "g" ppl;

*** observe uninstantiated "?x", should be instantiated by the above line ***
Seq.list_of ppls;

*)
