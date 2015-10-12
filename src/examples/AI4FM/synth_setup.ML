(* Some setup for synthesis on the AI4FM examples. As they use sets, and sets are represented as functions a=> bool in Isabelle,
   we must specify the arity of functions over sets, or else IsaCoSy will instantiated them too much.
  
   Also set up some simple provers and functions to process the output from synthesis.
 
*)

structure SynthSetup = 
struct 

(* A function that won't allow boolean variables *)
fun not_bool_hole hole_nm synth_trm = 
  let
  val vars = Trm.vars_of synth_trm
  in 
    not(exists (fn (vnm,vtyp) => (vnm=(Hole.dest hole_nm) andalso Trm.typ_name_eq vtyp @{typ "bool"})) vars)
  end;
fun is_hole_in_lhs hole_nm synth_trm =
        (Zipper.mktop synth_trm)
          |> Subst.on_lhs_of_eq 
          |> ZipperSearch.leaves_lr 
          |> Seq.list_of
          |> List.find (fn z => 
                           let val t = Zipper.trm z 
                           in 
                             if (Term.is_Var t) then 
                               fst (Term.dest_Var t) = (Hole.dest hole_nm)
                             else false
                           end)
          |> is_some;
fun not_bool_in_lhs hole_nm synth_trm = 
    (not_bool_hole hole_nm synth_trm) andalso (is_hole_in_lhs hole_nm synth_trm)

(* Need to write special one of these, looking up airities *)
local open Constraints in

fun my_typ_unify_check ctyp typ avoidenv = 
      if Term.is_TVar typ then true
      else
        let 
          val (renaming, ctyp2) = InstEnv.rename_typ_tvars 
                                           (InstEnv.init_renaming avoidenv)
                                         ctyp
        in
          could_typ_unify (typ, ctyp2) (InstEnv.avoid_of_renaming renaming)
        end;


fun mk_constinfo ctxt airities all_consts (cname,typ) =          
      let 
        val ienv = InstEnv.init ctxt

        fun get_arity const = SynthNames.Constant.NTab.get airities (SynthNames.Constant.mk const);
        
        val airity = get_arity cname
        
        fun strip_argtyps airity typ args = 
            if airity < 1 then (args,typ)
            else 
               let val (argtyp,resttyp) = Term.dest_funT typ 
               in strip_argtyps (airity -1) resttyp (args@[argtyp]) end;

        val (argtyps, restyp) = strip_argtyps airity typ []
        val ind_args = Library.map_index (fn (ind, ty) => (ind, ty)) argtyps                

        (* Check allowed_args so types match and build table. *)
        val initATab = 
            List.foldl (fn ((arg_ind,atyp), tab) =>
              let
                val possargs = filter (fn (cn,cty) => 
                                          my_typ_unify_check (snd (strip_argtyps (get_arity cn) cty [])) 
                                                          atyp ienv) 
                                        all_consts
                val const_args = (map fst possargs) |> map Constant.mk      
              in insert_allowed (arg_ind, const_args) tab end)
              ArgPos.NTab.empty ind_args;  
        val cn = Constant.mk cname
      in
        (cn,
         CInfo{name = cn, 
              typ = typ,
              args = ind_args, (* As index * type pairs *)
              min_size = 1 + (List.length argtyps),
              commute_opt = NONE,
              commuted_defs = [],
              assoc_opt = NONE,
              allowedTab = initATab,
              constrTab =  Constraint.NTab.empty,
              start_constrs = [],
               weight = ~1})
      end;


fun mk_constinfo' ctxt airities all_consts (index, (cname,typ)) =
      let 
        val (cnm, cinfo) = mk_constinfo ctxt airities all_consts (cname, typ)
      in
        (cnm, Constraints.set_weight cinfo (index+1))
      end;

fun myinit' ctxt airities (all_consts,synth_consts, eqs, arb_trms, sort_constsf) =
      SynthNames.Constant.NTab.empty
          |> fold SynthNames.Constant.NTab.ins (map_index (mk_constinfo' ctxt airities synth_consts)
                                         (sort_constsf all_consts))
          |> fold add_constraints_from_eq eqs
          |> fold add_constraints_from_whole_term arb_trms;

fun myinit ctxt params const_airities = 
  myinit' ctxt const_airities (Symtab.dest (ConstraintParams.get_cconsts params), 
                  Symtab.dest (ConstraintParams.get_consts params), 
                  ConstraintParams.get_termrws params,
                  ConstraintParams.get_constr_trms params,
                  ConstraintParams.get_sort_lpo_precf params);


local open SynthInterface in

(*fun quick_try_auto ctxt term =  
    
        -> ((string (* proof description *)
             * Thm.thm) option (* proved or not *)
            * (string * Thm.thm) list); (* lemmas found during proof *) =
*)
fun ai4fm_config (c_thms as {conjs,thrms}) (constr_params, ctxt, old_thy_constrs) =
      let
        val (thms_w_prfs,lems_w_prfs) = fold (fn (thm,lemmas) => 
                                              fn (all_thms,all_lemmas) =>
                                             (thm::all_thms, lemmas@all_lemmas)) thrms ([],[])
        val just_thms = map snd thms_w_prfs
        val just_lemmas = map snd lems_w_prfs
        (* Uncomment to only generate constraints from valid rewrites *)
        (* val constr_thms = map_filter (OrderTerms.mk_valid_rw_def_prec old_thy_constrs) just_lemmas@just_thms *)
        val constr_thms = just_thms @ just_lemmas

        val nw_constr_params =  
            ConstraintParams.add_thms ctxt constr_thms constr_params
        (* Subsumption check built into SynthOutput *)
        val nw_ctxt = ctxt 
                       |> SynthOutput.add_thms thms_w_prfs
                       |> SynthOutput.add_thms lems_w_prfs
                       |> SynthOutput.add_conjs conjs
      in (nw_constr_params, nw_ctxt) end;
 
(* val auto_prover = Prover(quick_try_auto); *)

val ai4fm_result_config = ResultConfig(ai4fm_config);

(* Assuming we've generated equaities *)
fun part_config (c_thms as {conjs,thrms}) (constr_params, ctxt, old_thy_constrs) =
    let
     val (thms_w_prfs,lems_w_prfs) = fold (fn (thm,lemmas) => 
                                              fn (all_thms,all_lemmas) =>
                                             (thm::all_thms, lemmas@all_lemmas)) thrms ([],[])
        val thms = map snd thms_w_prfs
        (* Uncomment to only generate constraints from valid rewrites *)
        val constr_thms = map_filter (OrderTerms.mk_valid_rw_def_prec old_thy_constrs) thms
             
       (* Ignores the assumptions attached to the theorems, which we want. *)           
        val nw_constr_params =  
            ConstraintParams.add_thms ctxt constr_thms constr_params
        (* Subsumption check built into SynthOutput *)
        val nw_ctxt = ctxt 
                       |> SynthOutput.add_thms thms_w_prfs
                       |> SynthOutput.add_conjs conjs
      in (nw_constr_params, nw_ctxt) end;

val ai4fm_part_config = ResultConfig(part_config);
 


  (* Main function: Call IsaCoSy *)
  fun thm_synth (Prover prover) (CExFinder cex_finder) (ResultConfig result_config) 
      (VarAllowedFun var_allowed_fn) {max_size, min_size, max_vars, max_nesting}
      top_const const_arities (init_constr_params, init_ctxt) =
      let
        fun synth_one_size this_size (constr_params, ctxt0) =
            let 
              (* Compute current thy constraints and synthesise some terms *)
              val thy_constrs = myinit ctxt0 constr_params const_arities;
              val synth_trms = 
              (ConstrSynthesis.synthesise_terms' top_const var_allowed_fn 
                                                {size = this_size, max_vars = max_vars} 
                                                ctxt0 thy_constrs)
                |> Seq.map (SynthPrfTools.poss_add_Trueprop o Type.legacy_freeze o ConstrSynthesis.get_term)
                |> Seq.list_of;
              (* Record how many terms were synthesised for this size *)
              val ctxt = SynthOutput.add_to_tot this_size (List.length synth_trms) ctxt0
                         |>SynthOutput.add_sterms synth_trms ;
              (* Debug: What did we synthesise *)
              
   
              (* Counter example check *)
              val cand_trms = map_filter (cex_finder ctxt) synth_trms
  
              (* val _ = tracing ""; *)
              
              (* Check which conjectures can be proved. *)
              val (conjs1, thms1) = 
                  fold (fn conj_t => fn (conjs,thms1) => 
                           (case prover ctxt conj_t of 
                              (SOME thm, lemmas) => (conjs,(thm,lemmas)::thms1)
                             | _ => (conj_t::conjs,thms1)))
                       cand_trms
                       ([], []);
  
              (* Do relevant updates to the prover, theory constratints etc, from new theorems *)
              val (constr_params2,ctxt2) = 
                  result_config {conjs = conjs1, thrms = thms1} 
                                (constr_params,ctxt,thy_constrs)
            in 
              (constr_params2, ctxt2)
            end;
      in
        (*fold synth_one_size (min_size upto max_size) (init_constr_params, init_ctxt) *)
         fold synth_one_size (min_size upto max_size) 
             ((ConstraintParams.add_nesting_constrs init_ctxt max_nesting init_constr_params), 
              init_ctxt)
      end;



end
end 

end;
