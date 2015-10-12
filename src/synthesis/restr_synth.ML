
(* restricted Synthesis: adds extra constraints to synthesis:
   obl_const_nms must be used. 
*)
(* FIXME: same code in synthesis??? called restr_synthesis *)
structure RestrConstrSynth =
struct
local open SynthNames; open Constraints; open ConstrSynthesis; in

fun synthesise_terms2' (top_const, top_cinfo) var_allowed_fn 
                       max_size (max_vars : int) thy 
                       obl_const_nms unused_consts constInfoTab = 
    let 
      val top_cnstrs = Constraints.get_constrTab top_cinfo

      val (init_trm, init_holes, ienv, allowed_tab1) =     
          mk_new_term_bit top_cinfo (Hole.NTab.empty) (InstEnv.init thy)
      (* val hole_nms_typs = map (fn (nm,ty) => (Hole.mk nm, ty)) init_holes *)
      val hole_nms = map (fn (nm,ty) => Hole.mk nm) init_holes

      (* Debugging: make sure names here are different from the constant-info *)
      val init_constr_tab = Constraint.NTab.useup_names (Constraint.NTab.get_nameset top_cnstrs) 
                                                  Constraint.NTab.empty
      val constr_renamings = (rename_constraints top_cnstrs init_constr_tab)
                             |> Constraint.nmap_of_renaming
        
      val constr_dep_tab1 = 
          init_constr_dep_tab constr_renamings top_cnstrs

      (* Add renamed constraints to the constraint-table and to the table 
         of constraints for each hole *)
      val (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) = 
          List.foldl 
            (attach_constr top_cnstrs constr_renamings hole_nms)
                (Hole.NTab.empty, init_constr_tab, allowed_tab1, constr_dep_tab1) 
                (map snd (Constraints.get_start_constrs top_cinfo))

      val commute_opt = Constraints.get_commute_opt top_cinfo
      val synth_terms = 
          map (fn holesizes =>
                  Sterm {term = init_trm,
                         ienv = ienv,
                         allowedTab = allowed_tab,
                         constrTab = constr_tab,
                         holeConstrs = hole_constr_tab,
                         constrDepTab = constr_dep_tab,
                         holes_agenda = hole_nms,
                         hole_sizes = holesizes,
                         max_vars = max_vars})
              ((hole_size_combos commute_opt hole_nms (max_size -1))
                 |> map (fn l => (fold Hole.NTab.ins l Hole.NTab.empty)))
    in
      (Seq.of_list synth_terms)
         |> Seq.maps (fn strm => restr_synthesis var_allowed_fn constInfoTab 
                                        obl_const_nms (unused_consts, strm))
      |> Seq.list_of
      |> map (certify_strm thy)
    end;


val counter_ex_counter = ref 0;
fun synthesise_terms2 top_const var_allowed_fn max_size max_vars thy 
                         obl_const_nms constInfoTab = 
    let 
      val _ = counter_ex_counter := 0 (* Reset counter *)
      val top_cinfo = the (Constraints.lookup_const constInfoTab top_const)  
      val obl_consts =
          map (fn cnm => (cnm, Constraints.get_minsize 
                                 (Constant.NTab.get constInfoTab cnm))) 
                                  obl_const_nms
      val minsize = List.foldl (fn ((const, size), tot) => tot + size) 0 obl_consts
    
      val ((nw_cinfo_tab, new_thy), synth_conjs) = 
          Library.foldl_map (fn ((cinfo_tab, thry), this_size) => 
                        let 
                          val cand_strms = 
                              (synthesise_terms2' (top_const, top_cinfo) var_allowed_fn 
                                                  this_size max_vars thry 
                                                  obl_const_nms obl_consts cinfo_tab)
                                |> filter (fn strm => 
                                              SynthPrfTools.counter_ex_check_count 
                                                counter_ex_counter thry 
                                                (get_term strm))
                          val (thy2, proved) = 
                              Library.foldl_map (fn (thy1, strm) => 
                                      SynthPrfTools.ripple_conj_add_wrules thy1 
                                                                      (get_term strm))
                              (thry, cand_strms)
                          val cinfo_tab2 = 
                              List.foldl (fn ((thm_trm, prfs), cinfo) => 
                                        if (null prfs) then cinfo
                                        else Constraints.add_constraints_from_eq
                                               (ConstraintParams.termrw_of_term
                                               (Trm.change_frees_to_fresh_vars thm_trm)) cinfo)
                                    cinfo_tab proved
                        in
                          ((cinfo_tab2, thy2), proved)
                        end)
                    ((constInfoTab, thy), ((minsize+1) upto max_size))

      val (conjs, thrms) = 
          (flat synth_conjs)
            |> List.partition (fn (t, prfs) => null prfs)
    in
      ((nw_cinfo_tab, thy), (conjs, thrms))
    end;

fun synthesise_eq_terms2 max_size max_vars thy0 constInfoTab =
    synthesise_terms2 (Constant.mk "HOL.eq") 
      ConstrSynthesis.VarAllowed.is_hole_in_lhs 
      max_size max_vars thy0 
      constInfoTab;

(* *)
fun type_is_datatype thy (Type(n,_)) = (Symtab.defined (Datatype.get_all thy) n)
  | type_is_datatype _ _ = false;

fun constname_is_datatype_constr thy n = 
    type_is_datatype thy (snd (Term.strip_type (Sign.the_const_type thy n)));
         
(* A function that seems to synthesise equations about contaning exactly a single constant,
   for each constant in the cinfo-table. *)
fun synth_single_consts max_size max_vars thy cinfoTab = 
    let
      fun unzip (h::t) = 
          let 
            fun unzip_aux [] ls rs = (ls, rs)
              | unzip_aux ((l,r)::t) ls rs = unzip_aux t (l@ls) (r@rs)
          in unzip_aux (h::t) [] [] end;

      val (datatype_consts, fun_consts) = 
          List.partition (constname_is_datatype_constr thy) 
            (map Constant.string_of_name (Constant.NTab.keys cinfoTab))
      val ((nw_cinfo, nw_thy), results) = 
          Library.foldl_map (fn ((ctab,thy1), const) =>
                        synthesise_eq_terms2 max_size max_vars thy1 [Constant.mk const] ctab)
                    ((cinfoTab, thy), fun_consts)
    in
      ((nw_cinfo, nw_thy), unzip results)
    end;

(* Print out pretty results and some stats *)
fun synth_w_stats max_size max_vars thy0 obl_consts_strs constInfoTab =
    let 
      val obl_consts = map Constant.mk obl_consts_strs
      val _ = counter_ex_counter := 0 (* Reset counter *)
      val ((cinfo, thy), (conjs, thrms)) = 
           synthesise_eq_terms2 max_size max_vars thy0 obl_consts constInfoTab
          (*synth_single_consts max_size max_vars thy0 constInfoTab *)
      val ctxt = ProofContext.init_global thy
      val conjectures = map fst conjs
      val theorems = map fst thrms 
      val (ac_things, comm_thms) =  
          (map (fn (nm, cinfo) => 
                   if ((Constant.dest nm) = "HOL.eq")
                   then ([], []) (* Exclude = as these thms are built in *)
                   else
                     let 
                       val assoc = Constraints.get_assoc_opt cinfo
                       val comm = Constraints.get_commute_opt cinfo
                       val com_defs = Constraints.get_commuted_defs cinfo
                     in 
                       ((map_filter I [assoc, comm]), com_defs)
                     end) 
               (Constant.NTab.list_of cinfo))
            |> (fn thms => (flat (map fst thms), flat (map snd thms)))
           
      val line =  Pretty.str "-----------------------";
      val pretty_thms =  line::(Pretty.str "Synthesised theorems: ")::
                         (map (fn trm => Trm.pretty ctxt trm) theorems)
      val pretty_conjs = line::(Pretty.str "Synthesised conjectures (not proved): ")::
                         (map (fn trm => Trm.pretty ctxt trm) conjectures)
      val pretty_ac = line::(Pretty.str "AC-properties found: ")::
                      (map (fn trm => Trm.pretty ctxt trm) ac_things)
      val pretty_commutes = line::(Pretty.str "Commuted versions of defs: ")::
                      (map (fn trm => Trm.pretty ctxt trm) comm_thms)
      val _ = Pretty.writeln (Pretty.chunks(pretty_thms @ pretty_conjs 
                                            @ pretty_ac @ pretty_commutes))
    in
      writeln ("\n False conjectures synthesised: " ^(Int.toString (!counter_ex_counter)))
    end;

end; (* local *)
end;
