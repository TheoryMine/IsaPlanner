(* Structure for storing and working with partially synthesised terms and their constraints *)

structure STerm =
struct
local open SynthNames; open SynthConstr in

(* datatype of terms being synthesised. This is really a partial/schematic term, with 
   constraints attached to it. *)
datatype T = Sterm of
         {term : Term.term,
          ienv : InstEnv.T, 
          hole_domains : ConstantName.NSet.T HoleName.NTab.T, (* meta-vars in term => allowed consts *)
          synth_constrs : SynthConstr.T ConstraintName.NTab.T, (* constraints on term being synthesised *)
          hole_constrs : ConstraintName.NSet.T HoleName.NTab.T, (* hole => constraints on that hole *)
          hole_sizes : int HoleName.NTab.T, (* size/depth constraint for each hole, currently number of function symbols *)
          holes_agenda : (HoleName.name * Trm.typ) list, (* holes agenda (ordered) for next instantiation *)
          max_vars : int (* Max number of different vars allowed *)
         };

(***  Getting, setting, updating ***)
fun get_term (Sterm rep) = (#term rep)
fun get_ienv (Sterm rep) = (#ienv rep)
fun get_hole_domains (Sterm rep) = (#hole_domains rep)
fun get_synth_constrs (Sterm rep) = (#synth_constrs rep)
fun get_hole_constrs (Sterm rep) = (#hole_constrs rep)
fun get_hole_sizes (Sterm rep) = (#hole_sizes rep)
fun get_holes_agenda (Sterm rep) = (#holes_agenda rep)
fun get_max_vars (Sterm rep) = (#max_vars rep);

fun update_term f (Sterm rep) = 
                 Sterm {term = f (#term rep), ienv = #ienv rep, hole_domains = #hole_domains rep,
                        synth_constrs = #synth_constrs rep, hole_constrs = #hole_constrs rep,
                        hole_sizes = #hole_sizes rep, 
                        holes_agenda = #holes_agenda rep, max_vars = #max_vars rep};
fun update_ienv f (Sterm rep) = 
                 Sterm {term = #term rep, ienv = f(#ienv rep), hole_domains = #hole_domains rep,
                        synth_constrs = #synth_constrs rep, hole_constrs = #hole_constrs rep,
                        hole_sizes = #hole_sizes rep, 
                        holes_agenda = #holes_agenda rep, max_vars = #max_vars rep};
fun update_hole_domains f (Sterm rep)=
                        Sterm {term = #term rep, ienv = #ienv rep, hole_domains = f(#hole_domains rep),
                        synth_constrs = #synth_constrs rep, hole_constrs = #hole_constrs rep,
                        hole_sizes = #hole_sizes rep, 
                        holes_agenda = #holes_agenda rep, max_vars = #max_vars rep};
fun update_synth_constrs f (Sterm rep) =
                        Sterm {term = #term rep, ienv = #ienv rep, hole_domains = #hole_domains rep,
                        synth_constrs = f(#synth_constrs rep), hole_constrs = #hole_constrs rep,
                        hole_sizes = #hole_sizes rep, 
                        holes_agenda = #holes_agenda rep, max_vars = #max_vars rep};
fun update_hole_constrs f (Sterm rep) =
                         Sterm {term = #term rep, ienv = #ienv rep, hole_domains = #hole_domains rep,
                        synth_constrs = #synth_constrs rep, hole_constrs = f(#hole_constrs rep), 
                        hole_sizes = #hole_sizes rep, 
                        holes_agenda = #holes_agenda rep, max_vars = #max_vars rep};  
                       
fun update_hole_sizes f (Sterm rep) = 
                         Sterm {term = #term rep, ienv = #ienv rep, hole_domains = #hole_domains rep,
                        synth_constrs = #synth_constrs rep, hole_constrs = #hole_constrs rep, 
                        hole_sizes = f(#hole_sizes rep), 
                        holes_agenda = #holes_agenda rep, max_vars = #max_vars rep};  
fun update_holes_agenda f (Sterm rep) = 
                       Sterm {term = #term rep, ienv = #ienv rep, hole_domains = #hole_domains rep,
                        synth_constrs = #synth_constrs rep, hole_constrs = #hole_constrs rep, 
                        hole_sizes = #hole_sizes rep, 
                        holes_agenda = f(#holes_agenda rep), max_vars = #max_vars rep};  

fun update_max_vars f (Sterm rep) = 
                  Sterm {term = #term rep, ienv = #ienv rep, hole_domains = #hole_domains rep,
                         synth_constrs = #synth_constrs rep,  hole_constrs = #hole_constrs rep,
                         hole_sizes = #hole_sizes rep, 
                         holes_agenda = #holes_agenda rep, max_vars = f (#max_vars rep)};

fun set_ienv nw_ienv sterm = update_ienv (K nw_ienv) sterm ;
fun set_synth_constrs nw_synth_constrs sterm = update_synth_constrs (K nw_synth_constrs) sterm;
fun set_holes_agenda nw_agenda sterm = update_holes_agenda (K nw_agenda) sterm;
fun set_hole_constrs nw_hole_constrs sterm = update_hole_constrs (K nw_hole_constrs) sterm;
           
fun get_ctxt (Sterm rep) = InstEnv.get_ctxt (#ienv rep);

fun lookup_constr sterm cnm = ConstraintName.NTab.get (get_synth_constrs sterm) cnm;
fun lookup_constrs_of_hole sterm hole = 
     (HoleName.NTab.get (get_hole_constrs sterm) hole)
     |> HoleName.NSet.list_of
     |> map (fn cnm => (cnm, lookup_constr sterm cnm));

fun lookup_domain_of_hole sterm hole = 
    HoleName.NTab.get (get_hole_domains sterm) hole;

fun lookup_hole_size sterm hole = HoleName.NTab.get (get_hole_sizes sterm) hole;

fun lookup_forbidden_vars sterm hole = 
    map_filter (fn (cnm,c) => case c of NotVar(p,v) =>
                                            (case p of Hole(_) => SOME v | _ => NONE)
                                        | _ => NONE) 
               (lookup_constrs_of_hole sterm hole);

(* Delete cnm from holes *)
fun delete_hole_constrs cnm holes hole_constrs =
    List.foldl(fn (h, hole_cs) => 
                      HoleName.NTab.update
                      (h, ConstraintName.NSet.delete cnm (HoleName.NTab.get hole_cs h)) 
                      hole_cs)
              hole_constrs holes;

fun delete_from_domain cnm hole hole_doms =
     HoleName.NTab.update
                   (hole, ConstantName.NSet.delete cnm (HoleName.NTab.get hole_doms hole))
                   hole_doms; 

fun delete_from_holes_agenda hole = 
    update_holes_agenda (Library.remove (fn (h, (h1,_)) => HoleName.name_eq (h,h1)) hole);

(* Insert cnm for hole *)
fun insert_hole_constr cnm hole hole_constrs = 
     HoleName.NTab.update
                   (hole, ConstraintName.NSet.add cnm 
                                (HoleName.NTab.get hole_constrs hole)) hole_constrs;  
                      
(* Search over holes using depth-first search *)
fun add_nw_holes_depthfs nw_holes agenda = nw_holes @ agenda;

(* Size by depth, but not a good idea, too many terms at each iteration *)
fun depth_restr old_hole nw_holes hole_sizes = 
      let 
        val n = HoleName.NTab.get hole_sizes old_hole
      in fold (fn (nw_h, _) => fn sizes=> 
          HoleName.NTab.ins (HoleName.mk nw_h, n-1) sizes) nw_holes hole_sizes 
      end;

(* All combinations of sizes that can be assigned to the holes *)
fun all_size_combs [] max_size = []
  | all_size_combs [h] max_size = [[(h,max_size)]]
  | all_size_combs (h::t) max_size = 
    maps (fn s => map (fn other_comb => (h,s)::other_comb) 
                      (all_size_combs t (max_size-s))) 
         (0 upto max_size);
(*
fun all_decr_combs [] max_size = []
  | all_decr_combs [h] max_size = [[(h,max_size)]]
  | all_decr_combs (h::t) max_size = 
*)

(* Idea: Invert this measure for RHS, then more likely to get a valid RW rule for commutative functions. *)
fun is_decr_size _ [] = true
  | is_decr_size _ [x] = true
  | is_decr_size is_in_rhs ((h1,size1)::(h2,size2)::t) = 
    if (is_in_rhs) then 
      size1 <= size2 andalso (is_decr_size is_in_rhs t)
    else
      size1 >= size2 andalso (is_decr_size is_in_rhs t);
      

(* Here, the size should say how many function symbols are allowed.
   If the function most recently added to the term, whos arguments are the new holes,
   is commutative, the holes are ordered according to size.  *)
fun set_hole_sizes_numfuns commute_opt old_hole old_hole_in_rhs nw_hole_nms strm =
    case nw_hole_nms of 
      [] => Seq.single strm
    | (_::_) => 
      let
        val old_hole_size = HoleName.NTab.get (get_hole_sizes strm) old_hole 
        val all_sizes = all_size_combs nw_hole_nms (old_hole_size-1)
        val set_sizes = case commute_opt of
                          SOME _ => filter (is_decr_size old_hole_in_rhs) all_sizes
                        | NONE => all_sizes
      in
        (map (fn comb => 
                 List.foldl (fn (((h,_),s),sterm) => 
                                (update_hole_sizes (HoleName.NTab.ins (HoleName.mk h,s)) sterm))
                            strm comb) 
             set_sizes) 
          |> Seq.of_list
      end;

(* Pretty printing *)
fun pretty_sterm (st as Sterm rep) = 
    let val ctxt = get_ctxt st in
    Pretty.chunks 
    [
     Pretty.block [Pretty.str "term: ", Trm.pretty ctxt (#term rep)],
     Pretty.block [Pretty.str "ienv: ", InstEnv.pretty (#ienv rep)],
     Pretty.block [Pretty.str "hole_domains: ", 
                   HoleName.NTab.pretty ConstantName.NSet.pretty (#hole_domains rep)],
     Pretty.block [Pretty.str "synth_constrs: ", 
                   ConstraintName.NTab.pretty SynthConstr.pretty_constr (#synth_constrs rep)],
     Pretty.block [Pretty.str "hole_constr: ", 
                   HoleName.NTab.pretty ConstraintName.NSet.pretty (#hole_constrs rep)],
     Pretty.block [Pretty.str "holes_depths: ", 
                   HoleName.NTab.pretty (Pretty.str o Int.toString) (#hole_sizes rep)],
    Pretty.block [Pretty.str "holes_agenda: ", 
                   Pretty.list "[" "]" (map (HoleName.pretty_name o fst)  (#holes_agenda rep))],
     Pretty.block [Pretty.str "max_vars: ", Pretty.str (Int.toString (#max_vars rep))]
    ]
    end;

val print_sterm = Pretty.writeln o pretty_sterm;
fun print_constrs constrs = 
    Pretty.writeln (ConstraintName.NTab.pretty SynthConstr.pretty_constr constrs);

fun new_hole typ ienv = InstEnv.new_uninst_var (("h", 0), typ) ienv


(* Given a cinfo, introduce new holes for each of the constants arguments. 
   Keep track of which argument positions correspond to which new holes. 
   Update the sterm to know about the new holes and their domains. *)
fun set_nw_hole_domains cinfo (arg_ind, ty) (strm,arg2holes) =
     let
        val (var, ienv2) = new_hole ty (get_ienv strm)
        val nw_hole_nm = HoleName.mk var
        val arg2holes' = ArgName.NTab.ins (arg_ind, nw_hole_nm) arg2holes 
        val arg_domain = ConstInfo.lookup_arg_domain cinfo arg_ind
                      
        val strm' = update_hole_domains 
                     (HoleName.NTab.ins (nw_hole_nm, arg_domain)) strm
        in ((var, ty), (set_ienv ienv2 strm', arg2holes')) end;

(* Make new synthesis constraints from the thy-constraints of a given constant,
   and insert these in the sterm.
   Keeps track of which argument positions correspond to which new hole,
   and which theory constraint correspond to which new synthesis constraint. *)
fun set_nw_constrs arg2hole_map (cnm,constr) (strm, cnstr_nm_map) =
    let 
       val (nw_cnm,nw_constrs) = 
            ConstraintName.NTab.add (cnm, SynthConstr.from_thy_constr arg2hole_map constr) 
                                    (get_synth_constrs strm)
       in
         (set_synth_constrs nw_constrs strm, 
                                 ConstraintName.NTab.ins (cnm, nw_cnm) cnstr_nm_map)
       end;
(* Given which argument positions correspond to which new hole, and which
   theory constraint correspond to which new synthesis constraint, 
   update the sterm's map between new holes and their constraints.  *)
fun set_nw_hole_constrs arg2hole_map constr_renamings (arg, cs) strm =
    let 
       val renamed_cs = map (fn c => ConstraintName.NTab.get constr_renamings c) 
                            (ConstraintName.NSet.list_of cs)
       val hole = ArgName.NTab.get arg2hole_map arg
       in
         update_hole_constrs (HoleName.NTab.ins (hole, 
                              ConstraintName.NSet.of_list renamed_cs)) strm 
       end;

(* Should update existing synthesis constraints, given an instantiation for a hole, and
   remove that hole from the sterm. cnm is the name for the updated constrait constr, 
   holes are the holes the constraint refered to prior to being updated. *)
fun manage_upd_constrs (cnm,old_holes,constr) sterm = 
    case constr of
      VIOLATED => raise ERROR "Sterm.manage_upd_constrs: Instantiation violated a constraint."
    | SATISFIED => sterm 
                   |> update_synth_constrs (ConstraintName.NTab.delete cnm)
                   |> update_hole_constrs (delete_hole_constrs cnm old_holes) 
    | NotConst(p,const) => 
                  (case p of
                  (* Remove const from the domain of h, then drop it. *)
                  Hole(h) => sterm |> update_hole_domains (delete_from_domain const h)
                                   |> update_synth_constrs (ConstraintName.NTab.delete cnm)
                                   |> update_hole_constrs (delete_hole_constrs cnm old_holes) 
                 (* Make sure h points to constraint *)
                 | HolePath(h,_) => sterm |> update_hole_constrs (insert_hole_constr cnm h)
                                          |> update_synth_constrs (ConstraintName.NTab.update (cnm, constr))
                  )
    | NotVar(p,_) => sterm 
                       |> update_hole_constrs (insert_hole_constr cnm (SynthConstr.top_hole_of_pos p))
                       |> update_synth_constrs (ConstraintName.NTab.update (cnm, constr))
              
    | Or(_) => (List.foldl (fn (h,strm) => update_hole_constrs (insert_hole_constr cnm h) strm) 
                           sterm (SynthConstr.top_holes_of_constr constr))
                 |> update_synth_constrs (ConstraintName.NTab.update (cnm, constr))

    | UnEqual(_) => (List.foldl (fn (h,strm) => update_hole_constrs (insert_hole_constr cnm h) strm) 
                           sterm (SynthConstr.top_holes_of_constr constr))
                      |> update_synth_constrs (ConstraintName.NTab.update (cnm, constr));

(*Propagete constraint updates through an sterm. *)
fun update_sterm_const_inst arg2hole_map hole const sterm = 
      let       
       val upd_constrs = map (fn (cnm, c) => 
                              (cnm, SynthConstr.top_holes_of_constr c,
                              SynthConstr.update_constrs_on_hole arg2hole_map hole const c)) 
                         (lookup_constrs_of_hole sterm hole)
       in
          (fold manage_upd_constrs upd_constrs sterm)
          |> update_hole_domains (HoleName.NTab.delete hole) (*remove the instantiated hole *)
          |> update_hole_constrs (HoleName.NTab.delete hole)
          |> update_hole_sizes (HoleName.NTab.delete hole)
          |> delete_from_holes_agenda hole
       end;

(* Build the term used to instantiate some hole in sterm, given the cinfo. 
   Update holes and constraints in sterm to include the new things.
   This function is responsible of adding the new holes and constraints,
   and then update the existing constraints in which the instantiated hole 
   is involved.*)                       
fun inst_sterm_w_const sterm (hole,htyp) cinfo = 
  let
      val (const_nm, const_typ) = (ConstantName.dest (ConstInfo.get_name cinfo),
                                   ConstInfo.get_typ cinfo)
      val (_, nw_const_typ) = 
          InstEnv.rename_typ_tvars (InstEnv.init_renaming (get_ienv sterm)) const_typ 


      val (typed_args, typ_rnms) = 
          fold_map (fn (arg,typ) => fn rnm => 
                            let val (rnm',typ') = InstEnv.rename_typ_tvars rnm typ
                            in ((arg,typ'), rnm') end)
                         (ConstInfo.get_args cinfo) (InstEnv.init_renaming (get_ienv sterm));

      (* Check the position of this hole *)
      val is_hole_in_rhs = SynthLib.is_hole_in_rhs (HoleName.dest hole) (get_term sterm);

     (* Make new holes and set their domains in the sterm *)
     val (nw_hole_nms, (sterm1, arg2hole_map)) =
         fold_map (set_nw_hole_domains cinfo) 
                       typed_args 
                       (set_ienv (InstEnv.avoid_of_renaming typ_rnms) sterm, ArgName.NTab.empty)
           
    (* Add newly created holes to the agenda *)
    val sterm2 = sterm1 
                 |> update_holes_agenda (add_nw_holes_depthfs 
                                           (map (fn (nm,ty) => (HoleName.mk nm,ty)) nw_hole_nms))

    (* Copy constraints from the const into the sterm. Keep track of renamings of constraints. *)
    val (sterm3, constr_nm_map) = 
        ConstraintName.NTab.fold (set_nw_constrs arg2hole_map)
                                 (ConstInfo.get_constrs cinfo)
                                 (sterm2, ConstraintName.NTab.empty)

    (* Finally, insert the hole-to-constraint map for the new constraints *)
    val sterm4 = ArgName.NTab.fold 
                     (set_nw_hole_constrs arg2hole_map constr_nm_map)
                     (ConstInfo.get_arg_constrs cinfo) sterm3

     (* The term (containting the new holes) for instantiating some hole in the sterm with *)
     val inst_trm = 
          Term.list_comb (Const(const_nm, nw_const_typ), map Trm.mk_var nw_hole_nms)
     (* Should really only get one unifier here, then also compute all possible sizes for the new holes. *)
     val inst_strms = (MyUnify.unifiers (get_ienv sterm4, 
                                      [(Trm.mk_var (HoleName.dest hole, htyp), inst_trm)]))
                    |> Seq.map (fn ienv' => (update_term (InstEnv.inst_trm ienv') sterm4)
                                            |> set_ienv ienv')
                    |> Seq.maps (set_hole_sizes_numfuns (ConstInfo.get_commute_opt cinfo) hole is_hole_in_rhs nw_hole_nms) 
    in 
      Seq.map (update_sterm_const_inst arg2hole_map hole (ConstInfo.get_name cinfo)) inst_strms
    end;

 
(* Should remove the next hole from the agenda, and find all constants that are allowed to
   instantiate it *)
fun inst_nxt_hole_const thyConstrs sterm = 
    case (get_holes_agenda sterm) of 
      [] => Seq.empty
     | ((hole,typ)::hs) =>
        let 
          val domain = ConstantName.NSet.list_of (lookup_domain_of_hole sterm hole)
          (* If this hole is allowed less than 1 function, we can only instantiate by constants,
            not of function type. *)
          val consts = if ((lookup_hole_size sterm hole) < 1)
                       then filter (TheoryConstraints.is_fn thyConstrs) domain
                       else filter (not o (TheoryConstraints.is_fn thyConstrs)) domain
          in
            Seq.maps (fn const => (TheoryConstraints.lookup_const thyConstrs const)
                              |> inst_sterm_w_const sterm (hole,typ)) 
                      (Seq.of_list consts)
         end;

(* Update the sterm after instatiating hole by a variable *)
fun update_sterm_var_inst hole sterm = 
    let 
       (* Must have been instantiated to a Free *)
       val (_, Free(varnm,_)) = InstEnv.get_var_inst (get_ienv sterm) (HoleName.dest hole)      
       val upd_constrs = map (fn (cnm, c) => 
                             (cnm, SynthConstr.top_holes_of_constr c,
                              SynthConstr.update_constrs_on_hole_var hole varnm c)) 
                         (lookup_constrs_of_hole sterm hole)
       in
          (fold manage_upd_constrs upd_constrs sterm)
          |> update_hole_domains (HoleName.NTab.delete hole) (*remove the instantiated hole *)
          |> update_hole_constrs (HoleName.NTab.delete hole)
          |> update_hole_sizes (HoleName.NTab.delete hole)
          |> delete_from_holes_agenda hole
       end;

(* Instantiate the next hole with a variable. *)
fun inst_nxt_hole_var var_allowedf sterm = 
    case (get_holes_agenda sterm) of 
        [] => Seq.empty
        | ((hole,typ)::hs) =>    
        if ((lookup_hole_size sterm hole) > 0) then Seq.empty
          (* The number of functions to go in this hole is 0, we should put a variable here *)
          else 
            let
              (* Instanitate the current hole with a variable *)
              fun inst_strm var_trm = 
                            (MyUnify.unifiers (get_ienv sterm, 
                                       [(Trm.mk_var (HoleName.dest hole, typ), var_trm)]))
                            |> Seq.map (fn ienv' => (update_term (InstEnv.inst_trm ienv') sterm)
                                                     |> set_ienv ienv')
                
              val paramtab = Trm.params_of(get_term sterm);
              (* Can we re-use some of the existing vars? *)
              val old_frees_insts =  
                  Seq.maps inst_strm
                          (Seq.of_list 
                               (Library.subtract 
                                  (fn (v1,free) => v1 = fst (Term.dest_Free free))
                                  (lookup_forbidden_vars sterm hole)
                                  (map (fn (nm,ty) => Free(nm,ty)) 
                                       (Trm.TrmParams.get_plist paramtab))))

              (* Can we insert a fresh var? *)
              val fresh_free_insts = 
                  if (var_allowedf hole sterm andalso (get_max_vars sterm) > 0)
                  then (Trm.TrmParams.add1 ("x", typ) paramtab) |> fst
                                       |> (fn nm => inst_strm (Free(nm,typ)))
                  else Seq.empty
              in 
                Seq.append
                (Seq.map (fn strm => strm 
                            |> (update_sterm_var_inst hole)
                            |> update_max_vars (fn mvars=>mvars-1)) 
                         fresh_free_insts)
                (Seq.map (update_sterm_var_inst hole) old_frees_insts)

              end;              
(* Creates an empty sterm with just one hole of given type *)
fun empty typ ctxt = 
    let 
      val (varnm, ienv) = new_hole typ (InstEnv.init ctxt)
    in
     Sterm {term = Var(varnm,typ),
          ienv = ienv,
          hole_domains = HoleName.NTab.empty,
          synth_constrs = ConstraintName.NTab.empty,
          hole_constrs = HoleName.NTab.empty, 
          hole_sizes = HoleName.NTab.empty,
          holes_agenda = [(HoleName.mk varnm,typ)],
          max_vars = 0
         }
     end;
 
fun init_w_const (const,typ) size max_vars ctxt thyConstrs = 
    let 
      val (varnm, ienv) = new_hole typ (InstEnv.init ctxt)
      val hole = HoleName.mk varnm
      val (_,hole_typ) = Term.strip_type typ
    in
     inst_nxt_hole_const thyConstrs 
     (Sterm {term = Var(varnm,hole_typ),
             ienv = ienv,
             hole_domains = HoleName.NTab.ins (hole, ConstantName.NSet.single const) 
                                              (HoleName.NTab.empty),
             synth_constrs = ConstraintName.NTab.empty,
             hole_constrs = HoleName.NTab.ins (hole,ConstraintName.NSet.empty) HoleName.NTab.empty,
             hole_sizes = HoleName.NTab.ins (hole, size) (HoleName.NTab.empty),
             holes_agenda = [(hole,hole_typ)],
             max_vars = max_vars})
     end;

(*Assume size refers to the depth of the term, then the new holes will have different size
  depending on where they are in term. *)
fun init_w_term term max_size max_vars ctxt thyConstrs =
    let 
      fun depth_of_target z = (Term.dest_Var (Zipper.trm z), 
                               length (filter 
                                         (fn c => case c of Zipper.C.D.AppL _ => true | _ => false)
                                         (Zipper.ctxt z)))
          
      val var_zips = (Zipper.mktop term) 
                       |> ZipperSearch.leaves_lr 
                       |> Seq.list_of
                       |> filter (Term.is_Var o Zipper.trm) 
      val holes = map (Term.dest_Var o Zipper.trm) var_zips
      val free_vars = Trm.TrmParams.get_plist (Trm.params_of term)
      val mvars = max_vars - (length free_vars)      
    in
      (Sterm {term = term,
              ienv = InstEnv.of_trm ctxt term,
              hole_domains = fold (fn (hole,typ) => 
                                      HoleName.NTab.ins (HoleName.mk hole, ConstantName.NSet.of_list
                                                    (TheoryConstraints.get_consts_of_typ typ thyConstrs)))
                                              holes (HoleName.NTab.empty),
              synth_constrs = ConstraintName.NTab.empty,
              hole_constrs = fold (fn (hole,_) => 
                                      HoleName.NTab.ins (HoleName.mk hole, ConstraintName.NSet.empty)
                                  ) holes (HoleName.NTab.empty),
              hole_sizes = fold (fn ((hole,_),depth) => 
                                   HoleName.NTab.ins (HoleName.mk hole, max_size-depth)) 
                               (map depth_of_target var_zips) (HoleName.NTab.empty),
              holes_agenda = map (fn (hole,typ) => (HoleName.mk hole, typ)) holes,
              max_vars = if mvars < 0 then 0 else mvars})
    end;

end (* local open *)
end; (* struct *)
