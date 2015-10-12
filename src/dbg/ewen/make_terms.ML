(* create a new theory using IsaP and Main *)
  Trm.drop_var_args_flag := false;

val thry = Theory.begin_theory "test" [theory "Main", theory "IsaP"];
    ML_Context.set_context (SOME (Context.Theory thry));

    (* make a new empty proof plan/reasoning state *)
val init_rst = RState.init_from_thy (the_context());

    (*------------- Problem setup -------------*)
val problem_name = "Test.doubleArray0"
val problem_term = 
    PPlan.read_prop
      (RState.get_pplan init_rst) 
      "(I --> (ALL i. ((i = 0) --> (((i >= 0) & (i <= ?X0 pv_a)) & (ALL i'. (((i' >= 0) & (i'<= ?X0 pv_a)) --> (((i' ~= (length pv_a)) = False) --> I))))))) & (((pv_i >=0) & (pv_i <= ?X0 pv_a)) --> (((pv_i ~= (length pv_a)) = True) --> (ALL x. ((pv_i >= 0) & ((pv_i < (length pv_a)) & (((pv_i >= 0) & (pv_i < (length pv_a))) & (ALL i. ((i = (pv_i + 1)) --> ((i >= 0) & (i <= ?X0 pv_a))))))))))";

    (*------------- Make state from problem -------------*)
val rst = 
    init_rst |> (RstPP.add_new_conj (problem_name, problem_term));
val [rst2] = Seq.list_of (DTacRTechn.safe problem_name rst);

    (*------------- terms from strings -------------*)
val useful_bits = 
    PPlan.read_prop
      (RState.get_pplan init_rst)  "(F (op &) (0 :: nat) (op <) (op =) (a | b) (length :: ?'a list => nat))";
    TermDbg.writeterm useful_bits;
val useful_bits2 = 
    PPlan.read_prop
      (RState.get_pplan init_rst)  "(F (0 :: nat) (?a :: ?'a))";
    TermDbg.writeterm useful_bits2;

    (*------------- basic constants -------------*)
val and_term = (("HOL.conj", Type("fun", [Type("HOL.bool", []), Type("fun", [Type("HOL.bool", []), Type("HOL.bool", [])])])));
val zero_term = (("HOL.zero", Type("nat", [])));
val or_term = (("HOL.disj", Type("fun", [Type("HOL.bool", []), Type("fun", [Type("HOL.bool", []), Type("HOL.bool", [])])])));

val eq_term = (("HOL.eq", Type("fun", [Type("nat", []), Type("fun", [Type("nat", []), Type("HOL.bool", [])])])));
val less_term = (("Orderings.less_eq", Type("fun", [Type("nat", []), Type("fun", [Type("nat", []), Type("HOL.bool", [])])])));
    (* val length_term = (("Nat.size", Type("fun", [Type("List.list", [TVar( ("'a", 0), ["HOL.type"])]), Type("nat", [])]))); *)
      (* FIXME: should use tvars and use type-unification *)
val length_term = (("Nat.size", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("nat", [])])));
(*val length_term = (("Nat.size", Type("fun", [Type("List.list", [TFree("'b", ["HOL.type"])]), Type("nat", [])])));*)

val constrs = [less_term,length_term];
    (* val constrs = [zero_term,less_term,eq_term,length_term]; *)


fun possible_insts (possible_consts_typ_inst, args_typs) final_typ = 
    map fst 
  (filter snd (* make sure we are of the right type *)
    ((map (fn (i,argtyp) => 
        let val (arg_needs,arg_makes) = Term.strip_type argtyp
        in (* FIXME: do full unif ... (Trm.clean_unify_typs thry [(arg_makes,final_typ)]) *)
             ((arg_needs, Bound i), arg_makes = final_typ)
        end
          ) ((Library.downto ((length args_typs) - 1,0)) ~~ args_typs))
     @ (map (fn (rn, ctyp, ctrm) =>   
          let val (c_needs,c_makes) = Term.strip_type ctyp
          in (* FIXME: do full unif ... (Trm.clean_unify_typs thry [(arg_makes,final_typ)]) *)
         ((c_needs, ctrm), c_makes = final_typ)
          end)
      possible_consts_typ_inst)));

fun one_of_each ([] : 'a Seq.seq list) = (Seq.empty : 'a list Seq.seq)
  | one_of_each [Hseq] = Seq.map (fn h => [h]) Hseq
  | one_of_each (Hseq :: MoreSeqs) = 
    (case Seq.pull Hseq of 
       NONE => Seq.empty
     | SOME (h,morehs) => 
       (case Seq.pull (one_of_each MoreSeqs) of 
    NONE => Seq.empty
  | SOME (t,morets) => 
    Seq.cons (h::t)
       (Seq.append (Seq.map (fn t2 => h::t2) morets) 
             (one_of_each (morehs :: MoreSeqs)))));

    (* make terms rec *)
fun make_terms (possible_consts_typ_inst, args_typs) final_typ = 
    let val (finalplug, needmoreplugs) =
      List.partition (null o fst) (possible_insts (possible_consts_typ_inst, args_typs) final_typ);
      
  fun complete_plugs (moreargs : Term.typ list, t : Term.term) = 
      (Seq.map 
         (fn l => Term.list_comb (t,l))
         (one_of_each (map (make_terms (possible_consts_typ_inst, args_typs)) moreargs))
       : Term.term Seq.seq);
    in
      Seq.append (Seq.map snd (Seq.of_list finalplug))
     (Seq.maps complete_plugs (Seq.of_list needmoreplugs))
    end;


(* For the moment restrict things with boolean args to one operation *)

    (* make terms rec *)
fun make_mvar_terms vars (possible_consts_typ_inst, args_typs) final_typ = 
    let val (finalplug, needmoreplugs) =
      List.partition (null o fst) 
         (possible_insts (possible_consts_typ_inst, args_typs) final_typ);

  fun mvar_plugs (moreargs : Term.typ list, t : Term.term) = 
      let 
        val (L,vars2) = 
      fold (fn ty => fn (L,vars) => 
            let val (outname,vars2) = Trm.Var.NTab.add (("Y",0), ty) vars
            in ((Term.list_comb
             (Var (outname, args_typs ---> ty), 
              map Bound (Library.downto ((length args_typs) - 1,0))))
          :: L, vars2) end)
           moreargs ([],vars)
      in (vars2, Term.list_abs (map (pair "") args_typs,Term.list_comb (t, L))) end
    in
      (map (fn (_,t) => (vars, Term.list_abs (map (pair "") args_typs,t)))
     finalplug)
      @ (map mvar_plugs needmoreplugs)
    end;

fun real_uninst_vars ienv = 
    filter (fn (n,ty) => Basics.is_none (InstEnv.lookup_var_inst ienv n))
     (InstEnv.uninst_vars_of ienv);

    (* FIXME: in_args_typs should be able to grow dynamically when we work
with higher order things. *)
fun inc_instantiations (possible_consts_typ_inst,in_arg_tys) uvars (ienv,vars) = 
    (* map (fn (ienv2,vars2) => 
         let val newvars = Trm.Var.NTab.difference vars2 vars in 
     (fold InstEnv.add_uninst_var (Trm.Var.NTab.dest newvars) ienv2, vars2)
         end) *)
      (fold (fn (n,ty) => (* the next var to inst *)
       fn ivL => (* list of possible inst so far *)
       let val (arg_tys,fin_typ) = Term.strip_type ty in
         maps
           (fn (ienv,vars) => (* inst and vars so far *)
              map (fn (vars2,t) => (* each new inst for n *)
                   (InstEnv.add_var_inst (n,(ty,t)) ienv,
                    vars2))
              (make_mvar_terms 
                 vars (possible_consts_typ_inst,in_arg_tys) fin_typ))
           ivL
       end)
      uvars [(ienv, vars)]);

fun inc_inst_rtechn possible_consts_typ_inst arg_typs rst = 
    let 
      val pplan = RState.get_pplan rst;
      val thry = PPlan.get_theory pplan;
  (*     val vars = PPlan.get_vars pplan;
      val (typsvars,trmvars) = Trm.dest_vtab vars;
      val uvars = real_uninst_vars (PPlan.get_ienv pplan);
 *)
      val uvars = InstEnv.uninst_vars_of (PPlan.get_ienv pplan);
      val insts = map fst (inc_instantiations (possible_consts_typ_inst,arg_typs) 
                                              uvars (InstEnv.init thry,trmvars));
    in
      Seq.of_list
  (map (fn i => rst |> RstPP.inst i 
        |> RState.set_rtechn NONE
        |> (DescripCInfo.set_rst 
        (RstName.pretty 
           (Pretty.block 
              [Pretty.str "Instantiating ",
               Pretty.list "[" "]"
               (map (Trm.Var.pretty_name o fst) 
              (real_uninst_vars i))]))))
       insts)
    end;

local open RTechnEnv; in

fun uninst_vars_of rst = InstEnv.uninst_vars_of 
         (PPlan.get_ienv (RState.get_pplan rst));

fun is_ground rst = null (uninst_vars_of rst);


fun do_ground_inst_rtechn constrs rst = 
    let 
      val pplan = RState.get_pplan rst;
      val thry = PPlan.get_theory pplan;
      val vars = PPlan.get_vars pplan;
      val (typsvars,trmvars) = Trm.dest_vtab vars;
      val [(varX,X_typ)] = Trm.Var.NTab.dest trmvars;
      val arg_typs = fst (Term.strip_type (Var.NTab.get trmvars varX));
      val renaming = TrmRename.init vars;
      val rename_typf = TrmRename.rename_type (fst TrmRename.ignore_none) renaming;
      val possible_consts_typ_inst = 
    map (fn (name,typ) => 
      let val (rn,typ2) = rename_typf typ 
      in (rn, typ2, Const (name,typ2)) end) 
        constrs;

        val ienv = fold InstEnv.add_uninst_var (Trm.Var.NTab.dest trmvars) 
            (PPlan.get_ienv pplan);
        val rst2 = RState.update_pplan (Prf.set_ienv ienv) rst;
    in
      repeat_until is_ground (inc_inst_rtechn possible_consts_typ_inst arg_typs) rst2
    end;


val funtechn = 
    refine (RstName.str "instr then quickcheck then auto")
           ((do_ground_inst_rtechn constrs)
        thenr DTacRTechn.safe 
              thenr QCheckAutoRTechn.quickcheck 
        thenr (rstif (fn rst => null (QCheckAutoRTechn.get_bad_goals rst))
         DTacRTechn.auto
         fail));

end;


    raise ERROR "done.";

    (*-------------  -------------*)

val pplan = RState.get_pplan rst;
val thry = PPlan.get_theory pplan;
val rst = 
    init_rst |> (RstPP.add_new_conj (problem_name, problem_term));
val rst = rst |> (RState.set_rtechn (SOME (do_ground_inst_rtechn constrs)));
val rst = rst |> (RState.set_rtechn (SOME funtechn));


(*interactive: *)
     PPInterface.ipp_rst rst;


      (* automatic *) 
val final_rst = Seq.list_of (RState.search (MSearch.breadthfs()) rst);

val instopt = InstEnv.lookup_var_inst  (PPlan.get_ienv (RState.get_pplan (hd final_rst))) ("X",0);

    case instopt of NONE => raise ERROR "foo!"
      | SOME x => writeln "yay!";
