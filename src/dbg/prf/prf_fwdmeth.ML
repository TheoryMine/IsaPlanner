Trm.drop_var_args_flag := false;
ML_Context.set_context (SOME (Context.Theory (theory "Main")));
val thry = (theory "Main");
val p = Prf.init (the_context());
val t = 
    Prf.read_top_term 
      p "(!! z. g z = f z) ==> (EX x. f x) ==> (EX y. g y)";
val (g,p) = p |> Prf.conj_top_term "g" t;

(* backward proof method *)
val premeth_p = p;
val p = Prf.start_bck_meth "g" p;
val (exi_name, p) = p |> Prf.insert_thm (thm "exE");
val [(gs,p)] = Seq.list_of (Prf.apply_resol_bck exi_name "g" p);
val [(gs,p)] = Seq.list_of (Prf.apply_resol_bck "i" "exEd" p);
val (gs,p) = Prf.end_bck_meth "g" ("exE",p) premeth_p;

val ((gs,p) :: L) = Seq.list_of (p |> Prf.apply_rule_thm (thm "exI") "exEe");

(* change '=' assumption to '==' *)
val premeth_p = p;
val p = Prf.start_fwd_meth p;
val (eqr_nm, p) = p |> Prf.insert_thm (thm "eq_reflection");
val asmstogoals = GoalNCol.dest (Cx.get_lasms (Prf.get_ndname_cx p eqr_nm));
val fwdfromnm = "h";
val ((concnm,subgnms),p) = 
    p |> Prf.lift_and_show_above eqr_nm asmstogoals fwdfromnm;
val subgnm = hd subgnms;
val ((gs,p)::L) = Seq.list_of (Prf.apply_resol_bck fwdfromnm subgnm p);
val (concnm2,(sgs,p)) = Prf.end_fwd_meth 
                    ("fwd eq_reflection",(concnm,p)) premeth_p;

(* apply goal subst *)
val (r as ((n,nd),(cxn,cx))) = APrf.get_result (Prf.get_aprf p) "exIb";
val z = Zipper.mktop (APrf.nd_get_trm nd);
val z2 = z |> Zipper.move_down_right; (* go under Trueprop *)

val (((newg,gs),p)::L) = 
    Seq.list_of (p |> Prf.apply_subst_bck concnm2 (z2,"exIb"));

val [(gs,p)] = 
  Seq.list_of (Prf.apply_resol_bck "exEf" "exIc" p);

writeln "DONE!!!";
