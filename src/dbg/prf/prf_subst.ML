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
val (gs,p) = Prf.end_bck_meth "g" ("exE with:" ^ "i",p) premeth_p;

val ((gs,p) :: L) = Seq.list_of (p |> Prf.apply_rule_thm (thm "exI") "exEe");
(*  or more verbose version...
val exI_dtac = IsaDTac.Rule.rule_th (thm "exI");
val ((gs,p) :: L) = Seq.list_of (p |> Prf.apply_dtac exI_dtac "exEe");
*)

val atomise_eq = thm "HOL.atomize_eq";
val symmetric = thm "ProtoPure.symmetric";
val unatomise_eq = 
    Thm.put_name "unatomise"
                  (Drule.zero_var_indexes (atomise_eq RS symmetric));

val (unatomise, p) = p |> Prf.insert_thm unatomise_eq;

(* flexes *)
val flexes = (Prf.get_flexes p);

(* result and zipper *)
val (r as ((n,nd),(cxn,cx))) = APrf.get_result (Prf.get_aprf p) "h";
val z = Zipper.mktop (APrf.nd_get_trm nd);
(* apply fwd subst at zipper *)
val ((newi,(gs,p))::L) = 
    Seq.list_of (p |> Prf.apply_subst_fwd unatomise (z,"h"));

(* apply goal subst *)
val (r as ((n,nd),(cxn,cx))) = APrf.get_result (Prf.get_aprf p) "exIb";
val z = Zipper.mktop (APrf.nd_get_trm nd);
val z2 = z |> Zipper.move_down_right; (* go under Trueprop *)

val (((newg,gs),p)::L) = 
    Seq.list_of (p |> Prf.apply_subst_bck newi (z2,"exIb"));

val [(gs,p)] = 
  Seq.list_of (Prf.apply_resol_bck "exEf" "exIc" p);

writeln "DONE!!!";
