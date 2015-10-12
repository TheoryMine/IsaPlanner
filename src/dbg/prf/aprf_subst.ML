Trm.drop_var_args_flag := false;
context (theory "Main");
val thry = (theory "Main");
val p = Prf.init (the_context());
val t = 
    Prf.read_top_term 
      p "(!! z. g z = f z) ==> (EX x. f x) ==> (EX y. g y)";
val (g,p) = p |> Prf.conj_top_term "g" t;

(* backward proof method *)
val premeth_p = p;
val p = Prf.prep_bck_subprf "g" p;
val (exi_name, p) = p |> Prf.insert_thm (thm "exE");

val [(gs,p)] = Seq.list_of (Prf.apply_resol_bck exi_name "g" p);
val [(gs,p)] = Seq.list_of (Prf.apply_resol_bck "h" "exEd" p);
val (gs,p) = Prf.apply_bck_meth "g" ("exE",(K p)) premeth_p;

val exI_dtac = IsaDTac.Rule.rule_th (thm "exI");
val ((gs,p) :: L) = Seq.list_of (p |> Prf.apply_dtac exI_dtac "exEe");

val atomise_eq = thm "HOL.atomize_eq";
val symmetric = thm "ProtoPure.symmetric";
val unatomise_eq = 
    Thm.name_thm ("unatomise",
                  Drule.zero_var_indexes (atomise_eq RS symmetric));

val (unatomise, p) = p |> Prf.insert_thm unatomise_eq;

(* flexes *)
val flexes = Trm.mk_flexes (Prf.get_ffs p);

(* result and zipper *)
val (r as ((n,nd),(cxn,cx))) = APrf.get_result (Prf.get_aprf p) "i";
val z = Zipper.mktop (APrf.nd_get_trm nd);
(* apply fwd subst at zipper *)
val ((newi,(gs,p))::L) = 
    Seq.list_of (p |> Prf.apply_subst_fwd unatomise (z,"i"));

(* apply goal subst *)
val (r as ((n,nd),(cxn,cx))) = APrf.get_result (Prf.get_aprf p) "exEg";
val z = Zipper.mktop (APrf.nd_get_trm nd);
val z2 = z |> Zipper.move_down_right; (* go under Trueprop *)

val (((newg,gs),p)::L) = 
    Seq.list_of (p |> Prf.apply_subst_bck newi (z2,"exEg"));

val [(gs,p)] = 
  Seq.list_of (Prf.apply_resol_bck "exEf" "exEh" p);

writeln "DONE!!!";