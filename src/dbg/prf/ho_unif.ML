Trm.drop_var_args_flag := false;
ML_Context.set_context (SOME (Context.Theory (theory "Main")));
val thry = (theory "Main");
val p0 = Prf.init (the_context());
val t = 
    Prf.read_top_term 
      p0 "!! h l t. rev((rev t) @ [h] @ l) = ?F1 ((?F2 (rev (l :: 'a list)) h l t :: 'a list ) @ (t:: 'a list)) h l t";

val (g,p) = p0 |> Prf.conj_top_term "g" t;

val wr = 
    Prf.read_top_term 
      p "!! x xs. (rev xs) @ [x] == rev (x # xs)";

val (rev_def,p) = p |> Prf.conj_top_term "rev_def" wr;


val ((wr_name, sgs),p) = Prf.lift_and_show_above rev_def [] g p;

val cx = Prf.get_ndname_cx p g;
val fixes = Cx.get_fixed_trm_ps cx;

val gz = (Prf.get_ndname_ctrm p g) 
           |> Zipper.mktop           
           |> Subst.move_to_rhs_of_eq
           |> Zipper.move_down_left
           |> Zipper.move_down_left
           |> Zipper.move_down_left
           |> Zipper.move_down_right
           |> Zipper.move_down_left
           |> Zipper.move_down_right
           |> Zipper.move_down_left
           |> Zipper.move_down_left
           |> Zipper.move_down_left
           |> Zipper.move_down_right
           |> Zipper.move_down_left;

val rz = (Prf.get_ndname_ctrm p wr_name) 
           |> Zipper.mktop
           |> Subst.move_to_lhs_of_eq
           |> Zipper.trm |> Zipper.mktop 
           |> Zipper.move_down_left
           |> Zipper.move_down_right
           |> Zipper.move_down_left

val ppl = p;


val SOME(app_zip,p) = MiddleOutRW.inst_for_partwrule ppl rz gz;


Seq.list_of (Prf.apply_subst wr_name g app_zip p);

raise ERROR "done!";




val t2 = 
    Prf.read_top_term 
      p "!! h l. Suc(length (l @ (h#l))) = ?F1 (length ((?F2 ((l :: 'a list) @ l) h l) :: 'a list)) h l ";

val (g2,p2) = p0 |> Prf.conj_top_term "g2" t2;

val wr2 = 
    Prf.read_top_term 
      p2 "!! x xs. length (x # xs) == Suc(length (xs :: 'a list)) ";

val (len_def,p2) = p2 |> Prf.conj_top_term "len_def" wr2;


val ((wr_name2, sgs2),p2) = Prf.lift_and_show_above rev_def [] g2 p2;


val gz2 = (Prf.get_ndname_ctrm p2 g2) 
           |> Zipper.mktop           
           |> Subst.move_to_rhs_of_eq
           |> Zipper.move_down_left 
           |> Zipper.move_down_left 
           |> Zipper.move_down_right
           |> Zipper.move_down_left ;

 
  
    
val rz2 = (Prf.get_ndname_ctrm p2 wr_name2) 
           |> Zipper.mktop
           |> Subst.move_to_lhs_of_eq
           |> Zipper.trm |> Zipper.mktop
           |> Zipper.move_down_left;

val ppl = p2;

val SOME(app_zip,p2) = inst_for_partwrule ppl rz2 gz2;
Seq.list_of (Prf.apply_subst wr_name2 g2 app_zip p2);

(* backward proof method *)
val premeth_p = p;
val p = Prf.start_meth ["g"] p;
val (exi_name, p) = p |> Prf.insert_thm (thm "exE");
val [(gs,p)] = Seq.list_of (Prf.apply_resol_bck exi_name "g" p);
val [(gs,p)] = Seq.list_of (Prf.apply_resol_bck "i" "exEd" p);
val (gs,p) = Prf.end_meth ("exE with:" ^ "i") [] ["g"] p premeth_p;

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
val (((newi,gs),p)::L) = 
    p |> Prf.apply_subst unatomise "h" z 
      |> Seq.list_of;

(* apply goal subst *)
val (r as ((n,nd),(cxn,cx))) = APrf.get_result (Prf.get_aprf p) "exIb";
val z = Zipper.mktop (APrf.nd_get_trm nd);
val z2 = z |> Zipper.move_down_right; (* go under Trueprop *)

val (((newg,gs),p)::L) = 
    p |> Prf.apply_subst newi "exIb" z2
      |> Seq.list_of;

val [(gs,p)] = 
  Seq.list_of (Prf.apply_resol_bck "exEf" "exIc" p);

writeln "DONE!!!";
