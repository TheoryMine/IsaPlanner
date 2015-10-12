Trm.drop_var_args_flag := false;
val thry = (theory "Main");
val gctxt = (Context.Theory thry);
ML_Context.set_context (SOME gctxt);
val ctxt = (ProofContext.init thry);
val p = Prf.init ctxt;
val t = 
    Prf.read_top_term 
      p "(!! z1. g z1 = f z1) ==> (EX x y. f x y) ==> (EX x y. g x y)";
   (* unification: doesn't do eta-expansion for subst...
      p "(!! z1 z2. g z1 z2 = f z1 z2) ==> (EX x y. f x y) ==> (EX x y. g x y)"; *)
val (g,p) = p |> Prf.conj_top_term "g" t;

(* for metaeq use:  "symmetric" *)
val ((h2,p)::L) = 
    Seq.list_of (p |> Prf.apply_frule_thm (thm "sym") "h");

val th = (thm "sym");
val fname = "h";

val [((g2,gs),p)] = 
PolyML.exception_trace (fn () => Seq.list_of (Subst.apply "h" false "g" p));

val [((i2,gs),p)] = 
PolyML.exception_trace (fn () => Seq.list_of (Subst.apply h2 false "i" p));

val [(gs,p)] = 
PolyML.exception_trace (fn () => Seq.list_of (Prf.apply_resol_bck "i" "j" p));


writeln "DONE!!!";

(* 
val (r as ((n,nd),(cxn,cx))) = Prf.get_result p "g";
val z = Zipper.mktop (APrf.nd_get_trm nd);
val z2 = z |> Zipper.move_down_right (* go under Trueprop *)
           |> Zipper.move_down_right (* go right at EX *)
           |> Zipper.move_down_abs (* go under EX abs *)
           |> Zipper.move_down_right (* go right at EX *)
           |> Zipper.move_down_abs; (* go under EX abs *)

val (((newg,gs),p)::L) = 
    Seq.list_of (p |> Prf.apply_subst_bck "h" (z2,"g"));
*)
;;
