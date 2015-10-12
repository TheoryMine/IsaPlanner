
(* instantiate theorems to not have any arguments *)
fun drop_thm_var_args th = 
    let 
      val ffs = map Logic.mk_equals (Thm.tpairs_of th);
      val prop = Thm.prop_of th;
      val fullt = Logic.list_implies (ffs,prop);
      val vtab = BasicTrm.vtab_of fullt;
      val vars = BasicTrm.Var.NTab.list_of (snd vtab);
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
    in 
      fold (fn (n,ty) => 
               (case ty 
                 of Type _ => 
                    let 
                      val (argtyps, desttype) = strip_type ty
                      val inst = 
                          ctermify 
                            (Term.list_abs (map (pair "") argtyps,
                                           Var(n,desttype)))
                    in
                      Thm.instantiate 
                        ([], [(ctermify (Var (n,ty)),
                               inst)])
                    end
                  | _ => I))
           vars
           th 
    end;

fun drop_trm_var_args t = 
    let 
      val vtab = BasicTrm.vtab_of t;
      val vars = BasicTrm.Var.NTab.list_of (snd vtab);
    in 
      fold (fn (n,ty) => 
               (case ty 
                 of Type _ => 
                    let 
                      val (argtyps, desttype) = strip_type ty
                      val inst = 
                          (Term.list_abs (map (pair "") argtyps,
                                          Var(n,desttype)))
                    in
                      Term.instantiate ([], [((n,ty),inst)])
                    end
                  | _ => I))
           vars
           t 
    end;

fun pretty_thm_minimal_vars th0 =
    let val th = drop_thm_var_args th0 in
      (* If we are before CPure then use basic printing: no abbrevs *)
      if (List.length (Theory.ancestors_of (Thm.theory_of_thm th)) < 4) then 
        Display.pretty_thm th
      else 
        ProofContext.pretty_thm (ProofContext.init (Thm.theory_of_thm th)) th
    end;

fun pretty_thm th =
      (* If we are before CPure then use basic printing: no abbrevs *)
      if (List.length (Theory.ancestors_of (Thm.theory_of_thm th)) < 4) then 
        Display.pretty_thm th
      else 
        ProofContext.pretty_thm (ProofContext.init (Thm.theory_of_thm th)) th;

val pprint_thm = Pretty.pprint o pretty_thm;
install_pp (make_pp ["Thm", "thm"] pprint_thm);

