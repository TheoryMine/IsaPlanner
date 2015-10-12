structure MkEquation =
struct


type SchematicTerm = {schema : Term.term, insts : Term.term Seq.seq};

type EqClass = {rep : Term.term, (* Representative, e.g schematic term with fewest vars *)
                trms : Term.term list, (* Other schematic terms in this class *)
                eqs : Term.term list} (* Ground equations which were tested *)

(* ------------------------------------------------------------------*)
fun inst_trm ctxt var t inst = 
    let 
      val ienv = InstEnv.of_trm ctxt t;
    in 
      (MyUnify.unifiers (ienv, [(Trm.mk_var var, inst)]))
        |> Seq.map (fn ienv' => InstEnv.inst_trm ienv' t)
    end;

(* Variables of t in left-to-right order *)
fun vars_lr t = 
    (ZipperSearch.leaves_lr (Zipper.mktop t))
      |> Seq.map_filter (Trm.opt_dest_var o Zipper.trm)
      |> Seq.list_of;         

fun inst_var_w_fresh ctxt (varnm,vtyp) t = 
          let
            val paramtab = Trm.params_of t
            val nw_nm = fst (Trm.TrmParams.add1 ("x", vtyp) paramtab) 
          in 
            inst_trm ctxt (varnm,vtyp) t (Free(nw_nm,vtyp))
          end;

fun inst ctxt max_vars trm = 
    case (vars_lr trm) of
      [] => trm
    | (v::_) => inst ctxt max_vars (inst_var_w_fresh var trm);

(* ------------------------------------------------------------------*)

(* eq_c is the class we're currently testing against *)
fun test1 ctxt other_eq_class (rem, eq_c) =
    let
      val t1 = hd eq_c
      val t2 = hd other_eq_class 
    in
      if (Type.could_unify ((Term.type_of t1), (Term.type_of t2)))
      then
        let
          val eq = HOLogic.mk_eq(t1,t2)
        in  
          if (SynthPrfTools.counter_ex_check ctxt eq)
          then (rem, eq_c @ other_eq_class)
          else (other_eq_class::rem, eq_c)
      else (other_eq_class::rem, eq_c)
    end;

fun test (classes, tested) = 
    case classes of 
      [] => tested
    | (eq_c::eqcs) =>  
      let
        val (rem, nw_eq_c) = fold test1 eqcs ([],eq_c)
      in
        test (rem, nw_eq_c::tested)
      end;

(* Try to find equations, give the term schemas. Note: only tries terms where all vars different. *)
fun mk_eqs ctxt max_vars schematic_trms = 
    let 
      val most_gen_insts = inst_vars ctxt max_vars schematic_trms
      val eq_classes = map (fn t => [t]) most_gen_insts;
    in
      test (eq_classes, [])
    end;

end;
