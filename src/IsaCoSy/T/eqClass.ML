structure EqClass =
struct

type SchematicTerm = {schema : Term.term, insts : Term.term Seq.seq};


(* This code is for instantiating a term putting Frees in place of Vars,
   but lazily. Most general comes first. *) 
datatype step =
         Finished of Term.term
       | Progress of Term.term Seq.seq;


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

(* All alternatives of instantiations, decreasing in generality. *)
fun inst_1var ctxt trm =
    let  
      fun inst_var_w_fresh (varnm,vtyp) t = 
          let
            val paramtab = Trm.params_of t
            val nw_nm = fst (Trm.TrmParams.add1 ("x", vtyp) paramtab) 
          in 
            inst_trm ctxt (varnm,vtyp) t (Free(nw_nm,vtyp))
          end;

      fun inst_var_w_existing (varnm,vtyp) t = 
          let 
            val frees = Seq.of_list (Trm.term_frees t)
          in
            Seq.maps (inst_trm ctxt (varnm, vtyp) t) frees
          end;
    in
      case (vars_lr trm) of
        [] => Finished trm
      | (var::_) =>
        Progress(Seq.append 
                   (inst_var_w_fresh var trm) 
                   (inst_var_w_existing var trm))
    end;
            
(* FIXME: If frees is [] this won't work, also wrong if there are more vars in the rhs than lhs.
   Probably want to pick the term with more vars as LHS. *)
fun inst_1var_rhs frees ctxt trm = 
    case (vars_lr trm) of
      [] => Finished trm
    | (var::_) =>
      Progress (Seq.maps (inst_trm ctxt var trm) (Seq.of_list frees));

fun inst_vars inst_fun ctxt trm_seq =
    let 
      fun recf ss () = 
          (case Seq.pull ss 
            of NONE => NONE
             | SOME (hs,ss2) => 
               (case inst_fun ctxt hs of 
                  Progress ss3 => recf (Seq.append ss3 ss2) ()
                | Finished hs2 => SOME (hs2, Seq.make (recf ss2))))
    in Seq.make (recf trm_seq) end;

fun mk_ground ctxt t = inst_vars (inst_1var) ctxt (Seq.single t);

fun mk_ground_rhs ctxt lhs rhs_schema = 
    let val frees = Trm.term_frees lhs
    in
      inst_vars (inst_1var_rhs frees) ctxt (Seq.single rhs_schema)
    end;


(* ----------------------------------------------- *)
(* For a schematic LHS and RHS, test the most general instantiations first. If an equation is found, stop
   without exploring more specific instantiations. *)

fun test1_rhs ctxt lhs rhs_seq = 
   case Seq.pull rhs_seq of 
     NONE => NONE
   | SOME (rhs,rhss) => 
     (let
        val eq = HOLogic.mk_eq(lhs,rhs)
      in  
        if (SynthPrfTools.counter_ex_check ctxt eq)
        then SOME eq
        else test1_rhs ctxt lhs rhss 
      end);

fun test1_lhs ctxt lhs_seq rhs_schema =
    case (Seq.pull lhs_seq) of
      NONE => NONE 
    | SOME (lhs,lhss) => 
      let 
        (* val rhs_seq = mk_ground_rhs ctxt lhs rhs_schema *)
        val rhs_seq = mk_ground ctxt rhs_schema
      in
        (case (test1_rhs ctxt lhs rhs_seq) of
           NONE => test1_lhs ctxt lhss rhs_schema
         | SOME eq => SOME eq)
      end; 

 
(* THINK: Now we test one LHS inst against all insts of the first RHS before proceeding to the next one. 
          Would be better doing it breadth first, i.e. try most general instace of all terms first, then next
          and so on, hopefully never having to try against the very specific ones. *)
fun test_if_eq ctxt (t1, t2) = 
    if (Type.could_unify ((Term.type_of t1), (Term.type_of t2)))
    then
      let 
         val lhs_seq = mk_ground ctxt t1
      in
        test1_lhs ctxt lhs_seq t2
      end
    else NONE;


(* ---------------------------------------------------------------- *)
fun test_rhs_comm ctxt lhs rhs_seq = 
    case Seq.pull rhs_seq of 
      NONE => NONE
    | SOME (rhs,rhss) => 
      if (Trm.trm_name_eq lhs rhs) then (* Avoid testing this instantiation with itself *)
        test_rhs_comm ctxt lhs rhss
      else
        let
          val eq = HOLogic.mk_eq(lhs,rhs)
        in  
          if (SynthPrfTools.counter_ex_check ctxt eq)
          then SOME eq
          else test_rhs_comm ctxt lhs rhss 
        end;

fun test_lhs_comm ctxt lhs_seq rhs_schema = 
    case (Seq.pull lhs_seq) of
        NONE => NONE 
      | SOME (lhs,lhss) => 
        let 
          (* val rhs_seq = mk_ground_rhs ctxt lhs rhs_schema *)
          val rhs_seq = mk_ground_rhs ctxt lhs rhs_schema
        in
          case (test_rhs_comm ctxt lhs rhs_seq) of
            NONE => test_lhs_comm ctxt lhs_seq rhs_schema
          | SOME eq => SOME eq
        end;

fun test_if_commutative ctxt t = 
    if ((List.length (Trm.vars_of t)) < 2) 
    then NONE
    else test_lhs_comm ctxt (mk_ground ctxt t) t;
 
(* ---------------------------------------------------------------- *)

(* Here one should have the terms in some sort of better datastructure, so it's a given order in which
the terms are tried as LHSides, right now the list of remaining terms is reversed at each iteration! *) 
fun split_aux _ _ [] (eqs, other_ts) = (eqs, other_ts)
  | split_aux ctxt t1 (t2::ts) (eqs, other_ts) =
      case (test_if_eq ctxt (t1,t2)) of
        SOME eq => (eq::eqs, other_ts @ ts) (* split_aux ctxt t1 ts (eq::eqs, other_ts) *)(* Do we really want to continue testing here?*)
      | NONE => split_aux ctxt t1 ts (eqs, other_ts @ [t2]);
             
(*
fun mk_schemes ctxt t = {schema = t, insts = mk_ground ctxt t}  
*)
fun try_mk_eqs _ [] (eqs, remaining) = (eqs, remaining) (* remaining are the terms not in any equation *)
  | try_mk_eqs ctxt ts (eqs, remaining) = 
    let 
      fun var_order (t1,t2) = Library.rev_order 
                                (Library.int_ord (List.length (Trm.vars_of t1), 
                                                  List.length(Trm.vars_of t2)));

      (* val schemes = map mk_schemes (Library.sort var_order ts) *)
      val (t1::ts) = Library.sort var_order ts
      (*val lhs_seq = mk_ground ctxt t1 *)
      val (nw_eqs, rem) = split_aux ctxt t1 ts ([],[]) 
    in
      if (null nw_eqs) then
         (* If we found no equation, perhaps we can test the schematic term against
           another instantiation of itself to create a commutativity theorem. *)
        case (test_if_commutative ctxt t1) of
           SOME eq => try_mk_eqs ctxt rem ((eq::eqs), remaining)
         | NONE => try_mk_eqs ctxt rem (eqs, remaining @ [t1])
      else
        try_mk_eqs ctxt rem ((nw_eqs @ eqs), remaining)
    end;


end;
