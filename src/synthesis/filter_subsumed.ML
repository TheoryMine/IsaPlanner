(* ------------------------------------------------------- *)
(* Subsumption check and related functions *)
(* ------------------------------------------------------- *)
signature FILTER_SUBSUMED =
sig
  type T (* subsumption net data *)
  structure Ctxt : PROOF_DATA
  
  (* check and add term, checks for commutativity w.r.t. = *)
  val is_subsumed : term -> Proof.context 
      -> (Proof.context (* new context, (subsumption net maybe updated with this term) *)
          * term option (* optionally, term that subsumed this one *))
end;


structure DB_FilterSubsumed =
struct
  
  datatype T = SubNetData of {sub_net : SubsumptionNet.T};
  fun init thy = SubNetData{sub_net = SubsumptionNet.empty};
  fun get_snet (SubNetData rep) = #sub_net rep;
  fun update_snet f (SubNetData rep) = SubNetData{sub_net = f (#sub_net rep)}
  
  val set_snet = update_snet o K;
  
  structure Ctxt = Proof_Data(type T = T val init = init)
  
  fun add_term t ctxt = 
      let 
        val snet = SubsumptionNet.add_term ctxt t (get_snet (Ctxt.get ctxt))
      in Ctxt.map (set_snet snet) ctxt end;

  (* Strictly speaking I suppose we should check if something matching t is in the list,
     *)
  fun in_snet ctxt t = 
      not (List.null (Net.lookup (get_snet (Ctxt.get ctxt)) (Net.key_of_term t)));
   
  fun equal_size_eq z =
      let 
        fun size_of_trm t =
            case t of 
              t1$t2 => (size_of_trm t1) + (size_of_trm t2)
            | Term.Abs(a,ty,body) => 1 + size_of_trm body
            | _ => 1
      in
         size_of_trm (Zipper.trm (Subst.move_to_lhs_of_eq z)) = 
         size_of_trm (Zipper.trm (Subst.move_to_rhs_of_eq z))
      end
      (* if it isn't an equation *)
      handle Subst.LData.bad_term_exp _ => false;
  
  (* Commutes the arguments if this is an equation *)
  fun swap_eq z =
      case Zipper.trm z of
        (Const("HOL.eq",ty)$arg1$arg2) =>
         Const("HOL.eq",ty)$arg2$arg1
      | t => t; 
  

  fun check (conjs,thrms) ctxt =
      let 
        val nw_ctxt = fold (fn (_,thm) => fn ctxt => add_term (Thm.prop_of thm) ctxt) thrms ctxt
        val thrms' = filter (fn (_,thm) => in_snet nw_ctxt (Thm.prop_of thm)) thrms

        (* Don't let conjectures subsume theorems, so do them after *)
        val nw_ctxt2 = fold add_term conjs nw_ctxt
        val conjs' = filter (in_snet nw_ctxt2) conjs
      in
        (nw_ctxt2, (conjs', thrms'))
      end;
  (* Simple subsumption check *)
(*  fun is_subsumed trm ctxt = 
      let val (not_subsumed, nw_ctxt) = add_term trm ctxt
      in 
        if not_subsumed 
        then 
          let val z = Zipper.mktop(trm)
          in (* Check if a commuted version of this term has been seen.
              This should be done in OLD context otherwise for instace
              commutativity subsumes itself!*)
            if (equal_size_eq z)
            then
              let val (not_subs2, nw_ctxt2) = add_term (swap_eq z) ctxt
              in 
                if not_subs2 then (nw_ctxt, SOME trm) else (nw_ctxt2, NONE) end
            else (nw_ctxt, SOME trm)
          end
        else (nw_ctxt, NONE) (*val _ = subsumpt_counter := !subsumpt_counter +1 *)
      end;
  *)
end; (* struct *)

structure FilterSubsumed  = DB_FilterSubsumed;

(* ------------------------------------------------------- *)


  
  (*
  fun filter_subsumed trms subst_net =
      let 
        (* val timer = Timer.startCPUTimer () *)
        val result = 
          List.foldl (fn (trm, (snet, unsubsumed)) => 
                    let 
                      val (not_subsumed, nw_snet) = 
                          SubsumptionNet.add_term (fst trm) snet
                    in 
                      if not_subsumed 
                      then 
                        let val z = Zipper.mktop(fst trm)
                        in
                        (* Check if a commuted version of this term has been seen *)
                          if (equal_size_eq z)
                          then
                            let val (not_subs2, nw_snet2) =
                                    SubsumptionNet.add_term (swap_eq z) snet
                            in 
                              if not_subs2
                              then (nw_snet2, (unsubsumed @ [trm]))
                              else (nw_snet2, unsubsumed)
                            end
                          else
                          (nw_snet, (unsubsumed @ [trm]))
                        end
                      else 
                        let 
                          val _ = subsumpt_counter := !subsumpt_counter +1
                        in (nw_snet, unsubsumed) end
                    end) 
                (subst_net, []) trms
       (* val _ = subsumpt_time := !subsumpt_time + (#usr (Timer.checkCPUTimer timer)) *)
      in result end;
  *)
