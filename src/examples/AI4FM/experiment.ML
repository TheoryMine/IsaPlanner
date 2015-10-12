structure Experiment =
struct

(* Set assumptions according to Gudmund's schemes*)
val setmem = Thm.term_of @{cpat "Set.member :: X => (X => bool) => bool"};
val arrow = Const ("==>", @{typ"prop => prop => prop"})
val trueprop = Const ("HOL.Trueprop", @{typ "bool => prop"})
val forest = Const ("QRELind3.Forest", @{typ "(X \<times> X => bool) => bool"});
val roots = Const ("QRELind3.roots", @{typ "(X \<times> X => bool) => X => bool" });
val not = @{term "HOL.Not"};
val eq = Thm.term_of @{cpat "HOL.eq :: X => X => bool"};

(* Forest f ==> ... *)
fun set_forest_asm concl (forestnm, ftyp) =  
  arrow $ (trueprop $ (forest $ Free (forestnm, ftyp))) $ concl;

(* Forest f ==> r : roots f ==> ... *)
fun set_forest_roots_asm concl ((forestnm,ftyp), (elemnm, etyp)) = 
    arrow $ (trueprop $ (forest $ Free (forestnm, ftyp))) $
     (arrow $ (trueprop $ (setmem $ Free (elemnm, etyp) $ 
                                    (roots $ Free (forestnm,ftyp))))
            $ concl);

(* r : roots f ==> ... (asumes Forest f asm already set) *) 
fun set_root_asm concl ((forestnm,ftyp), (elemnm, etyp)) = 
    arrow $ (trueprop $ (setmem $ Free (elemnm, etyp) $ 
                                (roots $ Free (forestnm,ftyp))))
            $ concl;

(* Forest f ==> not (r : roots f) ==> ... *)    
fun set_forest_not_roots_asm concl ((forestnm,ftyp), (elemnm, etyp)) =
    arrow $ (trueprop $ (forest $ Free (forestnm, ftyp))) $
     (arrow $ (trueprop $ (not $ (setmem $ Free (elemnm, etyp) $ 
                                    (roots $ Free (forestnm,ftyp)))))
            $ concl);

(* not (r : roots f) ==> ... *)    
fun set_not_roots_asm concl ((forestnm,ftyp), (elemnm, etyp)) =
    arrow $ (trueprop $ (not $ (setmem $ Free (elemnm, etyp) $ 
                                    (roots $ Free (forestnm,ftyp)))))
            $ concl;

(* Forest f ==> r1 : roots f ==> r2 : roots f ==> r1 /= r2 ==> ... *)
fun set_forest_2roots_asm concl ((forestnm,ftyp), ((enm1, etyp1), (enm2,etyp2))) =
     arrow $ (trueprop $ (forest $ Free (forestnm, ftyp))) $
     (arrow $ (trueprop $ (setmem $ Free (enm1, etyp1) $ 
                                    (roots $ Free (forestnm,ftyp)))) $
      (arrow $ (trueprop $ (setmem $ Free (enm2, etyp2) $ 
                                    (roots $ Free (forestnm,ftyp)))) $
       (arrow $ (trueprop $ (not $ (eq $ Free (enm1, etyp1) $ Free (enm2, etyp2)))) 
              $ concl))) 

fun set_2roots_asm concl ((forestnm,ftyp), ((enm1, etyp1), (enm2,etyp2))) =
     arrow $ (trueprop $ (setmem $ Free (enm1, etyp1) $ 
                                    (roots $ Free (forestnm,ftyp)))) $
      (arrow $ (trueprop $ (setmem $ Free (enm2, etyp2) $ 
                                    (roots $ Free (forestnm,ftyp)))) $
       (arrow $ (trueprop $ (not $ (eq $ Free (enm1, etyp1) $ Free (enm2, etyp2)))) 
              $ concl))

fun all_pairs l1 l2 =
    case l1 of [] => []
             | h::t => (map (fn e => (h,e)) l2) @ (all_pairs t l2);

fun pairs_of_list l = 
    case l of [] => [] | [x] => [] | (h::t) => (all_pairs [h] t) @ (pairs_of_list t)

fun all_triples fs es = 
    all_pairs fs (pairs_of_list es)

(* Check if there are any free vars in conjecture that can be used in assumptions *)

(* Does the term contain f $$ x? Add asm Forest f; x notin roots f.*) 
fun contains_app t = 
    let
      fun matches_app t =  
          case t of 
            (Const("QRELind3.xapp", _) $ Free(forest,ftyp) $ Free(elem,etyp)) =>
            SOME((forest,ftyp),(elem,etyp))
          | _ => NONE;

      val asms = (Zipper.mktop t)
                 |> ZipperSearch.all_td_lr
                 |> Seq.map_filter (matches_app o Zipper.trm)
                 |> Seq.list_of;                 
    in
     if (null asms) then NONE 
     else SOME(List.foldl (fn (trm,a) => set_forest_not_roots_asm a trm) t asms)
    end;

(* does term contain root x f? Add asm Forest f*)
(*fun contains_root t = 
    let
      fun matches_root t =  
          case t of 
            (Const("QRELind3.root", _) $ Free(elem,etyp) $ Free(forest,ftyp)) =>
            SOME((forest,ftyp), (elem,etyp))
          | _ => NONE;

      val asms = (Zipper.mktop t)
                 |> ZipperSearch.all_td_lr
                 |> Seq.map_filter (matches_root o Zipper.trm)
                 |> Seq.list_of;   
      val forest_asms= List.foldl (fn (trm,  a) => set_forest_asm (fst a) trm) t asms 
      val root_asms = List.foldl (fn (trm, a) => set_forest_roots_asm a trm) t asms
    in
     if (null asms) then NONE 
     else SOME(forest_asms @ root_asms)
    end;
*)
(*
fun get_forest_frees t =
    let 
      fun subterm forest t = 
          case t of 
            Const("QRELind3.root", _) $ element $ forest => true | _ => false

      val forest_arg_typ = @{typ "xmap"};
      val forests = filter (fn (free,typ) => Trm.typ_name_eq forest_arg_typ typ)
                    (Trm.frees_of t);
      val (hard_fs, opt_fs) = List.partition 
                           (fn (free,typ) => Term.exists_subterm (subterm (Free (free,typ))) t) 
                           forests     
    in 
      case forests of [] => NONE | _ => SOME (t, hard_fs, opt_fs) 
    end;
*)
fun get_forest_and_elem_frees t =
	    let 
	      val forest_arg_typ = @{typ "xmap"};
	      val forests = filter (fn (free,typ) => Trm.typ_name_eq forest_arg_typ typ)
	                    (Trm.frees_of t) 
        val elem_typ =  @{typ "X"};
        val elems = filter (fn (free,typ) => Trm.typ_name_eq elem_typ typ)
                         (Trm.frees_of t)    
	    in 
	      case forests of [] => NONE | _ => SOME (t, forests, elems) 
	    end;

(* Assume all things that can be forests indeed are forests. *)
fun mk_forest_conjs (c, forests) = 
    List.foldl (fn (forest,trm) => set_forest_asm trm forest) c forests ;

fun mk_neg_roots_conj (c,forests,elems) = 
    let 
      val set_roots = map (set_not_roots_asm c) (all_pairs forests elems)
    in 
      map (fn c => List.foldl (fn (forest,trm) => set_forest_asm trm forest) c forests)
          set_roots
    end;

(* Filter out anything with f$$r first. *)
fun mk_roots_conjs (c,forests,elems) =   
    let 
      fun appsubterm t = 
          case t of 
            Const("QRELind3.xapp", _) $ Free(_,_) $ Free(_,_) => true | _ => false;
    in 
      if (Term.exists_subterm appsubterm c) 
      then NONE
      else
        let
          val set_roots = map (set_root_asm c) (all_pairs forests elems)
        in 
          SOME (map (fn c => (List.foldl (fn (forest,trm) => set_forest_asm trm forest) c forests)) set_roots)
        end
    end;

(* Filter out anything with f$$r *)
fun mk_two_roots_conjs (c,forests,elems) = 
    if (List.length elems <2) then NONE 
    else
      let 
      fun appsubterm t = 
          case t of 
            Const("QRELind3.xapp", _) $ Free(_,_) $ Free(_,_) => true | _ => false
      in 
        if (Term.exists_subterm appsubterm c) 
        then NONE
        else 
          let 
            val set_roots = map (set_2roots_asm c) (all_triples forests elems)
          in 
            SOME (map (fn c => List.foldl (fn (forest,trm) => set_forest_asm trm forest) c forests) set_roots)
        end
    end;

(* Also get the frees that are of element type (X) *)
(*fun get_elem_frees (t, hardfs, optfs) = 
    let
      fun subterm (forest, elem) t = 
          case t of 
            Const("QRELind3.xapp", _) $ forest $ elem => true | _ => false
      val elem_typ =  @{typ "X"};
      val elems = filter (fn (free,typ) => Trm.typ_name_eq elem_typ typ)
                         (Trm.frees_of t)
       val (opthard_pairs, optopt_pairs) = List.partition 
                           (fn ((f,ftyp), (e,etyp)) => 
                               Term.exists_subterm (subterm ((Free (f,ftyp)), (Free (e,etyp)))) t) 
                           (all_pairs opt_fs elems)
       val (hard_hardpairs, opt_hardpairs) = List.partition 
                           (fn ((f,ftyp), (e,etyp)) => 
                               Term.exists_subterm (subterm ((Free (f,ftyp)), (Free (e,etyp)))) t) 
                           (all_pairs hard_fs elems)
    in
      case elems of [] => NONE | _ => SOME(t, forests, elems) 
    end;
*)

(*
fun get_2_elem_frees (t, forests, elems) = 
    if (List.length elems >=2) then SOME (t, forests, elems) else NONE;

*)
end;
