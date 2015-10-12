(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_measure_tabs.ML
    Author:     Dominic Mulligan, University of Edinburgh
                dpm_edinburgh@yahoo.com
    Created:    3 Sept, 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Tables for calculating a measure.  Most are composite (i.e. their
    value types are other tables).  Placed in one file for easier
    loading.

*) 
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature MODALITY_INFO =
  sig
    type GoalModeInfo;
    val empty : GoalModeInfo;
    val goal_mode_info_i : GoalModeInfo -> int -> GoalModeInfo
    val update : GoalModeInfo -> RRipplingATerms.T -> RRipplingATerms.T -> GoalModeInfo option
    val pretty : GoalModeInfo -> Pretty.T;
    val pretty_gmis : (string * GoalModeInfo) list -> Pretty.T;
    val print : GoalModeInfo -> unit;
    val print_gmis : (string * GoalModeInfo) list -> unit;
  end;
                                
structure ModalityInfo : MODALITY_INFO =
  struct

    (* goalname * position table * type table *)
    type GoalModeInfo = (((RREmbeddingLib.PO Inttab.table) Inttab.table) * (RRipplingATerms.WT list Inttab.table))

    val empty = (Inttab.empty, Inttab.empty);

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (* Relational Rippling Modality Info Tables
       
       goal_mode_info_i: initialises goal modality information.  Second
       parameter is the number of arguments the particular relation, to
       which the gmi corresponds, has (i.e. r a b == 3, succ x y == 2).
       GoalModeInfo -> Int -> GoalModeInfo

       update: takes two aterms - one from before a rewrite, and one from
       after.  If the rewrite is allowed, the tables also supplied are
       updated with the new information.  Otherwise, returns NONE.
       Important that we always respect prior choices - when we allow a
       rewrite, we agree to be bound by the choices made in that rewrite
       for the rest of the rippling process.
       GoalModeInfo -> ATerm -> ATerm -> GoalModeInfo
    *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

    fun goal_mode_info_i gmi num_args =
      let
        fun aux_pos table 0 = table
          | aux_pos table n =
              let
                fun aux table 0 = (Inttab.update (0, RREmbeddingLib.UNDEF) table)
                  | aux table n = aux (Inttab.update (n-1, RREmbeddingLib.UNDEF) table) (n-1)
              in
                aux_pos (Inttab.update (n-1, aux Inttab.empty num_args) table) (n - 1)
              end

        fun aux_typ table 0 = table
          | aux_typ table n =
              aux_typ (Inttab.update (n-1, []) table) (n - 1)
      in
        (aux_pos Inttab.empty num_args, aux_typ Inttab.empty num_args)
      end

    (* Marks all positions in a pair of lists where differences exist between them. *)
    fun differences_at l1 l2 =
      let
        fun aux [] _ _ = []
          | aux _ [] _ = []
          | aux (h1::t1) (h2::t2) n =
              if h1 = h2 then
                aux t1 t2 (n+1)
              else
                (n, h1, h2)::(aux t1 t2 (n+1))
      in
        aux l1 l2 0
      end

    (* The tables are constructed dynamically.  Any decisions we make now, we agree to be
       bound by later on.  For this reason, we need to check whether an update is allowed
       before updating the tables.  If no current record exists, then the update is allowed.
       If a current record exists, and it is compatible with our intended update (i.e. we
       know that WFNone < WFRel and we wish to add that WFFunc < WFNone, then this should
       be added.  If the update is incompatible, then we return NONE.
    *)
    (* TODO: this is pretty inefficient - some of the lists are traversed three or four
       times for slightly different information.  This can probably be sped up significantly,
       although we'll leave it for now.
    *)
    fun update_typ typ [] = SOME(typ)
      | update_typ typ ((n, from, to)::t) =
          let
            val lookup = Inttab.lookup typ n
          in
            case lookup of
              NONE =>
                update_typ (Inttab.update (n, [from, to]) typ) t
            | SOME(lst) =>
                (case lst of
                   [] => update_typ (Inttab.update (n, [from, to]) typ) t
                 | lst =>
                     let
                       fun member l i = List.exists (fn x => x=i) l;

                       fun at l i =
                         let
                           fun aux [] _ _ = NONE
                             | aux (h::t) item index =
                                 if h=item then SOME(index)
                                 else aux t item (index+1)
                         in
                           aux l i 0
                         end;

                       fun is_known l from to =
                         let
                           val pos_from = at l from
                           val pos_to = at l to
                         in
                           case pos_from of
                             NONE =>
                               (case pos_to of
                                  NONE => false
                                | SOME(x) => false)
                           | SOME(x) =>
                               (case pos_to of
                                  NONE => false
                                | SOME(y) =>
                                    if x<y then true else false)
                         end;

                       fun is_compatible l from to =
                         let
                           val pos_from = at l from
                           val pos_to = at l to
                         in
                           case pos_from of
                             NONE =>
                               (case pos_to of
                                  NONE => true
                                | SOME(to') => true)
                           | SOME(from') =>
                               (case pos_to of
                                  NONE =>
                                    if (from' + 1) < length l then
                                      false
                                    else
                                      true
                                | SOME(to') =>
                                    if from' < to' then
                                      true
                                    else
                                      false)                               
                         end

                       (* Assumes compatibility of addition.  Fails gracefully?? *)
                       fun add_typ_info [] from to = [from, to]
                         | add_typ_info (h::t) from to =
                             if h=from then
                               (h::to::t)
                             else if h=to then
                               (from::to::t)
                             else h::(add_typ_info t from to)
                     in
                       if is_known lst from to then
                         update_typ typ t
                       else
                         if is_compatible lst from to then
                           update_typ (Inttab.update (n, add_typ_info lst from to) typ) t
                         else
                           NONE
                     end)
          end

    (* If a wave-front ``evaporates" in one argument position, but another appears in a
       differing position, we say that the evaporated position is more important than the
       second position.  We need to keep track of this data in the tables.
    *)
    (* TODO: this is pretty inefficient - some of the lists are traversed three or four
       times for slightly different information.  This can probably be sped up significantly,
       although we'll leave it for now.
    *)
    fun update_pos pos _ [] = SOME(pos)
      | update_pos pos [] _ = SOME(pos)
      | update_pos pos (h::t) dis =
          let
            fun is_defined pos l r =
              let
                val lookupr = Inttab.lookup pos r
                val lookupl = Inttab.lookup pos l
              in
                case lookupr of
                  NONE =>
                    (case lookupl of
                      NONE => false
                    | SOME(ltab) =>
                        let
                          val lookupr' = Inttab.lookup ltab r
                        in
                          case lookupr' of
                            NONE => false
                          | _ => true
                        end)
                | SOME(rtab) =>
                    let
                      val lookupl' = Inttab.lookup rtab l
                    in
                      (case lookupl' of
                        NONE => false
                      | SOME(x) =>
                          (case x of
                            RREmbeddingLib.UNDEF => false
                          | _ => true))
                    end
              end

            (* Assumes compatibility, I think.  Should fail gracefully without, though! *)
            fun get_definition pos l r =
              let
                val lookupr = Inttab.lookup pos r
                val lookupl = Inttab.lookup pos l
              in
                case lookupr of
                  NONE =>
                    (case lookupl of
                      NONE => NONE
                    | SOME(ltab) =>
                        let
                          val lookupr' = Inttab.lookup ltab r
                        in
        lookupr'
                        end)
                | SOME(rtab) =>
                    let
                      val lookupl' = Inttab.lookup rtab l
                    in
          lookupl'
                    end
              end

            fun is_compatible elem h def =
              case def of
                RREmbeddingLib.LT => (elem < h)
              | RREmbeddingLib.GT => (elem > h)
              | _ => true

            fun aux pos elem [] = SOME(pos)
              | aux pos elem (h::t) =
                  if is_defined pos elem h then
                    let
                      val def = get_definition pos elem h
                    in
                      case def of
                        NONE => (* shouldn't happen *) NONE
                      | SOME(x) =>
                          let
                            val compatibility = is_compatible elem h x
                          in
                            if compatibility then
                              aux pos elem t
                            else
                              NONE
                          end
        end
                  else
                    if elem < h then
                      let
                        val lookup = Inttab.lookup pos elem
                      in
                        case lookup of
                          NONE =>
                            let
                              val pos' = Inttab.update (elem, Inttab.update (h, RREmbeddingLib.LT) Inttab.empty) pos
                            in
                              aux pos' elem t
                            end
                        | SOME(rtab) =>
                            (* we know that it isn't defined, so the only value that this could be
                               is UNDEF!
                            *)
                            let
            val pos' = Inttab.update (elem, Inttab.update (h, RREmbeddingLib.GT) rtab) pos
                            in
                              aux pos' elem t
                            end
                      end
        else
                      let
                        val lookup = Inttab.lookup pos elem
                      in
                        case lookup of
                          NONE =>
                            let
                              val pos' = Inttab.update (elem, Inttab.update (h, RREmbeddingLib.GT) Inttab.empty) pos
                            in
                              aux pos' elem t
                            end
                        | SOME(rtab) =>
                            (* we know that it isn't defined, so the only value that this could be
                               is UNDEF!
                            *)
                            let
            val pos' = Inttab.update (elem, Inttab.update (h, RREmbeddingLib.GT) rtab) pos
                            in
                              aux pos' elem t
                            end
                      end
            val pos' = aux pos h dis
          in
            case pos' of
              NONE => NONE
            | SOME(p) => update_pos p t dis
          end 

    fun update (gmi as (pos, typ)) prev_atrm new_atrm =
      let
        val comb_prev = RRTrmUtil.combinator_name (RRipplingATerms.inst_skel_term prev_atrm)
        val comb_new = RRTrmUtil.combinator_name (RRipplingATerms.inst_skel_term new_atrm)
        val num_args_prev = RRipplingATerms.num_args prev_atrm
        val num_args_new = RRipplingATerms.num_args new_atrm
      in
        if comb_prev = comb_new then
          if num_args_prev = num_args_new then
            let
              val wf_pos_prev = RRipplingATerms.wave_fronts_at prev_atrm
              val wf_pos_new = RRipplingATerms.wave_fronts_at new_atrm
              val wf_movements = differences_at wf_pos_prev wf_pos_new
      in
        case wf_movements of
    [] => SOME(pos,typ)
        | _ =>
    let
      val typ' = update_typ typ wf_movements
    in
      case typ' of
                    NONE => NONE
      | SOME(t) =>
                    let
                      val app = map (fn(x,y,z) => x) (List.filter (fn(x,y,z) => y=RRipplingATerms.WFNone) wf_movements)
                      val dis = map (fn(x,y,z) => x) (List.filter (fn(x,y,z) => z=RRipplingATerms.WFNone) wf_movements)
                      val pos' = update_pos pos app dis
                    in
                      case pos' of
      NONE => NONE
                      | SOME(p) => SOME(p, t)
                    end
    end
      end
          else
            NONE
        else
          NONE
      end

    val pretty_int = (Pretty.str o Int.toString)

    fun pretty_pos_tab pt =
      let
        fun pretty_po_inttab poi =
          let
            fun pretty_po p =
              case p of
                RREmbeddingLib.LT => (Pretty.str "LT")
              | RREmbeddingLib.GT => (Pretty.str "GT")
              | RREmbeddingLib.UNDEF => (Pretty.str "UNDEF")

            fun pretty_record r = 
              Pretty.list "(" ")" [(pretty_int o fst) r, (pretty_po o snd) r]
          in          
            Pretty.list "[" "]" (map pretty_record (Inttab.dest poi))
          end

        fun pretty_record r =
          Pretty.list "(" ")" [(pretty_int o fst) r, (pretty_po_inttab o snd) r]
      in
        Pretty.list "[" "]" ((map pretty_record) (Inttab.dest pt))
      end

    fun pretty_typ_tab tt =
      let
        fun pretty_wf w =
          case w of
            RRipplingATerms.WFFunc => (Pretty.str "WFFunc")
          | RRipplingATerms.WFNone => (Pretty.str "WFNone")
          | RRipplingATerms.WFRel(x) => (Pretty.str ("WFRel <" ^ (Int.toString x) ^ ">"))

        fun pretty_record r =
          Pretty.list "(" ")" [pretty_int (fst r), Pretty.list "[" "]" (map pretty_wf (snd r))];
      in
        Pretty.list "[" "]" (map pretty_record (Inttab.dest tt))
      end

    fun pretty gmi =
      Pretty.list "{" "}" [(pretty_pos_tab o fst) gmi, (pretty_typ_tab o snd) gmi]

    fun pretty_gmis g =
      let
        fun pretty_record r =
          Pretty.list "(" ")" [(Pretty.str o fst) r, (pretty o snd) r]
      in
        Pretty.list "[" "]" (map pretty_record g)
      end

    val print = Pretty.writeln o pretty;

    val print_gmis = Pretty.writeln o pretty_gmis;

  end;

(*
(* Unit testing... *)
(* use_thy "~/Project/Proofs/Relations2"; *)
val atrm_to_str = (Pretty.string_of o (RRipplingATerms.pretty (the_context ())));
val pp = Prf.init (the_context ());
val expr_1 = Prf.read_top_term pp "(a::nat) (b::'a) c \<in> r***";
val expr_2 = Prf.read_top_term pp "r (b::'a) (d::'a)";
val expr_3 = Prf.read_top_term pp "r (d::'a) (e::'a)";
val expr_4 = Prf.read_top_term pp "(a::nat) (e::'a) c \<in> r***";
val expr_5 = Prf.read_top_term pp "(a::nat) (d::'a) c \<in> r***";
val expr_6 = Prf.read_top_term pp "r (e::'a) (f::'a)";
val expr_7 = Prf.read_top_term pp "(a::nat) (f::'a) c \<in> r***";
val expr_8 = Prf.read_top_term pp "(a::nat) (b::'a) (e::'a) \<in> r***";
val expr_9 = Prf.read_top_term pp "r (c::'a) (d::'a)";
val rtab = RRippleCInfo.add_relational_link RelationTab.empty expr_2 "expr_2";
val rtab = RRippleCInfo.add_relational_link rtab expr_3 "expr_3";
val rtab = RRippleCInfo.add_relational_link rtab expr_6 "expr_6";
val rtab = RRippleCInfo.add_relational_link rtab expr_9 "expr_9";
val mode_r = ModalityInfo.goal_mode_info_i ModalityInfo.empty 4;
val instenv = InstEnv.init (the_context ());
val [embed1] = Seq.list_of (RREmbeddingLib.embed rtab instenv expr_1 expr_4);
val [embed2] = Seq.list_of (RREmbeddingLib.embed rtab instenv expr_1 expr_1);
val [embed3] = Seq.list_of (RREmbeddingLib.embed rtab instenv expr_1 expr_5);
val [embed4] = Seq.list_of (RREmbeddingLib.embed rtab instenv expr_1 expr_7);
val [embed5] = Seq.list_of (RREmbeddingLib.embed rtab instenv expr_4 expr_8);
val [raem1] = RRipplingATerms.r_aterms_of_eterm (snd embed1);
val [raem2] = RRipplingATerms.r_aterms_of_eterm (snd embed2);
val [raem3] = RRipplingATerms.r_aterms_of_eterm (snd embed3);
val [raem4] = RRipplingATerms.r_aterms_of_eterm (snd embed4);
val [raem5] = RRipplingATerms.r_aterms_of_eterm (snd embed5);
val SOME(mode_r) = ModalityInfo.update mode_r raem1 raem5;
val SOME(mode_r) = ModalityInfo.update mode_r raem1 raem2;
val d1 = (Inttab.dest o snd) mode_r;
val SOME(mode_r) = ModalityInfo.update mode_r raem2 raem3;
val d2 = (Inttab.dest o snd) mode_r;
ModalityInfo.update mode_r raem2 raem4;
*)
