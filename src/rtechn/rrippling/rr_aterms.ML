(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ripple_aterms.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Modified:   Dominic Mulligan, University of Edinburgh
                dpm_edinburgh@yahoo.com
    Created:    24 Feb 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Our Annotated terms for relational rippling.  Based on the functional
    version.
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RRIPPLE_ATERMS =
sig

    type annot
    type T

    datatype WT = WFFunc | WFRel of int | WFNone;

    (* restricted and unrestricted aterms from and eterm *)
    (* These allows adjacent wave fronts with differing directions *)
    val r_aterms_of_eterm : RREmbeddingLib.eterm -> T list
    val u_aterms_of_eterm : RREmbeddingLib.eterm -> T list

    val num_args: T -> int

    (* These disallows adjacent wave fronts with differing directions: *)
    (* They require that adjacent wave fronts have the same direction *)
    val cr_aterms_of_eterm : RREmbeddingLib.eterm -> T list
    val cu_aterms_of_eterm : RREmbeddingLib.eterm -> T list
                                                     
    val fo_measure_of : T -> int list * int list
    val ho_measure_of : T -> int list * int list
    val undirected_measure_of : T -> int list
    val dsum_measure_of : T -> int
    val wdsum_measure_of : T -> int

    val relational_measure_of : T -> int * int (* functional * relational *)

    val wave_fronts_at : T -> WT list;

    val inst_skel_term : T -> Term.term

    val pterm_of : T -> Term.term

    val pretty : Proof.context -> T -> Pretty.T

end;

(* Rippling Notation *)
signature RRIPPLE_NOTATION =
sig 
    (* constants used for ripple notation for term pretty printing *)
    val wave_front_out : string;
    val wave_front_in : string;
    val sink : string;
end;

functor RRippleATermsFUN(RRippleNotation : RRIPPLE_NOTATION) : RRIPPLE_ATERMS =
struct

exception aterm_destruct_exp of string;

(* structure RippleNotation = RippleNotation *)

datatype dir = dir_in | dir_out;

datatype WT = WFFunc | WFRel of int | WFNone;

(* The type for annotated term contexts: uses dtrm from the TrmCtxt 
   This is part of a term above a point in the term tree. *)
type annot = (dir * TrmCtxtData.dtrm) list;

(* annotated terms *)
datatype T = 
         aApp of (T * T) * annot
       | aAbs of (string * Term.typ * T) * annot
       | aConst of (string * Term.typ) * annot
       | aFree of (string * Term.typ) * annot
       | aVar of ((string * int) * Term.typ) * annot 
       | aRelated of ((string * Term.typ) * (string * Term.typ)) * int * annot
       | aBound of int * annot
       | aSink of ((string * int) * Term.term) * annot;

(*  *)
fun out_annot_of_trmctxt c = 
    map (fn x => (dir_out, x)) c;

fun in_annot_of_trmctxt c = 
    map (fn x => (dir_in, x)) c;

(* make all possible directed annotations of an term context. 
   allowing ajacent wave fronts to have different directions *)
fun bidir_annots_of_trmctxt tc = 
    List.foldr
        (fn (dt,aL) => map (fn a => (dir_out, dt)::a) aL @
                       map (fn a => (dir_in, dt)::a) aL) 
        [[]] tc;

(* Create both an outward and an inward dir for this wave front.
   This makes all adjacent wave fronts have the same direction *)
fun bothdirs_annots_of_trmctxt [] =  [[]] 
  | bothdirs_annots_of_trmctxt tc = 
    [out_annot_of_trmctxt tc, in_annot_of_trmctxt tc];

  (* create all possible pairs with fst element from the first list
     and snd element from teh second list *)
fun all_pairs xs ys = 
    let 
        fun all_pairs_aux yss [] _ acc = acc
          | all_pairs_aux yss (x::xs) [] acc = 
            all_pairs_aux yss xs yss acc
          | all_pairs_aux yss (xs as (x1::x1s)) (y::ys) acc = 
                               all_pairs_aux yss xs ys ((x1,y)::acc)
      in
        all_pairs_aux ys xs ys []
      end;

(* consrtuction of aterms wihtout the inward sink restriction -
   i.e. allows outward and inward to be anywhere in the annoatted
   term. *)

fun u_aterms_of_eterm_aux mkannotdirf e = 
    let 
      fun rf (RREmbeddingLib.eApp ((e1, e2), a)) = 
          map aApp (all_pairs (all_pairs (rf e1) (rf e2))
            (mkannotdirf a))
        | rf (RREmbeddingLib.eAbs((s,y,e),a)) = 
          map (fn (t,a) => aAbs((s,y,t), a)) 
        (all_pairs (rf e) (mkannotdirf a))
        | rf (RREmbeddingLib.eConst((s,y),a)) = 
          map (fn au => aConst((s,y), au)) (mkannotdirf a)
        | rf (RREmbeddingLib.eFree((s,y),a)) = 
          map (fn a2 => aFree((s,y), a2)) (mkannotdirf a)
        | rf (RREmbeddingLib.eRelated(((s1, y1), (s2,y2)), n, a)) =
          map (fn a2 => aRelated(((s1, y1), (s2, y2)), n, a2)) (mkannotdirf a)
        | rf (RREmbeddingLib.eVar(((s,i),y),a)) = 
          map (fn a2 => aVar(((s,i),y), a2)) (mkannotdirf a)
        | rf (RREmbeddingLib.eBound(i,a)) = 
          map (fn a2 => aBound(i, a2)) (mkannotdirf a)
        | rf (RREmbeddingLib.eSink((ix,t),a)) = 
          map (fn a2 => aSink((ix,t), a2)) (mkannotdirf a);
    in rf e end;

  fun wave_fronts_at atrm =
        let
    fun wave_fronts_at' atrm =
          case atrm of
      aApp((left, right), ctxt) => ((wave_fronts_at' left) @ (wave_fronts_at' right))
    | aAbs((name, typ, trm), ctxt) => wave_fronts_at' trm
    | aRelated(((nm1, tp1), (nm2, tp2)), index, ctxt) => [WFRel(index)]
    | aSink(((nm, index), trm), ctxt) => [WFNone]
    | aFree((name, typ), ctxt) =>
        (case ctxt of
          [] => [WFNone]
        | _ => [WFFunc]) (* is it safe to assume this? *)
    | _ => []
  in
    wave_fronts_at' atrm
  end

(* annotated terms with unrestricted (u) inward wave fronts *)
(* implicit eterm *)
val u_aterms_of_eterm = 
    u_aterms_of_eterm_aux bidir_annots_of_trmctxt;
(* annotated terms with compound and unrestricted (cu) inward wave fronts *)
val cu_aterms_of_eterm = 
    u_aterms_of_eterm_aux bothdirs_annots_of_trmctxt;


(* only allow inward directions if a sink is below (w.r.t. flattened syntax) *)
(* note: utaf is annotation function *)
(* all possible directed aterms of an embedding *)
fun r_aterms_of_eterm_aux mkannotdirf e = 
    let 
        fun make_annots allowinward a = 
            if allowinward then
                mkannotdirf a
            else [out_annot_of_trmctxt a];

        fun rf (RREmbeddingLib.eApp ((e1, e2), a)) = 
            let 
                val (sink1, at1s) = rf e1
                val (sink2, at2s) = rf e2
                val hassink = sink1 orelse sink2
                val annots = make_annots hassink a
            in
                (hassink, map aApp (all_pairs (all_pairs at1s at2s) annots))
            end
          | rf (RREmbeddingLib.eAbs((s,y,e),a)) = 
            let 
                val (hassink, at1s) = rf e 
                val annots = make_annots hassink a
            in 
                (hassink, map (fn (at,a) => aAbs((s,y,at), a)) 
                              (all_pairs at1s annots))
            end
          | rf (RREmbeddingLib.eConst((s,y),a)) = 
            (false, [aConst((s,y), out_annot_of_trmctxt a)])
          | rf (RREmbeddingLib.eFree((s,y),a)) = 
            (false, [aFree((s,y), out_annot_of_trmctxt a)])
          | rf (RREmbeddingLib.eRelated(((s1,y1),(s2,y2)),n,a)) =
            (false, [aRelated(((s1,y1),(s2,y2)), n, out_annot_of_trmctxt a)])
          | rf (RREmbeddingLib.eVar(((s,i),y),a)) = 
            (false, [aVar(((s,i),y), out_annot_of_trmctxt a)])
          | rf (RREmbeddingLib.eBound(i,a)) = 
            (false, [aBound(i, out_annot_of_trmctxt a)])
          | rf (RREmbeddingLib.eSink((ix,t),a)) = 
            (true, [aSink((ix,t), in_annot_of_trmctxt a)]);
    in
        snd (rf e)
    end;



(* Two kinds of depth measure for HOAS terms, a first order (flat) and a
   higher order one.
   Note: not stable of eta-contraction: embedding eta-expands term,
   thus we assume eta-expanded *)
fun fo_term_height (a $ b) =
    Int.max (1 + fo_term_height b, (fo_term_height a))
  | fo_term_height (Abs(_,_,t)) = fo_term_height t
  | fo_term_height _ = 0;

fun ho_term_height  (a $ b) =
    1 + (Int.max (ho_term_height b, ho_term_height a))
  | ho_term_height (Abs(_,_,t)) = ho_term_height t
  | ho_term_height _ = 0;


(* Inward wave front restricted annotated terms *)
(* implicit eterm *)
val r_aterms_of_eterm = r_aterms_of_eterm_aux bidir_annots_of_trmctxt;
val cr_aterms_of_eterm = r_aterms_of_eterm_aux bothdirs_annots_of_trmctxt;

(* this will treat wave fronts as maximally split - ie 1 point for
   each bit in the wave front. We measure in a fo-style. 
   Because embedding terms are in eta-expanded form, we ignore abstractions
*)
fun addto_fo_measure (_, TrmCtxt.D.Abs _) m = m
  | addto_fo_measure (dir_out,TrmCtxt.D.AppL t) (om,im) = 
    (Int.max (fo_term_height t, 1 + om), im)
  | addto_fo_measure (dir_in,TrmCtxt.D.AppL t) (om,im) = 
    (om, Int.max (fo_term_height t, 1 + im))
  | addto_fo_measure (dir_out,TrmCtxt.D.AppR t) (om,im) =  
    (Int.max (fo_term_height t, om), im)
  | addto_fo_measure (dir_in,TrmCtxt.D.AppR t) (om,im) =  
    (om, Int.max (fo_term_height t, im))

fun fo_measure_of_annot l = 
    fold addto_fo_measure l (0,0);

(* For a higher order term height measure we add 1 to the measure even
   if the dtrm is on the right. *)
fun addto_ho_measure (_, TrmCtxt.D.Abs _) m = m
  | addto_ho_measure (dir_out,TrmCtxt.D.AppL t) (om,im) = 
    (Int.max (ho_term_height t, 1 + om), im)
  | addto_ho_measure (dir_in,TrmCtxt.D.AppL t) (om,im) = 
    (om, Int.max (ho_term_height t, 1 + im))
  | addto_ho_measure (dir_out,TrmCtxt.D.AppR t) (om,im) =  
    (Int.max (ho_term_height t, 1 + om), im)
  | addto_ho_measure (dir_in,TrmCtxt.D.AppR t) (om,im) =  
    (om, Int.max (ho_term_height t, 1 + im))

fun ho_measure_of_annot l = 
    fold addto_ho_measure l (0,0);

(* we use lists of possible measures - this function creates a 
   single possibility *)
fun single_measure_of_annot mesf annot =
    let
        val (om, im) = mesf annot
    in
        ([om], [im])
    end;

(* construct measures for an aterm, parameterised on the treatment of
   application to allow both a flattened and HO treatment *)
(* FIME: use a tail recursive version to save rev's later *)
fun measure_of_aux appmf annotmesf at = 
    let 
        fun mf (aApp((a1, a2), n)) = 
            appmf (mf a1) (mf a2) (annotmesf n)
          | mf (aAbs ((s,y,a), n)) = 
            let
                val (om,im) = annotmesf n
                val (oms, ims) = mf a
            in
                (om :: oms, im :: ims)
            end
          | mf (aConst (d, n)) = single_measure_of_annot annotmesf n
          | mf (aFree (d, n)) = single_measure_of_annot annotmesf n
          | mf (aRelated (d, n', n)) = single_measure_of_annot annotmesf n
          | mf (aVar (d, n)) = single_measure_of_annot annotmesf n
          | mf (aBound (d, n)) = single_measure_of_annot annotmesf n
          | mf (aSink (d, n)) = single_measure_of_annot annotmesf n
        val (om,im) = mf at
    in
        (rev om, rev im)
    end;

(* create an integer list difference measure for the embedding,
    numbers indicate how many wave fronts at that level of term tree *)
fun add_measures ([], b) = b
  | add_measures (a, []) = a
  | add_measures (ah::at, bh::bt) = 
    (ah + bh) :: add_measures (at, bt);

(* two kinds of treatment for combining measures of HOAS application *)
fun fo_appmf (oms1, ims1) (oms2, ims2) (om, im) = 
    ((add_measures(oms1,om::oms2)), (add_measures(ims1,im::ims2)));

fun ho_appmf (oms1, ims1) (oms2, ims2) (om, im) = 
    (om::(add_measures(oms1,oms2)), (im::add_measures(ims1,ims2)));

(* the measures the two kinds of treatment of application. Note that
compound treatment does not require a different measure function as,
in this case, only wave fronts of one direction occur in an annotation. *)
val fo_measure_of = measure_of_aux fo_appmf fo_measure_of_annot;
val ho_measure_of = measure_of_aux ho_appmf ho_measure_of_annot;

(* make a single list which is the undirected measure (first order style) *)
fun undirectify_measures (oms, ims) = add_measures(oms, rev ims)
val undirected_measure_of = undirectify_measures o measure_of_aux fo_appmf fo_measure_of_annot;

(* this is a measure based on the sum of the distance from every
outward directed directed annotation to the top of the term tree,
added to the sum distance of every inward wave front to each sink. 
*)
fun dsum_measure_of_aux mesf mesf_leaf at = 
    let 
      val inc_sinkds = map (fn x => 1 + x)
      fun mf d (aApp((a1, a2), n)) = 
          let val (sinkd1,m1) = mf d a1
              val (sinkd2,m2) = mf (d + 1) a2
              val sinkds = sinkd1 @ (inc_sinkds sinkd2)
          in (sinkds, m1 + m2 + mesf d sinkds n) end
        | mf d (aAbs ((s,y,a), n)) = 
          let val (sinkds, m) = mf (d + 1) a
              val sinkds' = inc_sinkds sinkds
          in (sinkds', m + mesf d sinkds' n) end
        | mf d (aConst (_, n)) = ([], mesf_leaf d n)
        | mf d (aFree (_, n)) = ([], mesf_leaf d n)
        | mf d (aRelated (_, _, n)) = ([], mesf_leaf d n)
        | mf d (aVar (_, n)) = ([], mesf_leaf d n)
        | mf d (aBound (_, n)) = ([], mesf_leaf d n)
        | mf d (aSink (_, n)) = ([0], mesf_leaf d n)
    in snd (mf 0 at) end;

(* Note: these measures require the sink restriction - as otherwise
inward wave fronts all have measure 0 - an alternative measure would
then be to count the distance to leafs, instaed of only sinks. *)
(* measure based on size of wave front * distance from top *)
fun mesf_wdsum topd sinkds n = 
    let val (om,im) = fo_measure_of_annot n in
      (topd * om) + (foldr (fn (sd, m) => im * sd + m) 0 sinkds)
    end;
fun mesf_wdsum_leaf topd n = (topd * fst (fo_measure_of_annot n));
val wdsum_measure_of = dsum_measure_of_aux mesf_wdsum mesf_wdsum_leaf;

(* measure based on distance from top, ignoring size. *)
fun mesf_dsum topd sinkds n = 
    let val (om,im) = fo_measure_of_annot n in
      (if om > 0 then topd else 0) + 
      (if im > 0 then foldr (fn (sd, m) => sd + m) 0 sinkds else 0)
    end;
fun mesf_dsum_leaf topd n = 
    let val (om,_) = fo_measure_of_annot n in
      if om > 0 then topd else 0 end;
val dsum_measure_of = dsum_measure_of_aux mesf_dsum mesf_dsum_leaf;

fun relational_measure_of at =
  let
    fun aux at =
        case at of
            aApp((a1, a2), n) => (aux a1) + (aux a2)
          | aAbs((s, y, a), n) => (aux a)
          | aRelated(_, x, n) => x
          | _ => 0
  in
      (dsum_measure_of at, aux at)
  end

(* A term representing the skeleton, but with sinks instantiated to
   their current content and relvars represented as freevars*)
fun inst_skel_term (aApp((a1, a2), _))  = (inst_skel_term a1) $ (inst_skel_term a2)
  | inst_skel_term (aAbs ((s,ty,a), _)) = (Abs(s,ty,(inst_skel_term a)))
  | inst_skel_term (aConst (d, _)) = (Const d)
  | inst_skel_term (aFree (d, _)) = (Free d)
  | inst_skel_term (aRelated (((s1,y1),(s2,y2)),n,_)) = (Free(("[related: " ^ s1 ^ " and " ^ s2 ^ "]"),y1))
  | inst_skel_term (aVar (d, n)) = (Var d)
  | inst_skel_term (aBound (d, _)) = (Bound d)
  | inst_skel_term (aSink ((d,t), _)) = t;


(* Pretty printing annotated terms, by constructing a regular term
   that we print, using Isabelle's pretty printer. *)
fun pterm_of_dirterm T (t, dir_out) = 
    let val ty = Term.type_of1 (T, t) in
        Const(RippleNotation.wave_front_out, ty --> ty) $ t
    end
  | pterm_of_dirterm T (t, dir_in) = 
    let val ty = Term.type_of1 (T, t) in
        Const(RippleNotation.wave_front_in, ty --> ty) $ t
    end;

fun pterm_of_sink T ((s,i),t) = 
    let val ty = Term.type_of1 (T, t) in
        Const(RippleNotation.sink, ty --> ty) $ t
    end;

(* ADD: provide a version that will print out wave fronts in a
grouped, minimal fashion *)

(* the term function that is prettifies the application of the annot *)
fun ptermf_of_annot T ((_, TrmCtxt.D.Abs(s,y))::al) t = 
    ptermf_of_annot T al (Abs(s,y,t))
  | ptermf_of_annot T ((dir, TrmCtxt.D.AppL l)::al) t = 
    ptermf_of_annot 
      T al ((pterm_of_dirterm ((TrmCtxt.ty_ctxt (map snd al)) @ T) (l,dir)) $ t)
  | ptermf_of_annot T ((dir, TrmCtxt.D.AppR r):: al) t = 
    ptermf_of_annot 
      T al (t $ (pterm_of_dirterm ((TrmCtxt.ty_ctxt (map snd al)) @ T) (r,dir)))
  | ptermf_of_annot T [] t = t;

fun pterm_of at = 
    let 
        fun rf T (aApp((a1, a2), n)) = 
            let val T2 = ((TrmCtxt.ty_ctxt (map snd n)) @ T) in
                ptermf_of_annot T n ((rf T2 a1) $ (rf T2 a2)) end
          | rf T (aAbs ((s,y,a), n)) = 
            let val T2 = y :: ((TrmCtxt.ty_ctxt (map snd n)) @ T)
            in ptermf_of_annot T n (Abs(s,y, rf T2 a)) end
          | rf T (aConst (d, n)) = 
            ptermf_of_annot T n (Const d)
          | rf T (aFree (d, n)) = 
            ptermf_of_annot T n (Free d)
          | rf T (aRelated (((s1,y1),(s2,y2)),n',n)) =
            ptermf_of_annot T n (Free(("Related " ^ s1 ^ " and " ^ s2), y1))
          | rf T (aVar (d, n)) = 
            ptermf_of_annot T n (Var d)
          | rf T (aBound (d, n)) = 
            ptermf_of_annot T n (Bound d)
          | rf T (aSink (d, n)) = 
            ptermf_of_annot T n
            (pterm_of_sink ((TrmCtxt.ty_ctxt (map snd n))@T) d);
    in rf [] at end;

fun num_args trm =
  let        
    fun aux (Free(nm, typ)) = 1
      | aux (Var((nm, ind), typ)) = 1
      | aux (Abs(nm, typ, trm'')) = (aux trm'')
      | aux (x $ y) = (aux x) + (aux y)
      | aux z = 0
  in
    aux (inst_skel_term trm)
  end

fun pretty ctxt at = 
    Trm.pretty ctxt (pterm_of at);

end;

structure RRipplingNotation : RRIPPLE_NOTATION =
  struct
    val wave_front_out = ">"
    val wave_front_in = "<"
    val sink = "#"
  end

structure RRipplingATerms =
  RRippleATermsFUN(RRipplingNotation);
