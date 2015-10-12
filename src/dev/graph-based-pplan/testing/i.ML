(* Interaction with proof env *)
signature PRF_INTERFACE =
  sig
    type T

    exception inapplicable_exp of string

    val proofref : T ref

    val add_goal : string -> unit
    val add_goal_i : BasicTrm.T -> unit
    val apply : DTac.T -> Prf.gname -> unit
    val b : unit -> unit

    val get : unit -> Prf.gname list * DB_Prf.T
    val get_gs : unit -> Prf.gname list
    val get_p : unit -> Prf.T
    val get_stack : unit -> T
    val init : unit -> unit
    val l : unit -> int
    val ls : unit -> int list
    val pr : unit -> unit
    val prf : unit -> unit
    val print : string list * DB_Prf.T -> unit

    val u : unit -> unit

end;

structure I : PRF_INTERFACE=
struct

exception inapplicable_exp of string;

type T = (Prf.gname list * Prf.T) list list;

(* init proof ref *)
val proofref = ref [] : T ref;

(* get *)
fun get_stack () = ! proofref;
val get = hd o hd o get_stack; 
val get_gs = fst o get;
val get_p = snd o get;

(* printing *)
fun print (newgs, p) = 
    let 
      val gs = Prf.GNTab.dest (Prf.get_open_gnames p)
    in
      Pretty.writeln (Pretty.chunks 
        [Pretty.list "[" "]" (map Pretty.str newgs),
         Pretty.str "--------",
         (Prf.pretty_gs gs p)])
    end;

val pr = print o get;
(* fun prs () = Prf.print_struct (get_p()); *)
val prf = Prf.print_full o get_p;

(* init/creation *)
fun init () = 
      (proofref 
       := [[([],(Prf.init (the_context())))]]; 
       pr());

(* add new goals *)
fun add_goal_i t = 
    let val (n,p) = Prf.add_topgoal_trm t (get_p())
    in
      (proofref := ([([n],p)] :: (get_stack())); 
       pr())
    end;

fun add_goal s = add_goal_i (Prf.read_top_term (get_p()) s);

(* undo *)
fun u () = 
    (case !proofref 
      of [] => raise inapplicable_exp "u: nothing to undo."
       | (_::l) => (proofref := l; pr()));

(* back *)
fun b () = 
    (case !proofref 
      of [] => raise inapplicable_exp "b: at start."
       | ([]::l) => (proofref := l; pr())
       | ((h::t)::l) => (proofref := t::l; pr()));

(* length *)
fun l () = length (hd (!proofref));
fun ls () = map length (!proofref);


fun apply d s = 
    (proofref := 
               (case Seq.list_of (Prf.apply_dtac d s (get_p()))
                 of [] => 
                    raise (inapplicable_exp "apply: no results.")
                  | l => 
                    l :: (get_stack())); 
     pr());

(* apply *)
(* 
fun res th s = (proofref := 
                         (case (Seq.list_of (Prf.res_thm th s (get_ffp())))
                          of [] => 
                             raise (inapplicable_exp "app: no results.")
                           | l => 
                              (map (apsnd Prf.FFPr) l) :: (get_stack())); 
               pr());

fun dtac d s = (proofref := 
                         (case (Seq.list_of (Prf.apply_dtac_to_nd d s (get_ffp())))
                          of [] => 
                             raise (inapplicable_exp "app: no results.")
                           | l => 
                              (map (apsnd Prf.FFPr) l) :: (get_stack())); 
               pr());

fun appf f = (proofref := 
                         (case (Seq.list_of (f (get())))
                          of [] => 
                             raise (inapplicable_exp "app: no results.")
                           | l => 
                             (l :: (get_stack()))); 
               pr());
*)
end;



fun d_subst th = 
    DTac.mks_i 
      (("subst: " ^ (Thm.name_of_thm th)), 
       (fn (thry, _, _) => 
           EqSubst.eqsubst_tac (ProofContext.init thry) [0] [th] 1));

fun d_rtac  th = DTac.mk (Pretty.str ("res: " ^ (Thm.name_of_thm th)),
                         rtac th 1);



(* basic tools *)
fun term_of_str s = 
    let val thry = (the_context()) in
      (ProofContext.read_term (ProofContext.init thry) s) end;

fun cterm_of_str s = 
    let val thry = (the_context()) in
      Thm.cterm_of thry (term_of_str s) end;
