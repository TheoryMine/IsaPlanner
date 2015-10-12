(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/isar_lang.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    The basic Isar script language elements in a declarative form

    USES: dmethod.ML (declarative Isar Methods)

*)
structure IsarLang =
struct


(* type of an Isar goal decloration, as used by show, and theorem etc
   complex! Note: 'a will start as 'b DAttr.T *)
datatype 'a goalsdecT = 
         Termdec of 
         ((bstring * (* name for shows terms *)
          'a list (* attributes for shows terms *)
         ) * 
         (Term.term * (* conclusion *)
          (Term.term list * (* "is" matched terms ? *)
           Term.term list) (* ? terms *)
         ) list) list
       | Stringdec of
         ((string * (* name for shows terms *)
          'a list (* attributes for shows terms *)
         ) * 
         (string * (* conclusion *)
          (string list * (* "is" matched terms ? *)
           string list) (* ? terms *)
         ) list) list;

(* making Isar-suitable doal declarations from declrative attribute
   goal declorartions. *)
fun goaldec_attr_map f x = 
    (map (fn ((n,attrs), ls) => 
             ((n,(map f attrs)), ls))
         x);
fun isar_ctxt_goaldec_of d = 
    goaldec_attr_map DAttrib.ctxt_attrf d;
fun isar_thry_goaldec_of d = 
    goaldec_attr_map DAttrib.thry_attrf  d;
fun isar_src_goaldec_of d = 
    goaldec_attr_map DAttrib.src_of d;

(* useful functions for show, theorem, have etc *)
fun nothing_after_global_qed contextandthms thms thry = thry;
fun nothing_after_qed contextandthms thms pst = Seq.single pst;

(* prtty printing ctxt attributes *)
fun pretty_attributes ctxt [] = Pretty.block []
  | pretty_attributes ctxt (attrs as _::_) = 
    Pretty.list "[" "]" (map (fn a => DAttrib.ctxt_pretty a ctxt) attrs);

(* pretty printing *)
(* FIXME: add attribute printing *)
fun pretty_name paf (name, attributes) = 
    if name = "" then Pretty.block [] else
    Pretty.block [Pretty.str name,
                  paf attributes,
                  Pretty.str ": "];

fun pretty_showterm ptf (t, matches) =
    Pretty.str ("\"" ^ (ptf t) ^ "\"");

fun pretty_showterms ptf [] = []
  | pretty_showterms ptf [a] = [pretty_showterm ptf a]
  | pretty_showterms ptf (h :: (t as (h2::t2))) =
    (pretty_showterm ptf h) :: (Pretty.str " and ") :: 
    (pretty_showterms ptf t);

fun pretty_shown_str ptf paf (nmdec, showterms) = 
    Pretty.block ((pretty_name paf nmdec) :: 
    (pretty_showterms ptf showterms));

fun pretty_shown ptf paf (nmdec, showterms) = 
    Pretty.block ((pretty_name paf nmdec) :: 
    (pretty_showterms ptf showterms));

(* FIXME: What does it mean to have more than one showns? when does
this happen? and is what I've done right? certianly not! *)
fun pretty_showns_aux ptf paf [] = []
  | pretty_showns_aux ptf paf [a] = [pretty_shown ptf paf a]
  | pretty_showns_aux ptf paf (h :: (t as (h2::t2))) = 
    (pretty_shown ptf paf h) 
    :: (Pretty.str " and ") 
    :: (pretty_showns_aux ptf paf t); 

(* FIXME: What does it mean to have more than one showns? when does
this happen? and is what I've done right? certianly not! *)
fun pretty_showns ptf paf (Stringdec d) = pretty_showns_aux I paf d 
  | pretty_showns ptf paf (Termdec d) = pretty_showns_aux ptf paf d;


(* pretty print and separate with " and " *)
fun pretty_with_ands f [] = []
  | pretty_with_ands f [a] = [f a]
  | pretty_with_ands f (h :: (t as (h2::t2))) =
    (f h) :: (Pretty.str " and ") :: (pretty_with_ands f t);


fun pretty_thm_and_attr ctxt (thm, attrs) = 
    Pretty.block [Pretty.str (Thm.name_of_thm thm),
                  pretty_attributes ctxt attrs];

fun pretty_thmnm_and_attr ctxt (thmnm, attrs) = 
    Pretty.block [Pretty.str (thmnm),
                  pretty_attributes ctxt attrs];

(* create a pretty string from Args.src *)
fun string_of_isar_args_src src = 
    let 
      val ((s, Tlist), pos) = Args.dest_src src 
      val str_of_args = (implode (map (fn t => " " ^ Args.string_of t) Tlist))
    in
      (s ^ str_of_args)
    end;

val goals_of_pst = Thm.prems_of o snd o snd o Proof.get_goal;

fun step_pair_of_pst pst = (pst, goals_of_pst pst);

(* the structure for the Isar element multi_theorem that is used to
start the new proof of a theorem or lemma *) (* FIXME: add in dattr
for locale elemtns. *) 
(* FIXME: optimise for fakelocalthm's - ie
prune redundant data - these are for faking the context of a proof *)
structure Theorem =
struct 

val name = "theorem";

(* contains local attributes, but for some reason still theory attributes? *)
(*  Theory.theory Thm.attribute goalsdecT;  *)
type goaldecT = DAttrib.T goalsdecT;

(* FIXME: use: elements and coordinate with goaldecT, ie if it is an term 
   based declaration (internal), or a string based one (toplevel/user) *)
datatype T = 
     Thmthm of
     { kind : string,
       afterqed : Proof.context * Thm.thm list ->  Thm.thm list list 
                  -> Theory.theory -> Theory.theory, 
       locale : string option,
       name : string,
       attributes : DAttrib.T list, (* top level attributes of top name *)
       showing : goaldecT, (* contains local attributes *)
       ctxt : Proof.context 
     } (* a normal thm *)
   | Ctxtthm of 
     { ctxt : Proof.context,
       goalterm : Term.term
     } (* show goal from an Isar context *)
   | Pstthm of 
     { pst : Proof.state }; (* direct use of an Isar pst *)


fun mk_goaldecterm_of_term t  = 
    Termdec [(("", []), [(t, ([],[]))])] : goaldecT;

fun mk_goaldecterm_of_string s  = 
    Stringdec [(("", []), [(s, ([],[]))])] : goaldecT;



(* initialise a new proof plan of kind k, from a theory thy, 
   given name n and term t *)
fun mk_init_multi_theorem_i k ctxt (n : string,t : Term.term) =  
    (Thmthm { kind = k,
              afterqed = nothing_after_global_qed,
              locale = NONE,
              name = n,
              attributes = [],
              showing = mk_goaldecterm_of_term t,(* why is this a list? *)
              ctxt = ctxt
              } : T);

(* initialise a new proof plan of kind k, from a theory thy, 
   given name n and term t *)
fun mk_init_multi_theorem k ctxt (n : string,s : string) =  
    (Thmthm { kind = k,
              afterqed = nothing_after_global_qed,
              locale = NONE,
              attributes = [],
              name = n,
              showing = mk_goaldecterm_of_string s, (* why is this a list? *)
              ctxt = ctxt
              } : T);

fun mk_init_from_ctxt_i ctxt (t : Term.term) =  
    (Ctxtthm {ctxt = ctxt, goalterm = t} : T);

fun mk_init_from_pst_i pst  = Pstthm {pst = pst};

(* theorems and lemmas *)
val mk_init_theorem = mk_init_multi_theorem "theorem";
val mk_init_theorem_i = mk_init_multi_theorem_i "theorem";
val mk_init_lemma = mk_init_multi_theorem "lemma";
val mk_init_lemma_i = mk_init_multi_theorem_i "lemma";


local
(* clunky way...
  val proto_sign = Theory.sign_of ProtoPure.thy;
  fun read_prop s = read_cterm proto_sign (s, propT);
  val ignored_main_goal = Thm.term_of (read_prop "PROP ?A"); *)
(* use above, and "TermLib.writeterm" to get below, efficient form *)
  val ignored_main_goal = Var( ("A",0), Type("prop", []));
in

(* function to start a new proof *)
(* FIXME: use elements *)
fun startf (Thmthm { kind, afterqed, locale, name, 
                     attributes, showing, ctxt }) = 
    step_pair_of_pst 
      (case showing of 
         Termdec d => 
         Proof.theorem_i 
           kind afterqed locale
           (name, map DAttrib.thry_attrf attributes)
           (isar_thry_goaldec_of d) ctxt
       | Stringdec d => 
         Proof.theorem
           kind afterqed locale
           (name, map DAttrib.src_of attributes)
           (isar_src_goaldec_of d) ctxt )
(* THINK: is this really the right way to do things? *) 
(* We make a normal theorem, but then cut in the context we want *)
(* these are really only for using pplanning as a method - note that a
method can only access the ctxt, the pst, else we would be much better
off. *)
(* Note, its a quite complex thing that requires us to use the
schematic varaible: we need to be able to always succeed, but we can't
use isarr-fixed variables in the goal prop, (not allwed when you
declare a theorem), and yet we also neeßd to use a "show" statement so
that we get a shown theorem as the result... really its a hack, the
'right' way to do this is have a proper proof state constructed -
without having to cut in an earlier context etc. *)
  | startf (Ctxtthm {goalterm, ctxt}) = 
    let
      val fakeshowing = [(("", []), [(ignored_main_goal, ([],[]))])];
      val reallyshowing = [(("", []), [(goalterm, ([],[]))])];
      val thry = ProofContext.theory_of ctxt;
      val triv_meth_text = 
          Method.Basic 
            (Method.method thry (Args.src (("-", []), Position.none)));
    in
      step_pair_of_pst 
        ((Proof.theorem_i 
            "ignoredkind" 
            nothing_after_global_qed
            NONE
            ("ignoredname", []) fakeshowing ctxt)
           |> Proof.proof (SOME triv_meth_text) |> Seq.hd
           |> Proof.map_context (K ctxt)
           |> Proof.show_i 
           nothing_after_qed
           (* HACK: two of the same contexts in order to make outer_context look correct, 
            else, it looks like the context of the initial goal, before the context mapping *)
           reallyshowing (* goaldec: what we should solve *)
           false (* print results *)
   (* NOTE: we don't use NONE method - this will try some default method! *)
           |> Proof.proof (SOME triv_meth_text) |> Seq.hd
           |> Proof.show_i 
           nothing_after_qed
           reallyshowing (* goaldec: what we should solve *)
           false 
        )
    end (* let *)
    (* everything is direct if we already have a pst... *)
  | startf (Pstthm {pst}) = step_pair_of_pst pst;


end; (* local *)


(* copy... *)
val copy = I;

(* FIXME: unused exp ? *)
exception bad_data_exp of string;


(* pretty func *)
fun prettyf (Thmthm { kind, afterqed, locale, name, 
                      attributes, showing, ctxt }) = 
    (Pretty.block [Pretty.str (kind ^ " "), 
                   pretty_name (pretty_attributes ctxt) (name, attributes),
                   Pretty.block (pretty_showns (IsarTools.string_of_term_in_ctxt ctxt) 
                                               (pretty_attributes ctxt)
                                               showing)])
  | prettyf (Ctxtthm rep) =     
    (Pretty.block [Pretty.str "-- {* Inserting Isar proof of ", 
                      Pretty.quote (ProofContext.pretty_term 
                                      (#ctxt rep) (#goalterm rep)),
                      Pretty.str ". *}"])
  | prettyf (Pstthm rep) = 
    (Pretty.block [Pretty.str "-- {* Generating Isar proof script *}"]);

  structure E = 
  PScriptConstrFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val startf = startf;
        val prettyf = prettyf;
        val copy = copy;
      end
  );

(*
TEST with: 

val mythmdecinfo = 
    (IsarLang.Theorem.mk_init_theorem 
       (theory "Main") ("ug", read "Trueprop (P x)"));

val mypp = IsarLang.Theorem.E.mkplan mythmdecinfo;

Pretty.writeln (PScript.pretty mypp);
*)

end;



(* the structure for the Isar element Fix *)
structure Fix =
struct 

val name = "fix";

type T = (string list * typ option) list * Term.term list;

exception bad_data_exp of string;

val copy = I;

fun fix s = ([([s],NONE)], []) : T;
fun fix_i s = (s, []) : T;

(* the apply function *)
fun applyf (params, newgoals) (pst, goals) = 
    (Proof.fix_i params pst, newgoals);

(* pretty printing fixes... *)
fun prettyf_aux ctxt [] = 
    raise bad_data_exp (name ^ ":prettyf_aux: " ^ 
                           "Can't fix nothing!")
  | prettyf_aux ctxt (l as h :: t)  = 
    let 
      fun pretty_names [] = []
        | pretty_names [h] = [Pretty.str h]
        | pretty_names (h::(t as h2::t2)) = 
          (Pretty.str h) :: (Pretty.str  " ") :: (pretty_names t)

      fun pretty_v ([],_) =
          raise bad_data_exp 
                  (name ^ ":prettyf_aux:pretty_fix_v" ^ 
                   "Can't fix nothing!")
        | pretty_v (vs, NONE) = 
          Pretty.block (pretty_names vs)
        | pretty_v (vs, SOME ty) = 
          Pretty.block [Pretty.block (pretty_names vs), 
                        Pretty.str " :: ",
                        Pretty.quote (ProofContext.pretty_typ ctxt ty)]

      fun pretty_vs [] = []
        | pretty_vs [h] = [pretty_v h]
        | pretty_vs (h::(t as h2::t2)) = 
          (pretty_v h) :: (Pretty.str  " and ") :: (pretty_vs t)

    in
      Pretty.block (pretty_vs l)
    end;

fun prettyf (l, newgoals) ctxt =
    (0, Pretty.block [Pretty.str "fix ", 
                      prettyf_aux ctxt l]);


  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );



(* isar_term_prep: prepare a term for Isar, i.e with fixed params,
substituted into the goal etc. We avoid name clashes w.r.t the
context/Isar naming systems, and possibly types with "__"-ending
names. We do this by making all previous 

Note argument for correctness of this code: we assume internal names
are always distinct and are a strict super-set of the externally used
names. Thus, taking internal names and removing "__" gives a strictly
larger set of names than the external names, and thus any new names
which are distinct will be fresh both internally and externally. *)
fun fix_params ctxt t = 
    let 
      val ctxtnames = 
          map (fn n => ((Syntax.dest_skolem n) handle Fail _ => n)) 
              (ProofContext.fixed_names_of ctxt)

      val fixed_params = rev (Logic.strip_params t) 

      val prev_free_names = 
          (map (fn (Free (n,ty)) => 
                  ((Syntax.dest_skolem n) handle Fail _ => n)
                | _ => raise ERROR_MESSAGE 
                               "isar_term_prep: this can't be happening!?")
              (Term.term_frees t))
          @ ctxtnames
    
      (* make the new Isar parameters unique (using varient) 
              w.r.t. each other and the old *)
      val unique_fixed_params = 
          fst (foldr
                 (fn ((n,ty), (uns,vns)) => 
                     let 
                       (* make sure param names do not end in "__" *)
                       val n' = ((Syntax.dest_skolem n) handle Fail _ => n)
                       val n2 = Term.variant vns n' in
                       ((n2,ty)::uns,n2::vns)
                     end)
                 ([], prev_free_names) fixed_params)

      val isar_fixed_params = map (fn (n,ty) => ([n], SOME ty)) 
                              unique_fixed_params

      fun mk_isar_term fixed_vars t = 
          Term.subst_bounds ((map (fn (n,ty) => 
                                      Free (Syntax.skolem n, ty)) 
                                  fixed_vars), t)
       val isar_prems = 
          map (mk_isar_term unique_fixed_params)
              (Logic.strip_assums_hyp t)

      val concl_with_fixed_vars = 
          mk_isar_term unique_fixed_params 
                       (Logic.strip_assums_concl t)
    in
      (isar_fixed_params, 
       [Logic.list_implies (isar_prems, concl_with_fixed_vars)])
    end;


end;



(* the structure for the Isar element Fix *)
structure IsarProof =
struct 

val name = "proof";

type T = DMethod.T;

val copy = I;

fun of_named_meth name_and_meth = name_and_meth;          

fun prettyf d ctxt = 
    (1, Pretty.block [Pretty.str "proof (", 
                      DMethod.pretty_of d ctxt, 
                      Pretty.str ")"]);

(* the apply function *)
fun applyf d (pst, _) = 
    case Seq.pull (Proof.proof (SOME (DMethod.mtext_of 
                                         d (Proof.context_of pst))) 
                                pst) of 
      NONE => raise IsarTools.meth_exp "IsarLang.IsarProof.applyf: no result"
    | SOME (pst', _) => step_pair_of_pst pst';

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* the structure for the Isar element Fix *)
structure Apply =
struct 

val name = "apply";

type T = DMethod.T;

val copy = I;

fun of_named_meth name_and_meth = (name_and_meth : T);

fun prettyf d ctxt = 
    (0, Pretty.block [Pretty.str "apply (", 
                      DMethod.pretty_of d ctxt,
                      Pretty.str ")"]);

(* the apply function *)
fun applyf d (pst, _) = 
    case Seq.pull (Proof.refine (DMethod.mtext_of 
                                    d (Proof.context_of pst)) pst) of 
      NONE => raise IsarTools.meth_exp "IsarLang.Apply.applyf: no result"
    | SOME (pst', _) => step_pair_of_pst pst';

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* the structure for local qeds *)
structure LocalQed =
struct 

val name = "local_qed";


type T = DMethod.T option;

val copy = I;

fun of_dmeth dmeth = SOME dmeth;
fun none dmeth = NONE;
fun of_dmeth_opt dmethopt = dmethopt;

fun prettyf (SOME d) ctxt = 
    (~1, Pretty.block [Pretty.str "qed (", 
                       DMethod.pretty_of d ctxt,
                       Pretty.str ")"])
  | prettyf NONE ctxt = (~1, Pretty.str "qed");


(* the apply function *)
fun applyf NONE (pst, _) = 
    (case Seq.pull (Proof.local_qed (NONE,true) pst) of 
       NONE => raise IsarTools.meth_exp "IsarLang.LocalQed.applyf: BADNESS: no result of no dmethod - something has gone very strange???"
     | SOME (pst', _) => step_pair_of_pst pst')
  | applyf (d as (SOME m)) (pst, _) = 
    (case Seq.pull (Proof.local_qed  
                      (SOME (DMethod.mtext_of 
                               m (Proof.context_of pst)), true)
                      pst) of 
      NONE => raise IsarTools.meth_exp "IsarLang.LocalQed.applyf: no result"
    | SOME (pst', _) => step_pair_of_pst pst');

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* the structure to fake global qeds *)
structure GlobalQed =
struct 

val name = "global_qed";

type T = DMethod.T option;

val copy = I;

fun of_dmeth dmeth = SOME dmeth;
fun none dmeth = NONE;
fun of_dmeth_opt dmethopt = dmethopt;

fun prettyf (SOME d) ctxt = 
    (~1, Pretty.block [Pretty.str "qed (", 
                       DMethod.pretty_of d ctxt,
                       Pretty.str ")"])
  | prettyf NONE ctxt = (~1, Pretty.str "qed");


exception global_qed_exp of string;

(* the apply function *)
fun applyf NONE (pst, _) = 
    pst |> Proof.refine (Method.finish_text (NONE, true))
        |> Seq.hd 
        |> step_pair_of_pst
  | applyf (d as (SOME m)) (pst, _) = 
    pst |> Proof.refine (Method.finish_text 
                           (SOME (DMethod.mtext_of 
                                    m (Proof.context_of pst)),true))
        |> Seq.hd 
        |> step_pair_of_pst;

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* the structure for general qed, context dependent, uses global and local qed *)
structure Qed =
struct 

val name = "qed";


type T = DMethod.T option;

val copy = I;

fun of_dmeth dmeth = SOME dmeth;
fun none dmeth = NONE;
fun of_dmeth_opt dmethopt = dmethopt;

fun prettyf (SOME d) ctxt = 
    (~1, Pretty.block [Pretty.str "qed (", 
                       DMethod.pretty_of d ctxt,
                       Pretty.str ")"])
  | prettyf NONE ctxt = (~1, Pretty.str "qed");

(* if we are at the end of the proof, then fake result and give back a
next block command to clean up - ie leave us with the proved global
gaol at the thm object *)
fun applyf dm (a as (pst, goals)) = 
    if Proof.level pst <= 2 then 
      GlobalQed.applyf dm a
    else LocalQed.applyf dm a;

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;




(* the structure for the Isar element Fix *)
structure By =
struct 

val name = "by";

type T = DMethod.T;

val copy = I;

fun of_named_meth name_and_meth = name_and_meth;

fun prettyf d ctxt = 
    (0, Pretty.block [Pretty.str "by (", 
                      DMethod.pretty_of d ctxt,
                      Pretty.str ")"])

(* the apply function *)
(* FIXME: add second arg to by, ie for local qed 
by m1 m2 = proof m1 qed m2
Note that Method.local_terminal_proof does both the proof and qed step
*)
fun applyf d (pst, _) = 
    case Seq.pull (Proof.local_terminal_proof 
                     (DMethod.mtext_of d (Proof.context_of pst),NONE)
                     pst) of 
      NONE => raise IsarTools.meth_exp "IsarLang.By.applyf: no result"
    | SOME (pst',_) => step_pair_of_pst pst';

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;


(* the structure for the Isar element Show *)
structure Show =
struct 

val name = "show";

type goaldecT = DAttrib.T goalsdecT;
type T = goaldecT;

val copy = I;

fun show_term term = Termdec [(("", []), [(term, ([],[]))])];
fun show_named_term (name, term) = Termdec [((name, []), [(term, ([],[]))])];
fun show_named_termstr (name, s) = Stringdec [((name, []), [(s, ([],[]))])];

(* the apply function *)
fun applyf' (Termdec d) pst = Proof.show_i 
                                nothing_after_qed
                                (isar_ctxt_goaldec_of d) (* goaldec: what we should solve *)
                                false (* print results *)
                                pst
(* the apply function *)
  | applyf' (Stringdec d) pst = Proof.show 
                                  nothing_after_qed
                                  (isar_src_goaldec_of d) (* goaldec: what we should solve *)
                                  false (* print results *)
                                  pst;

fun applyf d (pst, goals) = step_pair_of_pst (applyf' d pst)

fun prettyf d ctxt = 
    (0, Pretty.block 
          [Pretty.str "show ",
           Pretty.block (pretty_showns 
                           (IsarTools.string_of_term_in_ctxt ctxt) 
                           (pretty_attributes ctxt)
                           d)]);    
  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;


(* the structure for the Isar element Thus *)
structure Thus =
struct 

val name = "thus";

type goaldecT = DAttrib.T goalsdecT;
type T = goaldecT;

val copy = I;

fun thus_term term = Termdec [(("", []), [(term, ([],[]))])];
fun thus_named_term (name, term) = Termdec [((name, []), [(term, ([],[]))])];
fun thus_named_termstr (name, s) = Stringdec [((name, []), [(s, ([],[]))])];

(* the apply function *)
fun applyf' (Termdec d) pst = 
    pst |> Proof.chain 
        |> (Proof.show_i nothing_after_qed 
                         (isar_ctxt_goaldec_of d) (* goaldec: what we should solve *)
                         false (* print results *)
                         )

(* the apply function *)
  | applyf' (Stringdec d) pst =
    pst |> Proof.chain 
        |> (Proof.show nothing_after_qed
                       (isar_src_goaldec_of d) (* goaldec: what we should solve *)
                       false (* print results *)
                       );

fun applyf d (pst, _) = step_pair_of_pst (applyf' d pst);


fun prettyf d ctxt = 
      (0, Pretty.block 
            [Pretty.str "thus ",
             Pretty.block (pretty_showns 
                             (IsarTools.string_of_term_in_ctxt ctxt)
                             (pretty_attributes ctxt)
                             d)]);

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;




(* the structure for the Isar element Assume *)
structure Assume =
struct 

(* exception isar_assume of  *)

val name = "assume";

type goaldecT = DAttrib.T goalsdecT;
type T = goaldecT;

val copy = I;

fun assume_named_term (name, term) = Termdec [((name, []), [(term, ([],[]))])];
fun assume_named_termstr (name, s) = Stringdec [((name, []), [(s, ([],[]))])];
fun assume_named_terms l = 
    Termdec (map (fn (name, term) =>
                     ((name, []), [(term, ([],[]))]))
                 l);

fun assume_named_term_wattr ((name, term), dattrs) = 
    Termdec [((name, dattrs), [(term, ([],[]))])];

fun assume_named_terms_wattr l = 
    Termdec (map (fn ((name, term),dattrs) =>
                     ((name, dattrs), [(term, ([],[]))]))
                 l);


(* the apply function *)
(* implicit extra argument: Proof.state *)
fun applyf' (Termdec d) = Proof.assume_i (isar_ctxt_goaldec_of d)
  | applyf' (Stringdec d) = Proof.assume (isar_src_goaldec_of d); 
fun applyf d (pst, goals) = (applyf' d pst, goals)

fun prettyf d ctxt = 
    (0, Pretty.block 
          [Pretty.str "assume ",
           Pretty.block (pretty_showns 
                           (IsarTools.string_of_term_in_ctxt ctxt) 
                           (pretty_attributes ctxt)
                           d)]);
     
  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;





(* the structure for the Isar element Have *)
structure Have =
struct 

val name = "have";

type goaldecT = DAttrib.T goalsdecT;
type T = goaldecT;

val copy = I;

fun have_term term = Termdec [(("", []), [(term, ([],[]))])];
fun have_named_term (name, term) = Termdec [((name, []), [(term, ([],[]))])];
fun have_named_termstr (name, s) = Stringdec [((name, []), [(s, ([],[]))])];

(* the apply function *)
fun applyf' (Termdec d) pst = 
    Proof.have_i 
      nothing_after_qed
      (isar_ctxt_goaldec_of d)
      false
      pst
  | applyf' (Stringdec d) pst = 
    Proof.have 
      nothing_after_qed
      (isar_src_goaldec_of d)
      false
      pst;

fun applyf d (pst, _) = 
    step_pair_of_pst (applyf' d pst);

fun prettyf d ctxt = 
    (0, Pretty.block 
          [Pretty.str "have ",
           Pretty.block (pretty_showns 
                           (IsarTools.string_of_term_in_ctxt ctxt)
                           (pretty_attributes ctxt) d)]);

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* the structure for the Isar element Hence *)
structure Hence =
struct 

val name = "hence";

type goaldecT = DAttrib.T goalsdecT;
type T = goaldecT;

val copy = I;

fun hence_term term = Termdec [(("", []), [(term, ([],[]))])];
fun hence_named_term (name, term) = Termdec [((name, []), [(term, ([],[]))])];
fun hence_named_termstr (name, s) = Stringdec [((name, []), [(s, ([],[]))])];

(* the apply function *)
fun applyf' (Termdec d) pst = 
    pst |> Proof.chain 
        |> (Proof.have_i 
              nothing_after_qed
              (isar_ctxt_goaldec_of d)
              false)
  | applyf' (Stringdec d) pst =
    pst |> Proof.chain 
        |> (Proof.have 
              nothing_after_qed
              (isar_src_goaldec_of d)
              false); 

fun applyf d (pst, _) = 
    step_pair_of_pst (applyf' d pst);

fun prettyf d ctxt = 
    (0, Pretty.block 
          [Pretty.str "hence ",
           Pretty.block (pretty_showns 
                           (IsarTools.string_of_term_in_ctxt ctxt)
                           (pretty_attributes ctxt) d)]);

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* the structure for the Isar element from *)
structure From =
struct 

val name = "from";

datatype T = froms_i of (Thm.thm * DAttrib.T list) list
           | froms of (xstring * DAttrib.T list) list;

val copy = I;

fun from_thms (thms) = froms_i [(thms, [])];
fun from_thm_attrs thms_and_attr = froms_i;
fun from_names strs = froms (map (fn s => (s,[])) strs);
fun from_names_atts strs = froms;

(* the apply function, implicit pst *) (* note we use have with no
name or extra attr for the named version *) (* note we make a list of
theorems but only use a string: this is becasue a string already
stands for a list inside isar, although, often the list is a
singleton. *)
fun applyf (froms d) (pst, goals)= 
    ((Proof.chain o 
      (Proof.note_thmss
          (* what is this? overall name? *)
         (map (fn (s,attrs) => 
                  (("",[]),
                   [(PureThy.Name s,map DAttrib.src_of attrs)]))
              d))) pst,
     goals)
  | applyf (froms_i d) (pst, goals) = 
    ((Proof.chain o (Proof.note_thmss_i 
      (map (fn (thm,attrs) => 
               (("",[]), 
                [([thm],map DAttrib.ctxt_attrf attrs)])) 
           d))) pst,
    goals)

fun prettyf (froms_i d) ctxt = 
    (0, Pretty.block 
          [Pretty.str "from ",
           Pretty.block (pretty_with_ands 
                           (pretty_thm_and_attr ctxt) d)])
  | prettyf (froms d) ctxt = 
    (0, Pretty.block 
          [Pretty.str "from ",
           Pretty.block (pretty_with_ands 
                           (pretty_thmnm_and_attr ctxt) d)]);

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* Then isar proof command *)
structure Then =
struct 

val name = "then";

type T = unit;

val copy = I;

fun applyf (d : T) (pst, goals) = (Proof.chain pst, goals);

fun prettyf d ctxt = (0, Pretty.str "then");

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;



(* Gaps that solve goals *)
(* structure GoalGap =
struct 

val name = "goalgap";

type T = GapTac.I.T;

val copy = I;

fun applyf (d : T) (pst, []) = 
    raise IsarTools.meth_exp "IsarLang.Gap.applyf: no goal to gap."
  | applyf (d : T) (pst, (g::gs)) = 
    By.applyf (GapTac.I.dmeth_of d) (pst, (g::gs));

structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = 
            DMethod.pretty_of o GapTac.I.dmeth_of;
        val copy = I;
      end
  );

val gap = NONE : DTechn.T option;
fun plan_gap r = (SOME r) : DTechn.T option;

end;
*)

(* the structure for the Isar element from *)
(* Note same as from, but without forward chaining *)
structure Note =
struct 

val name = "note";

datatype T = note_i of (Thm.thm * DAttrib.T list) list
           | note of (xstring * DAttrib.T list) list;

val copy = I;

fun note_thms (thms) = note_i [(thms, [])];
val note_thm_attrs = note_i;
fun note_names strs = note (map (fn s => (s,[])) strs);
val note_names_atts = note;

(* the apply function, implicit pst *) (* note we use have with no
name or extra attr for the named version *) (* note we make a list of
theorems but only use a string: this is becasue a string already
stands for a list inside isar, although, often the list is a
singleton. *)
fun applyf (note d) (pst, goals) = 
    (Proof.note_thmss
       (map (fn (s,attrs) => 
                (("",[]), [(PureThy.Name s,map DAttrib.src_of attrs)])) d) pst, 
     goals)
  | applyf (note_i d) (pst, goals) = 
    (Proof.note_thmss_i 
       (map (fn (thm,attrs) => 
                (("",[]), [([thm],map DAttrib.ctxt_attrf attrs)])) d) pst, 
     goals);

fun prettyf (note_i d) ctxt = 
    (0, Pretty.block 
          [Pretty.str "note ",
           Pretty.block (pretty_with_ands 
                           (pretty_thm_and_attr ctxt) d)])
  | prettyf (note d) ctxt = 
    (0, Pretty.block 
          [Pretty.str "note ",
           Pretty.block (pretty_with_ands 
                           (pretty_thmnm_and_attr ctxt) d)]);

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;




(* Next isar proof command *)
structure Next =
struct 

val name = "next";

type T = unit;

val copy = I;

fun applyf (d : T) (pst, goals) = step_pair_of_pst (Proof.next_block pst);

fun prettyf d ctxt = (0, Pretty.str "next");

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;




(* "done" isar proof command *)
structure Done =
struct 

val name = "next";
type T = unit;
val copy = I;

fun applyf (d : T) (pst, _) = 
    (case Seq.pull (Proof.local_done_proof pst) of 
       NONE => raise IsarTools.meth_exp "IsarLang.Done.applyf: produced no new states?!"
     | SOME (pst', _) => step_pair_of_pst pst')

fun prettyf d ctxt = (0, Pretty.str "done");

  structure E = 
  PScriptElemFUN( 
    structure K = 
      struct
        type T = T; (* int is state id that strings are for *)
        val name = name;
        val applyf = applyf;
        val prettyf = prettyf;
        val copy = I;
      end
  );

end;




end;




(*
TEST with: 

use "ROOT.ML";

val mythy = (theory "Main");

context mythy;

val mythmdecinfo = 
    (IsarLang.Theorem.mk_init_theorem 
       mythy ("ug", read "Trueprop (a + b = b + (a :: nat))"));

val mypp = IsarLang.Theorem.E.mkplan mythmdecinfo;

fun induct_nmeth s = 
    ("induct \"" ^ s ^ "\"", 
     Method.Basic (Method.method 
                     mythy
                     (Args.src (("induct", [Args.string(s,Position.none)]), 
                                Position.none))));

val my_proofcmd_data = IsarLang.IsarProof.of_named_meth (induct_nmeth "a");

val mypp = IsarLang.IsarProof.E.addstep my_proofcmd_data mypp;

Pretty.writeln (PScript.pretty mypp);
Pretty.writeln (Pretty.chunks (PScript.pretty_last_pst mypp));

*)

