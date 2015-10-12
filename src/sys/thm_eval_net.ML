(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/thm_eval_net.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    16 Jun 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Evaluation nets holding theorems

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature THM_EVAL_NET = 
sig

exception thm_eval_net_exp of string;

structure RuleNet : RULE_NET where type RuleData.T = Thm.thm

type rulenet
type evalord

(* type searchfT =
     Sign.sg -> int -> rulenet -> BasicIsaFTerm.FcTerm 
      -> RuleNet.matchT Seq.seq
*)

(* the "(IsaFTerm.Term -> 'a Seq)" part of the second arg is the
low level matching function that checks if the term matches at this
point. ? change the type to give the Ts separately? *)
val mk_evalord : (string * ((IsaFTerm.FcTerm -> RuleNet.matchT Seq.seq) -> 
                            IsaFTerm.FcTerm -> RuleNet.matchT Seq.seq)) 
                  -> evalord

val insert : (Thm.thm * rulenet) -> rulenet
val delete : (Thm.thm * rulenet) -> rulenet
val merge : (rulenet * rulenet) -> rulenet
val new : string * evalord -> rulenet
val empty_copy : rulenet -> rulenet

val evalord_of : rulenet -> evalord
val rules_of : rulenet -> Thm.thm list
val kind_of : rulenet -> SafeObject.kind
val name_of : rulenet -> string

val kind_of_evalord : evalord -> SafeObject.kind
val name_of_evalord : evalord -> string

(* General matching tools - find matches/unifiers below this fcterm *)
val find_fcterm_matches : EQSubstTac.searchinfo -> rulenet 
                          -> RuleNet.matchT Seq.seq
val find_fcterm_unifiers : EQSubstTac.searchinfo -> rulenet
                          -> RuleNet.matchT Seq.seq

val pretty_evalord : evalord -> Pretty.T
val pretty : rulenet -> Pretty.T
val print : rulenet -> unit

end;



(* specific version of the above for thms which looks in a subgoal *)
(* val find_sg_thm_matches : rulenet -> Type.tsig -> (int * Thm.thm) 
                          -> RuleNet.matchT Seq.seq*)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
functor ThmEvalNetFUN (structure EqRuleData : EQRULE_DATA) 
(* : THM_EVAL_NET *)
= struct

exception thm_eval_net_exp of string;

structure RuleNet = RuleNetFUN(structure RuleData = 
struct 
  type T = Thm.thm 
(*   val tsig_of = Sign.tsig_of o Thm.sign_of_thm *)
  val lhs_of = (fst o Logic.dest_equals o Thm.concl_of);
  val eq = Thm.eq_thm
  fun pretty th = 
    Pretty.chunks 
    [ Pretty.block [Pretty.str "Rule: ",
                    Pretty.str (Thm.name_of_thm th)],
      Pretty.indent 2 (Pretty.block [Pretty.str "lhs: ",
                       Sign.pretty_term (Thm.sign_of_thm th) (lhs_of th)]),
      Pretty.indent 2 (Pretty.block [Pretty.str "thm: ",
                                     Display.pretty_thm th])];
end);

datatype evalord = 
         evalord of {kind : SafeObject.kind, 
                     searchf : ((IsaFTerm.FcTerm -> RuleNet.matchT Seq.seq) -> 
                                IsaFTerm.FcTerm -> RuleNet.matchT Seq.seq)}

fun kind_of_evalord (evalord r) = #kind r;
fun name_of_evalord ev = SafeObject.name_of_kind (kind_of_evalord ev);
fun searchf_of_evalord (evalord r) = #searchf r;

fun mk_evalord (s, f) = evalord {kind = SafeObject.kind s, 
                                 searchf = f};

datatype rulenet = rulenet of {kind : SafeObject.kind, (* unique name *)
                               net : RuleNet.T, 
                               evalord : evalord};

fun net_of (rulenet r) = #net r;
fun rules_of (rulenet r) = RuleNet.dest (#net r);
fun kind_of (rulenet r) = #kind r;
fun name_of rn = SafeObject.name_of_kind (kind_of rn);

fun evalord_of (rulenet r) = #evalord r;
fun evalord_name_of (rulenet r) = name_of_evalord (#evalord r);
fun evalord_searchf_of (rulenet r) = searchf_of_evalord (#evalord r);

(* fun set_evalord (e, rulenet r) = 
    rulenet{ kind = #kind r, net = #net r, evalord = e}; *)

(* rulenet operations *) 

(* Note: we encure that all rules in the next have zero var indicies
so that matching lookup only has to incremenet indecies of the rule by
1, once. *)
fun insert (th, rulenet r) = 
    let val meqths = map (fn th => Thm.name_thm (Thm.name_of_thm th,
                                                 Drule.zero_var_indexes th))
                         (EqRuleData.prep_meta_eq th)
    in rulenet {kind = #kind r, 
                net = foldr RuleNet.insert (#net r) meqths, 
                evalord = #evalord r} end;
fun delete (th, rulenet r) = 
    let val meqths = EqRuleData.prep_meta_eq th
    in rulenet {kind = #kind r, 
                net = foldr RuleNet.delete (#net r) meqths,
                evalord = #evalord r} end;
fun new (s, eord) = rulenet {kind = SafeObject.kind s, 
                             evalord = eord, 
                             net = RuleNet.empty};

fun empty_copy (rulenet rn) = rulenet {kind = #kind rn,
                                       evalord = #evalord rn, 
                                       net = RuleNet.empty};

(* should we not check the kind? *)
fun merge (rulenet r1, rulenet r2) = 
    if SafeObject.eq_kind (#kind r1, #kind r2) then 
       rulenet { kind = #kind r1, evalord = #evalord r1, 
                 net = RuleNet.merge (#net r1, #net r2) }
    else raise thm_eval_net_exp "merge";

(* pretty printing *)
fun pretty_evalord eord = Pretty.str (name_of_evalord eord);
fun pretty_rulenet_rules rnet = RuleNet.pretty;

fun pretty (rulenet r)= 
    Pretty.chunks [Pretty.str ("Theorem rulenet: " ^ 
                               (SafeObject.name_of_kind (#kind r))), 
                   Pretty.block [Pretty.str ("Using evalord: "),
                                 pretty_evalord (#evalord r)],
                   Pretty.str ("with rules: "),
                   RuleNet.pretty (#net r)];


val print = Pretty.writeln o pretty;

(* find matches below this particular focus term *) 
(* Assume incrememented indices *)
(* THINK: maybe use a functor to make search functions automatically
   do what IsaFTerm.find_fcterm_matches does. i.e. fake focusterm context *)
(* Note: implicit fcterm *)
fun find_fcterm_matches (thry, maxidx, ft) rnet = 
    IsaFTerm.find_fcterm_matches 
      (evalord_searchf_of rnet)
      (RuleNet.matcher thry (net_of rnet))
      ft;

fun find_fcterm_unifiers (sgn, maxidx, ft) rnet = 
    IsaFTerm.find_fcterm_matches 
      (evalord_searchf_of rnet)
      (RuleNet.unifier (maxidx, sgn) (net_of rnet))
      ft;

end; (* functor *)

structure ThmEvalNet = ThmEvalNetFUN(structure EqRuleData = EqRuleData);
