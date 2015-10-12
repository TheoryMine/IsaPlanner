(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Generic notion of And-Or-Datatypes  *)
(* IMPROVE: Allow subtypes of and-types *)
signature PPLAN_SPEC = 
sig

type method
type andgsplit

type meth (* situation name = data dname *)
type cname (* case name = data constructor name *)

type ppspec;

val init : ppspec;

val thendo : sname -> ppspec -> sname list * ppspec

val  : 

end;


(* 

induction => [*base_case, *step_case]
simpliciation => [*simplified_goal]
ripple_step => [*condition, *rippling, *blocked]

rippling = ripplestep => [*condition : simplification => !solved,
                          *rippling : rippling,
                          *blocked : [*blocked]]

weak_fert => [*wfert_goal]
strong_fert => !solved
generalisation => [*generalised_goal]

make_lemma => 

fertilisation = orelse{strong_fert => !solved,
                       weak_fert => [*weakfertilisation]}

induct_and_ripple = 
  induction=>[*base_case : simplification => [*unsolved_basecase],
              *step_case :
                rippling => 
                orelse{fertilisation => [*weak_fertilised_stepcase],
                       [*blocked_ripples]}

induct_and_ripple_and_spec = 
  induction=>[*base_case : simplification => [*unsolved_basecase],
              *step_case :
                rippling => 
                orelse{fertilisation => [*weak_fertilised_stepcase],
                       lemma_spec=>[*speculated_lemmas : [*lemmas],
                                    *rippled_steps : rippling]}

induct_ripple_and_conj = 
  induct_and_ripple => 
    [*unsolved_basecase : generalise => induct_ripple_and_conj,
     *weak_fertilised_stepcase : 
     *blocked_ripples :

*)

signature MDATA = 
sig
include DATA
type gname
type state
type methf
type branchf
end;

structure DB_MData = 
struct
open Data;
type gname = PPlan.gname
type state = RState.T
datatype methf = MethF of gname -> state -> state Seq.seq;
datatype branchf = BranchF of (gname list * gname list) * state 
                              -> (gname list * gname list) * (gname list * gname list);
end;

structure MData : MDATA = DB_MData;

(* We interpret methods as or-types and goal dividing functions as
and-types. Thus Proof Plan Specifications are an instance of
Data-Types. Some Invarients for Data rep: all or-types () method and
choice functions start with "m:" and all and-types (branch functions)
start with "bf:".  *)

functor PPlanSpecFun(MData : MDATA)
= struct

type gname = MData.gname;
type state = MData.state;

structure DnTab = UnderData.DnTab;
structure EnTab = UnderData.EnTab;
structure CnTab = UnderData.CnTab;


datatype mspec = Atomic of methf
               | Compound of dname; (* dname must be an method-point in a ppspec that it occurs in *)
datatype ppspec = 
         PPSpec of {graph : MData.dcontext,
                    branchfs : (Pretty.T * MData.branchf) DnTab.T,
                    methfs : (Pretty.T * mspec) DnTab.T
                   };

val init = 
    MData.add_maybedata 
      ("bf:input:", MData.MaybeAnds (EnTab.update ("input_goals:","m:")
                                                  EnTab.empty)
      MData.base_dcx



end;

structure DB_PPlanSpec = PPlanSpecFun(Data);

structure PPlanSpec : PPLAN_SPEC = DB_PPlanSpec;
