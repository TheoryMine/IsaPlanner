(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/isar_meths.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    the basic and generic Isar language Methods, in a declarative form
*)

structure IsarMeths = 
struct
exception isar_meths_exp of string;


(* Skip tactic - assumes SkipMeth has been loaded *)
structure Skip = 
struct

  val name = "skip"

  type T = unit;

  fun prettyf () ctxt = Pretty.str ("skip");
  fun textf () ctxt = Method.Basic (SkipMeth.meth); 
  (*       (Method.method (ProofContext.theory_of ctxt)
                       (Args.src (("skip", []), Position.none))); *)

  structure I = 
    DMethodInstFUN(
      structure K = 
      struct
        type T = T;
        val name = name;
        val textf = textf;
        val prettyf = prettyf;
      end)

  val skip = I.dmeth_of ();

end; (* skip *)



(* trivial method "-" *)
structure Triv = 
struct

  val name = "triv"

  type T = unit;

  fun prettyf () ctxt = Pretty.str ("-");
  fun textf () ctxt = 
      Method.Basic 
        (Method.method (ProofContext.theory_of ctxt)
                       (Args.src (("-", []), Position.none)));

  structure I = 
    DMethodInstFUN(
      structure K = 
      struct
        type T = T;
        val name = name;
        val textf = textf;
        val prettyf = prettyf;
      end)

  val trivmeth = I.dmeth_of ();

end; (* triv *)

(* the "rule" method... *)
structure Rule = 
struct

  val name = "rule"

  (* copied from Method.ML ... and added the CHANGED thing*)
  fun meth' tac x y = Method.METHOD (CHANGED_PROP o HEADGOAL o tac x y); 
  val some_rule = meth' Method.some_rule_tac;

  (* data that is used by rule *)
  datatype T = dthm of DThm.T

  (* pretty and text building functions... *)
  fun prettyf (dthm d) ctxt = 
      Pretty.block [Pretty.str "rule ", DThm.pretty d];

  fun textf (dthm d) ctxt = 
      Method.Basic (some_rule [DThm.finalthm_of d]);

  (* make the generic method tools *)
  structure I = 
    DMethodInstFUN(
      structure K = 
      struct
        type T = T;
        val name = name;
        val textf = textf;
        val prettyf = prettyf;
      end)

  fun rule dth = I.dmeth_of (dthm dth);

  fun rule_th th = rule (DThm.mk (th,[]));

end; (* Rule *)




(* We can allow a technque to directly 'fake' a declarative method,
this allows us to cheet by using knowledge about the result of a
method - so we give a prtetty printing function separately from the
actualy Method.text that is applied - in order that the Method.text
can save on computation. For this to be a valid step we must be sure
that the method is applied in a setting where the faked method
inlcudes the actualy method, and where the search is actually
performed. i.e. a "by" not an "apply" *)

structure Fake = 
struct

  val name = "fake"

  (* rule using the following rules... *)
  type T = {prettyf : Proof.context -> Pretty.T,
            textf : Proof.context -> Method.text};

  fun prettyf d ctxt = (#prettyf d) ctxt;
  fun textf d ctxt = (#textf d) ctxt;

  (* make the generic method tools *)
  structure I = 
    DMethodInstFUN(
      structure K = 
      struct
        type T = T;
        val name = name;
        val textf = textf;
        val prettyf = prettyf;
      end)

  (* generic consrtuctors *)
  fun mkfake x = x : T;

end; (* Fake *)



end; (* IsarMeths *)
