(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      parser.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Date:       20 Mar 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Parser for reading proof plans  *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature APRF_PARSER
= sig
(* String.explode  *)
end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure APrfParser
= struct

datatype term = Term of Trm.T;
datatype concl = Conc of (APrf.gname * term) * APrf.optmeth;
datatype quantifier = Quantif of Var.pname * (Var.typ option);
datatype result = CResult of (quantifier list * result list) * result list
                | AResult of concl;

fun pretty_quoted_term ctxt (Term t) = Pretty.quote (ProofContext.pretty t);
fun pretty_term ctxt (Term t) = ProofContext.pretty t;

datatype scan_state = ScanState of (Proof.context * string list);



fun LitS s (ScanState (ctxt,slist)) = 
    let val (s,slist) = (Scan.$$ s slist) 
    in (s,ScanState (ctxt,slist)) end;

fun ctxt_map_SF f (ScanState (ctxt,slist)) = ScanState (f ctxt,slist);

fun cx_SF f (st as ScanState (ctxt,slist)) = 
    let val (x,slist2) = f ctxt st
    in (x, ScanState (ctxt, slist2)) end;

fun str_cx_SF f (ScanState (ctxt,slist)) = 
    let val (x,slist2) = f ctxt slist
    in (x, ScanState (ctxt, slist2)) end;

fun str_SF f (ScanState (ctxt,slist)) = 
    let val (x,slist2) = f slist
    in (x, ScanState (ctxt, slist2)) end;


fun quotedS f = ((LitS "\"") |-- f --| (LitS "\""));
fun squaredS f = ((LitS "[") |-- f --| (LitS "]"));
fun parenthS f = ((LitS "(") |-- f --| (LitS ")"));
fun curlydS f = ((LitS "{") |-- f --| (LitS "}"));
fun squared_byS f = ((LitS "[by") |-- f --| (LitS "]"));
fun squared_qmS f = ((LitS "[?") |-- f --| (LitS "]"));

val nameS = str_SF (Scan.some SOME);
val thmS = str_cx_SF (fn ctxt => 
                          (Scan.some SOME) 
                            >> (ProofContext.get_thm ctxt 
                                o PureThy.Name)) ;
val quoted_typS = quotedS (str_cx_SF (fn ctxt => (Scan.some SOME) >> (ProofContext.read_typ ctxt)));
val quoted_termS = 
  quotedS (str_cx_SF (fn ctxt => Scan.some (SOME o ProofContext.read_term ctxt))) >> Term;

val toNamesS = Scan.optional (LitS "to:" |-- Scan.repeat1 (nameS)) [];

val methkind_thmS = (LitS "thm " |-- thmS) >> (APrf.methkind_thm);
val methkind_resS = (LitS "res " |-- nameS) >> (APrf.methkind_res);
val methkind_tacS = (LitS "tac " |-- nameS) >> (APrf.methkind_pretty o Pretty.str);

val methkindS = parenthS (methkind_tacS || methkind_resS || methkind_thmS);

val methS = 
    (squared_byS (methkindS -- toNamesS) >> APrf.optmeth_closed)
      || (squared_qmS (Scan.succeed APrf.optmeth_open));

val conclS = ((nameS --| (LitS ":")) -- quoted_termS) -- methS >> Conc;

val varS = (nameS -- (Scan.optional ((LitS ":") |-- quoted_typS >> SOME) NONE));

val quantifierS = ((LitS "ALL" ) |-- (Scan.repeat varS) --| (LitS ".")) >> (map Quantif);

fun resultS sl = (((((LitS "{" ) |-- ((Scan.optional quantifierS []) 
                                       -- (Scan.repeat resultS)) 
                                --| (LitS "|-"))
                              -- (Scan.repeat resultS) --| (LitS "}"))
                              >> CResult)
                   || (conclS >> AResult)) sl;

end;
