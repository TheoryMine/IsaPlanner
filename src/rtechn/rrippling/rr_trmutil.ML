(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_trmutil.ML
    Author:     Dominic Mulligan, University of Edinburgh
                dpm_edinburgh@yahoo.com
    Created:    24th August, 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Utility code for working on terms and embeddings that doesn't really
    fit elsewhere (or I haven't looked hard enough to find it a rightful
    home, yet!).

*) 
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RRTRM_UTIL =
  sig
    exception combinator_exn of string;

    val drop_meta_var_args : Term.term -> Term.term;
    val combinator_name : Term.term -> string;
    val term_info : Term.term -> (string * int);
    val print_term_info : Term.term -> unit;
    val num_args : Term.term -> int;
    val embedding_writeln : RREmbeddingLib.T -> unit;
    val term_writeln : Term.term -> unit;
  end

structure RRTrmUtil : RRTRM_UTIL =
  struct
    exception combinator_exn of string;


    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (* Relational Rippling Term Utilities:

       drop_meta_var_args: removes metavariable arguments from a term.  RR
       embedding requires that these be removed in all ``given" expressions.
       e.g. transforms r (?a b c) (?d e f) --> r ?a ?d
       Term -> Term

       num_args: calculates the number of arguments a relation possesses.
       Term -> Int

       combinator_name: returns the name of the relation itself.  Special
       case when all terms are Free;s - returns first free var in arg list,
       i.e. r a b --> r but x y z \<in> r*** --> rtc3.  Perhaps this isn't
       what we want to do?  Should we return the whole term instead?
       Term -> String

       term_info: returns combinator name and number of arguments of a
       relation.
       Term -> (String * Int)

       print_term_info: prints debugging information giving details of a
       given term.
       Term -> Unit

       embedding_writeln: writes an embedding eterm to standard output.
       Embedding -> Unit

       term_writeln: writes a term to standard output
       Term -> Unit
    *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

    fun drop_meta_var_args (Abs(s,ty,t)) = Abs(s,ty,drop_meta_var_args t)
      | drop_meta_var_args x = 
          let
      val (h,ts) = Term.strip_comb x
    in 
            (case h of 
         (Var (n,ty)) => Var (n, snd (Term.strip_type ty))
       | _ => Term.list_comb (h, map drop_meta_var_args ts))
    end;

    fun num_args trm =
          let
            val trm' = drop_meta_var_args trm

            fun aux (Free(nm, typ)) = 1
              | aux (Var(nm, typ)) = 1
              | aux (Abs(nm, typ, trm'')) = (aux trm'')
              | aux (x $ y) = (aux x) + (aux y)
              | aux z = 0
          in
            aux trm'
          end

    fun combinator_name trm =
          let
            fun try_dest_Trueprop (Const (@{const_name "HOL.Trueprop"}, _) $ T) = T
              | try_dest_Trueprop T = T;

            val comb = (fst o Term.strip_comb o try_dest_Trueprop) trm
          in
            case comb of
              Const(x,y) => x
            | Free(x,y) => x
            | _ => raise combinator_exn "no combinator name - possible malformed term"
          end

    fun term_info trm = (combinator_name trm, num_args trm)

    fun embedding_writeln em =
    Pretty.writeln (RREmbeddingLib.pretty_embedding 
                      (ProofContext.init (the_context())) em);

    fun term_writeln trm =
          Pretty.writeln (Trm.pretty (ProofContext.init (the_context())) trm);

    fun print_term_info trm =
          let
      val _ = writeln ("Term: [" ^ (Pretty.string_of (Trm.pretty (ProofContext.init (the_context())) trm)) ^ "], combinator name: [" ^ 
                      (combinator_name trm) ^ "], number of arguments: [" ^ ((Int.toString o num_args) trm) ^ "].")
          in
            ()
          end
  end;
