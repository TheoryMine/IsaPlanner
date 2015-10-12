(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_linkinfo.ML
    Author:     Dominic Mulligan, University of Edinburgh
                dpm_edinburgh@yahoo.com
    Created:    17 Aug, 2007
    Modified:   12 Sept 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    This structure maintains the link information during the
    rippling process.

*) 
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RRIPPLE_LINK_INFO =
  sig
      val add_relational_link : (Term.term list * PPlan.gname) list RelationTab.table -> Term.term -> PPlan.gname -> (Term.term list * PPlan.gname) list RelationTab.table;
      val add_relational_links : (Term.term list * PPlan.gname) list RelationTab.table -> (Term.term * PPlan.gname) list -> (Term.term list * PPlan.gname) list RelationTab.table;
      val calculate_min_link_val : (Term.term list * PPlan.gname) list RelationTab.table -> RelationTab.key -> RelationTab.key -> int option;
      val pretty : Proof.context -> (Term.term list * PPlan.gname) list RelationTab.table -> Pretty.T;
  end;

structure RRippleLinkInfo : RRIPPLE_LINK_INFO =
struct

    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (* Relational Rippling Link Info:

       add_relational_link: adds a relation to the relation table,
       ensuring that the table remains symmetric (not necessarily
       transitive, though!)
       Table -> Relation Term -> GoalName -> Table

       calculate_min_link_val: calculates the minimum lengthed path
       between two entries in the table.  If no path exists, returns
       NONE.  This is where the transitivity of connections is taken into
       account.
       Table -> Term -> Term -> int option

    *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

    (* Removes duplicates from a list. *)
    fun nub [] = []
      | nub (h::t) =
        h::(nub (filter (fn x => x <> h) t));

    (* Gets the arguments of a relation, stripping the predicate name. *)
    fun get_args trm =
        let
            val (h,t) = Term.strip_comb trm
        in
            (foldr (op @) [] (map (snd o Term.strip_comb) t))
        end;

    fun add_relational_link table relation_trm gname =
        let
            val vars = nub (get_args relation_trm);
                
            fun add_vars table [] count gname = table
              | add_vars table (h::t) count gname =
                if count = 0 then
                    table
                else
                    let
                        val contained = RelationTab.lookup table h
                    in
                        (case contained of
                             NONE => add_vars (RelationTab.update (h, [(t, gname)]) table) (t@[h]) (count - 1) gname
                           | SOME(x) =>
                             let
                                 val table' = RelationTab.delete h table
                             in
                                 add_vars (RelationTab.update (h, ((t, gname)::x)) table') (t@[h]) (count - 1) gname
                             end)
                    end
        in
            add_vars table vars (length vars) gname
        end

    fun add_relational_links table [] = table
      | add_relational_links table ((trm, nm)::t) =
        add_relational_links (add_relational_link table trm nm) t
    
    fun calculate_min_link_val table left_arg right_arg =
        let
            (* Finds the minimum of a list. *)
            val minlist = foldr (fn (x,y) => if x < y then x else y);

            (* List membership test. *)
            fun member [] item = false
              | member (h::t) item =
                if (h=item) then
                    true
                else
                    member t item

            fun get_all table node =
              let
                val contained = RelationTab.lookup table node
              in
                case contained of
                  NONE => []
                | SOME(x) => foldr (op @) [] (map fst x)
              end

            (* Returns a list of ``children" of a particular node. *)
            fun children table node =
                  let
                    val kids = get_all table node
                  in
                    nub kids
                  end

            (* Breadth first search with some small changes to find minimum paths. *)
            fun breadth_first table [] target count seen buffer = count::buffer
              | breadth_first table (u::toexplore) target count seen buffer =
                if member seen u then
                    breadth_first table toexplore target count seen buffer
                else
                    if member (get_all table u) target then
                        breadth_first table toexplore target (count+1) (u::seen) ((count + 1)::buffer)
                    else
                        if u = target then
                            breadth_first table toexplore target count seen (count::buffer)
                        else
                            let
                                (* val _ = (writeln ("Seeing " ^ (Pretty.string_of (Trm.pretty (the_context ()) u)))) *)
                                val kids = children table u
                            in
                                breadth_first table (kids@toexplore) target (count+1) (u::seen) buffer
                            end
        in
            (* Check whether both nodes are actually in the graph! *)
            if not (RelationTab.lookup table left_arg = NONE) andalso
               not (RelationTab.lookup table right_arg = NONE) then
                let
                    val b = (breadth_first table [left_arg] right_arg 0 [] [])
                in
                    case b of
                        [] => NONE
                      | [x] => SOME x
                      | (h::t) => SOME (minlist h t)
                end
            else
                NONE
        end
        
    fun pretty_trm ctxt t =
        Trm.pretty ctxt t

    fun pretty_trm_lst ctxt l = 
        Pretty.list "[" "]" (map (pretty_trm ctxt) l)
        
    fun pretty_element ctxt (l, g) =
        Pretty.list "(" ")" [pretty_trm_lst ctxt l, Pretty.str g]

    fun pretty_record ctxt (t, e) =
        Pretty.list "(" ")" [pretty_trm ctxt t, Pretty.list "[" "]" (map (pretty_element ctxt) e)]

    fun pretty_lst ctxt lst =
        Pretty.list "[" "]" (map (pretty_record ctxt) lst);

    fun pretty ctxt rtab =
        pretty_lst ctxt (RelationTab.dest rtab);
end;
