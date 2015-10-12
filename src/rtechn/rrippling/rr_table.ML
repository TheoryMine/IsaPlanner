(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_table.ML
    Author:     Dominic Mulligan, University of Edinburgh
                dpm_edinburgh@yahoo.com
    Created:    17th August, 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Tables are used in the relational rippling heuristic to store
    information on how variables are related through relations, and
    also to infer the modality data for relational arguments.
    The following code implements a generic table, where entries (V)
    are indexed by a key value (K).  A key may refer to multiple
    values in the table.  Keys must have an ordering provided.

    Not needed in the end.  Included as it defines the RelationTab.

*) 
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

structure RelationTab =
  Table(type key = Term.term
           fun ord(Free(a,b),Free(c,d)) = (* Better ordering needed, perhaps! *)
           if a=c then EQUAL else if a < c then LESS else GREATER
             | ord(a,b) =
                 if a=b then EQUAL else LESS);

(*
signature RRIPPLE_TABLE =
  sig
    type K
    type V
    type T

    val empty : T
    val contains : T -> K -> V -> bool
    val contains_key : T -> K -> bool
    val contains_value : T -> V -> bool
    val get_all : T -> K -> V list
    val add : T -> K -> V -> T
    val delete : T -> K -> V -> T
    val merge : T -> T -> T
    val merge_list : T list -> T
    val to_string: T -> string
  end

functor BinaryTreeRippleTableFUN (
  type K
  type V
  val ordk: K * K -> order
  val ordv: V * V -> order
  val k_to_string: K -> string
  val v_to_string: V -> string
) : RRIPPLE_TABLE where type K=K and type V=V =
  struct
    type K = K
    type V = V
    datatype T = Empty | Branch of T * (K * V) * T
  
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
    (* Relational Rippling Table:

       DESCRIPTION:

       Tables are stored as binary search trees, with the nodes being
       labeled as a K * V pairing.  The tree is ordered by the ordering
       on K, where K values of lesser or equal value are stored to the left
       of a given node, and K values of greater value are stored to the 
       left.
       Does not admit duplicate entries.

       contains: checks whether key-value pair is stored in table.
       Table -> Key -> Value -> Bool

       contains_key: checks whether a particular key is stored in the
       table.
       Table -> Key -> Bool

       contains_value: checks whether a particular value is stored in
       the table.
       Table -> Value -> Bool

       get_all: returns all values indexed by a particular key.
       Table -> Key -> Value list

       add: adds a key-value pairing to the table - not added if already
       stored in table.
       Table -> Key -> Value -> Table

       merge: merges two tables into a single one.
       Table -> Table -> Table

       merge_list: merges several tables into a single one.
       Table list -> Table
 
       delete: deletes a key-value pairing from the table, returning same
       table if not contained.
       Table -> Key -> Value -> Table

       to_string: self-explained.
       Table -> string

    *)
    (* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

    val empty = Empty;

    fun contains Empty key value = false
      | contains (Branch(a,(k,v),b)) key value =
          if ordk(k,key)=EQUAL andalso ordv(v,value)=EQUAL then true
          else
            case ordk(key,k) of
              GREATER => contains b key value
            | _ => contains a key value

    fun contains_key Empty key = false
      | contains_key (Branch(a,(k,v),b)) key =
          if ordk(k,key)=EQUAL then true
          else
            case ordk(key,k) of
              GREATER => contains_key b key
            | _ => contains_key a key

    fun contains_value Empty value = false
      | contains_value (Branch(a,(k,v),b)) value =
          if ordv(v,value) = EQUAL then true
          else (contains_value a value) orelse (contains_value b value)

    fun get_all Empty key = []
      | get_all (Branch(a,(k,v),b)) key =
          if ordk(k,key)=EQUAL then (v::(get_all a key)@(get_all b key))
          else ((get_all a key)@(get_all b key))

    fun add Empty key value = Branch(Empty, (key, value), Empty)
      | add (br as Branch(a,(k,v),b)) key value =
          case ordk(key,k) of
            GREATER => Branch(a,(k,v), add b key value)
          | EQUAL =>
            (case ordv(v,value) of
               EQUAL => br
             | _ => Branch(add a key value,(k,v),b))
          | LESS => Branch(add a key value,(k,v),b)

    fun merge Empty r = r
      | merge l Empty = l
      | merge (Branch(Empty,(k1,v1),Empty)) (Branch(Empty,(k2,v2),Empty)) =
          (case ordk(k1,k2) of
            GREATER => (Branch(Empty,(k1,v1),(Branch(Empty,(k2,v2),Empty))))
          | _ => (Branch((Branch(Empty,(k1,v1),Empty)),(k2,v2),Empty)))
      | merge (l as Branch(a1,(k1,v1),b1)) (r as Branch(a2,(k2,v2),b2)) =
          (case ordk(k1,k2) of
            GREATER => Branch(merge a1 r,(k1,v1),b1)
          | _ => Branch(a2,(k2,v2),merge l b2))

    fun merge_list list = foldr (fn(x,y) => merge x y) Empty list;
  
    fun delete Empty key value = Empty
      | delete (b as Branch(Empty,(k,v),Empty)) key value =
          if ordk(k,key)=EQUAL andalso ordv(v,value)=EQUAL then Empty
          else b
      | delete (br as Branch(l,(k,v),r)) key value =
          (case ordk(key,k) of
            GREATER => Branch(l,(k,v),delete r key value)
          | EQUAL =>
            (case ordv(v,value) of
               EQUAL => (merge l r)
             | _ => Branch(delete l key value,(k,v),delete r key value))
          | LESS => Branch(delete l key value,(k,v),r))

    fun to_string Empty = "Empty"
      | to_string (Branch(a,(k,v),b)) =
          "Branch(" ^ (to_string a) ^ "," ^ "(" ^ (k_to_string k) ^ "," ^ (v_to_string v) ^ ")" ^ "," ^ (to_string b) ^ ")"
  end

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* The relational table.
   Key types are term types, values are (term list * gname) pairs.
   Table's internal format looks like this:

   "a" --> (["b", "c"], "goal1"),
       ...
   "b" --> (["c", "a"], "goal2"),
       ...

   type K = Term.term
   type V = Term.term list * PPlan.gname

   We don't need to store the table in a transitive format (although
   it is stored in a symmetric format).  Just ensure that looking up a
   path in the table takes transitivity into account.
*)
structure RelationTab =
  BinaryTreeRippleTableFUN(type K = Term.term
                           type V = (Term.term list * PPlan.gname)
                           fun ordk(x,y) = (if x=y then EQUAL else LESS)
                           fun ordv((a,b),(c,d)) =
                             let
                               fun help [] [] = EQUAL
                                 | help _ [] = GREATER
                                 | help [] _ = LESS
                                 | help (h1::t1) (h2::t2) =
                                     (case ordk(h1,h2) of
                                       EQUAL => help t1 t2
                                     | x => x)
                             in
                               (case (help a c) of
                                 EQUAL => (if b=d then EQUAL else if b<d then LESS else GREATER)
                               | x => x)
                             end
                           val k_to_string = (Pretty.str_of) o (Trm.pretty (the_context()))
                           val v_to_string = fn(x,y) => "([ " ^ (foldr (fn(x,y) => x ^ " " ^ y) "" (map ((Pretty.str_of) o (Trm.pretty (the_context()))) x)) ^ "], " ^ y ^ ")");
*)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* UNIT TESTS.                                                       *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
