header{* Trees *}

theory Tree
imports Main IsaP

begin

datatype 'a BinTree = Leaf 'a                   
  | Node "'a BinTree" "'a" "'a BinTree" 

fun mirror :: "'a BinTree => 'a BinTree"
where 
    mirror_lf: "mirror (Leaf data) = Leaf data"
  | mirror_nd: "mirror (Node l data r) = Node (mirror r) data (mirror l)"
declare mirror_lf[wrule]
declare mirror_nd[wrule]

fun pre_ord :: "'a BinTree => 'a list"
where
    preord_lf: "pre_ord (Leaf data) = [data]"
  | preord_nd: "pre_ord (Node l data r) = data#((pre_ord l) @ (pre_ord r))"
declare preord_lf[wrule]
declare preord_nd[wrule]

fun post_ord :: "'a BinTree => 'a list"
where
    postord_lf: "post_ord (Leaf data) = [data]"
  | postord_nd: "post_ord (Node l data r) = 
                  (post_ord l) @ (post_ord r) @ [data]"
declare postord_lf[wrule]
declare postord_nd[wrule]

fun in_ord :: "'a BinTree => 'a list"
where
    in_ord_lf: "in_ord (Leaf data) = [data]"
  | in_ord_nd: "in_ord (Node l data r) = (in_ord l) @ [data] @ (in_ord r)"
declare in_ord_lf[wrule]
declare in_ord_nd[wrule]


(* Import some nat and list functions *)
consts len :: "'a list => nat"   ("len _" [500] 500)
primrec 
  len_nil[wrule]:     "len [] = 0"
  len_cons[wrule]:    "len (h # t) = Suc (len t)"

declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.inject[wrule]
declare List.append.simps[wrule]
declare List.rev.simps[wrule]
declare List.foldl.simps[wrule]

end;
