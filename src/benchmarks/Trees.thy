header{* Trees *}

theory Trees
imports Main IsaP

begin


datatype 'a BinTree = Leaf 'a                   
                      | Node "'a BinTree" "'a" "'a BinTree" 


fun treefold :: "('a => 'b => 'b) => 'b => 'a BinTree => 'b" 
where
      treefold_lf: "treefold f b (Leaf data) = f data b"
    | treefold_nd: "treefold f b (Node l data r) = treefold f (treefold f (f data b) l) r"


fun treemap :: "('a => 'b) => 'a BinTree => 'b BinTree"
where
    treemap_lf: "treemap f (Leaf data) = Leaf (f data)"
  | treemap_nd: "treemap f (Node l data r) = Node (treemap f l) (f data) (treemap f r)"



fun mirror :: "'a BinTree => 'a BinTree"
where 
    mirror_lf: "mirror (Leaf data) = Leaf data"
  | mirror_nd: "mirror (Node l data r) = Node (mirror r) data (mirror l)"


datatype 'a BinTree2  = Leaf2 'a                   
                     | Node2 "'a BinTree2" "'a BinTree2" 

fun lr_ord :: "'a BinTree2 => 'a list"
where
    lr_ord_lf: "lr_ord (Leaf2 data) = [data]"
  | lr_ord_nd: "lr_ord (Node2 l r) = (lr_ord l) @ (lr_ord r)"

declare lr_ord_lf[wrule]
declare lr_ord_nd[wrule]

fun rl_ord :: "'a BinTree2 => 'a list"
where
    rl_ord_lf: "rl_ord (Leaf2 data) = [data]"
  | rl_ord_nd: "rl_ord (Node2 l r) = (rl_ord r) @ (rl_ord l)"

declare rl_ord_lf[wrule]
declare rl_ord_nd[wrule]

fun treefold2 :: "('a => 'b => 'b) => 'b => 'a BinTree2 => 'b" 
where
      treefold2_lf: "treefold2 f b (Leaf2 data) = f data b"
    | treefold2_nd: "treefold2 f b (Node2 l r) = treefold2 f (treefold2 f b l) r"

declare treefold2_lf[wrule]
declare treefold2_nd[wrule]



fun in_ord :: "'a BinTree => 'a list"
where
    in_ord_lf: "in_ord (Leaf data) = [data]"
  | in_ord_nd: "in_ord (Node l data r) = (in_ord l) @ [data] @ (in_ord r)"

fun pre_ord :: "'a BinTree => 'a list"
where
    preord_lf: "pre_ord (Leaf data) = [data]"
  | preord_nd: "pre_ord (Node l data r) = data#((pre_ord l) @ (pre_ord r))"

fun postord :: "'a BinTree => 'a list"
where
    postord_lf: "postord (Leaf data) = [data]"
  | postord_nd: "postord (Node l data r) = (postord l) @ (postord r) @ [data]"


fun ltree_size :: "'a list BinTree => nat" 
where 
    ltree_size_lf: "ltree_size (Leaf l) = length l"
  | ltree_size_nd: "ltree_size (Node l d r) =  ltree_size l + length d + ltree_size r" 


lemma "treefold (%a. op + (length a)) 0 t + n = treefold (%a. op + (length a)) n t"
apply (induct t arbitrary: n)
apply simp
proof - 
  fix t1 t2 :: "'a list BinTree"
  fix b :: "'a list"
  fix n :: nat
  assume h1: "!!n. treefold (%a. op + (length a)) 0 t1 + n = treefold (%a. op + (length a)) n t1"
  assume h2: "!!n. treefold (%a. op + (length a)) 0 t2 + n = treefold (%a. op + (length a)) n t2"
  show "treefold (%a. op + (length a)) 0 (Node t1 b t2) + n =
        treefold (%a. op + (length a)) n (Node t1 b t2)"
    apply (unfold treefold_nd)
    apply (subst (1 2) h2[symmetric])
    apply simp
      -- "Observe now that goal = original goal with expression '(length b)'
      (including var b) for an old constant '0'; and '(length b + na)'
      for old n. This inspires the generalisation: 
      'treefold (%a. op + (length a)) x t + n = treefold (%a. op + (length a)) (x + n) t'"
    oops

lemma treefold_add: "treefold (%a. op + (length a)) x t + n = treefold (%a. op + (length a)) (x + n) t"
apply (induct t arbitrary: n x)
apply simp
proof - 
  fix t1 t2 :: "'a list BinTree"
  fix b :: "'a list"
  fix n x :: nat
  assume h1: "!!n x. treefold (%a. op + (length a)) x t1 + n 
    = treefold (%a. op + (length a)) (x + n) t1"
  assume h2: "!!n x. treefold (%a. op + (length a)) x t2 + n 
    = treefold (%a. op + (length a)) (x + n) t2"
  show "treefold (%a. op + (length a)) x (Node t1 b t2) + n
    = treefold (%a. op + (length a)) (x + n) (Node t1 b t2)"
    apply (unfold treefold_nd)
      -- "Note: many other weak fertilisations possible."
    apply (subst nat_add_assoc[symmetric])
    apply (subst (2) h1[symmetric])
    apply (subst h2[symmetric])
    apply simp
    done
qed

lemma treefold_add_0: "treefold (%a. op + (length a)) 0 t + n = treefold (%a. op + (length a)) n t"
apply (subst treefold_add)
apply simp
done

lemma treefold_lemma1: "treefold (%a. op + (length a)) 0 t1 + x + treefold (%a. op + (length a)) 0 t2 =
           treefold (%a. op + (length a)) (treefold (%a. op + (length a)) x t1) t2"
apply (subst treefold_add_0)
 apply (subst nat_add_commute)
  apply (subst treefold_add_0)
  apply simp
done
(*
lemma "treefold (%a. op + (length a)) 0 t1 + length a + treefold (%a. op + (length a)) 0 t2 =
           treefold (%a. op + (length a)) (treefold (%a. op + (length a)) (length a) t1) t2"
*)
lemma "ltree_size t = treefold (%a. op + (length a)) 0 t"
apply (induct t, simp)
proof - 
  fix t1 t2 :: "'a list BinTree"
  fix b :: "'a list"
  assume h1: "ltree_size t1 = treefold (%a. op + (length a)) 0 t1"
  assume h2: "ltree_size t2 = treefold (%a. op + (length a)) 0 t2"
  show "ltree_size (Node t1 b t2) = treefold (%a. op + (length a)) 0 (Node t1 b t2)"
  apply (unfold ltree_size_nd)  
  apply (unfold treefold_nd)
  apply (subst h1)
  apply (subst h2)
  apply (subst treefold_lemma1)  
  apply simp
 done
  (*apply (subst treefold_add)
   apply simp
   apply (subst nat_add_commute)
   apply (subst treefold_add)
   apply simp
done*)
qed

consts len :: "'a list \<Rightarrow> nat"   ("len _" [500] 500)
primrec 
  len_nil[wrule]:     "len [] = 0"
  len_cons[wrule]:    "len (h # t) = Suc (len t)"
declare append_Nil[wrule]
declare append_Cons[wrule]
declare List.rev.simps[wrule]
(*declare List.rev.simps(2)[wrule] *)
declare List.map.simps(1)[wrule]
declare List.map.simps(2)[wrule]
declare List.concat.simps[wrule]
declare foldl_Nil[wrule]
declare foldl_Cons[wrule]
declare List.foldr.simps(1)[wrule] 
declare List.foldr.simps(2)[wrule]
declare in_ord_lf[wrule]
declare in_ord_nd[wrule]
declare postord_lf[wrule]
declare postord_nd[wrule]
declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]

consts rotate :: "nat \<Rightarrow> 'a list => 'a list"
primrec
  rot_zero[wrule]:  "rotate 0 l = l"
  rot_suc[wrule]:   "rotate (Suc n) l = (case l of (h#t) => rotate n (t@[h])
                                                   | [] => [])" 

(*declare List.foldl_append[wrule] *)


(* Need to speculate how fold distribute over @
   "foldr f (xs @ ys) a = foldr f xs (foldr f ys a)" *)
(*
lemma "foldr (%l. op + (len l)) (in_ord t) n = foldr (%l. op + (len l)) (postord t) n"
apply (induct t, simp)
apply (unfold in_ord_nd)
apply (unfold postord_nd)
oops
*)
(* Need this lemma: "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys" *)
lemma "foldl (%a. %l.  a + (len l)) n (in_ord t)  = foldl (%a. %l. a + (len l)) n (postord t)"
apply (induct t arbitrary: n, simp)
proof - 
  fix t1 t2 :: "'a list BinTree"
  fix a :: "'a list"
  fix n :: "nat"
  assume h1: "!!n. foldl (%a l. a + len l) n (in_ord t1) = foldl (%a l. a + len l) n (postord t1)"
  assume h2: "!!n. foldl (%a l. a + len l) n (in_ord t2) = foldl (%a l. a + len l) n (postord t2)"
  show "foldl (%a l. a + len l) n (in_ord (Node t1 a t2)) = foldl (%a l. a + len l) n (postord (Node t1 a t2))"
apply simp
(*apply (unfold in_ord_nd)
apply (unfold postord_nd)
apply (subst (2) foldl_append)
apply (subst h1[symmetric])

apply (subst foldl_append)
apply (subst foldl_append)
apply (subst foldl_append)
apply (subst foldl_append)
apply (subst foldl.simps(2))
apply (subst foldl.simps(1))

apply (subst foldl.simps(2))
apply (subst foldl.simps(1)) *)
oops




lemma "(len l1 = len l2) ==> foldl (%a l. a + len l) (foldl (%a l. a + len l) na l1) l2 =
    foldl (%a l. a + len l) (foldl (%a l. a + len l) na l2) l1"
apply (induct l1 arbitrary: l2 n, simp)
apply simp
oops

lemma "foldl (%a. %l.  a + (len l)) n (lr_ord t)  = foldl (%a. %l. a + (len l)) n (rl_ord t)"
apply (induct t arbitrary: n, simp)
proof - 
  fix t1 t2 :: "'a list BinTree2"
  fix n :: "nat"
  assume h1: "!!n. foldl (%a l. a + len l) n (lr_ord t1) = foldl (%a l. a + len l) n (rl_ord t1)"
  assume h2: "!!n. foldl (%a l. a + len l) n (lr_ord t2) = foldl (%a l. a + len l) n (rl_ord t2)"
  show "foldl (%a l. a + len l) n (lr_ord (Node2 t1 t2)) =
           foldl (%a l. a + len l) n (rl_ord (Node2 t1 t2))"

apply (subst lr_ord_nd)
apply (subst rl_ord_nd)

apply (subst foldl_append)
apply (subst foldl_append)
apply (subst h1)
apply (subst h2)
oops


lemma "foldl (%a l. a + len l) nn (lr_ord t) = foldl (%a l. a + len l) nn (rev (lr_ord t))"
apply (induct t arbitrary: nn, simp)
proof -
 fix t1 t2 :: "'a list BinTree2"
  fix nn :: "nat"
 assume h1: "!!nn. foldl (%a l. a + len l) nn (lr_ord t1) = foldl (%a l. a + len l) nn (rev (lr_ord t1))"
 assume h2: "!!nn. foldl (%a l. a + len l) nn (lr_ord t2) = foldl (%a l. a + len l) nn (rev (lr_ord t2))"
 show "foldl (%a l. a + len l) nn (lr_ord (Node2 t1 t2)) = foldl (%a l. a + len l) nn (rev (lr_ord (Node2 t1 t2)))"
apply (subst lr_ord_nd)
apply (subst lr_ord_nd)

apply (subst foldl_append)
apply (subst h1)
oops

end
