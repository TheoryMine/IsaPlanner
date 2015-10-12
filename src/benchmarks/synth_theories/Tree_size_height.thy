header{* Test Synthesis on Trees *}

theory Tree_size_height

imports Main IsaP
begin

(* Add some common rules for Naturual numbers as wrules.*)
declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.add_0_right[wrule]
declare Nat.add_Suc_right[wrule]
declare Nat.nat_add_assoc[wrule]

datatype 'a Tree = 
    Leaf
  | Node "'a Tree" "'a" "'a Tree"

fun mirror ::"'a Tree \<Rightarrow> 'a Tree"
where
    mirror_leaf: "mirror Leaf = Leaf"
  | mirror_node: "mirror (Node l data r) = Node (mirror r) data (mirror l)"
declare mirror_leaf[wrule]
declare mirror_node[wrule]

fun nodes :: "'a Tree \<Rightarrow> nat"
where
    nodes_leaf: "nodes Leaf = 0"
  | nodes_node: "nodes (Node l data r) = 
                     (Suc 0) + nodes l + nodes r"
declare nodes_leaf[wrule]
declare nodes_node[wrule]

 fun max :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
    max_0: "max 0 y = y"
  | max_suc: "max (Suc x) y = (case y of 0 => (Suc x) | Suc z => Suc(max x z))"
declare max_0[wrule]
declare max_suc[wrule]

fun height :: "'a Tree \<Rightarrow> nat"
where
  height_leaf: "height Leaf = 0"
  | height_node: "height (Node l data r) = Suc(max (height l) (height r))"
declare height_leaf[wrule]
declare height_node[wrule]

end