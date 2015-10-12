theory HOLemSpec
imports Main IsaP
begin
declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.inject[wrule]

declare List.append.simps[wrule]
declare List.rev.simps[wrule]
declare List.map.simps[wrule]
declare List.concat.simps[wrule]
declare foldl_Nil[wrule]
declare foldl_Cons[wrule]

fun maps :: "('a => 'b list) => ('a list => 'b list)"
where
  maps_nil:   "maps f [] = []" |
  maps_cons:  "maps f (h#t) = (f h) @ (maps f t)"
declare maps_nil[wrule]
declare maps_cons[wrule]

consts len :: "'a list => nat"   ("len _" [500] 500)
primrec 
  len_nil[wrule]:     "len [] = 0"
  len_cons[wrule]:    "len (h # t) = Suc (len t)"


end;
