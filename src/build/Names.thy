theory Names
imports Pure
uses
(* Generic Tools for namers, fresh names tables, and collections *)
(* for creating fresh names, has name suc and pred operation, 
   also nameset with ability to make fresh names. *)
(* "../libs/names/dbg.ML" *) (* function to call for debug tool *)
"../libs/names/namer.ML" 
"../libs/names/namers.ML" (* instances of namer, StrName, etc *)

"../libs/names/basic_nameset.ML" (* basic sets of names *)  
"../libs/names/basic_nametab.ML" (* name tables which provide fresh names *)
"../libs/names/basic_renaming.ML" (* renaming, based on tables and sets *)

(* generic Name structure provies nametables, namesets and collections *)
"../libs/names/basic_names.ML"
"../libs/names/compound_renaming.ML" (* renaming within datatypes *)
"../libs/names/renaming.ML" (* renaming, based on tables and sets *)

(* as above, but with renaming *)
"../libs/names/nameset.ML" 
"../libs/names/nametab.ML" 

(* names + renaming for them *)
"../libs/names/names.ML" 

(* Binary Relations of finite name sets: good for dependencies *)
"../libs/names/name_map.ML" (* functions/mappings on names *)
"../libs/names/name_inj.ML" (* name iso-morphisms *)
"../libs/names/name_injendo.ML" (* name auto-morphisms (name iso where dom = cod) *)
"../libs/names/name_binrel.ML" (* bin relations on names *)

"../libs/names/umorph.ML" (* bin relations on names *)

begin 

end;