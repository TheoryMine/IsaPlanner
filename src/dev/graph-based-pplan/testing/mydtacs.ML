fun induct_dtac s = 
    DTac.mk (Pretty.str ("induct " ^ s), 
             induct_tac s 1);