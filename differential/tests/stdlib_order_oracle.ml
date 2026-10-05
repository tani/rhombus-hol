module S=Set.Make(Int)
module M=Map.Make(Int)
let keys=[7;2;9;1;5;8;3;6;4]
let s=List.fold_left (fun s k->S.add k s) S.empty keys
let m=List.fold_left (fun m k->M.add k (10*k) m) M.empty keys
let trace name visit =
 print_string (name^":");visit (fun k->print_int k;print_char ',');print_newline()
let ()=trace "set_exists" (fun f->ignore(S.exists (fun k->f k;false) s))
let ()=trace "set_for_all" (fun f->ignore(S.for_all (fun k->f k;true) s))
let ()=trace "map_exists" (fun f->ignore(M.exists (fun k _->f k;false) m))
let ()=trace "map_merge" (fun f->ignore(M.merge (fun k x _->f k;x) m m))
