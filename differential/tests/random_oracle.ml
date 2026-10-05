let () =
 Random.init 0;
 for i=0 to 99 do print_endline(string_of_int(Random.bits())) done;
 Random.init (-1);
 for i=0 to 99 do print_endline(string_of_int(Random.int 101)) done
