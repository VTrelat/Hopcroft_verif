(*
#directory "/home/tuerk/cava/Automata_Malik_Tuerk/implementation/code/OCaml/_build/";;
#directory "/home/tuerk/cava/Automata_Malik_Tuerk/implementation/code/OCaml/";;
#load "nums.cma";;
#load "unix.cma";;
#load "Automata_Export.cmo";;
#load "Automata.cmo";;
#load "hopcroft_modified.cmo"
*)

open Automata.NFA_string 
open Hopcroft_modified

let measure_compare s1 f1 s2 f2 (st_no, l_no, nfa1, nfa2) =
  let _ = Gc.full_major () in
  let st = Sys.time() in
  let r' = f1 nfa1 in
  let et = Sys.time() in
  let t1 = et -. st in

  let _ = Gc.full_major () in
  let st = Sys.time() in
  let _ = f2 nfa2 in
  let et = Sys.time() in
  let t2 = et -. st in

  let st_no' = Big_int.int_of_big_int (nfa_states_no r') in
  print_string (string_of_int st_no');
  print_string " / ";
  print_string (string_of_int st_no);
  print_string " states: ";
  print_string (string_of_int l_no);
  print_string " labels: ";
  print_string (s1 ^ (string_of_float t1) ^ " s   -   ");
  print_string (s2 ^ (string_of_float t2) ^ " s\n")



let measure_compare_simple s1 f1 s2 f2 (st_no, nfa) =
    measure_compare s1 f1 s2 f2 (st_no, 0, nfa, nfa)

let measure_single s1 f1 (st_no, nfa) =
  let _ = Gc.full_major () in
  let st = Sys.time() in
  let _ = f1 nfa in
  let et = Sys.time() in
  let t1 = et -. st in

  print_string (string_of_int st_no);
  print_string " states: ";
  print_string (s1 ^ (string_of_float t1) ^ " s\n");
  flush stdout


(* compare Hopcroft and Brzozowski *)

let minimise_NFA_compare =
  measure_compare_simple "Brzozowski " nfa_Brzozowski
     "Hopcroft NFA " nfa_Hopcroft_NFA;;

let minimise_DFA_compare =
    measure_compare_simple "Brzozowski " nfa_Brzozowski
     "Hopcroft DFA " nfa_Hopcroft

let determinise_measure =
  measure_single "determinise " nfa_determinise

let hopcroft_NFA_measure =
  measure_single "Hopcroft NFA " nfa_Hopcroft_NFA

let hopcroft_ICDFA_measure =
  measure_single "Hopcroft DFA " nfa_Hopcroft

let brzozowski_measure =
  measure_single "Brzozowski " nfa_Brzozowski


(* Generate some random NFAs 
   generate_random_NFAs #NFAs #states #labels #density #desity_accepting
*)

let hopcroft_ICDFA_FM_measure nfafun =
  let nfa = nfafun() in
  let nfa' = nfa_determinise nfa in
  let (q, a, d, i, f) = nfa_destruct_simple nfa' in
  let st_no = List.length q in
  let l_no = List.length a in
  let fm = build_automaton (q, a, d, i, f) in

  let _ = Gc.full_major () in
  let st = Sys.time() in
  let r' = nfa_Hopcroft nfa' in
  let et = Sys.time() in
  let t1 = et -. st in

  let _ = Gc.full_major () in
  let st = Sys.time() in
  let _ =  hopcroft fm in
  let et = Sys.time() in
  let t2 = et -. st in

  let st_no' = Big_int.int_of_big_int (nfa_states_no r') in
  print_string (string_of_int st_no');
  print_string " / ";
  print_string (string_of_int st_no);
  print_string " states: ";
  print_string (string_of_int l_no);
  print_string " labels: ";
  print_string ("Tuerk " ^ (string_of_float t1) ^ " s - ");
  print_string ("Baclet " ^ (string_of_float t2) ^ " s\n");
  flush stdout;;


let hopcroft_ICDFA_FM_measure_pres pf =
  let nfa = Automata.Presburger.pf_to_DFA pf in
  let _ = print_string "XXX" in
  let _ = flush stdout in
  let (q, a, d, i, f) = Automata.NFA_bool_list.nfa_destruct_simple nfa in
  let st_no = List.length q in
  let l_no = List.length a in
  let _ = print_string "XXX" in
  let _ = flush stdout in
  let fm = build_automaton (q, a, d, i, f) in

  let _ = Gc.full_major () in
  let st = Sys.time() in
  let r' = Automata.NFA_bool_list.nfa_Hopcroft nfa in
  let et = Sys.time() in
  let t1 = et -. st in

  let _ = Gc.full_major () in
  let st = Sys.time() in
  let _ =  hopcroft fm in
  let et = Sys.time() in
  let t2 = et -. st in

  let st_no' = Big_int.int_of_big_int (Automata.NFA_bool_list.nfa_states_no r') in
  print_string (string_of_int st_no');
  print_string " / ";
  print_string (string_of_int st_no);
  print_string " states: ";
  print_string (string_of_int l_no);
  print_string " labels: ";
  print_string ("Tuerk " ^ (string_of_float t1) ^ " s - ");
  print_string ("Baclet " ^ (string_of_float t2) ^ " s\n");
  flush stdout;;

let measure_gen f a =
  let _ = Gc.full_major () in
  let st = Sys.time() in
  let r = f a in
  let et = Sys.time() in
  let t1 = et -. st in
  t1


let normalise_NFA nfa =
  let nfa' = nfa_normalise nfa in
  let st_no = nfa_states_no nfa' in
  (Big_int.int_of_big_int st_no, nfa')

let normalise_DFA (n, nfa) =
  let nfa' = nfa_determinise nfa in
  let st_no = nfa_states_no nfa' in
  (Big_int.int_of_big_int st_no, nfa')


let normalise_DFA_FM (_, nfa) =
  let nfa' = nfa_determinise nfa in
  let (q, a, d, i, f) = nfa_destruct_simple nfa' in
  let st_no = List.length q in
  let l_no = List.length a in
  let fm = build_automaton (q, a, d, i, f) in
  (st_no, l_no, nfa', fm)


let count_states nfa =
  let st_no = nfa_states_no nfa
  in (Big_int.int_of_big_int st_no, nfa)


open Scanf 

let start_DFA c = fscanf c "%cDFA" (fun x -> ());;

let rec read_int_list l c =
  try
    fscanf c "%[' ']%d" (fun _ x -> read_int_list (x::l) c)
  with Scan_failure _ -> 
    fscanf c "\n" (List.rev l)

let read_trans c =
  fscanf c "%d %d %d " (fun x y z -> (x, y, z))


let rec read_trans_list l c =
  try
    read_trans_list ((read_trans c) :: l) c
  with Scan_failure _ -> (List.rev l)

let read_DFA c =
  let _ = start_DFA c in
  let f = read_int_list [] c in
  let d = read_trans_list [] c in
  (f, d)

let read_DFA_file file = 
  let in_file = open_in file in
  let rec read_DFAs l c = try
    read_DFAs ((read_DFA c) :: l) c
    with End_of_file -> (List.rev l) in
  let dfas = read_DFAs [] in_file in
  let _ = close_in in_file in
  dfas


let input_to_fm_DFA (f, d) = 
  let dfa = dfa_construct ([], [],
      List.map (fun (q1, a, q2) -> (q1, [Automata.Sigma_Param_string.int_to_sigma a], q2)) d, [0], f) in
  let (q, a, d, i, f) = nfa_destruct_simple dfa in
  let fm = build_automaton (q, a, d, i, f) in
  (fm, dfa)

let file = "../Automata_10000_100_2.txt"

let measure_gen_list f l = measure_gen (fun () -> List.fold_left (fun _ x -> (f x; ())) () l)

let measure_input_file file =
  let input_dfas = read_DFA_file file in
  let _ = print_string ("input parsed\n") in
  let fm_DFA_list = List.map input_to_fm_DFA input_dfas in
  let fm_list = List.map fst fm_DFA_list in
  let dfa_list = List.map snd fm_DFA_list in
  let _ = print_string ("input interpreted\n") in
  let tt = measure_gen_list nfa_Hopcroft dfa_list () in
  let tb = measure_gen_list hopcroft fm_list () in
  print_string ("Tuerk " ^ (string_of_float tt) ^ " s - ");
  print_string ("Baclet " ^ (string_of_float tb) ^ " s\n");;


let int_list_to_string il =
  "[" ^
  (String.concat ", " (List.map string_of_int il))
  ^ "]";;

let triple_to_string (a, b, c) =
  "(" ^ (string_of_int a) ^ ", "^(string_of_int b)^ ", " ^  (string_of_int c) ^  ")";;

let dfa_to_string (f, d) =
  "(" ^ (int_list_to_string f) ^ ", [" ^
   (String.concat ", " (List.map triple_to_string d)) ^ "])"

let dfa_to_ml dfa =
  "val _ = l := (" ^ (dfa_to_string dfa) ^ ") :: !l;\n"

let dfas_to_string dfas =
  "val l = ref []\n" ^
  (String.concat "" (List.map dfa_to_ml dfas)) ^
  "\nval dfas = rev (!l);\n"

let dfas_from_file file = print_string (dfas_to_string (read_DFA_file file));;


let measure_input_file file =
  let input_dfas = read_DFA_file file in
  let _ = Gc.full_major () in
  let _ = print_string ("input parsed\n") in
  let fm_DFA_list = List.map input_to_fm_DFA input_dfas in
  let fm_list = List.map fst fm_DFA_list in
  let dfa_list = List.map snd fm_DFA_list in
  let _ = print_string ("input interpreted\n") in
  let _ = Gc.full_major () in
  let tt = measure_gen (fun () -> List.map nfa_Hopcroft dfa_list) () in
  let _ = Gc.full_major () in
  let tb = measure_gen (fun () -> List.map hopcroft fm_list) () in
  (print_string ("Tuerk " ^ (string_of_float tt) ^ " s - ");
   print_string ("Baclet " ^ (string_of_float tb) ^ " s\n"));;



let arg=Sys.argv;;
(*dfas_from_file (arg.(1)) 
*)


measure_input_file (arg.(1)) 

(*

let _measure_pres pf =
  let nfa = Automata.Presburger.pf_to_DFA pf in
  let _ = print_string "XXX" in
  let _ = flush stdout in
  let (q, a, d, i, f) = Automata.NFA_bool_list.nfa_destruct_simple nfa in
  let st_no = List.length q in
  let l_no = List.length a in
  let _ = print_string "XXX" in
  let _ = flush stdout in
  let fm = build_automaton (q, a, d, i, f) in


let input_file = open_in "/home/tuerk/kkk";;

read_DFA input_file

start_DFA flux
read_int_list [] flux
read_int_list_list [] flux
read_newline flux



print_string "Enter a string: ";
let str = read_line () in
  print_string "Enter an integer: ";
  let num = read_int () in
    Printf.printf "%s%d\n" str num


fun scan_int s = 
sscanf "22 3 4" "%d %l" (fun x s -> (x, s))


open Automata.Presburger
let free_example = 
  pres_And (
    pres_Le ([3; -3; 2; 1; 5; 8; 45; 5], 7),
    pres_Eq ([1; -3; 4; 3; 7; 14; 3; 4], 9));;

hopcroft_ICDFA_FM_measure_pres free_example;;






let _ = Random.self_init();;
let arg=Sys.argv;;
let no = int_of_string(arg.(1));;
let st_no = int_of_string(arg.(2));;
let l_no = int_of_string(arg.(3));;
let den = float_of_string(arg.(4));;
let fden = float_of_string(arg.(5));;
let iden = float_of_string(arg.(6));;


let nfafun () = nfa_normalise (List.hd (generate_random_NFAs 1 st_no l_no den fden iden));;

for i = 1 to no do (hopcroft_ICDFA_FM_measure nfafun) done;;




let random_NFAs___Hopcroft2 = (List.map normalise_NFA (generate_random_NFAs no st_no l_no den fden iden));;
let random_NFAs___Hopcroft2_DFA_FM = (List.map normalise_DFA_FM random_NFAs___Hopcroft2)

let nfa = snd (List.hd random_NFAs___Hopcroft2)
;;
let _ = List.map hopcroft_ICDFA_FM_measure random_NFAs___Hopcroft2_DFA_FM;;
let _ = print_string "\n";;


let fib n=
  let rec aux n a b=
    if n=0 then a else aux (n-1) b (a^b) in
  aux n "1" "0";;

let fib_automaton n =
  let test=fib n in
  let m = String.length test in
  let trans i = (i mod m, ["a"], (i+1) mod m) in
  let rec transL i = if i = 0 then [] else (trans (i-1)) :: (transL (i-1)) in
  let rec acceptL i = if i = 0 then [] else 
       (if test.[i-1]='1' then ((i-1) :: (acceptL (i-1))) else (acceptL (i-1))) in
  nfa_construct ([], [], transL m, [0], acceptL m)

let x = hopcroft_ICDFA_measure (2, fib_automaton 20)

*)



