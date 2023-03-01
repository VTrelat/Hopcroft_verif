(*
#directory "/home/tuerk/cava/Automata_Malik_Tuerk/implementation/code/OCaml/_build/";;
#directory "/home/tuerk/cava/Automata_Malik_Tuerk/implementation/code/OCaml/";;
#load "nums.cma";;
#load "unix.cma";;
#load "Automata_Export.cmo";;
#load "Automata.cmo";;
*)

open Automata.NFA_bool_list
open Automata.Presburger

(* Examples *)
let stamp = pres_Forall (pres_Imp (pres_Le ([-1], -8), pres_Exist
  (pres_Exist (pres_Eq ([5; 3; -1], 0)))))

let example = pres_Forall (pres_Exist (pres_Or (pres_Eq ([1; -1], 5),
  pres_Forall (pres_Forall (pres_Imp (pres_Neg (pres_Le ([-1; 0],
  -6)), pres_Imp (pres_Eq ([1; 6; 0; -1], 0), pres_Eq ([0; 1],
  1))))))))

let example2 = pres_Forall (pres_Forall (pres_Forall (pres_Imp
  (pres_Neg (pres_Le ([-1], -2)), pres_Imp (pres_Eq ([1; 2; -1], 1),
  pres_Forall (pres_Forall (pres_Imp (pres_Neg (pres_Le ([-1], -2)),
  pres_Imp (pres_Eq ([1; 2; 0; 0; -1], 0), pres_Imp (pres_Exist
  (pres_Eq ([2; 0; 0; 0; 0; -1], 0)), pres_Eq ([0; 1; 0; -1],
  0)))))))))))

let harrison1 = pres_Exist (pres_Forall (pres_Imp (pres_Le
  ([-1; 1], 0), pres_Exist (pres_Exist (pres_And (pres_Le ([0; -1],
  0), pres_And (pres_Le ([-1], 0), pres_Eq ([8; 3; -1], 0))))))))

let harrison2 = pres_Exist (pres_Forall (pres_Imp (pres_Le
  ([-1; 1], 0), pres_Exist (pres_Exist (pres_And (pres_Le ([0; -1],
  0), pres_And (pres_Le ([-1], 0), pres_Eq ([8; 7; -1], 0))))))))

let stamp_false = pres_Forall (pres_Imp (pres_Le ([-1],
  (-7)), pres_Exist (pres_Exist (pres_Eq ([5; 3; -1], 0)))))

let example2_false = pres_Forall (pres_Forall (pres_Forall
  (pres_Imp (pres_Neg (pres_Le ([-1], -2)), pres_Imp (pres_Eq ([1; 2;
  -1], 1), pres_Forall (pres_Forall (pres_Imp (pres_Neg (pres_Le
  ([-1], -2)), pres_Imp (pres_Eq ([1; 2; 0; 0; -1], 0), pres_Imp
  (pres_Exist (pres_Eq ([3; 0; 0; 0; 0; -1], 0)), pres_Eq ([0; 1; 0;
  -1], 0)))))))))))

(*

(* Play around with "example" *)

let _ = print_string (pf_to_string example)
let example_DFA = pf_to_DFA example

(* Automata look boring, because they are minimal and only interested 
   in input [] *)
let _ = show_NFA (Some "example") example_DFA


(* lets eletuate it using my translation and the one from AFP *)
let example_valid = eval_pf_DFA example
let example_valid2 = eval_pf_dfa example

*)

let rec repeat n f p = if (n < 2) then f p else (f p; repeat (n-1) f p)

let bool_to_string b = if b then "True" else "False"

let measure_fun (s, p) =
  let _ = print_string (s^"\n") in
  let _ = print_string (pf_to_string p) in
  let _ = print_string "\n" in
  let _ = flush stdout in

  let _ = Gc.full_major () in
  let st = Sys.time() in
  let _ = repeat 999 eval_pf_DFA p in
  let et = Sys.time() in
  let t1 = string_of_float (et -. st) in

  let _ = Gc.full_major () in
  let st = Sys.time() in
  let _ = repeat 999 eval_pf_dfa p in
  let et = Sys.time() in
  let t2 = string_of_float (et -. st) in

  let _ = print_string ("DFA: "^t1^" s - "^"dfa: "^t2^" s\n\n") in
  let _ = flush stdout in
  ()


let examples = [("stamp", stamp);
                ("stamp", stamp);
                ("example", example);
                ("example2", example2);
                ("harrison1", harrison1);
                ("harrison2", harrison2);
                ("stamp_false", stamp_false);
                ("example2_false", example2_false)];;

let _ = List.map measure_fun examples;;

(* Let's have an automaton for formulas with free vars *)
let free_example = 
  pres_And (
    pres_Le ([1; -23; 2; 5], 17),
    pres_Eq ([11; -13; 3; 7], 19));;

let free_example_all = pres_Forall free_example

