(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*    Valerie Menissier-Morain, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* $Id: big_int.ml 10649 2010-08-18 13:22:48Z doligez $ *)

type big_int = int

(* Sign of a big_int *)
let sign_big_int bi = if bi > 0 then 1
else if bi = 0 then 0 else -1

let zero_big_int = 0
let unit_big_int = 1

(* Opposite of a big_int *)
let minus_big_int bi = -bi

(* Absolute value of a big_int *)
let abs_big_int bi = abs bi

(* Comparison operators on big_int *)

(*
   compare_big_int (bi, bi2) = sign of (bi-bi2)
   i.e. 1 if bi > bi2
        0 if bi = bi2
        -1 if bi < bi2
*)
let compare_big_int bi1 bi2 = compare bi1 bi2

let eq_big_int bi1 bi2 = bi1 = bi2 
and le_big_int bi1 bi2 = bi1 <= bi2
and ge_big_int bi1 bi2 = bi1 >= bi2
and lt_big_int bi1 bi2 = bi1 < bi2
and gt_big_int bi1 bi2 = bi1 > bi2

let max_big_int bi1 bi2 = if lt_big_int bi1 bi2 then bi2 else bi1
and min_big_int bi1 bi2 = if gt_big_int bi1 bi2 then bi2 else bi1

(* Operations on big_int *)

let pred_big_int bi = pred bi
let succ_big_int bi = succ bi

let add_big_int bi1 bi2 = bi1 + bi2

(* Coercion with int type *)
let big_int_of_int i = i
let add_int_big_int i bi = i + bi
let sub_big_int bi1 bi2 = bi1 - bi2

(* Returns i * bi *)
let mult_int_big_int i bi = i * bi
let mult_big_int bi1 bi2 = bi1 * bi2

(* (quotient, rest) of the euclidian division of 2 big_int *)
let quomod_big_int bi1 bi2 = (bi1 / bi2, bi1 mod bi2) 

let div_big_int bi1 bi2 = bi1 / bi2
and mod_big_int bi1 bi2 = bi1 mod bi2


let is_int_big_int bi = true
let int_of_big_int bi = bi


let string_of_big_int bi = string_of_int bi
let big_int_of_string s = int_of_string s
let square_big_int bi = bi * bi
let num_digits_big_int bi = 1
