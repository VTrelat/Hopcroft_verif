(*  Title:       Presburger Example Implementation
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

header {* Presburger Automata Implementation *}

theory RBT_CodeExport
imports Main 
        "RBT_NFAImpl"
        "RBT_Presburger_Impl"
begin

code_include OCaml "STArray" {*
module STArray = struct

type 'a cell = Value of 'a array | Invalid;;

exception AccessedOldVersion;;
exception Size;;

type 'a arrayref = ('a cell) ref;;

let fromList l = ref (Value (Array.of_list l));;
let array (size, v) = ref (Value (Array.make size v));;
let tabulate (size, f) = ref (Value (Array.init size f));;
let sub (aref, idx) = match !aref with
  Invalid -> raise AccessedOldVersion |
  (Value a) -> Array.get a idx;;

let update (aref,idx,v) =
  match !aref with
    Invalid -> raise AccessedOldVersion |
    (Value a) -> (
      aref := Invalid;
      Array.set a idx v;
      ref (Value a)
    );;

let length aref = match !aref with Invalid -> raise AccessedOldVersion |
                                   Value a -> Array.length a

let grow (aref, i, x) = match !aref with 
  Invalid -> raise AccessedOldVersion |
  (Value a) -> (
    let len=Array.length a in
    let na = Array.make (len+i) x in 
    (
      aref := Invalid;
      Array.blit a 0 na 0 len;
      ref (Value na)
    ));;

let shrink (aref, sz) = match !aref with
  Invalid -> raise AccessedOldVersion |
  (Value a) -> (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      tabulate (sz,fun i -> Array.get a i)
    )
  );;

module IsabelleMapping = struct
type 'a arrayType = 'a arrayref;;

let new_array (a:'a) (n:Big_int.big_int) = array (Big_int.int_of_big_int n, a);;

let array_length (a:'a arrayType) = Big_int.big_int_of_int (length a);;

let array_get (a:'a arrayType) i = sub (a, Big_int.int_of_big_int i);;

let array_set (a:'a arrayType) i (e:'a) = update (a, Big_int.int_of_big_int i, e);;

let array_of_list (xs:'a list) = fromList xs;;

let array_grow (a:'a arrayType) i (x:'a) = grow (a, Big_int.int_of_big_int i, x);;

let array_shrink (a:'a arrayType) sz = shrink (a,Big_int.int_of_big_int sz);;

end

end
*}

code_type array 
  (OCaml "_/ STArray.IsabelleMapping.arrayType")

code_const Array (OCaml "STArray.IsabelleMapping.array'_of'_list")
code_const new_array (OCaml "STArray.IsabelleMapping.new'_array")
code_const array_length (OCaml "STArray.IsabelleMapping.array'_length")
code_const array_get (OCaml "STArray.IsabelleMapping.array'_get")
code_const array_set (OCaml "STArray.IsabelleMapping.array'_set")
code_const array_grow (OCaml "STArray.IsabelleMapping.array'_grow")
code_const array_shrink (OCaml "STArray.IsabelleMapping.array'_shrink")
code_const array_of_list (OCaml "STArray.IsabelleMapping.array'_of'_list")

declare rs_ops_unfold[code_unfold]

declare gen_dfs.simps[code]
export_code
  prod_encode
  rs_nfa_construct
  rs_dfa_construct
  rs_nfa_destruct
  rs_nfa_destruct_simple
  rs_nfa_states_no
  rs_nfa_labels_no
  rs_nfa_trans_no
  rs_nfa_final_no
  rs_nfa_initial_no
  rs_nfa_rename_labels
  rs_nfa_rename_labels_gen
  rs_nfa_normalise
  rs_nfa_complement
  rs_nfa_bool_comb_gen
  rs_nfa_bool_comb
  rs_nfa_determinise
  rs_nfa_reverse
  rs_nfa_Brzozowski
  rs_nfa_accept
  rs_nfa_right_quotient_lists 
  rs_nfa_Hopcroft 
  rs_nfa_Hopcroft_NFA
  rs_nfa_language_is_empty
  rs_nfa_language_is_univ
  rs_nfa_language_is_subset
  rs_nfa_language_is_eq
  rs_eval_pf
  eval_pf_dfa
in OCaml module_name "Automata_Export" file "Automata_Export_RBT.ml"

code_include SML "STArray"
{*
structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell ref;

fun fromList l = ref (Value (Array.fromList l));
fun array (size, v) = ref (Value (Array.array (size,v)));
fun tabulate (size, f) = ref (Value (Array.tabulate(size, f)));
fun sub (ref Invalid, idx) = raise AccessedOldVersion |
    sub (ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (ref Invalid) => raise AccessedOldVersion |
    (ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      ref (Value a)
    );

fun length (ref Invalid) = raise AccessedOldVersion |
    length (ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of 
  (ref Invalid) => raise AccessedOldVersion |
  (ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x) 
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (ref Invalid) => raise AccessedOldVersion |
  (ref (Value a)) => (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

end;

end;


*}

code_type array 
  (SML "_/ STArray.IsabelleMapping.ArrayType")

code_const Array (SML "STArray.IsabelleMapping.array'_of'_list")
code_const new_array (SML "STArray.IsabelleMapping.new'_array")
code_const array_length (SML "STArray.IsabelleMapping.array'_length")
code_const array_get (SML "STArray.IsabelleMapping.array'_get")
code_const array_set (SML "STArray.IsabelleMapping.array'_set")
code_const array_grow (SML "STArray.IsabelleMapping.array'_grow")
code_const array_shrink (SML "STArray.IsabelleMapping.array'_shrink")
code_const array_of_list (SML "STArray.IsabelleMapping.array'_of'_list")


export_code
  prod_encode
  rs_nfa_construct
  rs_dfa_construct
  rs_nfa_destruct
  rs_nfa_destruct_simple
  rs_nfa_states_no
  rs_nfa_labels_no
  rs_nfa_trans_no
  rs_nfa_final_no
  rs_nfa_initial_no
  rs_nfa_accept
  rs_nfa_rename_labels
  rs_nfa_rename_labels_gen
  rs_nfa_normalise
  rs_nfa_complement
  rs_nfa_bool_comb_gen
  rs_nfa_bool_comb
  rs_nfa_determinise
  rs_nfa_reverse
  rs_nfa_right_quotient_lists
  rs_nfa_Brzozowski
  rs_nfa_Hopcroft
  rs_nfa_Hopcroft_NFA
  rs_nfa_language_is_empty
  rs_nfa_language_is_univ
  rs_nfa_language_is_subset
  rs_nfa_language_is_eq
  rs_eval_pf
  eval_pf_dfa
in SML file "Automata_Export_RBT.sml"

end
