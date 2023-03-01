(*
  no_document use_thy "ThisTheory";
  use_thy "ThatTheory";
*)

(* Theories from the Isabelle library that are not in Main *)
no_document use_thy "Infinite_Set";
no_document use_thy "Parity";

(* Theories proper to the development of Buchi automata *)
use_thy "Words";
use_thy "Dags";
use_thy "NDTable";
use_thy "Buchi";
use_thy "GBuchi";

use_thy "BuchiComplement";

