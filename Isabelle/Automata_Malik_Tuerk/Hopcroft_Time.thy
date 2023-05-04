section \<open>Running-time analysis of Hopcroft's algorithm\<close>

theory Hopcroft_Time
  imports
    (* Hopcroft_Minimisation *) (* Errors due to duplicate theories? Should we merge things?*)
    "../isabelle_llvm_time/thys/nrest/NREST_Main"
    "../isabelle_llvm_time/thys/vcg/Sep_Generic_Wp"
begin

text
\<open>
  Abstract level I
    def: Hopcroft_abstract
\<close>
(* thm Hopcroft_abstract_def *)
(* thm Hopcroft_abstract_f_def *)

definition "state_emptiness \<equiv> undefined"

definition "line1 \<equiv> SPECT[(\<lambda>Q. Q = {}) \<mapsto> cost ($state_emptiness)]"

text
\<open>
  Abstract level II
  Refinement of the specification for acquiring next state toward an inner loop.
    def: Hopcroft_set_f
\<close>
(* thm Hopcroft_set_f_def *)

text
\<open>
  Abstract level III
  Precomputation of the set of predecessors of the currently chosen set.
    def: Hopcroft_precompute_step
\<close>
(* thm Hopcroft_precompute_step_def *)

text
\<open>
  First data refinement
  Refinement towards efficient data structures. Partition of \<Q> \<rightarrow> maps
    def: Hopcroft_map
\<close>
(* thm Hopcroft_map_def *)

text
\<open>
  Second data refinement
  Classes as sets \<rightarrow> maps (bijection with natural numbers).
    def: Hopcroft_map2
\<close>
(* thm Hopcroft_map2_def *)

text
\<open>
  Implementation
  Instantiation of the locales
\<close>
(* thm hopcroft_impl_def *)
(* thm hop_impl.Hopcroft_code_def *)


end