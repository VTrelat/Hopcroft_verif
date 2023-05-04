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

definition "is_splitter = undefined"
definition "split_and_update = undefined"

definition "Hopcroft_abstract_fT \<A> \<equiv>
  bindT (\<lambda>(P, L). ASSERT (Hopcroft_abstract_invar \<A> (P, L)))
  (bindT (\<lambda>a. ASSERT (L \<noteq> {}))
  (bindT (\<lambda>_. SPECT (\<lambda>(a, p). (a, p) \<in> L))
  (bindT ((\<lambda>(a, p). SPECT (\<lambda>(P', L'). Hopcroft_update_splitters_pred \<A> p a P L L' \<and> P' = Hopcroft_split \<A> p a {} P))
  (\<lambda>(P', L'). RETURNT (P', L'))))))"

definition Hopcroft_abstractT where
  "Hopcroft_abstractT \<A> \<equiv>
   (if (\<Q> \<A> = {}) then RETURNT {} else (
    if (\<F> \<A> = {}) then RETURNT {\<Q> \<A>} else (
       do {
         (P, _) \<leftarrow> WHILEIT (Hopcroft_abstract_invar \<A>) Hopcroft_abstract_b
                           (Hopcroft_abstract_f \<A>) (Hopcroft_abstract_init \<A>);
         RETURN P
       })))"

definition "state_emptiness Q \<equiv> undefined"

definition "line1 Q \<equiv> SPECT[(\<lambda>Q. if Q = {} then RETURNT {} else RETURNT Q) \<mapsto> cost ($state_emptiness Q)]"

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