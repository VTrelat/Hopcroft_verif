section \<open>Running-time analysis of Hopcroft's algorithm\<close>

theory Hopcroft_Time
  imports
    (* Hopcroft_Minimisation *) (* Errors due to duplicate theories? Should we merge things?*)
    "../isabelle_llvm_time/thys/nrest/NREST_Main"
    (*"../isabelle_llvm_time/thys/vcg/Sep_Generic_Wp"*)
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

notepad
begin

definition Hopcroft_abstract_f where
"Hopcroft_abstract_f \<A> = 
 (\<lambda>(P, L). do {
     ASSERT (Hopcroft_abstract_invar \<A> (P, L));                             ($check_abstract_invar)
     ASSERT (L \<noteq> {});                                                       ($check_emptiness)
       (a,p) \<leftarrow> SPEC (\<lambda>(a,p). (a,p) \<in> L);                                   ($pick_splitter)
       (P', L') \<leftarrow> SPEC (\<lambda>(P', L'). Hopcroft_update_splitters_pred \<A> p a P L L' \<and>
                                    (P' = Hopcroft_split \<A> p a {} P));      ($split + $update_partition)
       RETURN (P', L')
     })"

definition Hopcroft_abstract_invar where
  "Hopcroft_abstract_invar \<A> = (\<lambda>(P, L). 
   is_weak_language_equiv_partition \<A> P \<and>
   (\<forall>ap \<in> L. fst ap \<in> \<Sigma> \<A> \<and> snd ap \<in> P) \<and>
   (\<forall>p1 a p2. (a \<in> \<Sigma> \<A> \<and> (\<exists>p1' \<in> P. p1 \<subseteq> p1') \<and> p2 \<in> P \<and>
       split_language_equiv_partition_pred \<A> p1 a p2) \<longrightarrow>
       (\<exists>p2'. (a, p2') \<in> L \<and> split_language_equiv_partition_pred \<A> p1 a p2')))"\<comment>\<open>has to be O(1)\<close>

definition Hopcroft_abstract_b where
"Hopcroft_abstract_b PL = (snd PL \<noteq> {})        ($check_emptiness)" \<comment>\<open>has to be O(1)\<close>

definition Hopcroft_abstract where
  "Hopcroft_abstract \<A> = 
   (if (\<Q> \<A> = {}) then RETURN {} else (                                                ($check_emptiness)
    if (\<F> \<A> = {}) then RETURN {\<Q> \<A>} else (                                            ($check_emptiness)
       do {                                                                             ($abstract_while)
         (P, _) \<leftarrow> WHILEIT (Hopcroft_abstract_invar \<A>) Hopcroft_abstract_b
                           (Hopcroft_abstract_f \<A>) (Hopcroft_abstract_init \<A>);
         RETURN P
       })))"\<comment>\<open>has to be O(card(\<Sigma> \<A>) * card(\<Q> \<A>) * log(card(\<Q> \<A>)))\<close>

end

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