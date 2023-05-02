section \<open>Running-time analysis of Hopcroft's algorithm\<close>

theory Hopcroft_Time
  imports
    Hopcroft_Minimisation
    "../isabelle_llvm_time/thys/lib/More_Asymptotics"
begin

text
\<open>
  Abstract level I
    def: Hopcroft_abstract
\<close>
thm Hopcroft_abstract_def

text
\<open>
  Abstract level II
  Refinement of the specification for acquiring next state toward an inner loop.
    def: Hopcroft_set_f
\<close>
thm Hopcroft_set_f_def

text
\<open>
  Abstract level III
  Precomputation of the set of predecessors of the currently chosen set.
    def: Hopcroft_precompute_step
\<close>
thm Hopcroft_precompute_step_def

text
\<open>
  First data refinement
  Refinement towards efficient data structures. Partition of \<Q> \<rightarrow> maps
    def: Hopcroft_map
\<close>
thm Hopcroft_map_def

text
\<open>
  Second data refinement
  Classes as sets \<rightarrow> maps (bijection with natural numbers).
    def: Hopcroft_map2
\<close>
thm Hopcroft_map2_def

text
\<open>
  Implementation
  Instantiation of the locales
\<close>
thm hopcroft_impl_def
thm hop_impl.Hopcroft_code_def

definition
  "hopcroft_impl_allcost m n \<equiv> m * n * Discrete.log n"

theorem "(\<lambda>(m, n). real (hopcroft_impl_allcost m n)) \<in> O(\<lambda>(m,n). real (m * n) * ln (real n))"
proof-
  have "(\<lambda>n. real (m * n * Discrete.log n)) \<in> O(\<lambda>n. real (m * n) *ln (real n))" for m
    using dlog by fastforce
  show ?thesis
    unfolding hopcroft_impl_allcost_def
    apply standard
    apply auto sorry
qed

end