section \<open>Running-time analysis of Hopcroft's algorithm\<close>

theory Hopcroft_Time
  imports Hopcroft_Minimisation
begin

text
\<open>
  Abstract level I
    def: Hopcroft_abstract
\<close>
term Hopcroft_abstract

text
\<open>
  Abstract level II
  Refinement of the specification for acquiring next state toward an inner loop.
    def: Hopcroft_set_f
\<close>

text
\<open>
  Abstract level III
  Precomputation of the set of predecessors of the currently chosen set.
    def: Hopcroft_precompute_step
\<close>

text
\<open>
  First data refinement
  Refinement towards efficient data structures. Partition of \<Q> \<rightarrow> maps
    def: Hopcroft_map
\<close>

text
\<open>
  Second data refinement
  Classes as sets \<rightarrow> maps (bijection with natural numbers).
    def: Hopcroft_map2
\<close>

end