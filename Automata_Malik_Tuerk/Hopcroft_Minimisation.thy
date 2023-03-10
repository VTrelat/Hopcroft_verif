(*  Title:       Hopcroft's Minimisation Algorithm 
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
    Updates:     Vincent Trélat <vincent.trelat@depinfonancy.net>
*)

section\<open>Hopcroft's Minimisation Algorithm\<close>

theory Hopcroft_Minimisation
  imports Main DFA
        "../Collections/ICF/Collections"
        "../Nested_Multisets_Ordinals/Multiset_More"
        "../Partition"

begin

text \<open> In this theory, Hopcroft's minimisation algorithm [see
Hopcroft, J.E.: An $n$ log $n$ algorithm for minimizing the states in a finite
  automaton. In Kohavi, Z. (ed.) The Theory of Machines and Computations.
Academic Press  189--196 (1971)] is verified. \<close>

subsection \<open> Main idea \<close>

text \<open> A determinisitic automaton with no unreachable states 
        can be minimised by merging equivalent states. \<close>

lemma merge_is_minimal :
assumes wf_A: "DFA \<A>"
    and connected: "SemiAutomaton_is_initially_connected \<A>"
    and equiv: "NFA_is_strong_equivalence_rename_fun \<A> f"
shows "DFA_is_minimal (NFA_rename_states \<A> f)"
  (is "DFA_is_minimal ?\<A>_min")
proof (rule DFA.DFA_is_minimal_intro)
  show "DFA ?\<A>_min"
    by (fact DFA___combine_equiv_states[OF wf_A equiv])
next
  have "\<And>q'. q' \<in> \<Q> \<A> \<Longrightarrow> (\<exists> q \<in> \<I> \<A>. \<exists>w. 
          LTS_is_reachable (\<Delta> (NFA_rename_states \<A> f)) (f q) w (f q'))"
  proof -
    fix q'
    assume q'_in_Q: "q' \<in> \<Q> \<A>"
    with connected obtain q w where
      q_in: "q \<in> \<I> \<A>" and
      reach: "LTS_is_reachable (\<Delta> \<A>) q w q'"
    unfolding SemiAutomaton_is_initially_connected_alt_def
    by (simp add: Bex_def Ball_def) metis

    from LTS_is_reachable___SemiAutomaton_rename_statesE[OF reach, of _ f] q_in 
    show "?thesis q'" unfolding NFA_rename_states_def by blast
  qed

  thus "SemiAutomaton_is_initially_connected ?\<A>_min"
    unfolding SemiAutomaton_is_initially_connected_alt_def
    by simp
next
  have wf_NFA : "NFA \<A>" using wf_A unfolding DFA_alt_def by simp
  from NFA.\<L>_in_state_rename_iff [OF wf_NFA
    NFA_is_strong_equivalence_rename_fun___weaken [OF equiv]]
  show "inj_on (\<L>_in_state ?\<A>_min) (\<Q> ?\<A>_min)"
    using equiv
    unfolding NFA_is_strong_equivalence_rename_fun_def inj_on_def
    by simp
qed

lemma merge_NFA_minimise :
assumes wf_A: "DFA \<A>"
    and connected: "SemiAutomaton_is_initially_connected \<A>"
    and equiv: "NFA_is_strong_equivalence_rename_fun \<A> f"
shows "NFA_isomorphic_wf (NFA_rename_states \<A> f) (NFA_minimise \<A>)"
proof -
  from wf_A have wf_A': "NFA \<A>" by (simp add: DFA_alt_def)
  note min = merge_is_minimal[OF wf_A connected equiv]

  show ?thesis 
    apply (simp add: NFA_isomorphic_wf___minimise [OF wf_A'] min)
    apply (rule NFA.\<L>_rename_iff [OF wf_A'])
    apply (rule NFA_is_strong_equivalence_rename_fun___weaken)
    apply (rule equiv)
  done
qed

text \<open> This allows to define a high level, non-executable version of a minimisation
        algorithm. These definitions and lemmata are later used as an abstract interface to
        an executable implementation. \<close>
definition Hopcroft_minimise :: "('q, 'a, 'x) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec" where
 "Hopcroft_minimise \<A> \<equiv> NFA_rename_states \<A> (SOME f. 
  NFA_is_strong_equivalence_rename_fun \<A> f \<and> (\<forall>q \<in> \<Q> \<A>. f q \<in> \<Q> \<A>))"

lemma Hopcroft_minimise_correct :
fixes \<A> :: "('q, 'a, 'x) NFA_rec_scheme"
assumes wf_A: "DFA \<A>"
    and connected: "SemiAutomaton_is_initially_connected \<A>"
shows "DFA_is_minimal (Hopcroft_minimise \<A>)" "\<L> (Hopcroft_minimise \<A>) = \<L> \<A>"
proof -
  define f where "f \<equiv> (SOME f. NFA_is_strong_equivalence_rename_fun \<A> f \<and> (\<forall>q \<in> \<Q> \<A>. f q \<in> \<Q> \<A>))"

  from Hilbert_Choice.someI_ex [where ?P = "\<lambda>f. NFA_is_strong_equivalence_rename_fun \<A> f \<and> 
     (\<forall>q \<in> \<Q> \<A>. f q \<in> \<Q> \<A>)", 
     OF NFA_is_strong_equivalence_rename_fun_exists]
  have f_OK: "NFA_is_strong_equivalence_rename_fun \<A> f" and f_subset: "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> f q \<in> \<Q> \<A>"
    by (simp_all add: f_def)

  from wf_A have wf_NFA: "NFA \<A>" unfolding DFA_alt_def by simp
  
  from NFA.\<L>_rename_iff [OF wf_NFA NFA_is_strong_equivalence_rename_fun___weaken[OF f_OK]]
  show "\<L> (Hopcroft_minimise \<A>) = \<L> \<A>"
    unfolding Hopcroft_minimise_def f_def[symmetric]
    by simp
 
  from merge_is_minimal [OF wf_A connected f_OK]
  show "DFA_is_minimal (Hopcroft_minimise \<A>)"
    unfolding Hopcroft_minimise_def f_def[symmetric]
    by simp
qed

lemma Hopcroft_minimise_\<Q> :
fixes \<A> :: "('q, 'a, 'x) NFA_rec_scheme"
shows "\<Q> (Hopcroft_minimise \<A>) \<subseteq> \<Q> \<A>"
proof -
  define f where "f \<equiv> (SOME f. NFA_is_strong_equivalence_rename_fun \<A> f \<and> (\<forall>q \<in> \<Q> \<A>. f q \<in> \<Q> \<A>))"

  from Hilbert_Choice.someI_ex [where ?P = "\<lambda>f. NFA_is_strong_equivalence_rename_fun \<A> f \<and> 
     (\<forall>q \<in> \<Q> \<A>. f q \<in> \<Q> \<A>)", 
     OF NFA_is_strong_equivalence_rename_fun_exists]
  have f_OK: "NFA_is_strong_equivalence_rename_fun \<A> f" and f_subset: "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> f q \<in> \<Q> \<A>"
    by (simp_all add: f_def)

  show "\<Q> (Hopcroft_minimise \<A>) \<subseteq> \<Q> \<A>"
    unfolding Hopcroft_minimise_def f_def[symmetric]
    using f_subset
    by (simp add: subset_iff image_iff) metis
qed

definition Hopcroft_minimise_NFA where
 "Hopcroft_minimise_NFA \<A> = Hopcroft_minimise (NFA_determinise \<A>)"

lemma Hopcroft_minimise_NFA_correct :
fixes \<A> :: "('q::{automaton_states}, 'a, 'x) NFA_rec_scheme"
assumes wf_A: "NFA \<A>"
shows "DFA_is_minimal (Hopcroft_minimise_NFA \<A>)" "\<L> (Hopcroft_minimise_NFA \<A>) = \<L> \<A>"
proof -
  let ?A' = "NFA_determinise \<A>"

  from NFA_determinise_is_DFA [OF wf_A]
  have wf_A': "DFA ?A'" .

  have connected: "SemiAutomaton_is_initially_connected ?A'"
    unfolding NFA_determinise_def efficient_determinise_NFA_def
    apply (rule SemiAutomaton_is_initially_connected___normalise_states)
    apply (simp add: SemiAutomaton_is_initially_connected___NFA_remove_unreachable_states)
  done
  note min_correct = Hopcroft_minimise_correct [OF wf_A' connected]

  from min_correct(1) show "DFA_is_minimal (Hopcroft_minimise_NFA \<A>)"
    unfolding Hopcroft_minimise_NFA_def .

  from min_correct(2) NFA_determinise_\<L>[OF wf_A]
  show "\<L> (Hopcroft_minimise_NFA \<A>) = \<L> \<A>"
    unfolding Hopcroft_minimise_NFA_def
    by auto
qed


text \<open> Now, we can consider the essence of Hopcroft's algorithm: 
finding a suitable renaming function.  Hopcroft's algorithm computes the Myhill-Nerode equivalence 
relation in form of a partition. From this partition, a renaming function can be easily derived. \<close>

subsection \<open> Basic notions \<close>

subsubsection \<open> Weak Equivalence Partitions \<close> 

text \<open> For Hopcroft's algorithm, we consider special partitions. They have to satisfy two 
properties: First, if two states are equivalent, they have to be in the same set of the partition.
This property will later allow an induction argument when splitting partitions. However,
for the base case, we need a stronger property. All sets of the considered partitions either contain
only accepting states or only non-accepting states. \<close>

definition is_weak_language_equiv_set where
  "is_weak_language_equiv_set \<A> p \<equiv>
   (p \<subseteq> \<Q> \<A>) \<and>                                  \<comment>\<open>p is a subset of the set of states of \<A>\<close>
   ((p \<subseteq> \<F> \<A>) \<or> (p \<inter> \<F> \<A> = {})) \<and>             \<comment>\<open>p either contains final states only or non final states only\<close>
   (\<forall>q1 \<in> \<Q> \<A>. \<forall>q2 \<in> \<Q> \<A>.                      \<comment>\<open>For any two states accepting the same language and if one belongs to p, so does the other\<close>
      \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2 \<and>
      q1 \<in> p \<longrightarrow> q2 \<in> p)"

lemma is_weak_language_equiv_setI [intro!] :
  "\<lbrakk>p \<subseteq> \<Q> \<A>; 
    (p \<subseteq> \<F> \<A>) \<or> (p \<inter> \<F> \<A> = {});
    \<And>q1 q2. \<lbrakk>q1 \<in> \<Q> \<A>; q2 \<in> \<Q> \<A>; q1 \<in> p;
            \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2\<rbrakk> \<Longrightarrow>
            q2 \<in> p\<rbrakk> \<Longrightarrow>
   is_weak_language_equiv_set \<A> p"
unfolding is_weak_language_equiv_set_def
by blast

lemma is_weak_language_equiv_setD :
  "\<lbrakk>is_weak_language_equiv_set \<A> p;
    q1 \<in> \<Q> \<A>; q2 \<in> \<Q> \<A>; \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2\<rbrakk> \<Longrightarrow>
   (q1 \<in> p) \<longleftrightarrow> (q2 \<in> p)"
unfolding is_weak_language_equiv_set_def by blast

definition is_weak_language_equiv_partition where
  "is_weak_language_equiv_partition \<A> P \<longleftrightarrow>
   is_partition (\<Q> \<A>) P \<and>
   (\<forall>p \<in> P. is_weak_language_equiv_set \<A> p)"

lemma is_weak_language_equiv_partitionI [intro!] :
  "\<lbrakk>is_partition (\<Q> \<A>) P;
    \<And>p. p \<in> P \<Longrightarrow> is_weak_language_equiv_set \<A> p\<rbrakk> \<Longrightarrow>
   is_weak_language_equiv_partition \<A> P" 
  unfolding is_weak_language_equiv_partition_def Ball_def
  by blast

lemma is_weak_language_equiv_partitionD1  :
  "\<lbrakk>is_weak_language_equiv_partition \<A> P;
    p \<in> P\<rbrakk> \<Longrightarrow> p \<subseteq> \<F> \<A> \<or> (p \<inter> \<F> \<A> = {})"
  unfolding is_weak_language_equiv_partition_def
            is_weak_language_equiv_set_def Ball_def
  by blast

lemma is_weak_language_equiv_partitionD2  :
  "\<lbrakk>is_weak_language_equiv_partition \<A> P;
    q1 \<in> \<Q> \<A>; q2 \<in> \<Q> \<A>; p \<in> P;
    \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2;
    q1 \<in> p\<rbrakk> \<Longrightarrow> q2 \<in> p"
  unfolding is_weak_language_equiv_partition_def 
     is_weak_language_equiv_set_def Ball_def
  by blast

lemma is_weak_language_equiv_partitionD2_iff :
  "\<lbrakk>is_weak_language_equiv_partition \<A> P;
    q1 \<in> \<Q> \<A>; q2 \<in> \<Q> \<A>; p \<in> P;
    \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2\<rbrakk> \<Longrightarrow> 
   q1 \<in> p \<longleftrightarrow> q2 \<in> p"
  by (metis is_weak_language_equiv_partitionD2)

lemma is_weak_language_equiv_partitionD3 :
  "is_weak_language_equiv_partition \<A> P \<Longrightarrow> 
   is_partition (\<Q> \<A>) P"
  unfolding is_weak_language_equiv_partition_def 
  by simp

text \<open> An alternative definition of
@{term is_weak_language_equiv_partition} 
(that is often used in literature about Hopcroft's algorithm)
can be given using the connection between partitions and equivalence relations. \<close>

definition Hopcroft_accepting_relation where
  "Hopcroft_accepting_relation \<A> \<equiv> {(q1, q2) . q1 \<in> \<Q> \<A> \<and> q2 \<in> \<Q> \<A> \<and> (q1 \<in> \<F> \<A> \<longleftrightarrow> q2 \<in> \<F> \<A>)}"
  (* q\<^sub>1 R\<^sub>H q\<^sub>2 \<equiv> q\<^sub>1 \<in> \<F>\<^sub>\<A> \<longleftrightarrow> q\<^sub>2 \<in> \<F>\<^sub>\<A> i.e. q\<^sub>1 R\<^sub>H q\<^sub>2 iff q\<^sub>1 and q\<^sub>2 are both final or both non-final *)

lemma equiv_Hopcroft_accepting_relation :
  "equiv (\<Q> \<A>) (Hopcroft_accepting_relation \<A>)"
unfolding Hopcroft_accepting_relation_def equiv_def refl_on_def sym_def trans_def
by auto

definition Hopcroft_accepting_partition where
  "Hopcroft_accepting_partition \<A> \<equiv> (\<Q> \<A>) // (Hopcroft_accepting_relation \<A>)"

lemma Hopcroft_accepting_partition_alt_def :
assumes wf_A: "NFA \<A>"
shows "Hopcroft_accepting_partition \<A> = {\<Q> \<A> - \<F> \<A>, \<F> \<A>} \<inter> {s. s \<noteq> {}}" \<comment>\<open>Corresponds to the base case\<close>
unfolding Hopcroft_accepting_partition_def quotient_def Hopcroft_accepting_relation_def Bex_def
using NFA.\<F>_consistent [OF wf_A]
by auto

definition Myhill_Nerode_relation where
  "Myhill_Nerode_relation \<A> \<equiv> {(q1, q2) . q1 \<in> \<Q> \<A> \<and> q2 \<in> \<Q> \<A> \<and> (\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2)}"
  (* q\<^sub>1 R\<^sub>M\<^sub>N q\<^sub>2 \<equiv> \<L>\<^sub>\<A>(q\<^sub>1) = \<L>\<^sub>\<A>(q\<^sub>2) *)

lemma equiv_Myhill_Nerode_relation :
  "equiv (\<Q> \<A>) (Myhill_Nerode_relation \<A>)"
unfolding Myhill_Nerode_relation_def equiv_def refl_on_def sym_def trans_def
by auto

definition Myhill_Nerode_partition where
  "Myhill_Nerode_partition \<A> \<equiv> (\<Q> \<A>) // (Myhill_Nerode_relation \<A>)"

lemma Myhill_Nerode_partition_alt_def :
  "Myhill_Nerode_partition \<A> = 
   {{q'. q' \<in> \<Q> \<A> \<and> \<L>_in_state \<A> q' = \<L>_in_state \<A> q} | q. q \<in> \<Q> \<A>}"
unfolding Myhill_Nerode_partition_def quotient_def Myhill_Nerode_relation_def Bex_def
by auto

lemma Myhill_Nerode_partition___\<F>_emp :
assumes \<F>_eq:  "\<F> \<A> = {}"
    and \<Q>_neq: "\<Q> \<A> \<noteq> {}" 
shows "Myhill_Nerode_partition \<A> = {\<Q> \<A>}"
proof -
  from \<F>_eq have "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> \<L>_in_state \<A> q = {}"
    unfolding \<L>_in_state_def by simp

  with \<Q>_neq show ?thesis 
    unfolding Myhill_Nerode_partition_alt_def
    by auto
qed

lemma Myhill_Nerode_partition___\<Q>_emp :
"\<Q> \<A> = {} \<Longrightarrow> Myhill_Nerode_partition \<A> = {}"
unfolding Myhill_Nerode_partition_def
by auto


lemma is_weak_language_equiv_partition_alt_def :
"is_weak_language_equiv_partition \<A> P \<longleftrightarrow>
 is_partition (\<Q> \<A>) P \<and>
 partition_less_eq (Myhill_Nerode_partition \<A>) P \<and>
 partition_less_eq P (Hopcroft_accepting_partition \<A>)" (* i.e. R\<^sub>M\<^sub>N \<subseteq> R\<^sub>P \<subseteq> R\<^sub>H on states of \<A>*)
proof (cases "is_partition (\<Q> \<A>) P")
  case False thus ?thesis unfolding is_weak_language_equiv_partition_def by simp
next
  case True note part_P = this

  from is_partition_find[OF part_P] is_partition_in_subset[OF part_P]
  show ?thesis
  unfolding is_weak_language_equiv_partition_def partition_less_eq_def
            Myhill_Nerode_partition_def Hopcroft_accepting_partition_def 
    apply (simp add: equiv_Myhill_Nerode_relation quotient_inverse equiv_Hopcroft_accepting_relation)
    apply (simp add: part_P is_weak_language_equiv_set_def relation_of_partition_def subset_iff 
                     set_eq_iff Ball_def Bex_def Myhill_Nerode_relation_def Hopcroft_accepting_relation_def)
    apply (intro iffI conjI allI impI)
    apply metis+
  done
qed


text \<open> Hopcroft's algorithm is interested in finding a partition such that
two states are in the same set of the partition, if and only if they are equivalent.
The concept of weak language equivalence partitions above guarantees that
two states that are equivalent are in the same partition. 

In the following, the missing property that all the states in one partition are equivalent is
formalised. \<close>

definition is_weak2_language_equiv_set where
  "is_weak2_language_equiv_set \<A> p \<equiv>
   (p \<subseteq> \<Q> \<A>) \<and>
   ((p \<subseteq> \<F> \<A>) \<or> (p \<inter> \<F> \<A> = {})) \<and>
   (\<forall>q1 \<in> \<Q> \<A>. \<forall>q2 \<in> \<Q> \<A>.  
      q1 \<in> p \<and> q2 \<in> p \<longrightarrow> \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2)"

lemma is_weak2_language_equiv_set_alt_def :
  "is_weak2_language_equiv_set \<A> p =
   ((p \<subseteq> \<Q> \<A>) \<and>
   (\<forall>q1 \<in> \<Q> \<A>. \<forall>q2 \<in> \<Q> \<A>.  
      q1 \<in> p \<and> q2 \<in> p \<longrightarrow> \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2))"   
unfolding is_weak2_language_equiv_set_def Ball_def
by auto (metis \<L>_in_state___in_\<F> in_mono)

definition is_weak2_language_equiv_partition where
  "is_weak2_language_equiv_partition \<A> P \<longleftrightarrow>
   is_partition (\<Q> \<A>) P \<and>
   (\<forall>p \<in> P. is_weak2_language_equiv_set \<A> p)"

lemma is_weak2_language_equiv_partition_alt_def :
"is_weak2_language_equiv_partition \<A> P \<longleftrightarrow>
 is_partition (\<Q> \<A>) P \<and> partition_less_eq P (Myhill_Nerode_partition \<A>)" (* i.e. R\<^sub>P \<subseteq> R\<^sub>M\<^sub>N on states of \<A> *)
proof (cases "is_partition (\<Q> \<A>) P")
  case False thus ?thesis unfolding is_weak2_language_equiv_partition_def by simp
next
  case True note part_P = this

  from is_partition_find[OF part_P] is_partition_in_subset[OF part_P]
  show ?thesis
  unfolding is_weak2_language_equiv_partition_def partition_less_eq_def Myhill_Nerode_partition_def
    apply (simp add: equiv_Myhill_Nerode_relation quotient_inverse)
    apply (simp add: part_P is_weak2_language_equiv_set_alt_def relation_of_partition_def 
                     subset_iff set_eq_iff Ball_def Bex_def Myhill_Nerode_relation_def)
    apply (intro iffI conjI allI impI)
    apply metis+
  done
qed

definition is_strong_language_equiv_set where
  "is_strong_language_equiv_set \<A> p \<equiv>
   is_weak_language_equiv_set \<A> p \<and>
   is_weak2_language_equiv_set \<A> p"

lemma is_strong_language_equiv_set_alt_def :
  "is_strong_language_equiv_set \<A> p =
   ((p \<subseteq> \<Q> \<A>) \<and>
    (\<forall>q1 \<in> p. \<forall>q2 \<in> \<Q> \<A>.  
      ((q2 \<in> p)) \<longleftrightarrow> (\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2)))"
proof (cases "p \<subseteq> \<Q> \<A>")
  case False thus ?thesis 
    unfolding is_strong_language_equiv_set_def
          is_weak2_language_equiv_set_def
          is_weak_language_equiv_set_def
    by simp
next
  case True note p_subset = this
  thus ?thesis
  proof (cases "(p \<subseteq> \<F> \<A>) \<or> (p \<inter> \<F> \<A> = {})")
    case False note not_F_prop = this
    then obtain q1 q2 where
      q12_neq_in_F: "(q1 \<in> \<F> \<A>) \<noteq> (q2 \<in> \<F> \<A>)" and
      q1_in: "q1 \<in> p" and q2_in: "q2 \<in> p" by auto

    thus ?thesis
      unfolding is_strong_language_equiv_set_def
                is_weak2_language_equiv_set_def
                is_weak_language_equiv_set_def
      apply (simp add: not_F_prop Bex_def)
      apply (rule impI)
      apply (rule_tac exI [where x = q1])
      apply (simp add: subset_iff)
      apply (rule_tac exI [where x = q2])
      apply (simp only: in_\<L>_in_state_Nil[symmetric] subset_iff set_eq_iff Bex_def)
      apply metis
    done
  next
    case True note F_prop = this
    have "((\<forall>q1\<in>\<Q> \<A>. \<forall>q2\<in>\<Q> \<A>. \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2 \<and> q1 \<in> p \<longrightarrow> q2 \<in> p) \<and>
           (\<forall>q1\<in>\<Q> \<A>. \<forall>q2\<in>\<Q> \<A>. ((q1 \<in> p) \<and> (q2 \<in> p)) \<longrightarrow> (\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2))) =
          (\<forall>q1\<in>p. \<forall>q2\<in>\<Q> \<A>. (q2 \<in> p) = (\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2))"
          (is "(?P11 \<and> ?P12) = ?P2") 
    proof (intro iffI)
      assume ?P2 hence
        "\<forall>q1\<in>p. \<forall>q2\<in>\<Q> \<A>. ((\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2) = (q2 \<in> p))"
        by metis
      thus "?P11 \<and> ?P12" by simp metis
    next
      assume pre: "?P11 \<and> ?P12" 
      thus ?P2
      proof (intro ballI)
        fix q1 q2
        assume q1_in_p: "q1 \<in> p" and q2_in_Q: "q2 \<in> \<Q> \<A>"
        from q1_in_p p_subset have q1_in_Q: "q1 \<in> \<Q> \<A>" by auto
        
        show "(q2 \<in> p) = (\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2)"
          by (metis q1_in_p q1_in_Q q2_in_Q pre) 
      qed
    qed
    thus ?thesis
      unfolding is_strong_language_equiv_set_def
                is_weak2_language_equiv_set_def
                is_weak_language_equiv_set_def
      by (simp add: p_subset F_prop)
  qed
qed

lemma is_strong_language_equiv_partition_fun_alt_def :
  "(P = Myhill_Nerode_partition \<A>) \<longleftrightarrow>
   (is_partition (\<Q> \<A>) P \<and> (\<forall>p\<in>P. is_strong_language_equiv_set \<A> p))"
proof 
  assume P_eq: "P = Myhill_Nerode_partition \<A>"
  show "is_partition (\<Q> \<A>) P \<and> (\<forall>p\<in>P. is_strong_language_equiv_set \<A> p)"
    unfolding is_partition_def P_eq Myhill_Nerode_partition_alt_def
              Ball_def is_strong_language_equiv_set_alt_def
    by auto
next
  assume pre: "is_partition (\<Q> \<A>) P \<and> (\<forall>p\<in>P. is_strong_language_equiv_set \<A> p)"
  note is_part = conjunct1[OF pre]
  have strong_set : "\<And>p. p \<in> P \<Longrightarrow> is_strong_language_equiv_set \<A> p" using pre by simp

  show "P = Myhill_Nerode_partition \<A>"
  proof (intro set_eqI iffI)
    fix p
    assume p_in_P: "p \<in> P"

    with is_part have "p \<noteq> {}" unfolding is_partition_def by blast
    then obtain q where q_in: "q \<in> p" by auto

    from strong_set [OF p_in_P] q_in
    show "p \<in> Myhill_Nerode_partition \<A>"
      unfolding Myhill_Nerode_partition_alt_def is_strong_language_equiv_set_alt_def
      apply (simp)
      apply (rule_tac exI [where x = q])
      apply (auto)
    done
  next
    fix p
    assume p_in: "p \<in> Myhill_Nerode_partition \<A>"
    then obtain q where 
      p_eq: "p = {q' \<in> \<Q> \<A>. \<L>_in_state \<A> q' = \<L>_in_state \<A> q}" and q_in_Q: "q \<in> \<Q> \<A>"
      unfolding Myhill_Nerode_partition_alt_def
      by auto

    from is_partition_find [OF is_part q_in_Q]
    obtain p' where p'_in_P: "p' \<in> P" and q_in_p': "q \<in> p'" by auto

    from strong_set [OF p'_in_P] q_in_p'
    have "p' = p"
      unfolding p_eq is_strong_language_equiv_set_alt_def
      by auto
    with p'_in_P show "p \<in> P" by simp
  qed
qed


subsubsection \<open> Initial partition \<close>

text \<open> By now, the essential concepts of different partitions have been introduced.
Hopcroft's algorithm operates by splitting weak language partitions. If no further split is 
possible, the searched partition has been found. For this algorithm a suitable initial
partition is needed: \<close>

lemma (in NFA) is_weak_language_equiv_partition_init :
  "is_weak_language_equiv_partition \<A> 
   (Hopcroft_accepting_partition \<A>)"
unfolding is_weak_language_equiv_partition_alt_def
proof (intro conjI)
  show "is_partition (\<Q> \<A>) (Hopcroft_accepting_partition \<A>)"
    unfolding Hopcroft_accepting_partition_def
    using equiv_Hopcroft_accepting_relation
    by (rule quotient_of_equiv_relation_is_partition)
next
  show "partition_less_eq (Hopcroft_accepting_partition \<A>) (Hopcroft_accepting_partition \<A>)"
    unfolding partition_less_eq_def by simp
next 
  have "Myhill_Nerode_relation \<A> \<subseteq> Hopcroft_accepting_relation \<A>"
    unfolding Myhill_Nerode_relation_def Hopcroft_accepting_relation_def
    by (simp add: subset_iff) (metis \<L>_in_state___in_\<F>)
  thus "partition_less_eq (Myhill_Nerode_partition \<A>) (Hopcroft_accepting_partition \<A>)"
    unfolding partition_less_eq_def Myhill_Nerode_partition_def Hopcroft_accepting_partition_def
    by (simp add: quotient_inverse equiv_Myhill_Nerode_relation equiv_Hopcroft_accepting_relation)
qed

subsubsection \<open> Splitting Partitions \<close>

text \<open> Next, we need to define how partitions are splitted. \<close>

definition split_set where
  "split_set P S = ({s \<in> S. P s}, {s \<in> S. \<not>P s})"

lemma split_set_empty [simp] :
  "split_set P {} = ({}, {})"
unfolding split_set_def by simp

lemma split_set_insert :
  "split_set P (insert s S) = 
   (let (ST, SF) = split_set P S in
    (if P s then (insert s ST, SF) else (ST, insert s SF)))"
unfolding split_set_def by auto

lemma split_set_union_distinct:
  "split_set P S = (S1, S2) \<Longrightarrow>
   (S = S1 \<union> S2) \<and> (S1 \<inter> S2 = {})"
unfolding split_set_def by auto
      
text \<open> Given two sets of states @{text p1}, @{text p2} of an automaton
        @{text \<A>} and a label @{text a}. The set @{text p1} is split according to whether
        a state in @{text p2} is reachable by @{text a}.\<close>
definition split_language_equiv_partition where
  "split_language_equiv_partition \<A> p1 a p2 = \<comment>\<open>(a, p2) splits p1.\<close>
   split_set (\<lambda>q. \<exists>q' \<in> p2. (q, a, q') \<in> \<Delta> \<A>) p1"

text \<open> Hopcroft's algorithm operates on deterministic automata. Exploiting the property, that
 the automaton is deterministic, the definition of splitting a partition becomes much simpler. \<close>
lemma (in DFA) split_language_equiv_partition_alt_def :
assumes p1_subset: "p1 \<subseteq> \<Q> \<A>"
    and a_in: "a \<in> \<Sigma> \<A>"
shows "split_language_equiv_partition \<A> p1 a p2 =
   ({q . \<exists>q'. q \<in> p1 \<and> (\<delta> \<A>) (q, a) = Some q' \<and> q' \<in> p2}, 
    {q . \<exists>q'. q \<in> p1 \<and> (\<delta> \<A>) (q, a) = Some q' \<and> q' \<notin> p2})"
unfolding split_language_equiv_partition_def split_set_def
using assms
apply (auto simp add: \<delta>_in_\<Delta>_iff)
by (metis DetSemiAutomaton_\<delta>_is_some LTS_to_DLTS_is_none \<delta>_def \<delta>_in_\<Delta>_iff subsetD)

lemma split_language_equiv_partition_disjoint :
  "\<lbrakk>split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)\<rbrakk> \<Longrightarrow>
   p1a \<inter> p1b = {}"
unfolding split_language_equiv_partition_def
by (simp add: split_set_union_distinct)

lemma split_language_equiv_partition_union :
  "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b) \<Longrightarrow>
   p1 = p1a \<union> p1b"
unfolding split_language_equiv_partition_def
by (simp add: split_set_union_distinct)

lemma split_language_equiv_partition_subset :
assumes "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)" 
shows "p1a \<subseteq> p1 \<and> p1b \<subseteq> p1"
using split_language_equiv_partition_union[OF assms]
by simp

text \<open> Splitting only makes sense if one of the resulting sets is non-empty. 
 This property is very important. Therefore, a special predicate is introduced. \<close>
definition split_language_equiv_partition_pred ::
  "('q, 'a, 'x) NFA_rec_scheme \<Rightarrow> 'q set \<Rightarrow> 'a \<Rightarrow> 'q set \<Rightarrow> bool" where
  "split_language_equiv_partition_pred \<A> p1 a p2 \<equiv> \<comment>\<open>(a, p2) is a splitter of p1.\<close>
    (fst (split_language_equiv_partition \<A> p1 a p2) \<noteq> {}) \<and> 
    (snd (split_language_equiv_partition \<A> p1 a p2) \<noteq> {})"

text \<open> Splitting according to this definition preserves the property 
        that the partition is a weak language equivalence partition. \<close>
lemma (in DFA) split_language_equiv_partition___weak_language_equiv_set :
assumes split: "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
    and a_in: "a \<in> \<Sigma> \<A>"
    and equiv_p1: "is_weak_language_equiv_set \<A> p1"
    and equiv_p2: "is_weak_language_equiv_set \<A> p2"
shows "is_weak_language_equiv_set \<A> p1a \<and> is_weak_language_equiv_set \<A> p1b"
proof -
  from equiv_p1 have p1_subset: "p1 \<subseteq> \<Q> \<A>"
    unfolding is_weak_language_equiv_set_def
    by fast

  from split_language_equiv_partition_union [OF split]
  have p1_eq: "p1 = p1a \<union> p1b" .

  have "\<And>p. p = p1a \<or> p = p1b \<Longrightarrow> is_weak_language_equiv_set \<A> p"
  proof -
    fix p
    assume p_eq: "p = p1a \<or> p = p1b"

    from p_eq p1_eq have p_subset: "p \<subseteq> p1" by blast      
    show "is_weak_language_equiv_set \<A> p"
    proof
      from p1_subset p_subset 
      show "p \<subseteq> \<Q> \<A>" by blast
    next
      from equiv_p1 
      have "p1 \<subseteq> \<F> \<A> \<or> p1 \<inter> \<F> \<A> = {}"
        unfolding is_weak_language_equiv_set_def
        by fast
      with p_subset 
      show "p \<subseteq> \<F> \<A> \<or> p \<inter> \<F> \<A> = {}" 
        by blast
    next
      fix q1 q2
      assume q1_in_Q: "q1 \<in> \<Q> \<A>"
         and q2_in_Q: "q2 \<in> \<Q> \<A>"
         and q1_q2_equiv: "\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2"
         and q1_in_p: "q1 \<in> p"
     
      from p1_eq p_eq q1_in_p have q1_in_p1: "q1 \<in> p1" by auto
      with equiv_p1 have "q2 \<in> p1"
        unfolding is_weak_language_equiv_set_def
        using q1_in_Q q2_in_Q q1_q2_equiv q1_in_p1
        by blast
      with p1_eq have q2_in: "q2 \<in> p1a \<or> q2 \<in> p1b" by simp

      obtain q1' q2' 
        where q1_delta: "(q1, a, q1') \<in> \<Delta> \<A>"
          and q2_delta: "(q2, a, q2') \<in> \<Delta> \<A>"
        using complete_LTS q1_in_Q q2_in_Q a_in
        unfolding LTS_is_complete_def by blast
      from \<L>_in_state___DFA___eq_reachable_step [OF DFA_axioms DFA_axioms q1_delta q2_delta
            q1_q2_equiv]
      have q1'_q2'_equiv: "\<L>_in_state \<A> q1' = \<L>_in_state \<A> q2'" .

      from q1_delta q2_delta \<Delta>_consistent have
         "q1' \<in> \<Q> \<A>" "q2' \<in> \<Q> \<A>" by simp_all
      hence in_p2 : "q1' \<in> p2 \<longleftrightarrow> q2' \<in> p2"
        using is_weak_language_equiv_setD 
            [OF equiv_p2 _ _ q1'_q2'_equiv]
        by simp
      
      from in_p2 p_eq q1_in_p q2_in split[symmetric]
      show "q2 \<in> p"
        using q1_delta [unfolded \<delta>_in_\<Delta>_iff] q2_delta [unfolded \<delta>_in_\<Delta>_iff]
        unfolding split_language_equiv_partition_alt_def [OF p1_subset a_in]
        by auto
    qed
  qed
  thus ?thesis by simp
qed

lemma (in DFA) split_language_equiv_partition_step :
assumes is_part: "is_weak_language_equiv_partition \<A> P"
    and p1_in : "p1 \<in> P"
    and a_in: "a \<in> \<Sigma> \<A>"
    and p2_equiv_set: "is_weak_language_equiv_set \<A> p2"    
    and split_pred: "split_language_equiv_partition_pred \<A> p1 a p2"
    and split: "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
shows "is_weak_language_equiv_partition \<A> ((P - {p1}) \<union> {p1a, p1b})"
      "(card ((P - {p1}) \<union> {p1a, p1b}) = Suc (card P))"
proof 
  from split_pred split have 
        p1ab_neq_Nil: "p1a \<noteq> {}" "p1b \<noteq> {}"
  unfolding split_language_equiv_partition_pred_def by simp_all

  from is_part have  
    "P \<subseteq> Pow (\<Q> \<A>)"
    unfolding is_weak_language_equiv_partition_def is_partition_def by auto
  with p1_in have p1_sub: "p1 \<subseteq> \<Q> \<A>" by auto

  note p1ab_disj = split_language_equiv_partition_disjoint [OF split]
  note p1ab_union = split_language_equiv_partition_union [OF split]
  
  let ?P' = "((P - {p1}) \<union> {p1a, p1b})"
  show is_part_P': "is_partition (\<Q> \<A>) ?P'" and card_P': "card ?P' = Suc (card P)" 
  proof -
    note is_partition_refine [OF finite_\<Q> _ _ p1ab_neq_Nil p1ab_disj p1ab_union, 
                              where P = "P - {p1}"]
         is_part 
    moreover
    have "insert p1 P = P" using p1_in by auto
    ultimately show "is_partition (\<Q> \<A>) ?P'" "card ?P' = Suc (card P)" 
      by (simp_all add: is_weak_language_equiv_partition_def)
  qed

  {
    fix p
    assume p_in_P': "p \<in> ?P'"
    show "is_weak_language_equiv_set \<A> p"
    proof (cases "p \<in> P")
      case True
      with is_part show ?thesis
        unfolding is_weak_language_equiv_partition_def
        by simp
    next
      case False
      hence p_eq: "p = p1a \<or> p = p1b" using p_in_P' by simp
      show ?thesis
      proof -
        from p1_in is_part
        have p1_equiv_set: "is_weak_language_equiv_set \<A> p1"    
          unfolding is_weak_language_equiv_partition_def by simp

        note split_language_equiv_partition___weak_language_equiv_set
          [OF split a_in p1_equiv_set p2_equiv_set]
        with p_eq show ?thesis by metis
      qed
    qed
  }
qed

text\<open> If no more splitting is possible, the desired strong language equivalence partition has been found. \<close>
lemma (in DFA) split_language_equiv_partition_final___weak2 :
assumes is_part: "is_partition (\<Q> \<A>) P"
   and accept_P: "\<And>p. p \<in> P \<Longrightarrow> (p \<subseteq> \<F> \<A>) \<or> (p \<inter> \<F> \<A> = {})"
   and no_split: "\<And>p1 a p2. \<lbrakk>p1 \<in> P; a \<in> \<Sigma> \<A>; p2 \<in> P\<rbrakk> \<Longrightarrow> 
       \<not>(split_language_equiv_partition_pred \<A> p1 a p2)"
   and p0_in: "p0 \<in> P"
shows "is_weak2_language_equiv_set \<A> p0"
proof (rule ccontr)
  assume "\<not> is_weak2_language_equiv_set \<A> p0"
  then obtain q1_0 q2_0 where q12_0_in_p0: "q1_0 \<in> p0" "q2_0 \<in> p0" and
     not_\<L>_eq_q12_0: "\<L>_in_state \<A> q1_0 \<noteq> \<L>_in_state \<A> q2_0"
    using p0_in is_partition_in_subset[OF is_part p0_in] accept_P[OF p0_in]
    unfolding is_weak2_language_equiv_set_def
      by metis

    define counter_P where "counter_P \<equiv> \<lambda>(q1, q2, p, w).
        (p \<in> P \<and> q1 \<in> p \<and> q2 \<in> p \<and>
        ((w \<in> \<L>_in_state \<A> q1) \<noteq> (w \<in> \<L>_in_state \<A> q2)))"

  have "\<exists>q1 q2 p w. counter_P (q1, q2, p, w)" 
  proof -
    from not_\<L>_eq_q12_0 obtain w where
      "(w \<in> \<L>_in_state \<A> q1_0) \<noteq> (w \<in> \<L>_in_state \<A> q2_0)"
      by (simp add: set_eq_iff) metis

    thus ?thesis
      apply (rule_tac exI [where x = q1_0])
      apply (rule_tac exI [where x = q2_0])
      apply (rule_tac exI [where x = p0])
      apply (rule_tac exI [where x = w])
      apply (simp add: counter_P_def q12_0_in_p0 p0_in)
    done
  qed

  with ex_has_least_nat [where P = counter_P and m = "\<lambda>(q1, q2, p, w). length w"]
  obtain q1 q2 p w where 
    counter_ex: "counter_P (q1, q2, p, w)" and
    min_counter: "\<And>q1' q2' p' w'. counter_P (q1', q2', p', w') \<Longrightarrow> length w \<le> length w'"
    by auto metis

  from counter_ex have 
    p_in: "p \<in> P" and
    q12_in_p: "q1 \<in> p" "q2 \<in> p" and
    w_equiv: "(w \<in> \<L>_in_state \<A> q1) \<noteq> (w \<in> \<L>_in_state \<A> q2)"
    unfolding counter_P_def by simp_all

  from p_in is_part have p_sub: "p \<subseteq> \<Q> \<A>"
    unfolding is_partition_def by auto
  with q12_in_p have q12_in_Q: "q1 \<in> \<Q> \<A>" "q2 \<in> \<Q> \<A>" by auto

  have "w \<noteq> []"
    using accept_P [OF p_in]
          w_equiv q12_in_p
    by auto
  then obtain a w' where w_eq: "w = a # w'" by (cases w, blast)
  from w_equiv w_eq have a_in: "a \<in> \<Sigma> \<A>"
    unfolding \<L>_in_state_def by auto (metis \<Delta>_consistent)+

  obtain q1' q2' where
    \<delta>_q1a: "(\<delta> \<A>) (q1, a) = Some q1'" and
    \<delta>_q2a: "(\<delta> \<A>) (q2, a) = Some q2'"
    using DetSemiAutomaton_\<delta>_is_some [OF q12_in_Q(1) a_in]
    using DetSemiAutomaton_\<delta>_is_some [OF q12_in_Q(2) a_in]
    by blast

  from is_partition_find[of "\<Q> \<A>" P q1'] is_part
       \<delta>_wf[OF \<delta>_q1a]
  obtain p' where p'_in: "p' \<in> P" and q1'_in: "q1' \<in> p'"
     unfolding is_weak_language_equiv_partition_def by metis

  from no_split [OF p_in a_in p'_in]
  have q2'_in: "q2' \<in> p'"
    using q12_in_p q1'_in \<delta>_q1a \<delta>_q2a a_in p_in p'_in
    unfolding 
      split_language_equiv_partition_pred_def
      split_language_equiv_partition_def split_set_def
    by (auto simp add: \<delta>_in_\<Delta>_iff)

  from w_equiv have
    w'_equiv: "(w' \<in> \<L>_in_state \<A> q1') \<noteq> (w' \<in> \<L>_in_state \<A> q2')"
    unfolding w_eq
    by (simp add: \<delta>_in_\<Delta>_iff \<delta>_q1a \<delta>_q2a a_in)

  from min_counter [of q1' q2' p' w']
  show "False"
    unfolding counter_P_def
    using w'_equiv
    by (simp add: p'_in q1'_in q2'_in w_eq)
qed

lemma (in DFA) split_language_equiv_partition_final :
assumes is_part: "is_weak_language_equiv_partition \<A> P"
    and no_split: "\<And>p1 a p2. \<lbrakk>p1 \<in> P; a \<in> \<Sigma> \<A>; p2 \<in> P\<rbrakk> \<Longrightarrow> 
       \<not>(split_language_equiv_partition_pred \<A> p1 a p2)"
shows "P = Myhill_Nerode_partition \<A>"
proof (rule ccontr)
  assume not_strong_part: "P \<noteq> Myhill_Nerode_partition \<A>"

  define counter_P where "counter_P \<equiv> \<lambda>(q1, q2, p, w).
        (p \<in> P \<and> q1 \<in> p \<and> q2 \<in> p \<and>
        ((w \<in> \<L>_in_state \<A> q1) \<noteq> (w \<in> \<L>_in_state \<A> q2)))"

  have "\<exists>q1 q2 p w. counter_P (q1, q2, p, w)" 
  proof (rule ccontr)
    assume "\<not> (\<exists>q1 q2 p w. counter_P (q1, q2, p, w))"
    hence p_equiv: "\<And>q1 q2 p. \<lbrakk>q2 \<in> p; q1 \<in> p; p \<in> P\<rbrakk> \<Longrightarrow> \<L>_in_state \<A> q1 = \<L>_in_state \<A> q2"       
      unfolding counter_P_def by auto

    have sub1: "P \<subseteq> Myhill_Nerode_partition \<A>"
    proof 
      fix p
      assume p_in_P: "p \<in> P"
      from p_in_P is_part have p_subset: "p \<subseteq> \<Q> \<A>"
        unfolding is_weak_language_equiv_partition_def is_partition_def by auto
      from p_in_P is_part have "p \<noteq> {}"
        unfolding is_weak_language_equiv_partition_def is_partition_def by auto
      with p_subset obtain q where q_in: "q \<in> p" "q \<in> \<Q> \<A>" by auto

      from p_in_P is_part have p_equiv': "is_weak_language_equiv_set \<A> p"
        unfolding is_weak_language_equiv_partition_def by auto

      have "p = {q' \<in> \<Q> \<A>. \<L>_in_state \<A> q' = \<L>_in_state \<A> q}"
      proof 
        from p_equiv' q_in
        have "\<And>q'. \<lbrakk>q' \<in> \<Q> \<A> ; \<L>_in_state \<A> q' = \<L>_in_state \<A> q\<rbrakk> \<Longrightarrow> q' \<in> p"
          unfolding is_weak_language_equiv_set_def by metis
        thus "{q' \<in> \<Q> \<A>. \<L>_in_state \<A> q' = \<L>_in_state \<A> q} \<subseteq> p"
          by auto
      next
        from p_equiv [OF q_in(1) _ p_in_P] p_subset
        show "p \<subseteq> {q' \<in> \<Q> \<A>. \<L>_in_state \<A> q' = \<L>_in_state \<A> q}"
          by auto
      qed        
      with q_in(2) show "p \<in> Myhill_Nerode_partition \<A>"
        unfolding Myhill_Nerode_partition_alt_def
        by blast
    qed

    have sub2: "Myhill_Nerode_partition \<A> \<subseteq> P"
    proof 
      fix p
      assume "p \<in> Myhill_Nerode_partition \<A>"
      then obtain q 
      where q_in_Q: "q \<in> \<Q> \<A>" and
            p_eq: "p = {q' \<in> \<Q> \<A>. \<L>_in_state \<A> q' = \<L>_in_state \<A> q}"
        unfolding Myhill_Nerode_partition_alt_def
        by blast
      from p_eq q_in_Q have q_in_p: "q \<in> p"
        unfolding p_eq by simp

      from is_part have p_part: "is_partition (\<Q> \<A>) P"
        unfolding is_weak_language_equiv_partition_def by fast

      from p_part q_in_Q obtain p' 
      where p'_in: "p' \<in> P"
        and q_in_p': "q \<in> p'"
        unfolding is_partition_def by blast

      from p'_in is_part have p_equiv': "is_weak_language_equiv_set \<A> p'"
        unfolding is_weak_language_equiv_partition_def by auto
      have p'_subset: "p' \<subseteq> \<Q> \<A>"
        using is_partition_in_subset [OF p_part p'_in] .

      have "p' = p"       
      proof 
        from p_equiv [OF q_in_p' _ p'_in] p'_subset
        show "p' \<subseteq> p" 
          unfolding p_eq          
          by auto
      next
        from p_equiv' q_in_Q q_in_p'
        have "\<And>q'. \<lbrakk>q' \<in> \<Q> \<A>; \<L>_in_state \<A> q' = \<L>_in_state \<A> q\<rbrakk> \<Longrightarrow> q' \<in> p'"
          unfolding p_eq is_weak_language_equiv_set_def by metis
        thus "p \<subseteq> p'"
          unfolding p_eq 
          by auto
      qed        
      with p'_in show "p \<in> P" by fast
    qed

    from not_strong_part sub1 sub2 show False by simp
  qed

  with ex_has_least_nat [where P = counter_P and m = "\<lambda>(q1, q2, p, w). length w"]
  obtain q1 q2 p w where 
    counter_ex: "counter_P (q1, q2, p, w)" and
    min_counter: "\<And>q1' q2' p' w'. counter_P (q1', q2', p', w') \<Longrightarrow> length w \<le> length w'"
    by auto metis

  from counter_ex have 
    p_in: "p \<in> P" and
    q12_in_p: "q1 \<in> p" "q2 \<in> p" and
    w_equiv: "(w \<in> \<L>_in_state \<A> q1) \<noteq> (w \<in> \<L>_in_state \<A> q2)"
    unfolding counter_P_def by simp_all

  from p_in is_part have p_sub: "p \<subseteq> \<Q> \<A>"
    unfolding is_weak_language_equiv_partition_def is_partition_def by auto
  with q12_in_p have q12_in_Q: "q1 \<in> \<Q> \<A>" "q2 \<in> \<Q> \<A>" by auto

  have "w \<noteq> []"
    using is_weak_language_equiv_partitionD1[OF is_part p_in]
          w_equiv q12_in_p
    by auto
  then obtain a w' where w_eq: "w = a # w'" by (cases w, blast)
  from w_equiv w_eq have a_in: "a \<in> \<Sigma> \<A>"
    unfolding \<L>_in_state_def by auto (metis \<Delta>_consistent)+
  obtain q1' q2' where
    \<delta>_q1a: "(\<delta> \<A>) (q1, a) = Some q1'" and
    \<delta>_q2a: "(\<delta> \<A>) (q2, a) = Some q2'"
    using DetSemiAutomaton_\<delta>_is_some [OF q12_in_Q(1) a_in]
    using DetSemiAutomaton_\<delta>_is_some [OF q12_in_Q(2) a_in]
    by blast

  from is_partition_find[of "\<Q> \<A>" P q1'] is_part
       \<delta>_wf[OF \<delta>_q1a]
  obtain p' where p'_in: "p' \<in> P" and q1'_in: "q1' \<in> p'"
     unfolding is_weak_language_equiv_partition_def by metis

  from no_split [OF p_in a_in p'_in]
  have q2'_in: "q2' \<in> p'"
    using q12_in_p q1'_in \<delta>_q1a \<delta>_q2a a_in p_in p'_in
    unfolding 
      split_language_equiv_partition_pred_def
      split_language_equiv_partition_def split_set_def
    by (auto simp add: \<delta>_in_\<Delta>_iff)

  from w_equiv have
    w'_equiv: "(w' \<in> \<L>_in_state \<A> q1') \<noteq> (w' \<in> \<L>_in_state \<A> q2')"
    unfolding w_eq
    by (simp add: \<delta>_in_\<Delta>_iff \<delta>_q1a \<delta>_q2a a_in)

  from min_counter [of q1' q2' p' w']
  show "False"
    unfolding counter_P_def
    using w'_equiv
    by (simp add: p'_in q1'_in q2'_in w_eq)
qed


subsection \<open> Naive implementation \<close>

definition Hopcroft_naive where
  "Hopcroft_naive \<A> = 
    WHILEIT (is_weak_language_equiv_partition \<A>) 
            \<comment>\<open>invariant: loop variable has to be a partition satisfying the weak
            equivalence property.\<close>

            (\<lambda>P. \<exists>p1 a p2. (p1 \<in> P \<and> a \<in> \<Sigma> \<A> \<and> p2 \<in> P \<and> split_language_equiv_partition_pred \<A> p1 a p2))
            \<comment>\<open>loop condition: there exists a splitter (p1, a, p2) splitting P in \<A>.\<close>
            (\<lambda>P. do { 
               (p1, a, p2) \<leftarrow> SPEC (\<lambda>(p1,a,p2). p1 \<in> P \<and> a \<in> \<Sigma> \<A> \<and> p2 \<in> P \<and> 
                   split_language_equiv_partition_pred \<A> p1 a p2); 
               let (p1a, p1b) = split_language_equiv_partition \<A> p1 a p2;
               RETURN ((P - {p1}) \<union> {p1a, p1b})})
            \<comment>\<open>loop body: pick such a splitter (p1, a, p2) splitting P into (p1a, p1b)
            and modify partition to (P - {p1}) \<union> {p1a, p1b}\<close>
            (Hopcroft_accepting_partition \<A>)"
            \<comment>\<open>loop variable: initial partition {final states, non-final states}\<close>

lemma (in DFA) Hopcroft_naive_correct :
  "Hopcroft_naive \<A> \<le> SPEC (\<lambda>P. P = Myhill_Nerode_partition \<A>)"
unfolding Hopcroft_naive_def
proof (rule WHILEIT_rule [where R = "measure (\<lambda>P. card (\<Q> \<A>) - card P)"])
  show "wf (measure (\<lambda>P. card (\<Q> \<A>) - card P))" by simp
next
  show "is_weak_language_equiv_partition \<A> (Hopcroft_accepting_partition \<A>)"
    by (rule is_weak_language_equiv_partition_init)
next
  show "\<lbrakk>is_weak_language_equiv_partition \<A> P; \<exists>p1 a p2. p1 \<in> P \<and> a \<in> \<Sigma> \<A> \<and> p2 \<in> P \<and> split_language_equiv_partition_pred \<A> p1 a p2\<rbrakk>
         \<Longrightarrow> SPEC (\<lambda>(p1, a, p2). p1 \<in> P \<and> a \<in> \<Sigma> \<A> \<and> p2 \<in> P \<and> split_language_equiv_partition_pred \<A> p1 a p2) \<bind> (\<lambda>(p1, a, p2). let (p1a, p1b) = split_language_equiv_partition \<A> p1 a p2 in RETURN (P - {p1} \<union> {p1a, p1b}))
              \<le> SPEC (\<lambda>s'. is_weak_language_equiv_partition \<A> s' \<and> (s', P) \<in> measure (\<lambda>P. card (\<Q> \<A>) - card P))" for P
    apply (intro refine_vcg)
    apply (simp)
    apply (clarify)
  proof -
    fix p1 a p2 p1a p1b
    assume "p1 \<in> P" "a \<in> \<Sigma> \<A>"  "p2 \<in> P" and
           weak_part_P: "is_weak_language_equiv_partition \<A> P" and
           split_pred: "split_language_equiv_partition_pred \<A> p1 a p2" and
           eval_part: "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"

    from \<open>p2 \<in> P\<close> weak_part_P have weak_set_p2: "is_weak_language_equiv_set \<A> p2"
      unfolding is_weak_language_equiv_partition_def by simp

    note step = split_language_equiv_partition_step  [OF weak_part_P \<open>p1 \<in> P\<close> \<open>a \<in> \<Sigma> \<A>\<close> weak_set_p2 split_pred eval_part]

    from is_partition_card_P[OF finite_\<Q> is_weak_language_equiv_partitionD3[OF step(1)]] step(2)
    have "card P < card (\<Q> \<A>)" by simp

    with step
    show "is_weak_language_equiv_partition \<A> (insert p1a (insert p1b (P - {p1}))) \<and>
          card (\<Q> \<A>) - card (insert p1a (insert p1b (P - {p1}))) < card (\<Q> \<A>) - card P" 
      by simp
  qed
next
  show "\<lbrakk>is_weak_language_equiv_partition \<A> P; \<nexists>p1 a p2. p1 \<in> P \<and> a \<in> \<Sigma> \<A> \<and> p2 \<in> P \<and> split_language_equiv_partition_pred \<A> p1 a p2\<rbrakk> \<Longrightarrow> P = Myhill_Nerode_partition \<A>" for P
    by (metis split_language_equiv_partition_final)
qed

(*    --- OLD PROOF ---

proof (rule WHILEIT_rule [where R = "measure (\<lambda>P. card (\<Q> \<A>) - card P)"])
  show "wf (measure (\<lambda>P. card (\<Q> \<A>) - card P))" by simp
next
  show "is_weak_language_equiv_partition \<A> (Hopcroft_accepting_partition \<A>)"
    by (rule is_weak_language_equiv_partition_init)
next
  note weak_part_P = goal3(1)
  show ?case
    apply (intro refine_vcg)
    apply (simp)
    apply (clarify)
  proof -
    fix p1 a p2 p1a p1b
    assume "p1 \<in> P" "a \<in> \<Sigma> \<A>"  "p2 \<in> P" and
           split_pred: "split_language_equiv_partition_pred \<A> p1 a p2" and
           eval_part: "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"

    from `p2 \<in> P` weak_part_P have weak_set_p2: "is_weak_language_equiv_set \<A> p2"
      unfolding is_weak_language_equiv_partition_def by simp

    note step = split_language_equiv_partition_step  [OF weak_part_P `p1 \<in> P` `a \<in> \<Sigma> \<A>` weak_set_p2 
      split_pred eval_part]

    from is_partition_card_P[OF finite_\<Q> is_weak_language_equiv_partitionD3[OF step(1)]] step(2)
    have "card P < card (\<Q> \<A>)" by simp

    with step
    show "is_weak_language_equiv_partition \<A> (insert p1a (insert p1b (P - {p1}))) \<and>
          card (\<Q> \<A>) - card (insert p1a (insert p1b (P - {p1}))) < card (\<Q> \<A>) - card P" 
      by simp
  qed
next
  case goal4 thus ?case
    by (metis split_language_equiv_partition_final)
qed

*)


subsection \<open> Abstract implementation \<close>

text \<open> The naive implementation captures the main ideas. However, one would like to optimise 
  for sets @{text p1}, @{text p2} and a label @{text a}. In the following, an explicit 
  set of possible choices for @{text p2} and @{text a} is maintained. An element from this
  set is chosen, all elements of the current partition processed and the set of possible choices
  (the splitter set) updated.

  For efficiency reasons, the splitter set should be as small as possible. The following lemma
  guarantees that a possible choice that has been split can be replaced by both split
  subsets.
\<close>

lemma split_language_equiv_partition_pred_split :
assumes p2ab_union: "p2a \<union> p2b = p2"
    and part_pred_p2: "split_language_equiv_partition_pred \<A> p1 a p2"
shows "split_language_equiv_partition_pred \<A> p1 a p2a \<or>
      split_language_equiv_partition_pred \<A> p1 a p2b"
proof -
  obtain p1a p1b where p1ab_eq: 
    "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
    by (rule prod.exhaust)

  with part_pred_p2 have p1ab_neq_emp: "p1a \<noteq> {}" "p1b \<noteq> {}"
    unfolding split_language_equiv_partition_pred_def
    by simp_all
  let ?P = "\<lambda>p2 q. \<exists>q'\<in>p2. (q, a, q') \<in> \<Delta> \<A>"

  from p1ab_neq_emp p1ab_eq 
    obtain qa qb 
    where qa_in: "qa \<in> p1" 
      and qb_in: "qb \<in> p1"
      and qa_P_p2: "?P p2 qa"
      and qb_neg_P_p2: "\<not> (?P p2 qb)"
    unfolding split_language_equiv_partition_def
              split_set_def
    by auto

  from qb_neg_P_p2 p2ab_union
  have qb_nin_P_p2ab : "\<not> (?P p2a qb)" "\<not> (?P p2b qb)"
    by auto

  show ?thesis
  proof (cases "?P p2a qa")
    case True 
    hence "split_language_equiv_partition_pred \<A> p1 a p2a"
      unfolding split_language_equiv_partition_pred_def
                split_language_equiv_partition_def split_set_def      
      using qb_nin_P_p2ab(1) qa_in qb_in
      by auto 
    thus ?thesis ..
  next
    case False
    with p2ab_union qa_P_p2 have "?P p2b qa" 
      by auto
    hence "split_language_equiv_partition_pred \<A> p1 a p2b"
      unfolding split_language_equiv_partition_pred_def
                split_language_equiv_partition_def split_set_def      
      using qb_nin_P_p2ab(2) qa_in qb_in
      by auto 
    thus ?thesis ..
  qed
qed

text \<open>
  More interestingly, if one already knows that there is no split according to a set @{text p2}
  (as it is for example not in the set of splitters), then it is sufficient to consider only one
  of its split components. 
\<close>
lemma (in DFA) split_language_equiv_partition_pred_split_neg :
assumes p2ab_union: "p2a \<union> p2b = p2"
    and p2ab_dist: "p2a \<inter> p2b = {}"
    and part_pred_p2: "\<not> (split_language_equiv_partition_pred \<A> p1 a p2)"
shows "(split_language_equiv_partition_pred \<A> p1 a p2a) \<longleftrightarrow>
       (split_language_equiv_partition_pred \<A> p1 a p2b)"
proof -
  obtain p1a p1b where p1ab_eq: 
    "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
    by (rule prod.exhaust) 
  with part_pred_p2 have p1ab_eq_emp: "p1a = {} \<or> p1b = {}"
    unfolding split_language_equiv_partition_pred_def
    by simp

  obtain p1aa p1ba where p1aba_eq: 
    "split_language_equiv_partition \<A> p1 a p2a = (p1aa, p1ba)"
    by (rule prod.exhaust) 

  obtain p1ab p1bb where p1abb_eq: 
    "split_language_equiv_partition \<A> p1 a p2b = (p1ab, p1bb)"
    by (rule prod.exhaust) 

  define P where "P \<equiv> \<lambda>p2 q. \<exists>q'\<in>p2. (q, a, q') \<in> \<Delta> \<A>"
  from p1aba_eq [symmetric] p1abb_eq[symmetric] p1ab_eq[symmetric] 
  have p1_eval: "
     p1aa = {q \<in> p1. P p2a q} \<and>
     p1ba = {q \<in> p1. \<not>P p2a q} \<and>
     p1ab = {q \<in> p1. P p2b q} \<and>
     p1bb = {q \<in> p1. \<not>P p2b q} \<and>
     p1a = {q \<in> p1. P p2 q} \<and>
     p1b = {q \<in> p1. \<not>P p2 q}"
  unfolding split_language_equiv_partition_def split_set_def P_def
  by simp
  
  have P_p2: "\<And>q. P p2 q = (P p2a q \<or> P p2b q)"
    by (simp add: P_def p2ab_union[symmetric])
       blast

  from p2ab_dist have "\<And>q. \<not>(P p2a q) \<or> \<not>(P p2b q)" 
    unfolding P_def
    by (auto simp add: \<delta>_in_\<Delta>_iff)
  with p1ab_eq_emp 
  have p1abb_eq_emp: "p1aa = {} \<or> p1ba = {} \<longleftrightarrow> p1ab = {} \<or> p1bb = {}"
    by (simp add: p1_eval P_p2) auto
  thus ?thesis
    unfolding split_language_equiv_partition_pred_def
              p1abb_eq p1aba_eq
    by simp blast
qed

text \<open> If a set @text{p1} can be split, then each superset can be split as well. \<close> 
lemma split_language_equiv_partition_pred___superset_p1:
assumes split_pred: "split_language_equiv_partition_pred \<A> p1 a p2"
    and p1_sub: "p1 \<subseteq> p1'"
shows "split_language_equiv_partition_pred \<A> p1' a p2"
proof -  
  obtain p1a p1b where p1ab_eq: 
    "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
    by (rule prod.exhaust) 
  obtain p1a' p1b' where p1ab_eq': 
    "split_language_equiv_partition \<A> p1' a p2 = (p1a', p1b')"
    by (rule prod.exhaust) 

  have "p1a \<subseteq> p1a' \<and> p1b \<subseteq> p1b'"
    using p1ab_eq p1ab_eq' p1_sub
    unfolding split_language_equiv_partition_def split_set_def
    by auto
  with split_pred 
  show ?thesis
    unfolding split_language_equiv_partition_pred_def
              p1ab_eq p1ab_eq'
    by auto
qed


subsubsection \<open> Splitting whole Partitions \<close>

definition split_language_equiv_partition_set where
  "split_language_equiv_partition_set \<A> a p p' =
   (let (p1', p2') = split_language_equiv_partition \<A> p' a p in
          {p1', p2'} \<inter> {p. p \<noteq> {}})"

definition Hopcroft_split where
  "Hopcroft_split \<A> p a res P =   
   (res \<union> \<Union>((split_language_equiv_partition_set \<A> a p) ` P))"
\<comment>\<open>split all p' \<in> P with splitter (a, p)\<close>

lemmas Hopcroft_split_full_def =
  Hopcroft_split_def [unfolded split_language_equiv_partition_set_def[abs_def]]
  
lemma Hopcroft_split_Nil [simp] :
  "Hopcroft_split \<A> p a res {} = res"
  unfolding Hopcroft_split_def
  by simp

definition Hopcroft_split_aux where
  "Hopcroft_split_aux \<A> p2 a res p1 =
   (let (p1a, p1b) = split_language_equiv_partition \<A> p1 a p2 in
      (if (p1a = {} \<and> p1b = {}) then res else
      (if p1a = {} then (insert p1b res) else
      (if p1b = {} then (insert p1a res) else
        (insert p1a (insert p1b res))))))"

lemma Hopcroft_split_aux_alt_def :
assumes p1_neq_Emp: "p1 \<noteq> {}"
shows "Hopcroft_split_aux \<A> p2 a res p1 =
   (let (p1a, p1b) = split_language_equiv_partition \<A> p1 a p2 in
      (if (p1a = {} \<or> p1b = {}) then (insert p1 res) else
        (insert p1a (insert p1b res))))"
proof -
  obtain p1a p1b where p1ab_eq: "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
    by (rule prod.exhaust)

  note p1ab_union = split_language_equiv_partition_union [OF p1ab_eq]
  note p1ab_disj = split_language_equiv_partition_disjoint [OF p1ab_eq]

  from p1ab_union p1ab_disj p1ab_eq p1_neq_Emp show ?thesis
  by (simp add: Hopcroft_split_aux_def p1ab_eq)
qed

lemma Hopcroft_split_Insert [simp] :
"Hopcroft_split \<A> p2 a res (insert p1 P) = 
 Hopcroft_split \<A> p2 a (Hopcroft_split_aux \<A> p2 a res p1) P"
by (cases "split_language_equiv_partition \<A> p1 a p2", 
    simp add: Hopcroft_split_def split_language_equiv_partition_set_def 
              Hopcroft_split_aux_def Let_def)

lemma (in DFA) Hopcroft_split_correct :
assumes is_part: "is_weak_language_equiv_partition \<A> (res \<union> P)"
    and p2_equiv_set: "is_weak_language_equiv_set \<A> p2"
    and a_in: "a \<in> \<Sigma> \<A>"
    and res_P_disjoint: "res \<inter> P = {}"
shows "is_weak_language_equiv_partition \<A> 
         (Hopcroft_split \<A> p2 a res P)" (is "?P1 res P")
      "(Hopcroft_split \<A> p2 a res P) \<noteq> (res \<union> P) \<longrightarrow>
        card (res \<union> P) < card (Hopcroft_split \<A> p2 a res P)" (is "?P2 res P")
proof - 
  from is_part finite_\<Q> have "finite (res \<union> P)"
    unfolding is_weak_language_equiv_partition_def
    by (metis is_partition_finite)
  hence fin_P: "finite P" by simp

  have "finite P \<Longrightarrow> res \<inter> P = {} \<Longrightarrow> is_weak_language_equiv_partition \<A> (res \<union> P) \<Longrightarrow> ?P1 res P \<and> ?P2 res P"
  proof (induct arbitrary: res rule: finite_induct)
    case empty thus ?case by simp
  next
    case (insert p1 P res)
    note p1_nin_P = insert(2)
    note ind_hyp = insert(3)
    note res_P_disjoint = insert(4)
    note is_part_p1 = insert(5)

    from res_P_disjoint have p1_nin_res: "p1 \<notin> res" by auto
    from is_part_p1
    have p1_neq_Emp: "p1 \<noteq> {}" and p1_sub: "p1 \<subseteq> \<Q> \<A>"
      unfolding is_weak_language_equiv_partition_def
                is_partition_def
      by auto
      
    obtain p1a p1b where p1ab_eq: "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
      by (cases "split_language_equiv_partition \<A> p1 a p2", blast)
    note p1ab_union = split_language_equiv_partition_union [OF p1ab_eq]

    let ?res'  = "Hopcroft_split_aux \<A> p2 a res p1"
    have pre: "is_weak_language_equiv_partition \<A> (?res' \<union> P) \<and>
               (?res' \<inter> P = {}) \<and>
               (((?res' \<union> P) \<noteq> insert p1 (res \<union> P)) \<longrightarrow>
                card (insert p1 (res \<union> P)) < card (?res' \<union> P))"
    proof (cases "p1a = {}")
      case True note p1a_eq = True
      hence p1b_eq: "p1b = p1" using p1ab_union by simp
      show ?thesis
        unfolding Hopcroft_split_aux_def p1ab_eq p1a_eq p1b_eq
        using p1_neq_Emp is_part_p1 res_P_disjoint p1_nin_P
        by simp
    next
      case False note p1a_neq_Emp = False
      show ?thesis
      proof (cases "p1b = {}")
        case True note p1b_eq = True
        hence p1a_eq: "p1a = p1" using p1ab_union by simp
        show ?thesis
          unfolding Hopcroft_split_aux_def p1ab_eq p1a_eq p1b_eq
          using p1_neq_Emp is_part_p1 res_P_disjoint p1_nin_P
          by simp
      next
        case False note p1b_neq_Emp = False
        have split_pred: "split_language_equiv_partition_pred \<A> p1 a p2"
          unfolding split_language_equiv_partition_pred_def
          by (simp add: p1ab_eq p1a_neq_Emp p1b_neq_Emp)
        
        have "\<And>p1'. p1' \<subseteq> p1 \<Longrightarrow> p1' \<notin> (res \<union> P)"
          using is_partition_distinct_subset 
            [OF is_weak_language_equiv_partitionD3 [OF is_part_p1], 
             where p = p1] p1_nin_P p1_nin_res 
          by simp
        hence p1ab_nin_P: "p1a \<notin> P \<and> p1b \<notin> P" using p1ab_union by simp

        have "(res \<union> P - {p1}) = res \<union> P" 
          using p1_nin_res p1_nin_P by auto
        with split_language_equiv_partition_step [OF is_part_p1 _ a_in 
            p2_equiv_set split_pred p1ab_eq]
        show ?thesis 
          unfolding Hopcroft_split_aux_def p1ab_eq 
          using p1a_neq_Emp p1b_neq_Emp p1_nin_res res_P_disjoint p1ab_nin_P
          by simp
      qed
    qed
    note pre1 = conjunct1 [OF pre]
    note pre2 = conjunct1 [OF conjunct2 [OF pre]]
    note pre3 = conjunct2 [OF conjunct2 [OF pre]]

    note ind_hyp' = ind_hyp[OF pre2 pre1]
    
    from conjunct1 [OF ind_hyp']
    have P1: "?P1 res (insert p1 P)" by simp

    from conjunct2 [OF ind_hyp'] pre3
    have P2: "?P2 res (insert p1 P)" 
      apply (cases "Hopcroft_split \<A> p2 a (Hopcroft_split_aux \<A> p2 a res p1) P =
     Hopcroft_split_aux \<A> p2 a res p1 \<union> P")
        apply simp
      apply (cases "Hopcroft_split_aux \<A> p2 a res p1 \<union> P \<noteq> insert p1 (res \<union> P)")
      apply simp_all
    done

    from P1 P2 show ?case ..
  qed
  with fin_P res_P_disjoint is_part
  show "?P1 res P" "?P2 res P" by simp_all
qed

lemma (in DFA) Hopcroft_split_correct_simple :
assumes is_part: "is_weak_language_equiv_partition \<A> P"
    and p2_in: "p2 \<in> P"
    and a_in: "a \<in> \<Sigma> \<A>"
shows "is_weak_language_equiv_partition \<A> (Hopcroft_split \<A> p2 a {} P)" 
      "(Hopcroft_split \<A> p2 a {} P) \<noteq> P \<Longrightarrow> 
       card P < card (Hopcroft_split \<A> p2 a {} P)"
proof - 
  from is_part p2_in have
    p2_equiv_set: "is_weak_language_equiv_set \<A> p2"
  unfolding is_weak_language_equiv_partition_def by simp

  note Hopcroft_split_correct [where ?res = "{}" and ?P=P, OF _ p2_equiv_set a_in]
  with is_part show 
    "is_weak_language_equiv_partition \<A> 
         (Hopcroft_split \<A> p2 a {} P)" 
    "(Hopcroft_split \<A> p2 a {} P) \<noteq> P \<Longrightarrow>
        card P < card (Hopcroft_split \<A> p2 a {} P)"
    by simp_all
qed

lemma (in DFA) split_language_equiv_partition_pred___split_not_eq:
assumes p1_in_split: "p1 \<in> (Hopcroft_split \<A> p2 a {} P)"
    and split_pred: "split_language_equiv_partition_pred \<A> p1 aa p2'"
shows "(aa, p2') \<noteq> (a, p2)"
proof -
  from p1_in_split
  obtain p pa pb where 
    pab_eq: "split_language_equiv_partition \<A> p a p2 = (pa, pb)" and
    p1_eq: "p1 = pa \<or> p1 = pb"
    unfolding Hopcroft_split_def split_language_equiv_partition_set_def[abs_def]
    by auto
      
  obtain p1a p1b where 
    p1ab_eq: "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
    by (rule prod.exhaust)

  have "p1a = p1 \<or> p1b = p1"
    using p1ab_eq p1_eq pab_eq
    unfolding split_language_equiv_partition_def split_set_def
    by auto
  with split_language_equiv_partition_disjoint [OF p1ab_eq]
       split_language_equiv_partition_subset [OF p1ab_eq]
  have "p1a = {} \<or> p1b = {}" by auto
  thus ?thesis    
    using split_pred
    by (rule_tac notI)
       (simp add: split_language_equiv_partition_pred_def
                  p1ab_eq)
qed  

lemma Hopcroft_split_in :
  "p \<in> Hopcroft_split \<A> p2 a {} P \<longleftrightarrow>
   ((p \<noteq> {}) \<and>
    (\<exists>p1 \<in> P. let (p1a, p1b) = split_language_equiv_partition \<A> p1 a p2 in 
             (p = p1a \<or> p = p1b)))"
unfolding Hopcroft_split_def split_language_equiv_partition_set_def[abs_def]
apply (simp del: ex_simps add: Bex_def ex_simps[symmetric])
apply (rule iff_exI)
apply (case_tac "split_language_equiv_partition \<A> x a p2")
apply auto
done


definition Hopcroft_splitted where
  "Hopcroft_splitted \<A> p a res P =   
   (res \<union> {(p', p1', p2')| p' p1' p2'. p' \<in> P \<and> p1' \<noteq> {} \<and> p2' \<noteq> {} \<and> 
      (p1', p2') = split_language_equiv_partition \<A> p' a p})"
  
lemma Hopcroft_splitted_Nil [simp] :
  "Hopcroft_splitted \<A> p a res {} = res"
  unfolding Hopcroft_splitted_def
  by simp

definition Hopcroft_splitted_aux where
  "Hopcroft_splitted_aux \<A> p2 a res p1 =
   (let (p1a, p1b) = split_language_equiv_partition \<A> p1 a p2 in
      (if p1a \<noteq> {} \<and> p1b \<noteq> {} then (insert (p1, p1a, p1b) res) else res))"

lemma Hopcroft_splitted_Insert [simp] :
"Hopcroft_splitted \<A> p2 a res (insert p1 P) = 
 Hopcroft_splitted \<A> p2 a (Hopcroft_splitted_aux \<A> p2 a res p1) P"
by (cases "split_language_equiv_partition \<A> p1 a p2", 
    auto simp add: Hopcroft_splitted_def Hopcroft_splitted_aux_def Let_def)

lemma Hopcroft_splitted_Insert_res :
"Hopcroft_splitted \<A> p2 a (insert ppp res) P = 
 insert ppp (Hopcroft_splitted \<A> p2 a res P)"
unfolding Hopcroft_splitted_def
by simp


lemma (in DFA) Hopcroft_split_in2 :
assumes is_part: "is_partition (\<Q> \<A>) P" and
        a_in:  "a \<in> \<Sigma> \<A>"
shows
  "p \<in> Hopcroft_split \<A> p2 a {} P \<longleftrightarrow>
   ((p \<in> P \<and> (\<forall>pa pb. (p, pa, pb) \<notin> (Hopcroft_splitted \<A> p2 a {} P))) \<or>
    (\<exists>p1 p1a p1b. (p1, p1a, p1b) \<in> Hopcroft_splitted \<A> p2 a {} P \<and>
                 (p = p1a \<or> p = p1b)))"
   (is "?ls = (?rs1 \<or> ?rs2)")
proof
  assume "?ls"
  then obtain p1 where
    p_not_emp: "p \<noteq> {}" and
    p1_in_P: "p1 \<in> P" and
    p_eq': "let (p1a, p1b) = split_language_equiv_partition \<A> p1 a p2 in 
             (p = p1a \<or> p = p1b)"
    by (simp add: Hopcroft_split_in Bex_def, metis)
  obtain p1a p1b where p1ab_eq: 
    "split_language_equiv_partition \<A> p1 a p2 = (p1a, p1b)"
    by (rule prod.exhaust) 
  with p_eq' have p_eq: "p = p1a \<or> p = p1b" by simp

  from is_partition_in_subset [OF is_part p1_in_P]
  have p1_sub: "p1 \<subseteq> \<Q> \<A>" .

  show "?rs1 \<or> ?rs2"
  proof (cases "(p1, p1a, p1b) \<in> Hopcroft_splitted \<A> p2 a {} P")
    case True
    with p_eq have "?rs2" by blast 
    thus ?thesis ..
  next
    case False note not_split = False
    hence p1ab_eq_Nil: "p1a = {} \<or> p1b = {}" 
      unfolding Hopcroft_splitted_def
      by (simp add: p1_in_P p1ab_eq)
    with split_language_equiv_partition_union [OF p1ab_eq] 
         p_not_emp p_eq
    have p1_eq: "p1 = p" by auto

    from p1_in_P p1_eq p1ab_eq p1ab_eq_Nil
    have ?rs1
      by (simp add: Hopcroft_splitted_def, metis)
    thus ?thesis ..
  qed
next
  assume rs12 : "?rs1 \<or> ?rs2"
  show "?ls"
  proof (cases ?rs1)
    case True note rs1 = this
    obtain pa pb where pab_eq: 
      "split_language_equiv_partition \<A> p a p2 = (pa, pb)"
      by (rule prod.exhaust)
    with rs1
    have pab_eq_emp: "pa = {} \<or> pb = {}" 
      unfolding Hopcroft_splitted_def
      by auto

    from rs1 is_partition_in_subset [OF is_part]
    have p_sub: "p \<subseteq> \<Q> \<A>" by simp

    from rs1 is_part 
    have p_not_emp: "p \<noteq> {}" 
      unfolding is_partition_def by auto

    from split_language_equiv_partition_union [OF pab_eq]
         pab_eq_emp p_not_emp rs1 pab_eq  
    show ?ls
      apply (simp add: Hopcroft_splitted_def Hopcroft_split_in Bex_def)
      apply (rule exI [where x = "p"])
      apply auto
    done
  next
    case False 
    with rs12 have "?rs2" by fast
    then obtain p1 p1a p1b where
       in_splitted: "(p1, p1a, p1b) \<in> Hopcroft_splitted \<A> p2 a {} P" and
       p_eq: "(p = p1a \<or> p = p1b)" by blast
    thus ?ls
      unfolding Hopcroft_splitted_def 
      by (auto simp add: Hopcroft_split_in Bex_def)
  qed
qed

lemma (in DFA) Hopcroft_split_in2_E [consumes 3,
   case_names in_P in_splitted]:
assumes "is_partition (\<Q> \<A>) P" "a \<in> \<Sigma> \<A>" "p \<in> Hopcroft_split \<A> p2 a {} P"
obtains (in_P) "p \<in> P" "\<And>pa pb. (p, pa, pb) \<notin> (Hopcroft_splitted \<A> p2 a {} P)"
      | (in_splitted) p1 p1a p1b where 
          "(p1, p1a, p1b) \<in> Hopcroft_splitted \<A> p2 a {} P"
          "p = p1a \<or> p = p1b"
using Hopcroft_split_in2 assms
by blast

lemma (in DFA) Hopcroft_split_eq :
assumes split_eq: "Hopcroft_split \<A> p a {} P = P"
    and a_in: "a \<in> \<Sigma> \<A>"
    and is_part: "is_partition (\<Q> \<A>) P"
shows "Hopcroft_splitted \<A> p a {} P = {}"
proof (rule ccontr)
  assume "Hopcroft_splitted \<A> p a {} P \<noteq> {}"
  then obtain p1 p1a p1b where in_splitted: "(p1, p1a, p1b) \<in> Hopcroft_splitted \<A> p a {} P"
    by auto
  hence p1ab_neq_Emp: "p1a \<noteq> {}" "p1b \<noteq> {}" and
        p1_in_P: "p1 \<in> P" and
        p1ab_eq: "split_language_equiv_partition \<A> p1 a p = (p1a, p1b)"
    unfolding Hopcroft_splitted_def by simp_all

  from is_partition_in_subset [OF is_part p1_in_P]
  have p1_sub: "p1 \<subseteq> \<Q> \<A>" .

  note p1ab_union = split_language_equiv_partition_union [OF p1ab_eq]
  note p1ab_disjoint = split_language_equiv_partition_disjoint [OF p1ab_eq]

  from p1ab_union p1ab_disjoint p1ab_neq_Emp 
  have "p1a \<inter> p1 \<noteq> {} \<and> p1a \<noteq> p1" by auto

  hence p1a_nin_P: "p1a \<notin> P"
    using p1_in_P is_part
    unfolding is_partition_def 
    by blast

  have p1a_in_split: "p1a \<in> Hopcroft_split \<A> p a {} P"
    unfolding Hopcroft_split_full_def 
    apply (simp add: Bex_def)
    apply (rule exI [where x = p1])
    apply (simp add: p1ab_eq p1_in_P p1ab_neq_Emp(1))
  done

  from p1a_nin_P p1a_in_split split_eq 
  show "False"
    by simp
qed


subsubsection \<open> Updating the set of Splitters \<close>

definition Hopcroft_update_splitters_pred_aux_upper :: 
"'a set \<Rightarrow> ('q set \<times> 'q set \<times> 'q set) set \<Rightarrow> ('q set) set \<Rightarrow>
    ('a \<times> 'q set) set \<Rightarrow> ('a \<times> 'q set) set \<Rightarrow> bool"
where
 "Hopcroft_update_splitters_pred_aux_upper Q splitted P L L' \<longleftrightarrow> 
  (\<forall>a p. (a, p) \<in> L' \<longrightarrow>
         ((a, p) \<in> L \<and> (\<forall>pa pb. (p, pa, pb) \<notin> splitted)) \<or>
         (\<exists>p' pa pb. (p', pa, pb) \<in> splitted \<and> a \<in> Q \<and> (p = pa \<or> p = pb)))"

definition Hopcroft_update_splitters_pred_aux_lower_not_splitted ::
"'a set \<Rightarrow> ('q set \<times> 'q set \<times> 'q set) set \<Rightarrow> ('q set) set \<Rightarrow>
    ('a \<times> 'q set) set \<Rightarrow> ('a \<times> 'q set) set \<Rightarrow> bool"
where
 "Hopcroft_update_splitters_pred_aux_lower_not_splitted Q splitted P L L' \<longleftrightarrow> 
   (\<forall>a p. ((a, p) \<in> L \<and> a \<in> Q \<and> p \<in> P \<and> 
          (\<forall>pa pb. (p, pa, pb) \<notin> splitted)) \<longrightarrow>
          (a, p) \<in> L')"

definition Hopcroft_update_splitters_pred_aux_lower_splitted_in_L ::
"'a set \<Rightarrow> ('q set \<times> 'q set \<times> 'q set) set \<Rightarrow> ('q set) set \<Rightarrow>
    ('a \<times> 'q set) set \<Rightarrow> ('a \<times> 'q set) set \<Rightarrow> bool"
where
 "Hopcroft_update_splitters_pred_aux_lower_splitted_in_L Q splitted P L L' \<longleftrightarrow> 
   (\<forall>a p pa pb. 
          ((a, p) \<in> L \<and> a \<in> Q \<and> (p, pa, pb) \<in> splitted) \<longrightarrow>
           ((a, pa) \<in> L') \<and> (a, pb) \<in> L')"


definition Hopcroft_update_splitters_pred_aux_lower_splitted ::
"'a set \<Rightarrow> ('q set \<times> 'q set \<times> 'q set) set \<Rightarrow> ('q set) set \<Rightarrow>
    ('a \<times> 'q set) set \<Rightarrow> ('a \<times> 'q set) set \<Rightarrow> bool"
where
 "Hopcroft_update_splitters_pred_aux_lower_splitted Q splitted P L L' \<longleftrightarrow> 
   (\<forall>a p pa pb. 
          (a \<in> Q \<and> (p, pa, pb) \<in> splitted) \<longrightarrow>
           ((a, pa) \<in> L') \<or> (a, pb) \<in> L')"


definition Hopcroft_update_splitters_pred_aux_lower ::
"'a set \<Rightarrow> ('q set \<times> 'q set \<times> 'q set) set \<Rightarrow> ('q set) set \<Rightarrow>
    ('a \<times> 'q set) set \<Rightarrow> ('a \<times> 'q set) set \<Rightarrow> bool"
where
 "Hopcroft_update_splitters_pred_aux_lower Q splitted P L L' \<longleftrightarrow> 
  Hopcroft_update_splitters_pred_aux_lower_not_splitted Q splitted P L L' \<and>
  Hopcroft_update_splitters_pred_aux_lower_splitted_in_L Q splitted P L L' \<and>
  Hopcroft_update_splitters_pred_aux_lower_splitted Q splitted P L L'"

lemmas Hopcroft_update_splitters_pred_aux_lower_full_def =
  Hopcroft_update_splitters_pred_aux_lower_def
  [unfolded Hopcroft_update_splitters_pred_aux_lower_not_splitted_def
            Hopcroft_update_splitters_pred_aux_lower_splitted_def
            Hopcroft_update_splitters_pred_aux_lower_splitted_in_L_def]

definition Hopcroft_update_splitters_pred_aux where
 "Hopcroft_update_splitters_pred_aux Q splitted P L L' \<longleftrightarrow>
  Hopcroft_update_splitters_pred_aux_lower Q splitted P L L' \<and> 
  Hopcroft_update_splitters_pred_aux_upper Q splitted P L L'"

lemmas Hopcroft_update_splitters_pred_aux_full_def =
  Hopcroft_update_splitters_pred_aux_def
  [unfolded Hopcroft_update_splitters_pred_aux_lower_full_def
            Hopcroft_update_splitters_pred_aux_upper_def,
   simplified]

lemma Hopcroft_update_splitters_pred_aux_I [intro!]:
 "\<lbrakk>Hopcroft_update_splitters_pred_aux_lower_not_splitted Q splitted P L L';
   Hopcroft_update_splitters_pred_aux_lower_splitted Q splitted P L L';
   Hopcroft_update_splitters_pred_aux_lower_splitted_in_L Q splitted P L L';
   Hopcroft_update_splitters_pred_aux_upper Q splitted P L L'\<rbrakk> \<Longrightarrow>
  Hopcroft_update_splitters_pred_aux Q splitted P L L'"
unfolding Hopcroft_update_splitters_pred_aux_def 
          Hopcroft_update_splitters_pred_aux_lower_def
by simp

lemma Hopcroft_update_splitters_pred_aux_upper___is_upper :
  "\<lbrakk>Hopcroft_update_splitters_pred_aux_upper Q splitted P L L'; L'' \<subseteq> L'\<rbrakk> \<Longrightarrow>
   Hopcroft_update_splitters_pred_aux_upper Q splitted P L L''"
unfolding Hopcroft_update_splitters_pred_aux_upper_def
by auto

lemma Hopcroft_update_splitters_pred_aux_lower___is_lower :
  "\<lbrakk>Hopcroft_update_splitters_pred_aux_lower Q splitted P L L'; L' \<subseteq> L''\<rbrakk> \<Longrightarrow>
   Hopcroft_update_splitters_pred_aux_lower Q splitted P L L''"
unfolding Hopcroft_update_splitters_pred_aux_lower_full_def
by blast

lemma Hopcroft_update_splitters_pred_aux_Emp_Id :
  "Hopcroft_update_splitters_pred_aux Q {} P L L"
   unfolding Hopcroft_update_splitters_pred_aux_def
   by (simp add: Hopcroft_update_splitters_pred_aux_upper_def
                 Hopcroft_update_splitters_pred_aux_lower_full_def)

definition Hopcroft_update_splitters_pred_aux_splitted_equiv_pred where
"Hopcroft_update_splitters_pred_aux_splitted_equiv_pred splitted1 splitted2 \<longleftrightarrow>
 (\<forall>p2 p2a p2b. (p2, p2a, p2b) \<in> splitted1 \<longrightarrow> 
    (p2, p2a, p2b) \<in> splitted2 \<or> (p2, p2b, p2a) \<in> splitted2) \<and>
 (\<forall>p2 p2a p2b. (p2, p2a, p2b) \<in> splitted2 \<longrightarrow> 
    (p2, p2a, p2b) \<in> splitted1 \<or> (p2, p2b, p2a) \<in> splitted1)"

lemma Hopcroft_update_splitters_pred_aux_splitted_equiv_pred_nin :
"Hopcroft_update_splitters_pred_aux_splitted_equiv_pred sp1 sp2 \<Longrightarrow>
 (\<forall>pa pb. (p, pa, pb) \<notin> sp1) \<longleftrightarrow> (\<forall>pa pb. (p, pa, pb) \<notin> sp2)"
unfolding Hopcroft_update_splitters_pred_aux_splitted_equiv_pred_def
by metis

lemma Hopcroft_update_splitters_pred_aux_splitted_upper_swap_rule :
assumes equiv_pred: "Hopcroft_update_splitters_pred_aux_splitted_equiv_pred sp1 sp2"
    and pre: "Hopcroft_update_splitters_pred_aux_upper Q sp1 P L L'"
shows "Hopcroft_update_splitters_pred_aux_upper Q sp2 P L L'"
using pre
unfolding Hopcroft_update_splitters_pred_aux_upper_def
  apply (simp add: Hopcroft_update_splitters_pred_aux_splitted_equiv_pred_nin [OF equiv_pred])
  apply (insert equiv_pred [unfolded Hopcroft_update_splitters_pred_aux_splitted_equiv_pred_def])
  apply metis
done   

lemma Hopcroft_update_splitters_pred_aux_splitted_lower_not_splitted_swap_rule :
assumes equiv_pred: "Hopcroft_update_splitters_pred_aux_splitted_equiv_pred sp1 sp2"
    and pre: "Hopcroft_update_splitters_pred_aux_lower_not_splitted Q sp1 P L L'"
shows "Hopcroft_update_splitters_pred_aux_lower_not_splitted Q sp2 P L L'"
using pre
unfolding Hopcroft_update_splitters_pred_aux_lower_not_splitted_def
  by (simp add: Hopcroft_update_splitters_pred_aux_splitted_equiv_pred_nin [OF equiv_pred])

lemma Hopcroft_update_splitters_pred_aux_splitted_lower_splitted_swap_rule :
assumes equiv_pred: "Hopcroft_update_splitters_pred_aux_splitted_equiv_pred sp1 sp2"
    and pre: "Hopcroft_update_splitters_pred_aux_lower_splitted Q sp1 P L L'"
shows "Hopcroft_update_splitters_pred_aux_lower_splitted Q sp2 P L L'"
using pre equiv_pred [unfolded Hopcroft_update_splitters_pred_aux_splitted_equiv_pred_def]
unfolding Hopcroft_update_splitters_pred_aux_lower_splitted_def
by metis

lemma Hopcroft_update_splitters_pred_aux_splitted_lower_splitted_in_L_swap_rule :
assumes equiv_pred: "Hopcroft_update_splitters_pred_aux_splitted_equiv_pred sp1 sp2"
    and pre: "Hopcroft_update_splitters_pred_aux_lower_splitted_in_L Q sp1 P L L'"
shows "Hopcroft_update_splitters_pred_aux_lower_splitted_in_L Q sp2 P L L'"
using pre equiv_pred [unfolded Hopcroft_update_splitters_pred_aux_splitted_equiv_pred_def]
unfolding Hopcroft_update_splitters_pred_aux_lower_splitted_in_L_def
by metis

lemma Hopcroft_update_splitters_pred_aux_splitted_swap_rule :
assumes equiv_pred: "Hopcroft_update_splitters_pred_aux_splitted_equiv_pred sp1 sp2"
    and pre: "Hopcroft_update_splitters_pred_aux Q sp1 P L L'"
shows "Hopcroft_update_splitters_pred_aux Q sp2 P L L'"
using Hopcroft_update_splitters_pred_aux_splitted_upper_swap_rule [OF equiv_pred, of Q P L L']
      Hopcroft_update_splitters_pred_aux_splitted_lower_splitted_swap_rule 
        [OF equiv_pred, of Q P L L']
      Hopcroft_update_splitters_pred_aux_splitted_lower_splitted_in_L_swap_rule 
        [OF equiv_pred, of Q P L L']
      Hopcroft_update_splitters_pred_aux_splitted_lower_not_splitted_swap_rule 
        [OF equiv_pred, of Q P L L']
      pre
unfolding Hopcroft_update_splitters_pred_aux_def
          Hopcroft_update_splitters_pred_aux_lower_def
by simp

definition Hopcroft_update_splitters_pred ::
  "('q, 'a, 'x) NFA_rec_scheme \<Rightarrow> 'q set \<Rightarrow> 'a \<Rightarrow> ('q set) set \<Rightarrow>
           ('a \<times> 'q set) set \<Rightarrow> ('a \<times> 'q set) set \<Rightarrow> bool"
where
 "Hopcroft_update_splitters_pred \<A> pp aa P L L' \<longleftrightarrow> 
  Hopcroft_update_splitters_pred_aux (\<Sigma> \<A>) (Hopcroft_splitted \<A> pp aa {} P) P 
    (L - {(aa, pp)}) L'"


lemma Hopcroft_update_splitters_pred_exists: 
  "\<exists>L'. Hopcroft_update_splitters_pred \<A> pp aa P L L'"
proof -
  let ?L' = "
    {(a, p) | a p. (a, p) \<in> L - {(aa, pp)} \<and> 
    (\<forall>pa pb. (p, pa, pb) \<notin> (Hopcroft_splitted \<A> pp aa {} P))} \<union>
    {(a, pa) | a p pa pb. a \<in> \<Sigma> \<A> \<and> (p, pa, pb) \<in> (Hopcroft_splitted \<A> pp aa {} P)} \<union>           
    {(a, pb) | a p pa pb. a \<in> \<Sigma> \<A> \<and> (p, pa, pb) \<in> (Hopcroft_splitted \<A> pp aa {} P)}"

  have "Hopcroft_update_splitters_pred \<A> pp aa P L ?L'"
    unfolding Hopcroft_update_splitters_pred_def
              Hopcroft_update_splitters_pred_aux_full_def
    by auto
  thus ?thesis by blast
qed


lemma Hopcroft_update_splitters_pred_in_E2 [consumes 2, case_names no_split split]: 
assumes L'_OK: "Hopcroft_update_splitters_pred \<A> pp aa P L L'"
    and in_L': "(a, p) \<in> L'"
obtains (no_split) "(a, p) \<in> L - {(aa, pp)}" "\<And>pa pb. (p, pa, pb) \<notin> (Hopcroft_splitted \<A> pp aa {} P)" 
      | (split) p' pa pb where "(p', pa, pb) \<in> (Hopcroft_splitted \<A> pp aa {} P)" 
                               "a \<in> \<Sigma> \<A>" "p = pa \<or> p = pb"
proof -
  from L'_OK have "Hopcroft_update_splitters_pred_aux_upper (\<Sigma> \<A>) 
                   (Hopcroft_splitted \<A> pp aa {} P) P (L - {(aa, pp)}) L'"
    unfolding Hopcroft_update_splitters_pred_def
              Hopcroft_update_splitters_pred_aux_def
    by fast
  with in_L' split no_split
  show ?thesis unfolding Hopcroft_update_splitters_pred_aux_upper_def 
  by blast
qed

lemma Hopcroft_update_splitters_pred___nin_splitted_in_L :
assumes L'_OK: "Hopcroft_update_splitters_pred \<A> p2 a P L L'"
    and p_in: "p \<in> P"
    and aa_in: "aa \<in> \<Sigma> \<A>"
    and nin_splitted: "\<And>pa pb. (p, pa, pb) \<notin> Hopcroft_splitted \<A> p2 a {} P"
    and in_L: "(aa, p) \<in> L - {(a, p2)}"
shows "(aa, p) \<in> L'"
proof -
  from L'_OK have "Hopcroft_update_splitters_pred_aux_lower_not_splitted (\<Sigma> \<A>) (Hopcroft_splitted \<A> p2 a {} P) P (L - {(a, p2)}) L'"
    unfolding Hopcroft_update_splitters_pred_def
              Hopcroft_update_splitters_pred_aux_def
              Hopcroft_update_splitters_pred_aux_lower_def
    by simp

  with in_L aa_in p_in nin_splitted
  show ?thesis 
  unfolding Hopcroft_update_splitters_pred_aux_lower_not_splitted_def
  by blast
qed

lemma Hopcroft_update_splitters_pred___in_splitted_in_L :
   "\<lbrakk>Hopcroft_update_splitters_pred \<A> p2 a P L L'; aa \<in> \<Sigma> \<A>;
    (p, pa, pb) \<in> Hopcroft_splitted \<A> p2 a {} P; (aa, p) \<in> L - {(a, p2)}\<rbrakk> \<Longrightarrow>
    (aa, pa) \<in> L' \<and> (aa, pb) \<in> L'"
unfolding Hopcroft_update_splitters_pred_def
          Hopcroft_update_splitters_pred_aux_def
          Hopcroft_update_splitters_pred_aux_lower_def
          Hopcroft_update_splitters_pred_aux_lower_splitted_in_L_def
by metis

lemma Hopcroft_update_splitters_pred___in_splitted :
  "\<lbrakk>Hopcroft_update_splitters_pred \<A> p2 a P L L'; aa \<in> \<Sigma> \<A>;
    (p, pa, pb) \<in> Hopcroft_splitted \<A> p2 a {} P\<rbrakk> \<Longrightarrow>
    (aa, pa) \<in> L' \<or> (aa, pb) \<in> L'"
unfolding Hopcroft_update_splitters_pred_def
          Hopcroft_update_splitters_pred_aux_def
          Hopcroft_update_splitters_pred_aux_lower_def
          Hopcroft_update_splitters_pred_aux_lower_splitted_def
by metis

lemma Hopcroft_update_splitters_pred___label_in :
"\<lbrakk>Hopcroft_update_splitters_pred \<A> p2 a P L L';
  \<And>ap. ap \<in> L \<Longrightarrow> fst ap \<in> \<Sigma> \<A>;
  (a', p) \<in> L'\<rbrakk> \<Longrightarrow> a' \<in> (\<Sigma> \<A>)"
by (rule Hopcroft_update_splitters_pred_in_E2) auto

lemma Hopcroft_update_splitters_pred___splitted_emp :
assumes L'_OK: "Hopcroft_update_splitters_pred \<A> p a P L L'" 
   and L_OK:  "\<And>ap. ap \<in> L \<Longrightarrow> fst ap \<in> \<Sigma> \<A> \<and> snd ap \<in> P"
   and splitted_emp: "Hopcroft_splitted \<A> p a {} P = {}"   
shows "L' = L - {(a, p)}"
proof (intro set_eqI iffI)
  fix aap2
  assume aap2_in: "aap2 \<in> L - {(a, p)}"
  obtain aa p2 where aap2_eq [simp]: "aap2 = (aa, p2)" by (rule prod.exhaust)

  from L_OK[of aap2] aap2_in have aap2_wf: "aa \<in> \<Sigma> \<A>" "p2 \<in> P" by simp_all

  from aap2_in splitted_emp
       Hopcroft_update_splitters_pred___nin_splitted_in_L
         [OF L'_OK aap2_wf(2)  aap2_wf(1)]
  show "aap2 \<in> L'"
    by simp
next
  fix aap2
  assume aap2_in: "aap2 \<in> L'"
  obtain aa p2 where aap2_eq [simp]: "aap2 = (aa, p2)" by (rule prod.exhaust)

  show "aap2 \<in> L - {(a, p)}"
    apply (rule Hopcroft_update_splitters_pred_in_E2 [OF L'_OK aap2_in[unfolded aap2_eq]])
    apply (simp_all add: splitted_emp)
  done
qed


subsubsection \<open> The abstract Algorithm \<close>

definition Hopcroft_abstract_invar where
  "Hopcroft_abstract_invar \<A> = (\<lambda>(P, L). 
   is_weak_language_equiv_partition \<A> P \<and>
   (\<forall>ap \<in> L. fst ap \<in> \<Sigma> \<A> \<and> snd ap \<in> P) \<and>
   (\<forall>p1 a p2. (a \<in> \<Sigma> \<A> \<and> (\<exists>p1' \<in> P. p1 \<subseteq> p1') \<and> p2 \<in> P \<and>
       split_language_equiv_partition_pred \<A> p1 a p2) \<longrightarrow>
       (\<exists>p2'. (a, p2') \<in> L \<and> split_language_equiv_partition_pred \<A> p1 a p2')))"
\<comment>\<open>P is a partition of the states satisfying weak language equivalence,
L is a subset of \<Sigma>\<times>P containing splitters of P.\<close>

lemma Hopcroft_abstract_invarI [intro!] :
  "\<lbrakk>is_weak_language_equiv_partition \<A> P;
    (\<And>a p. (a,p) \<in> L \<Longrightarrow> a \<in> \<Sigma> \<A> \<and> p \<in> P);
    (\<And>p1 a p2. \<lbrakk>is_weak_language_equiv_partition \<A> P;
       \<And>a p. (a,p) \<in> L \<Longrightarrow> a \<in> \<Sigma> \<A> \<and> p \<in> P;
       a \<in> \<Sigma> \<A>; p2 \<in> P; \<exists>p1' \<in> P. p1 \<subseteq> p1';
       split_language_equiv_partition_pred \<A> p1 a p2\<rbrakk> \<Longrightarrow>
       (\<exists>p2'. (a, p2') \<in> L \<and> split_language_equiv_partition_pred \<A> p1 a p2'))\<rbrakk> \<Longrightarrow>
   Hopcroft_abstract_invar \<A> (P, L)"
unfolding Hopcroft_abstract_invar_def
by auto metis

definition "Hopcroft_abstract_init \<A> \<equiv> (Hopcroft_accepting_partition \<A>, (\<Sigma> \<A> \<times> {\<F> \<A>}))"
\<comment>\<open>({{non-final states},{final states}}, letters \<times> final states)\<close>

lemma (in DFA) Hopcroft_abstract_invar_init :
assumes \<F>_OK: "\<F> \<A> \<noteq> {}"
shows "Hopcroft_abstract_invar \<A> (Hopcroft_abstract_init \<A>)" 
unfolding Hopcroft_abstract_init_def
proof
  show "is_weak_language_equiv_partition \<A> (Hopcroft_accepting_partition \<A>)"
    by (rule is_weak_language_equiv_partition_init)
next
  fix a p
  assume "(a,p) \<in> \<Sigma> \<A> \<times> {\<F> \<A>}"
  thus "a \<in> \<Sigma> \<A> \<and> p \<in> Hopcroft_accepting_partition \<A>"
    unfolding Hopcroft_accepting_partition_alt_def [OF NFA_axioms]
    using \<F>_OK 
    by simp
next
  fix p1 a p2
  let ?P = "Hopcroft_accepting_partition \<A>"
  assume p2_in: "p2 \<in> ?P"
     and split_pred: "split_language_equiv_partition_pred \<A> p1 a p2"
     and a_in: "a \<in> \<Sigma> \<A>" 
     and p1_sub_in: "\<exists>p1'\<in>Hopcroft_accepting_partition \<A>. p1 \<subseteq> p1'"

  have p1_sub: "p1 \<subseteq> \<Q> \<A>"
  proof -
    from p1_sub_in 
    obtain p1' where p1'_in: "p1' \<in> Hopcroft_accepting_partition \<A>" 
                 and p1_sub: "p1 \<subseteq> p1'"
      by blast
    from p1'_in have "p1' \<subseteq> \<Q> \<A>"
      unfolding Hopcroft_accepting_partition_alt_def [OF NFA_axioms]
      using \<F>_consistent
      by blast
    with p1_sub show "p1 \<subseteq> \<Q> \<A>" by simp
  qed
  have no_split_\<Q>: "\<not> (split_language_equiv_partition_pred \<A> p1 a (\<Q> \<A>))"
    unfolding split_language_equiv_partition_pred_def
              split_language_equiv_partition_alt_def [OF p1_sub a_in]
    by (simp add: \<delta>_in_\<Delta>_iff) (metis \<delta>_wf)

  have pred_eq:
       "split_language_equiv_partition_pred \<A> p1 a (\<F> \<A>) =
        split_language_equiv_partition_pred \<A> p1 a (\<Q> \<A> - \<F> \<A>)"
    apply (rule split_language_equiv_partition_pred_split_neg 
            [OF _ _ no_split_\<Q>])
    apply (insert \<F>_consistent)
    apply auto
  done

  with split_pred p2_in a_in
  have "(a, \<F> \<A>) \<in> \<Sigma> \<A> \<times> {\<F> \<A>} \<and> split_language_equiv_partition_pred \<A> p1 a (\<F> \<A>)"
    unfolding Hopcroft_accepting_partition_alt_def [OF NFA_axioms]
    by auto 
  thus "\<exists>p2'. (a, p2') \<in> \<Sigma> \<A> \<times> {\<F> \<A>} \<and> split_language_equiv_partition_pred \<A> p1 a p2'"
    by blast
qed

definition Hopcroft_abstract_b where
"Hopcroft_abstract_b PL = (snd PL \<noteq> {})"
\<comment>\<open>set of splitters is not empty\<close>

definition Hopcroft_abstract_f where
"Hopcroft_abstract_f \<A> = 
 (\<lambda>(P, L). do {
     ASSERT (Hopcroft_abstract_invar \<A> (P, L));                             \<comment>\<open>(P, L) satisfy the invariant\<close>
     ASSERT (L \<noteq> {});                                                       \<comment>\<open>set of splitters is not empty\<close>
       (a,p) \<leftarrow> SPEC (\<lambda>(a,p). (a,p) \<in> L);                                   \<comment>\<open>pick some splitter\<close>
       (P', L') \<leftarrow> SPEC (\<lambda>(P', L'). Hopcroft_update_splitters_pred \<A> p a P L L' \<and>
                                    (P' = Hopcroft_split \<A> p a {} P));      \<comment>\<open>split elements of P and update L accordingly\<close>
       RETURN (P', L')
     })"

definition Hopcroft_abstract where
  "Hopcroft_abstract \<A> = 
   (if (\<Q> \<A> = {}) then RETURN {} else (
    if (\<F> \<A> = {}) then RETURN {\<Q> \<A>} else (
       do {
         (P, _) \<leftarrow> WHILEIT (Hopcroft_abstract_invar \<A>) Hopcroft_abstract_b
                           (Hopcroft_abstract_f \<A>) (Hopcroft_abstract_init \<A>);
         RETURN P
       })))" 

lemma (in DFA) Hopcroft_abstract_invar_OK:
  "WHILE_invar_OK Hopcroft_abstract_b (Hopcroft_abstract_f \<A>) (Hopcroft_abstract_invar \<A>)"
unfolding Hopcroft_abstract_f_def Hopcroft_abstract_b_def[abs_def]
apply (rule WHILE_invar_OK_I)
apply (simp add: case_prod_beta)
apply (intro refine_vcg)
apply (simp add: image_iff)
apply (clarify)
apply (simp)
proof -
  fix P L a p2 L'
  assume invar_PL: "Hopcroft_abstract_invar \<A> (P, L)"
  assume p2a_in: "(a, p2) \<in> L"
  assume L'_OK: "Hopcroft_update_splitters_pred \<A> p2 a P L L'"
   
  from invar_PL p2a_in 
  have a_in: "a \<in> \<Sigma> \<A>" and p2_in_P: "p2 \<in> P" 
    unfolding Hopcroft_abstract_invar_def 
    by (simp_all add: Ball_def)

  from invar_PL have
    is_part: "is_partition (\<Q> \<A>) P"
    unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def
    by simp

  show "Hopcroft_abstract_invar \<A> (Hopcroft_split \<A> p2 a {} P, L')" 
  proof (rule Hopcroft_abstract_invarI)
    from Hopcroft_split_correct_simple [of P p2 a] a_in p2_in_P invar_PL
    show
      "is_weak_language_equiv_partition \<A> (Hopcroft_split \<A> p2 a {} P)"
      unfolding Hopcroft_abstract_invar_def
      by simp
  next
    fix a' p
    assume a'p_in: "(a', p) \<in> L'"

    have a'_in: "a' \<in> \<Sigma> \<A>"
      using Hopcroft_update_splitters_pred___label_in [OF L'_OK _ a'p_in]
            invar_PL
      unfolding Hopcroft_abstract_invar_def 
      by (auto simp add: Ball_def)

    note p_in_split = Hopcroft_split_in2 [OF is_part a_in, of p p2]

    from L'_OK a'p_in have p_in: "p \<in> Hopcroft_split \<A> p2 a {} P"
    proof (cases rule: Hopcroft_update_splitters_pred_in_E2)
      case no_split
      from no_split(1) invar_PL
      have "p \<in> P"
        unfolding Hopcroft_abstract_invar_def 
        by auto
      with no_split(2)
      show ?thesis 
        unfolding p_in_split by simp
    next
      case (split p0 pa pb)
      thus ?thesis 
        unfolding p_in_split
        by auto
    qed

    from a'_in p_in 
    show "a' \<in> \<Sigma> \<A> \<and> p \<in> Hopcroft_split \<A> p2 a {} P" 
      by simp
  next
    fix p1 aa p2'
    let ?P' = "Hopcroft_split \<A> p2 a {} P"
    assume p1_subset_P': "\<exists>p1' \<in> ?P'. p1 \<subseteq> p1'"
       and p2'_in_P': "p2' \<in> ?P'"
       and aa_in: "aa \<in> \<Sigma> \<A>"
       and split_pred: "split_language_equiv_partition_pred \<A> p1 aa p2'"
       and weak_part: "is_weak_language_equiv_partition \<A> ?P'"
       and L'_invar: "\<And>a p. (a, p) \<in> L' \<Longrightarrow> a \<in> \<Sigma> \<A> \<and> p \<in> ?P'"

    let ?in_L'_ex = "\<exists>p2''. (aa, p2'') \<in> L' \<and> split_language_equiv_partition_pred \<A> p1 aa p2''"
    have in_L_impl: "\<And>p2''. \<lbrakk>(aa, p2'') \<in> L; split_language_equiv_partition_pred \<A> p1 aa p2''\<rbrakk> 
                     \<Longrightarrow> ?in_L'_ex" 
    proof -
      fix p2''
      assume aa_p2''_in_L: "(aa, p2'') \<in> L" and 
             split_pred_p2'': "split_language_equiv_partition_pred \<A> p1 aa p2''"

      from aa_p2''_in_L invar_PL 
      have p2''_in_P: "p2'' \<in> P"
        unfolding Hopcroft_abstract_invar_def by auto

      thus ?in_L'_ex
      proof (cases "(aa, p2'') \<in> L'")
        case True with split_pred_p2''
        show ?thesis by blast
      next
        case False note aa_p2''_nin_L' = this
        have aa_p2''_neq: "(aa, p2'') \<noteq> (a, p2)"
        proof -
          from p1_subset_P' obtain p1' where
             p1'_in_P': "p1' \<in> ?P'" and
             p1_sub: "p1 \<subseteq> p1'" by blast

          from split_language_equiv_partition_pred___superset_p1 [OF split_pred_p2'' p1_sub]               
               p1'_in_P'
               split_language_equiv_partition_pred___split_not_eq
          show ?thesis by blast
        qed
        with aa_p2''_nin_L' aa_p2''_in_L 
        have "(\<exists>pa pb. (p2'', pa, pb) \<in> Hopcroft_splitted \<A> p2 a {} P)"
           using Hopcroft_update_splitters_pred___nin_splitted_in_L [OF L'_OK p2''_in_P aa_in]
           by blast 
        then obtain p2a'' p2b'' where p2''_in_split: 
           "(p2'', p2a'', p2b'') \<in> Hopcroft_splitted \<A> p2 a {} P" by blast

        have p2ab''_in_L': "(aa, p2a'') \<in> L' \<and> (aa, p2b'') \<in> L'"
          using aa_p2''_neq aa_p2''_in_L
          by (rule_tac Hopcroft_update_splitters_pred___in_splitted_in_L 
                         [OF L'_OK aa_in p2''_in_split])
              simp

        have "split_language_equiv_partition_pred \<A> p1 aa p2a'' \<or>
              split_language_equiv_partition_pred \<A> p1 aa p2b''"
        proof (rule split_language_equiv_partition_pred_split [OF _ split_pred_p2''])
          from p2''_in_split 
            have p2ab''_eq: "split_language_equiv_partition \<A> p2'' a p2 = (p2a'', p2b'')"
            unfolding Hopcroft_splitted_def
            by simp_all

          from is_partition_in_subset[OF is_part p2''_in_P]
          have p''_subset: "p2'' \<subseteq> \<Q> \<A>" .
            
          from split_language_equiv_partition_union [OF p2ab''_eq]
          show "p2a'' \<union> p2b'' = p2''" by simp
        qed
        with p2ab''_in_L' show ?thesis by blast
      qed
    qed

    have in_P_impl : 
      "\<And>p2''. \<lbrakk>p2'' \<in> P; split_language_equiv_partition_pred \<A> p1 aa p2''\<rbrakk> \<Longrightarrow>
       ?in_L'_ex"
    proof -
      fix p2''
      assume p2''_in_P : "p2'' \<in> P" "split_language_equiv_partition_pred \<A> p1 aa p2''"

      have p1_subset_exists: "\<exists>p1'\<in>P. p1 \<subseteq> p1'"
      proof -
        from p1_subset_P' obtain p1' where
             p1'_in_P': "p1' \<in> ?P'" and
             p1_sub: "p1 \<subseteq> p1'" by blast

        from p1'_in_P' obtain p1'' p1a' p1b' 
          where p1ab'_eq: "split_language_equiv_partition \<A> p1'' a p2 = (p1a', p1b')"
            and p1'_eq: "p1' = p1a' \<or> p1' = p1b'"
            and p1''_in_P: "p1'' \<in> P"
              by (auto simp add: Hopcroft_split_in)
        from is_partition_in_subset [OF is_part p1''_in_P]
             split_language_equiv_partition_union [OF p1ab'_eq]
        have p1''_eq : "p1'' = p1a' \<union> p1b'" by fast
        hence p1_subset: "p1 \<subseteq> p1''" 
          using p1'_eq p1_sub by blast
 
        from p1_subset p1''_in_P
        show ?thesis by blast
      qed

      with aa_in invar_PL p1_subset_exists p2''_in_P
      obtain p2''' where 
        "(aa, p2''') \<in> L" and
        "split_language_equiv_partition_pred \<A> p1 aa p2'''"
        unfolding Hopcroft_abstract_invar_def
        by blast
      with in_L_impl show ?in_L'_ex
        by simp
    qed

    show ?in_L'_ex
    using is_part a_in p2'_in_P'
    proof (cases rule: Hopcroft_split_in2_E)
      case in_P 
      from in_P(1) in_P_impl split_pred show ?thesis 
        by blast
    next
      case (in_splitted p2_0 p2_0a p2_0b)
      note p2_0_in_splitted = in_splitted(1)
      note p2'_eq = in_splitted(2)       
      define p2'_inv where "p2'_inv \<equiv> if p2' = p2_0a then p2_0b else p2_0a"

      from p2_0_in_splitted have p2_0_in_P: "p2_0 \<in> P"
        unfolding Hopcroft_splitted_def by simp

      show ?thesis
      proof (cases "(aa, p2') \<in> L' \<or> split_language_equiv_partition_pred \<A> p1 aa p2_0")
        case True with p2_0_in_P in_P_impl
        show ?thesis
          using split_pred by blast
      next
        case False 
        hence aa_p2'_nin_L' : "(aa, p2') \<notin> L'"
          and no_split_p2_0: "\<not>(split_language_equiv_partition_pred \<A> p1 aa p2_0)"
          by simp_all

        from Hopcroft_update_splitters_pred___in_splitted
            [OF L'_OK aa_in p2_0_in_splitted]
             p2'_eq aa_p2'_nin_L'
        have aa_p2'_inv_in_L': "(aa, p2'_inv) \<in> L'"
          unfolding p2'_inv_def by auto 

        from is_partition_in_subset [OF is_part p2_0_in_P] have
          p2_0_subset: "p2_0 \<subseteq> \<Q> \<A>" .

        from p2_0_in_splitted have split: "split_language_equiv_partition \<A> p2_0 a p2 =
            (p2_0a, p2_0b)"
          unfolding Hopcroft_splitted_def
          by simp
        note p2_0ab_union = split_language_equiv_partition_union [OF split]
        note p2_0ab_disj = split_language_equiv_partition_disjoint [OF split]

        from split_language_equiv_partition_pred_split_neg [OF p2_0ab_union[symmetric]
            p2_0ab_disj no_split_p2_0] 
        have "split_language_equiv_partition_pred \<A> p1 aa p2_0a =
              split_language_equiv_partition_pred \<A> p1 aa p2_0b" .
        with split_pred p2'_eq
        have "split_language_equiv_partition_pred \<A> p1 aa p2_0a \<and>
              split_language_equiv_partition_pred \<A> p1 aa p2_0b" by blast
        with p2'_inv_def have
          "split_language_equiv_partition_pred \<A> p1 aa p2'_inv" by metis
        with aa_p2'_inv_in_L' show ?thesis by blast
      qed
    qed
  qed
qed

lemma (in NFA) Hopcroft_abstract_invar___implies_finite_L:
assumes invar: "Hopcroft_abstract_invar \<A> PL"
  shows "finite (snd PL)"
proof -
  obtain P L where PL_eq[simp]: "PL = (P, L)" by (rule prod.exhaust)

  from invar 
  have L_sub: "L \<subseteq> \<Sigma> \<A> \<times> P" and part_P: "is_partition (\<Q> \<A>) P"
    unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def
    by auto

  from is_partition_finite [OF finite_\<Q> part_P] finite_\<Sigma>
  have "finite ((\<Sigma> \<A>) \<times> P)" by auto
  with L_sub show "finite (snd PL)" by (simp, rule finite_subset)
qed

definition Hopcroft_abstract_variant where
  "Hopcroft_abstract_variant \<A> = (measure (\<lambda>P. card (\<Q> \<A>) - card P)) <*lex*> (measure card)"

lemma (in DFA) Hopcroft_abstract_variant_OK:
  "WHILE_variant_OK Hopcroft_abstract_b (Hopcroft_abstract_f \<A>) (Hopcroft_abstract_invar \<A>)
    (Hopcroft_abstract_variant \<A>)"
proof (rule WHILE_variant_OK___extend_invariant)
  show "WHILE_invar_OK Hopcroft_abstract_b (Hopcroft_abstract_f \<A>) (Hopcroft_abstract_invar \<A>)"
    by (fact Hopcroft_abstract_invar_OK)
  show "wf (Hopcroft_abstract_variant \<A>)"
  unfolding Hopcroft_abstract_variant_def
  by (intro wf_lex_prod wf_measure)
next
  fix PL 
  assume invar : "Hopcroft_abstract_invar \<A> PL"
     and cond: "Hopcroft_abstract_b PL"
  obtain P L where PL_eq[simp]: "PL = (P, L)" by (rule prod.exhaust)

  from invar cond
  show "Hopcroft_abstract_f \<A> PL \<le> SPEC (\<lambda>PL'. (PL', PL) \<in> Hopcroft_abstract_variant \<A>)"
  unfolding Hopcroft_abstract_f_def Hopcroft_abstract_b_def PL_eq
  apply (simp only: case_prod_beta)
  apply (intro refine_vcg)
  apply (simp_all)
  apply (clarify)
  proof -
    fix a p L'
    assume ap_in: "(a, p) \<in> L"
       and L'_OK: "Hopcroft_update_splitters_pred \<A> p a P L L'"
    let ?P' = "Hopcroft_split \<A> p a {} P"
    
    from ap_in invar 
    have a_in: "a \<in> \<Sigma> \<A>" and
         p_in: "p \<in> P" and
         equiv_part_P: "is_weak_language_equiv_partition \<A> P"
      unfolding Hopcroft_abstract_invar_def 
      by auto
    from equiv_part_P have part_P: "is_partition (\<Q> \<A>) P"
      unfolding is_weak_language_equiv_partition_def by fast
  
    show "((?P', L'), (P, L)) \<in> Hopcroft_abstract_variant \<A>"
    proof (cases "?P' = P")
      case True note split_eq = this

      from Hopcroft_split_eq [OF split_eq a_in part_P]
      have "Hopcroft_splitted \<A> p a {} P = {}" .
      hence L'_eq: "L' = L - {(a, p)}"
        using invar 
        using Hopcroft_update_splitters_pred___splitted_emp [OF L'_OK]
        unfolding Hopcroft_abstract_invar_def PL_eq 
        by simp

      have fin_L: "finite L" 
        using Hopcroft_abstract_invar___implies_finite_L [OF invar] by simp
      show ?thesis
        unfolding Hopcroft_abstract_variant_def
        apply (simp add: L'_eq split_eq)
        apply (rule card_Diff1_less [OF fin_L ap_in])
      done
    next
      case False note split_neq = this

      from Hopcroft_split_correct_simple [OF equiv_part_P p_in a_in] split_neq
      have card_leq: "card P < card (Hopcroft_split \<A> p a {} P)" and
           equiv_part_P': "is_weak_language_equiv_partition \<A> (Hopcroft_split \<A> p a {} P)"
        by simp_all

      from equiv_part_P' have part_P': "is_partition (\<Q> \<A>) (Hopcroft_split \<A> p a {} P)"
        unfolding is_weak_language_equiv_partition_def by fast

      from is_partition_card_P [OF finite_\<Q> part_P]
           is_partition_card_P [OF finite_\<Q> part_P']
           card_leq
      have "card (\<Q> \<A>) - card (Hopcroft_split \<A> p a {} P) < card (\<Q> \<A>) - card P"
        by simp
      thus ?thesis
        unfolding Hopcroft_abstract_variant_def
        by (simp add: split_neq)
    qed
  qed
qed
   
lemma (in DFA) Hopcroft_abstract_variant_exists:
  "WHILE_variant_exists Hopcroft_abstract_b (Hopcroft_abstract_f \<A>) (Hopcroft_abstract_invar \<A>)"
unfolding WHILE_variant_exists_def
using Hopcroft_abstract_variant_OK by blast

lemma (in DFA) Hopcroft_abstract_correct :
  "Hopcroft_abstract \<A> \<le> SPEC (\<lambda>P. P = Myhill_Nerode_partition \<A>)"
proof (cases "\<Q> \<A> = {} \<or> \<F> \<A> = {}")
  case True thus ?thesis
    unfolding Hopcroft_abstract_def
    using Myhill_Nerode_partition___\<Q>_emp [of \<A>]
          Myhill_Nerode_partition___\<F>_emp [of \<A>]
    by simp blast
next
  case False thus ?thesis
    unfolding Hopcroft_abstract_def
  apply (rule_tac if_rule, simp)
  apply (rule_tac if_rule, simp)
  apply (rule_tac bind_rule)
  apply (simp add: case_prod_beta)
  apply (rule WHILEIT_rule_manual)
  apply (simp add: Hopcroft_abstract_invar_init)
  apply (simp add: Hopcroft_abstract_variant_exists)
  proof -
    fix PL
    assume invar: "Hopcroft_abstract_invar \<A> PL" 
       and not_cond: " \<not> (Hopcroft_abstract_b PL)"      
    obtain P L where PL_eq[simp]: "PL = (P, L)" by (rule prod.exhaust)

    from not_cond have L_eq[simp]: "L = {}"
      unfolding Hopcroft_abstract_b_def by simp

    from invar have "P = Myhill_Nerode_partition \<A>"
      unfolding Hopcroft_abstract_invar_def PL_eq L_eq
      apply (rule_tac split_language_equiv_partition_final)
      apply (simp_all add: Ball_def)
      apply (metis subset_refl)
    done

    thus "fst PL = Myhill_Nerode_partition \<A>"
      unfolding PL_eq by simp
  qed
qed

subsection \<open> Implementing step \<close>

text\<open> Above the next state of the loop was acquired using a specification. Now, let's refine this
specification with an inner loop. \<close>

definition Hopcroft_set_step_invar where
"Hopcroft_set_step_invar \<A> p a P L P' \<sigma> = 
 (Hopcroft_update_splitters_pred_aux (\<Sigma> \<A>) (Hopcroft_splitted \<A> p a {} (P - P')) P (L - {(a, p)}) (snd \<sigma>)
    \<and> fst \<sigma> = Hopcroft_split \<A> p a {} (P - P') \<union> P')" 
\<comment>\<open>Predicate for updating splitter and splitting partition\<close>

definition Hopcroft_set_step where
"Hopcroft_set_step \<A> p a P L =
 (do { PS \<leftarrow> SPEC (\<lambda>P'. (P' \<subseteq> P \<and> 
          (\<forall>p' \<in> P. split_language_equiv_partition_pred \<A> p' a p \<longrightarrow> p' \<in> P')));
       (P', L') \<leftarrow> FOREACHi (Hopcroft_set_step_invar \<A> p a P L) PS
         (\<lambda>p' (P', L'). do {
             let (pt', pf') = split_language_equiv_partition \<A> p' a p;
             if (pt' = {} \<or> pf' = {}) then (RETURN (P', L')) else
             do {
               (pmin, pmax) \<leftarrow> SPEC (\<lambda>pmm. (pmm = (pt', pf')) \<or> (pmm = (pf', pt')));
               let P' = (P' - {p'}) \<union> {pt', pf'};
               let L' = ({(a, p''). (a, p'') \<in> L' \<and> p'' \<noteq> p'} \<union>
                        {(a, pmin) | a. a \<in> \<Sigma> \<A>} \<union> {(a, pmax) |a. (a, p') \<in> L'});
               RETURN (P', L')
             }            
          }) (P, L - {(a, p)});
       RETURN (P', L')
     })"

lemma Hopcroft_set_step_correct_aux1 :
assumes P'_subset: "P' \<subseteq> P" 
    and P_part: "is_partition (\<Q> \<A>) P"
    and P'_prop: "\<And>p'. \<lbrakk>p' \<in> P; split_language_equiv_partition_pred \<A> p' a p\<rbrakk> \<Longrightarrow> p' \<in> P'"
shows "Hopcroft_set_step_invar \<A> p a P L P' (P, L - {(a, p)})"
proof - 
  have splitted_eq_Emp: "Hopcroft_splitted \<A> p a {} (P - P') = {}"
     unfolding Hopcroft_splitted_def split_language_equiv_partition_pred_def
     apply (rule set_eqI)
     apply (simp)
     apply (clarify)
     proof -
       fix p' pt' pf'
       assume "p' \<in> P" "p' \<notin> P'" "pt' \<noteq> {}" "pf' \<noteq> {}" and
              [symmetric]:"(pt', pf') = split_language_equiv_partition \<A> p' a p"
       with P'_prop [unfolded split_language_equiv_partition_pred_def, of p']
       show False by simp
     qed
 
  { fix p' pt' pf'
    assume "p' \<in> P" "p' \<notin> P'" and split_eq: "split_language_equiv_partition \<A> p' a p = (pt', pf')"
    with P'_prop[of p'] have ptf'_eq: "pt' = {} \<or> pf' = {}"
      unfolding split_language_equiv_partition_pred_def by simp blast

    from split_language_equiv_partition_union [OF split_eq] have p'_eq: "p' = pt' \<union> pf'" .

    { fix e
      assume "e \<in> pt'"
      with ptf'_eq have "pf' = {}" by auto
      with p'_eq have "pt' = p'" by simp
      with `p' \<in> P` `p' \<notin> P'` have "pt' \<in> P" "pt' \<notin> P'" by simp_all
    } note prop1 = this

    { fix e
      assume "e \<in> pf'"
      with ptf'_eq have "pt' = {}" by auto
      with p'_eq have "pf' = p'" by simp
      with `p' \<in> P` `p' \<notin> P'` have "pf' \<in> P" "pf' \<notin> P'" by simp_all
    } note prop2 = this
    note prop1 prop2 
  } note split_eq_P_aux = this

  from P_part have split_eq_P_aux2: "{} \<notin> P" unfolding is_partition_def by simp
  
  have split_eq_P: "Hopcroft_split \<A> p a {} (P - P') = P - P'"
    apply (rule set_eqI)
    apply (auto simp add: Hopcroft_split_in Bex_def)
    apply (simp add: split_eq_P_aux(1))
    apply (simp add: split_eq_P_aux(2))
    apply (simp add: split_eq_P_aux(3))
    apply (simp add: split_eq_P_aux(4))
    apply (simp add: split_eq_P_aux2)
    proof -
      fix p'
      assume "p' \<in> P" "p' \<notin> P'" 
      obtain pt' pf' where split_eq: "split_language_equiv_partition \<A> p' a p = (pt', pf')"
        by (rule prod.exhaust)

      note p'_eq = split_language_equiv_partition_union [OF split_eq] 

      from split_eq P'_prop[OF `p' \<in> P`] `p' \<notin> P'` have ptf'_eq: "pt' = {} \<or> pf' = {}"
        unfolding split_language_equiv_partition_pred_def by simp blast
      show "\<exists>xa. xa \<in> P \<and>
             xa \<notin> P' \<and>
             (case split_language_equiv_partition \<A> xa a p of
              (p1a, p1b) \<Rightarrow> p' = p1a \<or> p' = p1b)"
        apply (rule exI [where x = p'])
        apply (simp add: `p' \<in> P` `p' \<notin> P'` split_eq)
        apply (insert ptf'_eq)
        apply (auto simp add: p'_eq)
      done
    qed
        
  show ?thesis 
    unfolding Hopcroft_set_step_invar_def 
    using P'_subset
    by (auto simp add: Hopcroft_update_splitters_pred_aux_Emp_Id splitted_eq_Emp split_eq_P)
qed

lemma Hopcroft_set_step_correct_aux2 :
assumes P_part: "is_partition (\<Q> \<A>) P"
    and invar: "Hopcroft_set_step_invar \<A> p a P L P' (P'', L'')"
    and p'_in: "p' \<in> P'"
    and P'_subset: "P' \<subseteq> P"
    and p'_split: "split_language_equiv_partition \<A> p' a p = (pt', pf')"
    and ptf_eq: "pt' = {} \<or> pf' = {}"
shows "Hopcroft_set_step_invar \<A> p a P L (P' - {p'}) (P'', L'')"
proof -
  from p'_in P'_subset
  have P_diff_eq: "P - (P' - {p'}) = insert p' (P - P')" by auto

  from p'_in P'_subset P_part have p'_neq_emp: "p' \<noteq> {}"
    unfolding is_partition_def by auto

  from ptf_eq p'_neq_emp
  have split_aux_eq: "Hopcroft_split_aux \<A> p a {} p' = {p'}"
    unfolding Hopcroft_split_aux_def p'_split 
    apply (simp add: split_language_equiv_partition_union[OF p'_split])
    apply (cases "pt' = {}")
    apply (simp_all)
  done

  have splitted_aux_eq: "Hopcroft_splitted_aux \<A> p a {} p' = {}"
    unfolding Hopcroft_splitted_aux_def
    by (simp add: p'_split ptf_eq)

  from invar show ?thesis
    unfolding Hopcroft_set_step_invar_def
    apply (simp add: P_diff_eq splitted_aux_eq split_aux_eq)
    apply (simp add: Hopcroft_split_def)
    apply (auto simp add: p'_in)
  done
qed

lemma Hopcroft_set_step_correct_aux3 :
assumes L_OK: "\<And>a p. (a, p) \<in> L \<Longrightarrow> a \<in> \<Sigma> \<A>"
    and invar: "Hopcroft_set_step_invar \<A> p a P L P' (P'', L'')"
    and P_part: "is_partition (\<Q> \<A>) P"
    and p'_in_P': "p' \<in> P'"
    and P'_subset: "P' \<subseteq> P"
    and p'_split: "split_language_equiv_partition \<A> p' a p = (pt', pf')"
    and pt'_neq: "pt' \<noteq> {}"
    and pf'_neq: "pf' \<noteq> {}"
    and pmm: "((pmin, pmax) = (pt', pf')) \<or> ((pmin, pmax) = (pf', pt'))"
shows "Hopcroft_set_step_invar \<A> p a P L (P' - {p'}) 
    (insert pt' (insert pf' (P'' - {p'})), 
    {(a, p''). (a, p'') \<in> L'' \<and> p'' \<noteq> p'} \<union> {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
         {(a, pmax) |a. (a, p') \<in> L''})"
proof -
  from p'_in_P' P'_subset have "p' \<in> P" by auto
  hence P_diff_eq: "P - (P' - {p'}) = insert p' (P - P')" by auto

  from pt'_neq pf'_neq
  have split_aux_eq: "Hopcroft_split_aux \<A> p a {} p' = {pt', pf'}"
    unfolding Hopcroft_split_aux_def p'_split 
    by simp

  from split_language_equiv_partition_union[OF p'_split]
       split_language_equiv_partition_disjoint [OF p'_split]
       pt'_neq pf'_neq
  have ptf'_neq_p': "pt' \<noteq> p'" "pf' \<noteq> p'" by auto

  have splitted_aux_eq: "Hopcroft_splitted_aux \<A> p a {} p' = {(p', pt', pf')}"
    unfolding Hopcroft_splitted_aux_def
    by (simp add: p'_split pt'_neq pf'_neq)

  { fix p''
    assume p'_in_split: "p' \<in> split_language_equiv_partition_set \<A> a p p''" 
       and p''_in: "p'' \<in> P"

    from p'_in_split have "p' \<subseteq> p''"
      unfolding split_language_equiv_partition_set_def
      apply (simp split: prod.splits)
      apply (metis split_language_equiv_partition_subset)
    done

    from is_partition_distinct_subset[OF P_part p''_in `p' \<subseteq> p''`] `p' \<in> P`
    have p''_eq: "p'' = p'" by simp

    with p'_in_split ptf'_neq_p' have "False"
      unfolding split_language_equiv_partition_set_def
      by (simp add: p'_split)
  } 
  hence "p' \<notin> Hopcroft_split \<A> p a {} (P - P')" 
    unfolding Hopcroft_split_def
    by (auto simp add: Ball_def)
  hence split_diff_eq: "Hopcroft_split \<A> p a {} (P - P') - {p'} = Hopcroft_split \<A> p a {} (P - P')"
    by auto

  have prop1: "insert pt' (insert pf' (Hopcroft_split \<A> p a {} (P - P') \<union> P' - {p'})) =
               Hopcroft_split \<A> p a {} (P - (P' - {p'})) \<union> (P' - {p'})" 
    apply (simp add: P_diff_eq split_aux_eq Un_Diff split_diff_eq)
    apply (simp add: Hopcroft_split_def)
  done

  {
    define L' where "L' \<equiv> L - {(a, p)}"
    define L''' where "L''' \<equiv> ({(a, p''). (a, p'') \<in> L'' \<and> p'' \<noteq> p'} \<union> {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
      {(a, pmax) |a. (a, p') \<in> L''})"
    define splitted where "splitted \<equiv> Hopcroft_splitted \<A> p a {} (P - P')"
    define splitted' where "splitted' \<equiv> Hopcroft_splitted \<A> p a {} (P - (P' - {p'}))"
     assume pre[folded splitted_def L'_def]: "Hopcroft_update_splitters_pred_aux (\<Sigma> \<A>) 
        (Hopcroft_splitted \<A> p a {} (P - P')) P L' L''"

     have splitted'_eq[simp]: "splitted' = insert (p', pt', pf') splitted"
       unfolding splitted'_def splitted_def
       apply (simp add: P_diff_eq splitted_aux_eq)
       apply (simp add: Hopcroft_splitted_def)
     done

     { fix p'' pt'' pf''
       assume in_splitted: "(p'', pt'', pf'') \<in> splitted"

       { assume "p'' \<in> P" "p'' \<notin> P'"
            and "pt'' \<noteq> {}" "pf'' \<noteq> {}" 
            and split_p''_eq: "split_language_equiv_partition \<A> p'' a p = (pt'', pf'')"
         
         from split_language_equiv_partition_subset [OF split_p''_eq]   
         have "pt'' \<subseteq> p''" "pf'' \<subseteq> p''" by simp_all

         from split_language_equiv_partition_union [OF split_p''_eq]
              split_language_equiv_partition_disjoint [OF split_p''_eq]
              `pt'' \<noteq> {}` `pf'' \<noteq> {}`
         have "pt'' \<noteq> p''" "pf'' \<noteq> p''" by auto
 
         with is_partition_distinct_subset[OF P_part `p'' \<in> P` `pt'' \<subseteq> p''`]
              is_partition_distinct_subset[OF P_part `p'' \<in> P` `pf'' \<subseteq> p''`] 
              `p'' \<notin> P'` `p' \<in> P'` `p' \<in> P` `p'' \<in> P`
         have "(p'' \<noteq> p') \<and> (pt'' \<noteq> p') \<and> (pf'' \<noteq> p')" by auto
       }
       with in_splitted
       have "p'' \<noteq> p' \<and> pt'' \<noteq> p' \<and> pf'' \<noteq> p'"
         unfolding splitted_def Hopcroft_splitted_def
         by simp
     } note in_splitted = this

     have "Hopcroft_update_splitters_pred_aux (\<Sigma> \<A>) 
        (Hopcroft_splitted \<A> p a {} (P - (P' - {p'}))) P (L - {(a, p)})
        ({(a, p''). (a, p'') \<in> L'' \<and> p'' \<noteq> p'} \<union> {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
        {(a, pmax) |a. (a, p') \<in> L''})"
       unfolding splitted'_def[symmetric] L'_def[symmetric] L'''_def[symmetric]
     proof 
       from invar have
         "Hopcroft_update_splitters_pred_aux_lower_not_splitted (\<Sigma> \<A>) splitted P L' L''"
         unfolding Hopcroft_set_step_invar_def Hopcroft_update_splitters_pred_aux_def
                   Hopcroft_update_splitters_pred_aux_lower_def
                   L'_def[symmetric] splitted_def[symmetric]
         by simp
       thus "Hopcroft_update_splitters_pred_aux_lower_not_splitted (\<Sigma> \<A>) splitted' P L' L'''"
         unfolding Hopcroft_update_splitters_pred_aux_lower_not_splitted_def L'''_def
         by auto
     next
       from invar have
         "Hopcroft_update_splitters_pred_aux_lower_splitted (\<Sigma> \<A>) splitted P L' L''"
         unfolding Hopcroft_set_step_invar_def Hopcroft_update_splitters_pred_aux_def
                   Hopcroft_update_splitters_pred_aux_lower_def
                   L'_def[symmetric] splitted_def[symmetric]
         by simp
       thus "Hopcroft_update_splitters_pred_aux_lower_splitted (\<Sigma> \<A>) splitted' P L' L'''"
         unfolding Hopcroft_update_splitters_pred_aux_lower_splitted_def 
         using pmm 
         apply (simp add: conj_disj_distribL all_conj_distrib)
         apply (simp add: L'''_def)
         apply (rule conjI)
           apply metis
           apply (metis in_splitted)
       done        
     next
       from invar have pre:
         "Hopcroft_update_splitters_pred_aux_upper (\<Sigma> \<A>) splitted P L' L''"
         unfolding Hopcroft_set_step_invar_def Hopcroft_update_splitters_pred_aux_def
                   L'_def[symmetric] splitted_def[symmetric]
         by simp
       show "Hopcroft_update_splitters_pred_aux_upper (\<Sigma> \<A>) splitted' P L' L'''"
         unfolding Hopcroft_update_splitters_pred_aux_upper_def L'''_def 
         apply (simp add: conj_disj_distribL all_conj_distrib in_splitted)
         apply (intro conjI allI impI)
           apply (insert pre[unfolded Hopcroft_update_splitters_pred_aux_upper_def]) []
           apply metis

           apply (insert pmm)[] 
           apply (simp) 
           apply (metis)

           apply (subgoal_tac "a \<in> \<Sigma> \<A>")
           apply (insert pmm)[] 
           apply (simp) 
           apply (metis)

           apply (insert pre[unfolded Hopcroft_update_splitters_pred_aux_upper_def]) []
           apply (simp add: L'_def)
           apply (metis L_OK)
       done        
     next
       from invar have pre1:
         "Hopcroft_update_splitters_pred_aux_lower_not_splitted (\<Sigma> \<A>) splitted P L' L''"
         unfolding Hopcroft_set_step_invar_def Hopcroft_update_splitters_pred_aux_def
                   Hopcroft_update_splitters_pred_aux_lower_def
                   L'_def[symmetric] splitted_def[symmetric]
         by simp

       from invar have pre2:
         "Hopcroft_update_splitters_pred_aux_lower_splitted_in_L (\<Sigma> \<A>) splitted P L' L''"
         unfolding Hopcroft_set_step_invar_def Hopcroft_update_splitters_pred_aux_def
                   Hopcroft_update_splitters_pred_aux_lower_def
                   L'_def[symmetric] splitted_def[symmetric]
         by simp
       show "Hopcroft_update_splitters_pred_aux_lower_splitted_in_L (\<Sigma> \<A>) splitted' P L' L'''"
         unfolding Hopcroft_update_splitters_pred_aux_lower_splitted_in_L_def 
         apply (simp add: conj_disj_distribL all_conj_distrib)
         apply (simp add: L'''_def)
         apply (rule conjI)

         apply (intro allI impI)
         apply (subgoal_tac "(a, p') \<in> L''")
           apply (insert pmm)[]
           apply (simp add: ptf'_neq_p')
           apply metis

           apply (insert pre1[unfolded Hopcroft_update_splitters_pred_aux_lower_not_splitted_def])[]
           apply (metis in_splitted `p' \<in> P`)

           apply (insert pmm pre2[unfolded Hopcroft_update_splitters_pred_aux_lower_splitted_in_L_def])[]
           apply (metis in_splitted)
       done
     qed
  } note prop2 = this

  from invar show ?thesis
    unfolding Hopcroft_set_step_invar_def
    by (simp add: prop1 prop2)
qed

lemma Hopcroft_set_step_correct_aux4 :
assumes invar: "Hopcroft_set_step_invar \<A> p a P L {} (P'', L'')"
shows "Hopcroft_update_splitters_pred_aux (\<Sigma> \<A>) (Hopcroft_splitted \<A> p a {} P) P
        (L - {(a, p)}) L'' \<and>
       P'' = Hopcroft_split \<A> p a {} P"
using invar
unfolding Hopcroft_set_step_invar_def
  by simp

lemma (in DFA) Hopcroft_set_step_correct :
assumes part_P: "is_partition (\<Q> \<A>) P"
    and L_OK: "\<And>a p. (a, p) \<in> L \<Longrightarrow> a \<in> \<Sigma> \<A>"
shows "Hopcroft_set_step \<A> p a P L \<le>
       SPEC (\<lambda>(P', L'). Hopcroft_update_splitters_pred \<A> p a P L L' \<and> P' = Hopcroft_split \<A> p a {} P)"
unfolding Hopcroft_set_step_def Hopcroft_update_splitters_pred_def
apply (intro refine_vcg)
apply (simp_all)
  apply (metis finite_subset [OF _ is_partition_finite [OF finite_\<Q> part_P]])

  apply (rule Hopcroft_set_step_correct_aux1 [OF _ part_P]) apply (simp) apply blast
  
  apply (rule Hopcroft_set_step_correct_aux2 [OF part_P]) apply fast+

  apply (rule Hopcroft_set_step_correct_aux3 [OF _ _ part_P]) apply (simp add: L_OK) apply fast+

  apply (erule Hopcroft_set_step_correct_aux4)
done

definition Hopcroft_set_f where
"Hopcroft_set_f \<A> = 
 (\<lambda>(P, L). do {
       ASSERT (Hopcroft_abstract_invar \<A> (P, L));
       ASSERT (L \<noteq> {});
       (a,p) \<leftarrow> SPEC (\<lambda>(a,p). (a,p) \<in> L);
       (P', L') \<leftarrow> Hopcroft_set_step \<A> p a P L;
       RETURN (P', L')
     })"

subsection \<open> Precomputing Predecessors \<close>

text\<open> In the next refinement step the set of predecessors of the currently chosen
set @{text p} with respect to label @{text a} is precomputed. \<close>

definition Hopcroft_precompute_step where
"Hopcroft_precompute_step \<A> p a pre P L =
 (do { PS \<leftarrow> SPEC (\<lambda>P'. (P' \<subseteq> P \<and> (\<forall>p' \<in> P'. p' \<inter> pre \<noteq> {}) \<and>
          (\<forall>p' \<in> P. p' \<inter> pre \<noteq> {} \<and> split_language_equiv_partition_pred \<A> p' a p \<longrightarrow> p' \<in> P')));
       (P', L') \<leftarrow> FOREACHi (Hopcroft_set_step_invar \<A> p a P L) PS
         (\<lambda>p' (P', L'). do {
             let (pt', pct', pf', pcf') = 
              ({q . q \<in> p' \<and> q \<in> pre}, card {q . q \<in> p' \<and> q \<in> pre},
               {q . q \<in> p' \<and> q \<notin> pre}, card {q . q \<in> p' \<and> q \<notin> pre}); 
             if (pcf' = 0) then (RETURN (P', L')) else
             do {
               let (pmin, pmax) = (if (pcf' < pct') then (pf', pt') else (pt', pf'));
               let P' = (P' - {p'}) \<union> {pt', pf'};
               let L' = ({(a, p''). (a, p'') \<in> L' \<and> p'' \<noteq> p'} \<union>
                        {(a, pmin) | a. a \<in> \<Sigma> \<A>} \<union> {(a, pmax) |a. (a, p') \<in> L'});
               RETURN (P', L')
             }             
          }) (P, L - {(a, p)});
       RETURN (P', L')
     })"

lemma Hopcroft_precompute_step_correct :
assumes pre_OK: "pre = {q. \<exists>q'. q' \<in> p \<and> (q, a, q') \<in> \<Delta> \<A>}"
    and P_fin: "\<And>p. p \<in> P \<Longrightarrow> finite p"
shows "Hopcroft_precompute_step \<A> p a pre P L \<le> \<Down>Id (Hopcroft_set_step \<A> p a P L)"
unfolding Hopcroft_precompute_step_def Hopcroft_set_step_def
(* using [[goals_limit = 1]] *)
apply (rule bind_refine
  [where R' = "build_rel id (\<lambda>P'. \<forall>p\<in>P'. finite p \<and> p \<inter> pre \<noteq> {})"])
apply (simp add: pw_le_iff refine_pw_simps del: br_def)
apply (simp add: split_language_equiv_partition_pred_def split_language_equiv_partition_def 
                 split_set_def pre_OK)
  apply (insert P_fin)[]
  apply (simp add: set_eq_iff Bex_def Ball_def subset_iff)

  apply (subgoal_tac "\<forall>p'. split_language_equiv_partition \<A> p' a p =
   ({q. q \<in> p' \<and> q \<in> pre}, {q. q \<in> p' \<and> q \<notin> pre})") 
  apply (refine_rcg)
  apply (simp add: br_def)
  apply (simp add: br_def split_language_equiv_partition_def split_set_def pre_OK Bex_def)
  apply refine_rcg
  apply (rule inj_on_id)
  apply refine_dref_type
  apply (simp_all add: in_br_conv)
  apply (clarsimp simp: split_language_equiv_partition_def split_set_def pre_OK Bex_def)
  apply (subst card_0_eq)
  apply fastforce
  apply clarsimp apply (safe ; blast)
  apply (simp_all add: split_language_equiv_partition_def split_set_def pre_OK Bex_def)
  done

(* -- OLD PROOF --
(* after refine_rcg *)
apply (rule inj_on_id)
apply (simp)
apply (rule IdI)
apply (simp_all)

apply (auto)[]
apply (simp_all add: split_language_equiv_partition_def split_set_def pre_OK Bex_def)
*)

subsection \<open> Data Refinement \<close>

text\<open> Till now, the algorithm has been refined in several steps. However, the datastructures
remained unchanged. Let us now use efficient datastructures. Currently the state consists of
a partition of the states and a set of pairs of labels and state sets. In the following the
partition will be implemented using maps.

The partition @{text P} will be represented by a triple @{text "(im, sm, n)"}. 
This triple consists of a finite map @{text im} mapping indices (natural numbers) to sets, a map
@{text sm} mapping states to the index of the set it is in, and finally a natural number 
@{text n} that determines the number of used indices.\<close>

type_synonym ('q, 'a) partition_map_gen = "(nat \<Rightarrow> 'a option) * ('q \<Rightarrow> nat option) * nat"
type_synonym 'q partition_map = "('q, 'q set) partition_map_gen"

fun partition_map_\<alpha> :: "'q partition_map \<Rightarrow> ('q set) set" where
  "partition_map_\<alpha> (im, sm, n) = {p | i p. i < n \<and> im i = Some p}"

fun partition_map_invar :: "'q partition_map \<Rightarrow> bool" where
  "partition_map_invar (im, sm, n) \<longleftrightarrow>
   dom im = {i . i < n} \<and>                                     \<comment>\<open>domain is 0..n\<close>
   (\<forall>i. im i \<noteq> Some {}) \<and>                                    \<comment>\<open>no component is empty\<close>
   (\<forall>q i. (sm q = Some i) \<longleftrightarrow> (\<exists>p. im i = Some p \<and> q \<in> p))"  \<comment>\<open>sm and im map states and the corresponding indices correctly\<close>

definition partition_index_map :: "('q,'a) partition_map_gen \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "partition_index_map P i \<equiv> the ((fst P) i)" \<comment>\<open>returns im i if P = (im, sm, n)\<close>

definition partition_state_map :: "('q,'a) partition_map_gen \<Rightarrow> ('q \<Rightarrow> nat)" where
  "partition_state_map P q \<equiv> the (fst (snd P) q)" \<comment>\<open>returns sm q if P = (im, sm, n)\<close>

definition partition_free_index :: "('q,'a) partition_map_gen \<Rightarrow> nat" where
  "partition_free_index P \<equiv> snd (snd P)" \<comment>\<open>returns n if P = (im, sm, n)\<close>
lemma partition_free_index_simp[simp] :
  "partition_free_index (im, sm, n) = n" unfolding partition_free_index_def by simp

definition partition_map_empty :: "('q,'a) partition_map_gen" where
  "partition_map_empty \<equiv> (Map.empty, Map.empty, 0::nat)"

lemma partition_map_empty_correct :
  "partition_map_\<alpha> (partition_map_empty) = {}"
  "partition_map_invar (partition_map_empty)"
unfolding partition_map_empty_def
by simp_all

definition partition_map_sing :: "'a \<Rightarrow> 'q set \<Rightarrow> (('q, 'a) partition_map_gen)" where
  "partition_map_sing Q_rep Q = 
    (Map.empty (0 \<mapsto> Q_rep) , (\<lambda>q. if (q \<in> Q) then Some 0 else None), 1)"

lemma partition_map_sing_correct :
  "partition_map_\<alpha> (partition_map_sing Q Q) = {Q}"
  "partition_map_invar (partition_map_sing Q Q) \<longleftrightarrow> Q \<noteq> {}"
unfolding partition_map_sing_def
by simp_all

lemma partition_index_map_inj_on :
assumes invar: "partition_map_invar P"
    and p_OK: "\<And>i. i \<in> p \<Longrightarrow> i < partition_free_index P"
shows "inj_on (partition_index_map P) p"
unfolding inj_on_def
proof (intro ballI impI)
  fix i1 i2
  assume "i1 \<in> p"
  assume "i2 \<in> p"
  assume map_i12_eq: "partition_index_map P i1 = partition_index_map P i2"

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  from p_OK[OF \<open>i1 \<in> p\<close>] have "i1 < n" by simp
  with invar have "i1 \<in> dom im" by simp
  then obtain s1 where im_i1_eq: "im i1 = Some s1"
    by (simp add: dom_def, blast)

  from p_OK[OF \<open>i2 \<in> p\<close>] have "i2 < n" by simp
  with invar have "i2 \<in> dom im" by simp
  then obtain s2 where im_i2_eq: "im i2 = Some s2"
    by (simp add: dom_def, blast)

  from map_i12_eq \<open>im i1 = Some s1\<close> \<open>im i2 = Some s2\<close>
  have s2_eq[simp]: "s2 = s1" unfolding partition_index_map_def by simp

  from invar have "im i1 \<noteq> Some {}" by simp
  with im_i1_eq have "s1 \<noteq> {}" by simp
  then obtain q where "q \<in> s1" by auto

  from invar im_i1_eq \<open>q \<in> s1\<close> have "sm q = Some i1" by simp
  moreover
  from invar im_i2_eq \<open>q \<in> s1\<close> have "sm q = Some i2" by simp
  finally show "i1 = i2" by simp
qed

lemma partition_map_is_partition :
assumes invar: "partition_map_invar P"
shows "is_partition (\<Union> (partition_map_\<alpha> P)) (partition_map_\<alpha> P)"
proof
  fix p
  assume "p \<in> partition_map_\<alpha> P" 
  thus "p \<subseteq> \<Union>(partition_map_\<alpha> P)"
    by auto
next
  fix p
  assume p_in: "p \<in> partition_map_\<alpha> P"

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)
  from p_in obtain i where p_eq: "im i = Some p" and "i < n" by auto

  from invar have "im i \<noteq> Some {}" by simp
  with \<open>im i = Some p\<close> show "p \<noteq> {}" by simp
next
  fix q p1 p2
  assume p1_in: "p1 \<in> partition_map_\<alpha> P" 
     and p2_in: "p2 \<in> partition_map_\<alpha> P" 
     and q_in_p12: "q \<in> p1" "q \<in> p2"

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  from p1_in obtain i1 where p1_eq: "im i1 = Some p1" and "i1 < n" by auto
  from p2_in obtain i2 where p2_eq: "im i2 = Some p2" and "i2 < n" by auto

  from invar q_in_p12 have "sm q = Some i1" "sm q = Some i2"
    by (simp_all add: p1_eq p2_eq)
  hence "i2 = i1" by simp
  with p1_eq p2_eq show "p1 = p2" 
    by simp
qed simp


lemma partition_index_map_disj :
assumes invar: "partition_map_invar P"
    and i_j_OK: "i < partition_free_index P" "j < partition_free_index P"
shows "(partition_index_map P i \<inter> partition_index_map P j = {}) \<longleftrightarrow> (i \<noteq> j)"
proof -
  from partition_index_map_inj_on [OF invar, of "{i, j}"] i_j_OK
  have step1: "(i = j) = (partition_index_map P i = partition_index_map P j)"
    by (auto simp add: image_iff)

  note is_part = partition_map_is_partition [OF invar]

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  from invar i_j_OK
  have "i \<in> dom im" and "j \<in> dom im" by (simp_all)
  then obtain pi pj where im_i_eq: "im i = Some pi" and im_j_eq: "im j = Some pj" by blast
  
  from i_j_OK
  have ij_in: "partition_index_map P i \<in> partition_map_\<alpha> P \<and>
               partition_index_map P j \<in> partition_map_\<alpha> P"
    apply (simp add: partition_index_map_def im_i_eq im_j_eq)
    apply (metis im_i_eq im_j_eq)
  done

  from is_part ij_in
  show ?thesis
    unfolding step1 is_partition_def
    by auto
qed

lemma partition_map_is_partition_eq :
assumes invar: "partition_map_invar P"
    and part: "is_partition PP (partition_map_\<alpha> P)"
shows "PP = (\<Union> (partition_map_\<alpha> P))"
proof -
  note partition_map_is_partition[OF invar]
  with part show ?thesis
    unfolding is_partition_def by simp
qed


lemma partition_state_map_le :
assumes invar: "partition_map_invar P"
    and q_in: "q \<in> (\<Union> (partition_map_\<alpha> P))"
shows "partition_state_map P q < partition_free_index P"
proof -
  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)
  from q_in obtain i s where "im i = Some s"  "q \<in> s" "i < n" by auto
  from invar \<open>q \<in> s\<close> \<open>im i = Some s\<close> have sm_q_eq: "sm q = Some i" by simp  
  from sm_q_eq \<open>i < n\<close> show ?thesis by (simp add: partition_state_map_def)
qed


fun partition_map_split :: "'q partition_map \<Rightarrow> nat \<Rightarrow> 'q set => 'q set \<Rightarrow> 'q partition_map" where
  "partition_map_split (im, sm, n) i pmin pmax =
   (im (i \<mapsto> pmax) (n \<mapsto> pmin), 
    \<lambda>q. if (q \<in> pmin) then Some n else sm q,
    Suc n)"

definition Hopcroft_map_state_\<alpha> where
"Hopcroft_map_state_\<alpha> \<sigma> = \<comment>\<open>\<sigma> = ((im, sm, n), S::'q \<times>nat set)\<close>
   (partition_map_\<alpha> (fst \<sigma>), (apsnd (partition_index_map (fst \<sigma>))) ` (snd \<sigma>))"

definition Hopcroft_map_state_invar where
"Hopcroft_map_state_invar \<sigma> =
   (partition_map_invar (fst \<sigma>) \<and>                               \<comment>\<open>fst \<sigma> = (im, sm, n) is a well-formed mapping\<close>
    (\<forall>ap \<in> (snd \<sigma>). snd ap < partition_free_index (fst \<sigma>)))"    \<comment>\<open>for all (a, k) in (snd \<sigma>) = S, k < n\<close>

definition Hopcroft_map_state_rel where
  "Hopcroft_map_state_rel = build_rel Hopcroft_map_state_\<alpha> Hopcroft_map_state_invar"

lemma Hopcroft_map_state_rel_sv[refine] :
"single_valued Hopcroft_map_state_rel"
unfolding Hopcroft_map_state_rel_def
by (rule br_sv)

definition Hopcroft_map_step_invar where
"Hopcroft_map_step_invar \<A> p a P L P' \<sigma> \<longleftrightarrow> 
 Hopcroft_set_step_invar \<A> (partition_index_map P p) a (partition_map_\<alpha> P)
 ((apsnd (partition_index_map P)) ` L) ((partition_index_map P) ` P') 
   (Hopcroft_map_state_\<alpha> \<sigma>) \<and> Hopcroft_map_state_invar \<sigma>"

definition Hopcroft_map_step where
"Hopcroft_map_step \<A> p a pre P L =
 (do { ASSERT (pre \<subseteq> dom (fst (snd P)) \<and> dom (fst (snd P)) \<subseteq> \<Q> \<A>); 
       iS \<leftarrow> SPEC (\<lambda>iS. (iS \<subseteq> (partition_state_map P) ` pre \<and>
          (\<forall>i \<in> (partition_state_map P) ` pre. 
                 split_language_equiv_partition_pred \<A> (partition_index_map P i) a 
                   (partition_index_map P p) \<longrightarrow> i \<in> iS)));
       (P', L') \<leftarrow> FOREACHi (Hopcroft_map_step_invar \<A> p a P L) iS
         (\<lambda>(p'::nat) (P'::'q partition_map, L'). do {
             ASSERT (p' \<in> dom (fst P') \<and> p' \<in> dom (fst P) \<and> (fst P') p' = (fst P) p' \<and>
                     (snd (snd P)) \<le> (snd (snd P')));
             let (pt', pct', pf', pcf') = 
              ({q . q \<in> partition_index_map P' p' \<and> q \<in> pre}, card {q . q \<in> partition_index_map P' p' \<and> q \<in> pre},
               {q . q \<in> partition_index_map P' p' \<and> q \<notin> pre}, card {q . q \<in> partition_index_map P' p' \<and> q \<notin> pre}); 
             if (pcf' = 0) then (RETURN (P', L')) else
             do {
               let (pmin, pmax) = (if (pcf' < pct') then (pf', pt') else (pt', pf'));
               ASSERT (\<forall>ai \<in> L'. snd ai < partition_free_index P');
               let L' = {(a, partition_free_index P') | a. a \<in> \<Sigma> \<A>} \<union> L';
               let P' = partition_map_split P' p' pmin pmax;
               RETURN (P', L')
             }             
          }) (P, L - {(a, p)});
       RETURN (P', L')
     })"

lemma Hopcroft_map_step_correct :
fixes P :: "'q partition_map"
  and L :: "('a \<times> nat) set"
  and \<A> :: "('q, 'a, 'X) NFA_rec_scheme"
assumes PL_OK: "((P,L), (P', L')) \<in> Hopcroft_map_state_rel"
    and p_le: "p < partition_free_index P"
    and p'_eq: "p' = partition_index_map P p"
    and part_P': "is_partition (\<Q> \<A>) P'"
    and pre_subset: "pre \<subseteq> \<Q> \<A>"
shows "Hopcroft_map_step \<A> p a pre P L \<le> \<Down>Hopcroft_map_state_rel (Hopcroft_precompute_step \<A> p' a pre P' L')"
unfolding Hopcroft_precompute_step_def Hopcroft_map_step_def
apply (rule refine)
defer
apply (rule bind_refine [where R'="br (\<lambda>iS. (partition_index_map P) ` iS)  (\<lambda>iS. iS \<subseteq> ((partition_state_map P) ` pre))"])
apply (intro SPEC_refine_sv br_sv)
apply simp
apply clarify
defer
apply (rule bind_refine [where R' = Hopcroft_map_state_rel])
prefer 2
apply (simp add: Hopcroft_map_state_rel_def pw_le_iff refine_pw_simps)
apply (rename_tac iS PS)
apply auto[1]
apply (rule FOREACHi_refine[where \<alpha>="partition_index_map P" and \<Phi>'' =
  "\<lambda>PS PL'' _ _. (partition_free_index P \<le> partition_free_index (fst PL'')) \<and>
             (\<forall>i\<in>PS. fst (fst PL'') i = fst P i)"])
proof -
  from PL_OK have invar_P: "partition_map_invar P" and P'_eq: "P' = partition_map_\<alpha> P"
              and L_OK: "\<And>a p. (a, p) \<in> L \<Longrightarrow> p < partition_free_index P"
              and L'_eq: "L' = apsnd (partition_index_map P) ` L"
    unfolding Hopcroft_map_state_rel_def Hopcroft_map_state_invar_def[abs_def] 
              Hopcroft_map_state_\<alpha>_def[abs_def]
       apply (simp_all add: Hopcroft_map_state_\<alpha>_def Hopcroft_map_state_rel_def PL_OK fst_conv in_br_conv)
    by auto

  have \<Q>_eq: "\<Union>(partition_map_\<alpha> P) = \<Q> \<A>" 
    using partition_map_is_partition_eq[OF invar_P, folded P'_eq, OF part_P'] P'_eq
    by simp

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  show pre_subset': "pre \<subseteq> dom (fst (snd P)) \<and> dom (fst (snd P)) \<subseteq> \<Q> \<A>"
    using invar_P pre_subset
    apply (simp add: set_eq_iff dom_def subset_iff \<Q>_eq[symmetric])
    apply metis
  done

  from partition_state_map_le[OF invar_P, unfolded \<Q>_eq] 
  have P_state_map_leq: "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> partition_state_map (im, sm, n) q < n" by simp

  { fix iS 
    assume iS_subset: "iS \<subseteq> partition_state_map P ` pre"
       and in_iS_impl: "\<forall>i\<in>pre. split_language_equiv_partition_pred \<A>
               (partition_index_map P (partition_state_map P i)) a
               (partition_index_map P p) \<longrightarrow>
             partition_state_map P i \<in> iS"

    from iS_subset invar_P pre_subset'
    have prop1: "partition_index_map P ` iS \<subseteq> P'"
      apply (simp add: P'_eq subset_iff image_iff Bex_def dom_def partition_state_map_def
                       partition_index_map_def set_eq_iff)
      by (metis option.sel)
   
    { fix i'
      assume "i' \<in> iS" 
      with iS_subset have "i' \<in> (partition_state_map P) ` pre" by blast
      then obtain q where q_in_pre: "q \<in> pre" and i'_eq: "i' = partition_state_map P q"
        by auto      
      from q_in_pre pre_subset' obtain i'' where "sm q = Some i''" by auto
      with i'_eq have sm_q_eq: "sm q = Some i'" by (simp add: partition_state_map_def)

      with invar_P obtain p where im_i'_eq: "im i' = Some p" and q_in_p: "q \<in> p" by auto

      have "q \<in> partition_index_map (im, sm, n) i' \<inter> pre"
        by (simp add: partition_index_map_def im_i'_eq q_in_p q_in_pre)
      hence "partition_index_map (im, sm, n) i' \<inter> pre \<noteq> {}" by auto
    } note prop2 = this

    { fix p''
      assume p''_in: "p'' \<in> P'"
         and p''_not_disj_pre: "p'' \<inter> pre \<noteq> {}"
         and part_pred: "split_language_equiv_partition_pred \<A> p'' a p'"

      from p''_in obtain i' where i'_le: "i' < n" and im_i'_eq: "im i' = Some p''" 
        unfolding P'_eq by auto

      from p''_not_disj_pre obtain q where q_in_p'': "q \<in> p''" and q_in_pre: "q \<in> pre" by auto
      from invar_P have sm_q_eq: "sm q = Some i'"  by simp (metis im_i'_eq q_in_p'')

      have "partition_index_map P (partition_state_map P q) = p''"
        by (simp add: partition_state_map_def partition_index_map_def sm_q_eq im_i'_eq)
      with in_iS_impl p'_eq part_pred q_in_pre
      have "partition_state_map P q \<in> iS" by metis

      hence "p'' \<in> partition_index_map P ` iS" 
        apply (simp add: image_iff partition_index_map_def partition_state_map_def sm_q_eq)
        apply (metis im_i'_eq option.sel)
      done
    } note prop3 = this
    from prop1 prop2 prop3

    have "partition_index_map P ` iS \<subseteq> P' \<and>
          (\<forall>i'\<in>iS. partition_index_map P i' \<inter> pre \<noteq> {}) \<and>
          (\<forall>p'a\<in>P'.
              p'a \<inter> pre \<noteq> {} \<and> split_language_equiv_partition_pred \<A> p'a a p' \<longrightarrow>
              p'a \<in> partition_index_map P ` iS)" 
      by simp
  } note prop4 = this

  {
  fix iS PS 
  assume "(iS, PS) \<in> br ((`) (partition_index_map P))
          (\<lambda>iS. iS \<subseteq> partition_state_map P ` pre)"
  hence PS_eq[simp]: "PS = partition_index_map (im, sm, n) ` iS" and
        iS_subset: "iS \<subseteq> partition_state_map (im, sm, n) ` pre"
    apply (simp add: in_br_conv)+
    done

  have map_pre_subset: "partition_state_map P ` pre \<subseteq> {i. i < n}"
    apply (auto)
    apply (rule_tac P_state_map_leq)
    apply (insert pre_subset) 
    apply auto
  done 
  with iS_subset have iS_subset': "iS \<subseteq> {i. i < n}" by simp

  have im_inj_on: "\<And>S. S \<subseteq> {i. i < n} \<Longrightarrow> inj_on (partition_index_map P) S"
    apply (rule partition_index_map_inj_on[OF invar_P])
    apply (auto)
  done

  show "inj_on (partition_index_map P) iS"  by (intro im_inj_on iS_subset')
  show "PS = partition_index_map P ` iS" by simp

  show "((P, L - {(a, p)}), (P', L' - {(a, p')})) \<in> Hopcroft_map_state_rel"
  proof -
    have "(apsnd (partition_index_map (im, sm, n))) ` (L - {(a, p)}) =
          (((apsnd (partition_index_map (im, sm, n))) ` L) - 
           ((apsnd (partition_index_map (im, sm, n))) ` {(a, p)}))" 
      apply (rule inj_on_image_set_diff [where C = "UNIV \<times> {i. i < n}"])
      apply (simp add: apsnd_def)
      apply (rule map_prod_inj_on)
      apply (rule inj_on_id)
      apply (rule im_inj_on[unfolded P_eq], simp)
      apply (insert p_le L_OK)
      apply auto
    done

    hence "apsnd (partition_index_map (im, sm, n)) ` L - {(a, p')} =
           apsnd (partition_index_map (im, sm, n)) ` (L - {(a, p)})" by (simp add: p'_eq)

    with PL_OK show ?thesis
      by (simp add: Hopcroft_map_state_rel_def Hopcroft_map_state_\<alpha>_def[abs_def]
                     Hopcroft_map_state_invar_def in_br_conv)
  qed

  show "partition_free_index P \<le> partition_free_index (fst (P, L - {(a, p)})) \<and>
        (\<forall>i\<in>iS. fst (fst (P, L - {(a, p)})) i = fst P i)"
    by simp

  { fix it \<sigma> it' \<sigma>'
    assume "Hopcroft_set_step_invar \<A> p' a P' L' it' \<sigma>'"
           "(\<sigma>, \<sigma>') \<in> Hopcroft_map_state_rel" 
           "it' = partition_index_map P ` it"
    thus "Hopcroft_map_step_invar \<A> p a P L it \<sigma>"
      unfolding Hopcroft_map_state_rel_def Hopcroft_map_step_invar_def
      by (simp add: L'_eq p'_eq P'_eq in_br_conv)
  }

  apply_end clarify
  apply_end (simp only: fst_conv)
  apply_end (rule refine)

  { fix i it im' sm' n' sL x' it' P'' L'' i'
    assume "i \<in> it"
       and it_subset: "it \<subseteq> iS"
       and map_step_invar: "Hopcroft_map_step_invar \<A> p a P L it ((im', sm', n'), sL)"
       and "Hopcroft_set_step_invar \<A> p' a P' L' (partition_index_map P ` it) (P'', L'')"
       and in_rel: "(((im', sm', n'), sL), P'', L'') \<in> Hopcroft_map_state_rel"
       and map_i_i'_eq: "partition_index_map P i = partition_index_map P i'"
       and "i' \<in> it"
           "partition_free_index P \<le> partition_free_index (im', sm', n')" 
       and im'_eq: "\<forall>i\<in>it. im' i = fst P i"
    
    from map_pre_subset \<open>i \<in> it\<close> it_subset iS_subset' have i_le: "i < n"
      by (simp add: subset_iff)

    from map_pre_subset \<open>i' \<in> it\<close> it_subset iS_subset' have i'_le: "i' < n" 
      by (simp add: subset_iff)

    from im_inj_on[of "{i, i'}"] map_i_i'_eq have i'_eq[simp]: "i' = i"
      by (simp add: subset_iff i_le i'_le image_iff)

    define p'' where "p'' \<equiv> partition_index_map P i"
    define pt' where "pt' \<equiv> {q \<in> p''. q \<in> pre}"
    define pf' where "pf' \<equiv> {q \<in> p''. q \<notin> pre}"

    from im'_eq `i\<in>it` have p''_intro: "partition_index_map (im', sm', n') i = p''"
      unfolding p''_def partition_index_map_def by simp

    from `i \<in> it` it_subset iS_subset pre_subset'
    obtain q where q_in_pre: "q \<in> pre" and sm_q_eq: "sm q = Some i"
      apply (simp add: subset_iff image_iff partition_state_map_def dom_def)
      apply (metis option.sel)
    done

    from invar_P  sm_q_eq
    have q_in_p'': "q \<in> p''" by (auto simp add: p''_def partition_index_map_def) 

    have "q \<in> pt'"
      unfolding pt'_def 
      by (simp add: q_in_pre q_in_p'')
    hence pt'_neq_emp: "pt' \<noteq> {}" by auto

    define pmin where "pmin \<equiv> if card pf' < card pt' then pf' else pt'"
    define pmax where "pmax \<equiv> if card pf' < card pt' then pt' else pf'"
    
    have pminmax: "(if card pf' < card pt' then (pf', pt') else (pt', pf')) = (pmin, pmax)"
      unfolding pmin_def pmax_def by simp

    from \<open>partition_free_index P \<le> partition_free_index (im', sm', n')\<close> have
      n_le: "n \<le> n'" by simp

    from invar_P \<open>i < n\<close> have "i \<in> (dom im)" by simp
    hence im_i_eq: "im i = Some p''"
      by (auto simp add: dom_def set_eq_iff p''_def partition_index_map_def) 

    have "i \<in> dom im'"
      using n_le i_le map_step_invar 
      unfolding Hopcroft_map_step_invar_def Hopcroft_map_state_invar_def 
        by simp
 
    from \<open>i \<in> dom im\<close> \<open>i \<in> dom im'\<close> n_le
    show "i \<in> dom im' \<and> i \<in> dom (fst P) \<and> fst P i = fst P i \<and>
          snd (snd P) \<le> snd (snd (im', sm', n'))" by simp

    have "(if card pf' = 0 then RETURN ((im', sm', n'), sL)
     else ASSERT (\<forall>ai\<in>sL. snd ai < partition_free_index (im', sm', n')) \<bind>
                 (\<lambda>_. let L' = {(a, partition_free_index (im', sm', n')) |a. a \<in> \<Sigma> \<A>} \<union> sL;
                          P' = partition_map_split (im', sm', n') i pmin pmax
                        in RETURN (P', L')))
    \<le> \<Down> {(\<sigma>, \<sigma>').
         (\<sigma>, \<sigma>') \<in> Hopcroft_map_state_rel \<and>
         partition_free_index P \<le> partition_free_index (fst \<sigma>) \<and>
         (\<forall>i\<in>it - {i}. fst (fst \<sigma>) i = fst P i)}
       (if card pf' = 0 then RETURN (P'', L'')
        else let P' = P'' - {partition_index_map P i'} \<union> {pt', pf'};
                 L' = {(a, p''). (a, p'') \<in> L'' \<and> p'' \<noteq> partition_index_map P i'} \<union>
                      {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
                      {(a, pmax) |a. (a, partition_index_map P i') \<in> L''}
             in RETURN (P', L'))" 
    proof (cases "card pf' = 0")
       case True 
       with in_rel n_le im'_eq
       show ?thesis by (simp add: Bex_def Hopcroft_map_state_rel_def pw_le_iff refine_pw_simps)
    next
      case False note card_pf'_neq = this
      hence pf'_neq_emp: "pf' \<noteq> {}" by auto

      with pt'_neq_emp have pminmax_neq_emp: "pmin \<noteq> {}" "pmax \<noteq> {}"
         unfolding pmin_def pmax_def by simp_all

      have p''_eq_minmax: "p'' = pmin \<union> pmax"
         unfolding pmin_def pmax_def pt'_def pf'_def by auto
      have pminmax_disj: "pmin \<inter> pmax = {}" 
         unfolding pmin_def pmax_def pt'_def pf'_def by auto

      from n_le it_subset iS_subset' have n'_not_in: "n' \<notin> it" 
        by auto

      from in_rel have sL_OK: "\<And>a i. (a, i) \<in> sL \<Longrightarrow> i < n'"
           unfolding Hopcroft_map_state_rel_def Hopcroft_map_state_invar_def[abs_def] 
                     Hopcroft_map_state_\<alpha>_def[abs_def]
           by (auto simp add: in_br_conv)
      have in_rel': "
        (((im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n'),
          {(a, n') |a. a \<in> \<Sigma> \<A>} \<union> sL), insert pt' (insert pf' (P'' - {p''})),
         {(a, p'''). (a, p''') \<in> L'' \<and> p''' \<noteq> p''} \<union> {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
         {(a, pmax) |a. (a, p'') \<in> L''}) \<in> Hopcroft_map_state_rel" 
       proof -
         from i_le n_le have i_le': "i < n'" by simp
         hence i_neq_n': "i \<noteq> n'" by simp

         from in_rel have invar_P'': "partition_map_invar (im', sm', n')" and 
                          P''_eq: "P'' = partition_map_\<alpha> (im', sm', n')"
              and L''_eq: "L'' = apsnd (partition_index_map (im', sm', n')) ` sL"
           unfolding Hopcroft_map_state_rel_def Hopcroft_map_state_invar_def[abs_def] 
                     Hopcroft_map_state_\<alpha>_def[abs_def]
           by (auto simp add: in_br_conv)

         from invar_P'' i_le' have "i \<in> (dom im')" by simp
         hence im'_i_eq: "im' i = Some p''"
           by (auto simp add: dom_def p''_intro[symmetric] partition_index_map_def) 

         have invar_OK: "Hopcroft_map_state_invar
           ((im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n'),
           {(a, n') |a. a \<in> \<Sigma> \<A>} \<union> sL)" 
           apply (simp add: Hopcroft_map_state_invar_def i_neq_n' pminmax_neq_emp Ball_def
                            im'_eq all_conj_distrib imp_conjR)
           apply (intro conjI allI impI)
           proof -
             from invar_P'' have "dom im' = {i. i < n'}" by simp
             with i_le n_le show "insert n' (insert i (dom im')) = {i. i < Suc n'}"
               by auto
           next
             fix i'
             from invar_P'' show "im' i' \<noteq> Some {}" by simp
           next
             fix a i'
             assume "(a, i') \<in> sL"
             from sL_OK[OF this] have "i' < n'" .
             thus "i' < Suc n'" by simp
           next
             fix q
             assume "q \<in> pmin"
             thus "q \<notin> pmax" using pminmax_disj by auto
           next
             fix q
             from invar_P'' have "n' \<notin> dom im'" by simp
             hence "im' n' = None" unfolding dom_def by simp
             with invar_P'' show "sm' q \<noteq> Some n'"
               by simp
           next
             fix q i'
             assume "q \<notin> pmin" "i' \<noteq> i" "i' \<noteq> n'" 
             with invar_P'' show "(sm' q = Some i') = (\<exists>p. im' i' = Some p \<and> q \<in> p)" 
               by simp
           next
             fix q i' p
             assume "q \<in> pmin" "i' \<noteq> i"  and 
                    im'_i'_eq: "im' i' = Some p"
             
             from im'_i'_eq have "i' \<in> dom im'" by (simp add: dom_def)
             with invar_P'' have "i' < n'" by simp

             from `q \<in> pmin` have "q \<in> p''" 
               unfolding p''_eq_minmax by simp
             
             from partition_index_map_disj [OF invar_P'', of i i'] `q \<in> p''` `i' < n'` i_le n_le
             show "q \<notin> p"
               by (simp add: partition_index_map_def p''_intro[symmetric] im'_i'_eq `i' \<noteq> i`[symmetric] set_eq_iff)
           next
             fix q
             assume q_nin_min: "q \<notin> pmin"

             from invar_P'' have "(sm' q = Some i) \<longleftrightarrow> q \<in> p''"
               by (simp add: partition_index_map_def im'_i_eq)
              with q_nin_min show "(sm' q = Some i) \<longleftrightarrow> q \<in> pmax"
               unfolding p''_eq_minmax by simp
           qed
         
         have alpha_OK: "(insert pt' (insert pf' (P'' - {p''})),
               {(a, p'''). (a, p''') \<in> L'' \<and> p''' \<noteq> p''} \<union> {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
               {(a, pmax) |a. (a, p'') \<in> L''}) =
               Hopcroft_map_state_\<alpha>
                ((im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n'),
                {(a, n') |a. a \<in> \<Sigma> \<A>} \<union> sL)" 
            apply (simp add: Hopcroft_map_state_\<alpha>_def P''_eq)
            apply (intro conjI set_eqI)
            apply (simp_all split: prod.splits add: image_iff Bex_def i_neq_n')
            prefer 2
            apply clarify
            apply simp
            apply (rename_tac a pp) 
          proof -
            fix pp
            show "(pp = pt' \<or> pp = pf' \<or> (\<exists>i<n'. im' i = Some pp) \<and> pp \<noteq> p'') =
                  (\<exists>ia. (ia = i \<longrightarrow> i < Suc n' \<and> pmax = pp) \<and>
                    (ia \<noteq> i \<longrightarrow> (ia = n' \<longrightarrow> pmin = pp) \<and> (ia \<noteq> n' \<longrightarrow> ia < Suc n' \<and> im' ia = Some pp)))"
            proof (cases "pp = pt' \<or> pp = pf'")
               case True note pp_eq_ptf' = this
               show ?thesis 
               proof (cases "pp = pmax")
                 case True with pp_eq_ptf' i_le' show ?thesis
                   by auto
               next
                 case False 
                 with pp_eq_ptf' have "pp = pmin"
                   unfolding pmax_def pmin_def by auto
                  with pp_eq_ptf' i_le' show ?thesis
                   by auto
               qed
            next
               case False 
               hence pp_neq: "pp \<noteq> pt'" "pp \<noteq> pf'" "pp \<noteq> pmin" "pp \<noteq> pmax"
                 unfolding pmin_def pmax_def by simp_all

               { fix i'
                 have "((i' < n' \<and> im' i' = Some pp) \<and> pp \<noteq> p'') =
                       (i' \<noteq> i \<and> i' \<noteq> n' \<and> i' < Suc n' \<and> im' i' = Some pp)"
                 proof (cases "i' < n' \<and> im' i' = Some pp")
                   case False thus ?thesis by auto
                 next 
                   case True 
                   with partition_index_map_inj_on [OF invar_P'', of "{i', i}"] i_le'
                   show ?thesis 
                     apply (simp add: image_iff partition_index_map_def Ball_def
                                      p''_intro[symmetric])
                     apply auto
                   done
                 qed
               } note step = this 
 
               show ?thesis 
                 apply (simp del: ex_simps add: pp_neq pp_neq[symmetric] ex_simps[symmetric])
                 apply (rule iff_exI) 
                 apply (metis step)
               done
            qed
         next
            fix a pp
            { fix a pp
              have "(a, pp) \<in> L'' \<longleftrightarrow>
                    (\<exists>i'. (a, i') \<in> sL \<and> pp = the (im' i'))"
                unfolding L''_eq
                by (simp add: image_iff Bex_def partition_index_map_def)
              moreover
              { fix i'
                have "(a, i') \<in> sL \<and> pp = the (im' i') \<longleftrightarrow>
                      (a, i') \<in> sL \<and> i' < n' \<and> (im' i' = Some pp)"
                proof (cases "(a, i') \<in> sL")
                  case False thus ?thesis by simp
                next
                  case True note ai'_in_sL = this
                  from sL_OK[OF ai'_in_sL] have "i' < n'" .
                  with invar_P'' have "i' \<in> dom im'" by simp
                  with ai'_in_sL `i' < n'` show ?thesis by auto
                qed
              }
              ultimately have "(a, pp) \<in> L'' \<longleftrightarrow>
                               (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> (im' i' = Some pp))"
                by simp
            } note in_L''_eq = this

            { fix i'
              have "(im' i' = Some p'') \<longleftrightarrow> i' = i"
              proof
                assume "i' = i" 
                thus "im' i' = Some p''"
                  by (simp add: im'_i_eq)
              next
                assume im'_i'_eq: "im' i' = Some p''"
                hence "i' \<in> dom im'" by (simp add: dom_def)
                with invar_P'' have "i' < n'" by simp

                from partition_index_map_inj_on [OF invar_P'', of "{i, i'}"] `i' < n'` i_le'
                show "i' = i"
                  by (auto simp add: image_iff Bex_def partition_index_map_def im'_i'_eq im'_i_eq)
              qed
            } note im'_eq_p'' = this

            show " ((a, pp) \<in> L'' \<and> pp \<noteq> p'' \<or> pp = pmin \<and> a \<in> \<Sigma> \<A> \<or> pp = pmax \<and> (a, p'') \<in> L'') =
                   (\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = partition_index_map
                         (im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n') i')"
                   (is "?ls = (\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and> pp = ?pm i')")
              unfolding in_L''_eq
              apply (rule iffI)
              apply (elim disjE conjE exE)
              prefer 4
              apply (elim exE conjE disjE)
            proof -
              fix i'
              assume "pp = ?pm i'" "i' = n'" "a \<in> \<Sigma> \<A>"
              hence "pp = pmin \<and> a \<in> \<Sigma> \<A>" 
                by (simp add: partition_index_map_def)
              thus "(\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some pp) \<and> pp \<noteq> p'' \<or>
                    pp = pmin \<and> a \<in> \<Sigma> \<A> \<or>
                    pp = pmax \<and> (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some p'')" by simp
            next
              assume "pp = pmin" "a \<in> \<Sigma> \<A>" 
              thus "\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = ?pm i'"
                apply (rule_tac exI[where x = n'])
                apply (simp add: partition_index_map_def)
              done
            next
              fix i'
              assume "pp = pmax" "(a, i') \<in> sL" "i' < n'" "im' i' = Some p''"
              moreover from `im' i' = Some p''` have "i' = i" by (simp add: im'_eq_p'')
              ultimately
              show "\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = ?pm i'"
                apply (rule_tac exI[where x = i])
                apply (simp add: partition_index_map_def)
              done
            next
              fix i'
              assume "pp \<noteq> p''" "(a, i') \<in> sL" "i' < n'" "im' i' = Some pp"
              moreover from `im' i' = Some pp` `pp \<noteq> p''` 
                have "i' \<noteq> i" using im'_eq_p'' [of i', symmetric]
                  by simp
              ultimately
              show "\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = ?pm i'"
                apply (rule_tac exI[where x = i'])
                apply (simp add: partition_index_map_def)
              done
            next
              fix i'
              assume pp_eq: "pp = ?pm i'" and in_sL: "(a, i') \<in> sL" 

              from sL_OK[OF in_sL] have i'_le: "i' < n'" .
              with invar_P'' have "i' \<in> dom im'" by simp
              then obtain pp' where im'_i'_eq: "im' i' = Some pp'" by blast 

              show "(\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some pp) \<and> pp \<noteq> p'' \<or>
                    pp = pmin \<and> a \<in> \<Sigma> \<A> \<or>
                    pp = pmax \<and> (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some p'')" 
              proof (cases "i' = i")
                case True note i'_eq = this
                with pp_eq i_le' have "pp = pmax"
                  by (simp add: partition_index_map_def)
                with in_sL i'_eq have "pp = pmax \<and> (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some p'')"
                  apply simp
                  apply (rule exI [where x = i])
                  apply (simp add: im'_i_eq i_le')
                done
                thus ?thesis by blast
              next
                case False note i'_neq = this
                with im'_i'_eq pp_eq i'_le have pp_eq: "pp = pp'" 
                  by (simp add: partition_index_map_def)

                with i'_neq im'_eq_p'' [of i'] have pp_neq: "pp \<noteq> p''" 
                   by (simp add: im'_i'_eq)
                
                from in_sL i'_le pp_eq have "\<exists>i'. ((a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some pp)"
                  apply (rule_tac exI [where x = i'])
                  apply (simp add: im'_i'_eq)
                done
                with `pp \<noteq> p''` show ?thesis by blast
              qed
            qed
         qed
         from alpha_OK invar_OK show ?thesis by (simp add: Hopcroft_map_state_rel_def in_br_conv)
       qed

       from in_rel' n_le i_le card_pf'_neq n'_not_in im'_eq sL_OK
       show ?thesis 
         apply refine_rcg
         apply (simp_all add: partition_index_map_def im_i_eq Ball_def pw_le_iff 
                              Hopcroft_map_state_rel_def single_valued_def)
       done
    qed
    thus "(let (pt', pct', pf', pcf') =
              ({q \<in> partition_index_map (im', sm', n') i. q \<in> pre},
               card {q \<in> partition_index_map (im', sm', n') i. q \<in> pre},
               {q \<in> partition_index_map (im', sm', n') i. q \<notin> pre},
               card {q \<in> partition_index_map (im', sm', n') i. q \<notin> pre})
        in if pcf' = 0 then RETURN ((im', sm', n'), sL)
           else let (pmin, pmax) = if pcf' < pct' then (pf', pt') else (pt', pf')
                in ASSERT (\<forall>ai\<in>sL. snd ai < partition_free_index (im', sm', n')) \<bind>
                   (\<lambda>_. let L' = {(a, partition_free_index (im', sm', n')) |a. a \<in> \<Sigma> \<A>} \<union> sL;
                            P' = partition_map_split (im', sm', n') i pmin pmax
                        in RETURN (P', L')))
       \<le> \<Down> {(\<sigma>, \<sigma>').
            (\<sigma>, \<sigma>') \<in> Hopcroft_map_state_rel \<and>
            partition_free_index P \<le> partition_free_index (fst \<sigma>) \<and>
            (\<forall>i\<in>it - {i}. fst (fst \<sigma>) i = fst P i)}
          (let (pt', pct', pf', pcf') =
                 ({q \<in> partition_index_map P i'. q \<in> pre},
                  card {q \<in> partition_index_map P i'. q \<in> pre},
                  {q \<in> partition_index_map P i'. q \<notin> pre},
                  card {q \<in> partition_index_map P i'. q \<notin> pre})
           in if pcf' = 0 then RETURN (P'', L'')
              else let (pmin, pmax) = if pcf' < pct' then (pf', pt') else (pt', pf');
                       P' = P'' - {partition_index_map P i'} \<union> {pt', pf'};
                       L' = {(a, p''). (a, p'') \<in> L'' \<and> p'' \<noteq> partition_index_map P i'} \<union>
                            {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
                            {(a, pmax) |a. (a, partition_index_map P i') \<in> L''}
                   in RETURN (P', L'))" 
      apply (simp split del: if_splits 
                 del: P_eq
                 add: p''_def[symmetric] pt'_def[symmetric] pf'_def[symmetric] p''_intro)
      apply (unfold pminmax)
      apply (cases "card pf' = 0")
      apply (simp_all)
    done
  }
}
{
  fix x
  assume asm:"pre \<subseteq> dom (fst (snd P))" "dom (fst (snd P)) \<subseteq> \<Q> \<A>" "x \<subseteq> partition_state_map P ` pre"
    "\<forall>i\<in>pre. split_language_equiv_partition_pred \<A> (partition_index_map P (partition_state_map P i)) a (partition_index_map P p) \<longrightarrow> partition_state_map P i \<in> x"
  thus "\<exists>x'. (x, x') \<in> br ((`) (partition_index_map P)) (\<lambda>iS. iS \<subseteq> partition_state_map P ` pre) \<and>
                   x' \<subseteq> P' \<and> (\<forall>p'\<in>x'. p' \<inter> pre \<noteq> {}) \<and>
                   (\<forall>p'a\<in>P'. p'a \<inter> pre \<noteq> {} \<and> split_language_equiv_partition_pred \<A> p'a a p' \<longrightarrow> p'a \<in> x')"
    apply (simp add: in_br_conv)
    using P_eq prop4 by simp
}
qed 

(* -- OLD PROOF --
proof -
  show "single_valued Hopcroft_map_state_rel"
    unfolding Hopcroft_map_state_rel_def by (simp del: br_def)
next
  from PL_OK have invar_P: "partition_map_invar P" and P'_eq: "P' = partition_map_\<alpha> P"
              and L_OK: "\<And>a p. (a, p) \<in> L \<Longrightarrow> p < partition_free_index P"
              and L'_eq: "L' = apsnd (partition_index_map P) ` L"
    unfolding Hopcroft_map_state_rel_def Hopcroft_map_state_invar_def[abs_def] 
              Hopcroft_map_state_\<alpha>_def[abs_def]
    by auto

  have \<Q>_eq: "\<Union>partition_map_\<alpha> P = \<Q> \<A>" 
    using partition_map_is_partition_eq[OF invar_P, folded P'_eq, OF part_P'] P'_eq
    by simp

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  show pre_subset': "pre \<subseteq> dom (fst (snd P)) \<and> dom (fst (snd P)) \<subseteq> \<Q> \<A>"
    using invar_P pre_subset
    apply (simp add: set_eq_iff dom_def subset_iff \<Q>_eq[symmetric])
    apply metis
  done

  from partition_state_map_le[OF invar_P, unfolded \<Q>_eq] 
  have P_state_map_leq: "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> partition_state_map (im, sm, n) q < n" by simp

  { fix iS 
    assume iS_subset: "iS \<subseteq> partition_state_map P ` pre"
       and in_iS_impl: "\<forall>i\<in>pre. split_language_equiv_partition_pred \<A>
               (partition_index_map P (partition_state_map P i)) a
               (partition_index_map P p) \<longrightarrow>
             partition_state_map P i \<in> iS"

    from iS_subset invar_P pre_subset'
    have prop1: "partition_index_map P ` iS \<subseteq> P'"
      apply (simp add: P'_eq subset_iff image_iff Bex_def dom_def partition_state_map_def
                       partition_index_map_def set_eq_iff)
      apply (metis the.simps)
    done
   
    { fix i'
      assume "i' \<in> iS" 
      with iS_subset have "i' \<in> (partition_state_map P) ` pre" by blast
      then obtain q where q_in_pre: "q \<in> pre" and i'_eq: "i' = partition_state_map P q"
        by auto      
      from q_in_pre pre_subset' obtain i'' where "sm q = Some i''" by auto
      with i'_eq have sm_q_eq: "sm q = Some i'" by (simp add: partition_state_map_def)

      with invar_P obtain p where im_i'_eq: "im i' = Some p" and q_in_p: "q \<in> p" by auto

      have "q \<in> partition_index_map (im, sm, n) i' \<inter> pre"
        by (simp add: partition_index_map_def im_i'_eq q_in_p q_in_pre)
      hence "partition_index_map (im, sm, n) i' \<inter> pre \<noteq> {}" by auto
    } note prop2 = this

    { fix p''
      assume p''_in: "p'' \<in> P'"
         and p''_not_disj_pre: "p'' \<inter> pre \<noteq> {}"
         and part_pred: "split_language_equiv_partition_pred \<A> p'' a p'"

      from p''_in obtain i' where i'_le: "i' < n" and im_i'_eq: "im i' = Some p''" 
        unfolding P'_eq by auto

      from p''_not_disj_pre obtain q where q_in_p'': "q \<in> p''" and q_in_pre: "q \<in> pre" by auto
      from invar_P have sm_q_eq: "sm q = Some i'"  by simp (metis im_i'_eq q_in_p'')

      have "partition_index_map P (partition_state_map P q) = p''"
        by (simp add: partition_state_map_def partition_index_map_def sm_q_eq im_i'_eq)
      with in_iS_impl p'_eq part_pred q_in_pre
      have "partition_state_map P q \<in> iS" by metis

      hence "p'' \<in> partition_index_map P ` iS" 
        apply (simp add: image_iff partition_index_map_def partition_state_map_def sm_q_eq)
        apply (metis im_i'_eq the.simps)
      done
    } note prop3 = this

    from prop1 prop2 prop3
    show "partition_index_map P ` iS \<subseteq> P' \<and>
          (\<forall>i'\<in>iS. partition_index_map P i' \<inter> pre \<noteq> {}) \<and>
          (\<forall>p'a\<in>P'.
              p'a \<inter> pre \<noteq> {} \<and> split_language_equiv_partition_pred \<A> p'a a p' \<longrightarrow>
              p'a \<in> partition_index_map P ` iS)" 
      by simp
  }

  fix iS PS 
  assume "(iS, PS) \<in> br (op ` (partition_index_map P))
          (\<lambda>iS. iS \<subseteq> partition_state_map P ` pre)"
  hence PS_eq[simp]: "PS = partition_index_map (im, sm, n) ` iS" and
        iS_subset: "iS \<subseteq> partition_state_map (im, sm, n) ` pre" by simp_all

  have map_pre_subset: "partition_state_map P ` pre \<subseteq> {i. i < n}"
    apply (auto)
    apply (rule_tac P_state_map_leq)
    apply (insert pre_subset) 
    apply auto
  done 
  with iS_subset have iS_subset': "iS \<subseteq> {i. i < n}" by simp

  have im_inj_on: "\<And>S. S \<subseteq> {i. i < n} \<Longrightarrow> inj_on (partition_index_map P) S"
    apply (rule partition_index_map_inj_on[OF invar_P])
    apply (auto)
  done

  show "inj_on (partition_index_map P) iS"  by (intro im_inj_on iS_subset')
  show "PS = partition_index_map P ` iS" by simp

  show "((P, L - {(a, p)}), (P', L' - {(a, p')})) \<in> Hopcroft_map_state_rel"
  proof -
    have "(apsnd (partition_index_map (im, sm, n))) ` (L - {(a, p)}) =
          (((apsnd (partition_index_map (im, sm, n))) ` L) - 
           ((apsnd (partition_index_map (im, sm, n))) ` {(a, p)}))" 
      apply (rule inj_on_image_set_diff [where C = "UNIV \<times> {i. i < n}"])
      apply (simp add: apsnd_def)
      apply (rule map_pair_inj_on)
      apply (rule inj_on_id)
      apply (rule im_inj_on[unfolded P_eq], simp)
      apply (insert p_le L_OK)
      apply auto
    done

    hence "apsnd (partition_index_map (im, sm, n)) ` L - {(a, p')} =
           apsnd (partition_index_map (im, sm, n)) ` (L - {(a, p)})" by (simp add: p'_eq)

    with PL_OK show ?thesis
       by (simp add: Hopcroft_map_state_rel_def Hopcroft_map_state_\<alpha>_def[abs_def]
                     Hopcroft_map_state_invar_def)
  qed

  show "partition_free_index P \<le> partition_free_index (fst (P, L - {(a, p)})) \<and>
        (\<forall>i\<in>iS. fst (fst (P, L - {(a, p)})) i = fst P i)"
    by simp

  { fix it \<sigma> it' \<sigma>'
    assume "Hopcroft_set_step_invar \<A> p' a P' L' it' \<sigma>'"
           "(\<sigma>, \<sigma>') \<in> Hopcroft_map_state_rel" 
           "it' = partition_index_map P ` it"
    thus "Hopcroft_map_step_invar \<A> p a P L it \<sigma>"
      unfolding Hopcroft_map_state_rel_def Hopcroft_map_step_invar_def
      by (simp add: L'_eq p'_eq P'_eq)
  }

  apply_end clarify
  apply_end (simp only: fst_conv)
  apply_end (rule refine)

  { fix i it im' sm' n' sL x' it' P'' L'' i'
    assume "i \<in> it"
       and it_subset: "it \<subseteq> iS"
       and map_step_invar: "Hopcroft_map_step_invar \<A> p a P L it ((im', sm', n'), sL)"
       and "Hopcroft_set_step_invar \<A> p' a P' L' (partition_index_map P ` it) (P'', L'')"
       and in_rel: "(((im', sm', n'), sL), P'', L'') \<in> Hopcroft_map_state_rel"
       and map_i_i'_eq: "partition_index_map P i = partition_index_map P i'"
       and "i' \<in> it"
           "partition_free_index P \<le> partition_free_index (im', sm', n')" 
       and im'_eq: "\<forall>i\<in>it. im' i = fst P i"
    
    from map_pre_subset `i \<in> it` it_subset iS_subset' have i_le: "i < n" 
      by (simp add: subset_iff)

    from map_pre_subset `i' \<in> it` it_subset iS_subset' have i'_le: "i' < n" 
      by (simp add: subset_iff)

    from im_inj_on[of "{i, i'}"] map_i_i'_eq have i'_eq[simp]: "i' = i"
      by (simp add: subset_iff i_le i'_le image_iff)

    def p'' \<equiv> "partition_index_map P i"
    def pt' \<equiv> "{q \<in> p''. q \<in> pre}"
    def pf' \<equiv> "{q \<in> p''. q \<notin> pre}"

    from im'_eq `i\<in>it` have p''_intro: "partition_index_map (im', sm', n') i = p''"
      unfolding p''_def partition_index_map_def by simp

    from `i \<in> it` it_subset iS_subset pre_subset'
    obtain q where q_in_pre: "q \<in> pre" and sm_q_eq: "sm q = Some i"
      apply (simp add: subset_iff image_iff partition_state_map_def dom_def)
      apply (metis the.simps)
    done

    from invar_P  sm_q_eq
    have q_in_p'': "q \<in> p''" by (auto simp add: p''_def partition_index_map_def) 

    have "q \<in> pt'"
      unfolding pt'_def 
      by (simp add: q_in_pre q_in_p'')
    hence pt'_neq_emp: "pt' \<noteq> {}" by auto

    def pmin \<equiv> "if card pf' < card pt' then pf' else pt'"
    def pmax \<equiv> "if card pf' < card pt' then pt' else pf'"
    
    have pminmax: "(if card pf' < card pt' then (pf', pt') else (pt', pf')) = (pmin, pmax)"
      unfolding pmin_def pmax_def by simp

    from `partition_free_index P \<le> partition_free_index (im', sm', n')` have
      n_le: "n \<le> n'" by simp

    from invar_P `i < n` have "i \<in> (dom im)" by simp
    hence im_i_eq: "im i = Some p''"
      by (auto simp add: dom_def set_eq_iff p''_def partition_index_map_def) 

    have "i \<in> dom im'"
      using n_le i_le map_step_invar 
      unfolding Hopcroft_map_step_invar_def Hopcroft_map_state_invar_def 
        by simp
 
    from `i \<in> dom im` `i \<in> dom im'` n_le
    show "i \<in> dom im' \<and> i \<in> dom (fst P) \<and> fst P i = fst P i \<and>
          snd (snd P) \<le> snd (snd (im', sm', n'))" by simp

    have "(if card pf' = 0 then RETURN ((im', sm', n'), sL)
     else ASSERT (\<forall>ai\<in>sL. snd ai < partition_free_index (im', sm', n')) \<guillemotright>=
                 (\<lambda>_. let L' = {(a, partition_free_index (im', sm', n')) |a. a \<in> \<Sigma> \<A>} \<union> sL;
                          P' = partition_map_split (im', sm', n') i pmin pmax
                        in RETURN (P', L')))
    \<le> \<Down> {(\<sigma>, \<sigma>').
         (\<sigma>, \<sigma>') \<in> Hopcroft_map_state_rel \<and>
         partition_free_index P \<le> partition_free_index (fst \<sigma>) \<and>
         (\<forall>i\<in>it - {i}. fst (fst \<sigma>) i = fst P i)}
       (if card pf' = 0 then RETURN (P'', L'')
        else let P' = P'' - {partition_index_map P i'} \<union> {pt', pf'};
                 L' = {(a, p''). (a, p'') \<in> L'' \<and> p'' \<noteq> partition_index_map P i'} \<union>
                      {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
                      {(a, pmax) |a. (a, partition_index_map P i') \<in> L''}
             in RETURN (P', L'))" 
    proof (cases "card pf' = 0")
       case True 
       with in_rel n_le im'_eq
       show ?thesis by (simp add: Bex_def Hopcroft_map_state_rel_def pw_le_iff refine_pw_simps)
    next
      case False note card_pf'_neq = this
      hence pf'_neq_emp: "pf' \<noteq> {}" by auto

      with pt'_neq_emp have pminmax_neq_emp: "pmin \<noteq> {}" "pmax \<noteq> {}"
         unfolding pmin_def pmax_def by simp_all

      have p''_eq_minmax: "p'' = pmin \<union> pmax"
         unfolding pmin_def pmax_def pt'_def pf'_def by auto
      have pminmax_disj: "pmin \<inter> pmax = {}" 
         unfolding pmin_def pmax_def pt'_def pf'_def by auto

      from n_le it_subset iS_subset' have n'_not_in: "n' \<notin> it" 
        by auto

      from in_rel have sL_OK: "\<And>a i. (a, i) \<in> sL \<Longrightarrow> i < n'"
           unfolding Hopcroft_map_state_rel_def Hopcroft_map_state_invar_def[abs_def] 
                     Hopcroft_map_state_\<alpha>_def[abs_def]
           by auto
      have in_rel': "
        (((im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n'),
          {(a, n') |a. a \<in> \<Sigma> \<A>} \<union> sL), insert pt' (insert pf' (P'' - {p''})),
         {(a, p'''). (a, p''') \<in> L'' \<and> p''' \<noteq> p''} \<union> {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
         {(a, pmax) |a. (a, p'') \<in> L''}) \<in> Hopcroft_map_state_rel" 
       proof -
         from i_le n_le have i_le': "i < n'" by simp
         hence i_neq_n': "i \<noteq> n'" by simp

         from in_rel have invar_P'': "partition_map_invar (im', sm', n')" and 
                          P''_eq: "P'' = partition_map_\<alpha> (im', sm', n')"
              and L''_eq: "L'' = apsnd (partition_index_map (im', sm', n')) ` sL"
           unfolding Hopcroft_map_state_rel_def Hopcroft_map_state_invar_def[abs_def] 
                     Hopcroft_map_state_\<alpha>_def[abs_def]
           by auto

         from invar_P'' i_le' have "i \<in> (dom im')" by simp
         hence im'_i_eq: "im' i = Some p''"
           by (auto simp add: dom_def p''_intro[symmetric] partition_index_map_def) 

         have invar_OK: "Hopcroft_map_state_invar
           ((im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n'),
           {(a, n') |a. a \<in> \<Sigma> \<A>} \<union> sL)" 
           apply (simp add: Hopcroft_map_state_invar_def i_neq_n' pminmax_neq_emp Ball_def
                            im'_eq all_conj_distrib imp_conjR)
           apply (intro conjI allI impI)
           proof -
             from invar_P'' have "dom im' = {i. i < n'}" by simp
             with i_le n_le show "insert n' (insert i (dom im')) = {i. i < Suc n'}"
               by auto
           next
             fix i'
             from invar_P'' show "im' i' \<noteq> Some {}" by simp
           next
             fix a i'
             assume "(a, i') \<in> sL"
             from sL_OK[OF this] have "i' < n'" .
             thus "i' < Suc n'" by simp
           next
             fix q
             assume "q \<in> pmin"
             thus "q \<notin> pmax" using pminmax_disj by auto
           next
             fix q
             from invar_P'' have "n' \<notin> dom im'" by simp
             hence "im' n' = None" unfolding dom_def by simp
             with invar_P'' show "sm' q \<noteq> Some n'"
               by simp
           next
             fix q i'
             assume "q \<notin> pmin" "i' \<noteq> i" "i' \<noteq> n'" 
             with invar_P'' show "(sm' q = Some i') = (\<exists>p. im' i' = Some p \<and> q \<in> p)" 
               by simp
           next
             fix q i' p
             assume "q \<in> pmin" "i' \<noteq> i"  and 
                    im'_i'_eq: "im' i' = Some p"
             
             from im'_i'_eq have "i' \<in> dom im'" by (simp add: dom_def)
             with invar_P'' have "i' < n'" by simp

             from `q \<in> pmin` have "q \<in> p''" 
               unfolding p''_eq_minmax by simp
             
             from partition_index_map_disj [OF invar_P'', of i i'] `q \<in> p''` `i' < n'` i_le n_le
             show "q \<notin> p"
               by (simp add: partition_index_map_def p''_intro[symmetric] im'_i'_eq `i' \<noteq> i`[symmetric] set_eq_iff)
           next
             fix q
             assume q_nin_min: "q \<notin> pmin"

             from invar_P'' have "(sm' q = Some i) \<longleftrightarrow> q \<in> p''"
               by (simp add: partition_index_map_def im'_i_eq)
              with q_nin_min show "(sm' q = Some i) \<longleftrightarrow> q \<in> pmax"
               unfolding p''_eq_minmax by simp
           qed
         
         have alpha_OK: "(insert pt' (insert pf' (P'' - {p''})),
               {(a, p'''). (a, p''') \<in> L'' \<and> p''' \<noteq> p''} \<union> {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
               {(a, pmax) |a. (a, p'') \<in> L''}) =
               Hopcroft_map_state_\<alpha>
                ((im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n'),
                {(a, n') |a. a \<in> \<Sigma> \<A>} \<union> sL)" 
            apply (simp add: Hopcroft_map_state_\<alpha>_def P''_eq)
            apply (intro conjI set_eqI)
            apply (simp_all split: prod.splits add: image_iff Bex_def i_neq_n')
            prefer 2
            apply clarify
            apply simp
            apply (rename_tac a pp) 
          proof -
            fix pp
            show "(pp = pt' \<or> pp = pf' \<or> (\<exists>i<n'. im' i = Some pp) \<and> pp \<noteq> p'') =
                  (\<exists>ia. (ia = i \<longrightarrow> i < Suc n' \<and> pmax = pp) \<and>
                    (ia \<noteq> i \<longrightarrow> (ia = n' \<longrightarrow> pmin = pp) \<and> (ia \<noteq> n' \<longrightarrow> ia < Suc n' \<and> im' ia = Some pp)))"
            proof (cases "pp = pt' \<or> pp = pf'")
               case True note pp_eq_ptf' = this
               show ?thesis 
               proof (cases "pp = pmax")
                 case True with pp_eq_ptf' i_le' show ?thesis
                   by auto
               next
                 case False 
                 with pp_eq_ptf' have "pp = pmin"
                   unfolding pmax_def pmin_def by auto
                  with pp_eq_ptf' i_le' show ?thesis
                   by auto
               qed
            next
               case False 
               hence pp_neq: "pp \<noteq> pt'" "pp \<noteq> pf'" "pp \<noteq> pmin" "pp \<noteq> pmax"
                 unfolding pmin_def pmax_def by simp_all

               { fix i'
                 have "((i' < n' \<and> im' i' = Some pp) \<and> pp \<noteq> p'') =
                       (i' \<noteq> i \<and> i' \<noteq> n' \<and> i' < Suc n' \<and> im' i' = Some pp)"
                 proof (cases "i' < n' \<and> im' i' = Some pp")
                   case False thus ?thesis by auto
                 next 
                   case True 
                   with partition_index_map_inj_on [OF invar_P'', of "{i', i}"] i_le'
                   show ?thesis 
                     apply (simp add: image_iff partition_index_map_def Ball_def
                                      p''_intro[symmetric])
                     apply auto
                   done
                 qed
               } note step = this 
 
               show ?thesis 
                 apply (simp del: ex_simps add: pp_neq pp_neq[symmetric] ex_simps[symmetric])
                 apply (rule iff_exI) 
                 apply (metis step)
               done
            qed
         next
            fix a pp
            { fix a pp
              have "(a, pp) \<in> L'' \<longleftrightarrow>
                    (\<exists>i'. (a, i') \<in> sL \<and> pp = the (im' i'))"
                unfolding L''_eq
                by (simp add: image_iff Bex_def partition_index_map_def)
              moreover
              { fix i'
                have "(a, i') \<in> sL \<and> pp = the (im' i') \<longleftrightarrow>
                      (a, i') \<in> sL \<and> i' < n' \<and> (im' i' = Some pp)"
                proof (cases "(a, i') \<in> sL")
                  case False thus ?thesis by simp
                next
                  case True note ai'_in_sL = this
                  from sL_OK[OF ai'_in_sL] have "i' < n'" .
                  with invar_P'' have "i' \<in> dom im'" by simp
                  with ai'_in_sL `i' < n'` show ?thesis by auto
                qed
              }
              ultimately have "(a, pp) \<in> L'' \<longleftrightarrow>
                               (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> (im' i' = Some pp))"
                by simp
            } note in_L''_eq = this

            { fix i'
              have "(im' i' = Some p'') \<longleftrightarrow> i' = i"
              proof
                assume "i' = i" 
                thus "im' i' = Some p''"
                  by (simp add: im'_i_eq)
              next
                assume im'_i'_eq: "im' i' = Some p''"
                hence "i' \<in> dom im'" by (simp add: dom_def)
                with invar_P'' have "i' < n'" by simp

                from partition_index_map_inj_on [OF invar_P'', of "{i, i'}"] `i' < n'` i_le'
                show "i' = i"
                  by (auto simp add: image_iff Bex_def partition_index_map_def im'_i'_eq im'_i_eq)
              qed
            } note im'_eq_p'' = this

            show " ((a, pp) \<in> L'' \<and> pp \<noteq> p'' \<or> pp = pmin \<and> a \<in> \<Sigma> \<A> \<or> pp = pmax \<and> (a, p'') \<in> L'') =
                   (\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = partition_index_map
                         (im'(i \<mapsto> pmax, n' \<mapsto> pmin), \<lambda>q. if q \<in> pmin then Some n' else sm' q, Suc n') i')"
                   (is "?ls = (\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and> pp = ?pm i')")
              unfolding in_L''_eq
              apply (rule iffI)
              apply (elim disjE conjE exE)
              prefer 4
              apply (elim exE conjE disjE)
            proof -
              fix i'
              assume "pp = ?pm i'" "i' = n'" "a \<in> \<Sigma> \<A>"
              hence "pp = pmin \<and> a \<in> \<Sigma> \<A>" 
                by (simp add: partition_index_map_def)
              thus "(\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some pp) \<and> pp \<noteq> p'' \<or>
                    pp = pmin \<and> a \<in> \<Sigma> \<A> \<or>
                    pp = pmax \<and> (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some p'')" by simp
            next
              assume "pp = pmin" "a \<in> \<Sigma> \<A>" 
              thus "\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = ?pm i'"
                apply (rule_tac exI[where x = n'])
                apply (simp add: partition_index_map_def)
              done
            next
              fix i'
              assume "pp = pmax" "(a, i') \<in> sL" "i' < n'" "im' i' = Some p''"
              moreover from `im' i' = Some p''` have "i' = i" by (simp add: im'_eq_p'')
              ultimately
              show "\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = ?pm i'"
                apply (rule_tac exI[where x = i])
                apply (simp add: partition_index_map_def)
              done
            next
              fix i'
              assume "pp \<noteq> p''" "(a, i') \<in> sL" "i' < n'" "im' i' = Some pp"
              moreover from `im' i' = Some pp` `pp \<noteq> p''` 
                have "i' \<noteq> i" using im'_eq_p'' [of i', symmetric]
                  by simp
              ultimately
              show "\<exists>i'. (i' = n' \<and> a \<in> \<Sigma> \<A> \<or> (a, i') \<in> sL) \<and>
                         pp = ?pm i'"
                apply (rule_tac exI[where x = i'])
                apply (simp add: partition_index_map_def)
              done
            next
              fix i'
              assume pp_eq: "pp = ?pm i'" and in_sL: "(a, i') \<in> sL" 

              from sL_OK[OF in_sL] have i'_le: "i' < n'" .
              with invar_P'' have "i' \<in> dom im'" by simp
              then obtain pp' where im'_i'_eq: "im' i' = Some pp'" by blast 

              show "(\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some pp) \<and> pp \<noteq> p'' \<or>
                    pp = pmin \<and> a \<in> \<Sigma> \<A> \<or>
                    pp = pmax \<and> (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some p'')" 
              proof (cases "i' = i")
                case True note i'_eq = this
                with pp_eq i_le' have "pp = pmax"
                  by (simp add: partition_index_map_def)
                with in_sL i'_eq have "pp = pmax \<and> (\<exists>i'. (a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some p'')"
                  apply simp
                  apply (rule exI [where x = i])
                  apply (simp add: im'_i_eq i_le')
                done
                thus ?thesis by blast
              next
                case False note i'_neq = this
                with im'_i'_eq pp_eq i'_le have pp_eq: "pp = pp'" 
                  by (simp add: partition_index_map_def)

                with i'_neq im'_eq_p'' [of i'] have pp_neq: "pp \<noteq> p''" 
                   by (simp add: im'_i'_eq)
                
                from in_sL i'_le pp_eq have "\<exists>i'. ((a, i') \<in> sL \<and> i' < n' \<and> im' i' = Some pp)"
                  apply (rule_tac exI [where x = i'])
                  apply (simp add: im'_i'_eq)
                done
                with `pp \<noteq> p''` show ?thesis by blast
              qed
            qed
         qed
         from alpha_OK invar_OK show ?thesis by (simp add: Hopcroft_map_state_rel_def)
       qed

       from in_rel' n_le i_le card_pf'_neq n'_not_in im'_eq sL_OK
       show ?thesis 
         apply refine_rcg
         apply (simp_all add: partition_index_map_def im_i_eq Ball_def pw_le_iff 
                              Hopcroft_map_state_rel_def single_valued_def)
       done
    qed
    thus "(let (pt', pct', pf', pcf') =
              ({q \<in> partition_index_map (im', sm', n') i. q \<in> pre},
               card {q \<in> partition_index_map (im', sm', n') i. q \<in> pre},
               {q \<in> partition_index_map (im', sm', n') i. q \<notin> pre},
               card {q \<in> partition_index_map (im', sm', n') i. q \<notin> pre})
        in if pcf' = 0 then RETURN ((im', sm', n'), sL)
           else let (pmin, pmax) = if pcf' < pct' then (pf', pt') else (pt', pf')
                in ASSERT (\<forall>ai\<in>sL. snd ai < partition_free_index (im', sm', n')) \<guillemotright>=
                   (\<lambda>_. let L' = {(a, partition_free_index (im', sm', n')) |a. a \<in> \<Sigma> \<A>} \<union> sL;
                            P' = partition_map_split (im', sm', n') i pmin pmax
                        in RETURN (P', L')))
       \<le> \<Down> {(\<sigma>, \<sigma>').
            (\<sigma>, \<sigma>') \<in> Hopcroft_map_state_rel \<and>
            partition_free_index P \<le> partition_free_index (fst \<sigma>) \<and>
            (\<forall>i\<in>it - {i}. fst (fst \<sigma>) i = fst P i)}
          (let (pt', pct', pf', pcf') =
                 ({q \<in> partition_index_map P i'. q \<in> pre},
                  card {q \<in> partition_index_map P i'. q \<in> pre},
                  {q \<in> partition_index_map P i'. q \<notin> pre},
                  card {q \<in> partition_index_map P i'. q \<notin> pre})
           in if pcf' = 0 then RETURN (P'', L'')
              else let (pmin, pmax) = if pcf' < pct' then (pf', pt') else (pt', pf');
                       P' = P'' - {partition_index_map P i'} \<union> {pt', pf'};
                       L' = {(a, p''). (a, p'') \<in> L'' \<and> p'' \<noteq> partition_index_map P i'} \<union>
                            {(a, pmin) |a. a \<in> \<Sigma> \<A>} \<union>
                            {(a, pmax) |a. (a, partition_index_map P i') \<in> L''}
                   in RETURN (P', L'))" 
      apply (simp split del: if_splits 
                 del: P_eq
                 add: p''_def[symmetric] pt'_def[symmetric] pf'_def[symmetric] p''_intro)
      apply (unfold pminmax)
      apply (cases "card pf' = 0")
      apply (simp_all)
    done
  }
qed

*)

definition Hopcroft_map_f where
"Hopcroft_map_f \<A> = 
 (\<lambda>(P, L). do {
       ASSERT (Hopcroft_abstract_invar \<A> (Hopcroft_map_state_\<alpha> (P, L)));
       ASSERT (L \<noteq> {});
       (a,i) \<leftarrow> SPEC (\<lambda>(a,i). (a,i) \<in> L);
       ASSERT (i \<in> dom (fst P));
       let pre = {q. \<exists>q'. q' \<in> partition_index_map P i \<and> (q, a, q') \<in> \<Delta> \<A>};
       (P', L') \<leftarrow> Hopcroft_map_step \<A> i a pre P L;
       RETURN (P', L')
     })"

lemma (in DFA) Hopcroft_map_f_correct :
assumes PL_OK: "(PL, PL') \<in> Hopcroft_map_state_rel"
shows "Hopcroft_map_f \<A> PL \<le> \<Down>Hopcroft_map_state_rel (Hopcroft_abstract_f \<A> PL')"
proof -
  obtain P L where PL_eq[simp]: "PL = (P, L)" by (rule prod.exhaust)
  obtain P' L' where PL'_eq[simp]: "PL' = (P', L')" by (rule prod.exhaust)

  from PL_OK have PL_\<alpha>: "Hopcroft_map_state_\<alpha> (P, L) = (P', L')" 
              and invar: "Hopcroft_map_state_invar (P, L)"
    by (simp_all add: Hopcroft_map_state_rel_def in_br_conv)

  from PL_\<alpha> have P'_eq: "P' = partition_map_\<alpha> P"
             and L'_eq: "L' = apsnd (partition_index_map P) ` L"
    by (simp_all add: Hopcroft_map_state_\<alpha>_def)

  show ?thesis
    unfolding Hopcroft_map_f_def Hopcroft_abstract_f_def
    apply simp
    apply (refine_rcg)
    apply (simp_all only: PL_\<alpha>)
    apply (simp add: L'_eq)
    prefer 3
    apply clarify apply simp
    proof -
      show "(RES L) \<le> \<Down> (build_rel (apsnd (partition_index_map P)) (\<lambda>x. x \<in> L)) (RES L')"
        apply (simp del: br_def add: pw_le_iff refine_pw_simps in_br_conv)
        apply (simp add: L'_eq subset_iff image_iff Bex_def)
        apply blast
      done
    next
      fix a i a' p'
      assume abstr_invar: "Hopcroft_abstract_invar \<A> (P', L')"
         and in_rel: "((a, i), (a', p')) \<in> build_rel (apsnd (partition_index_map P)) (\<lambda>x. x \<in> L)"

      from in_rel have a'_eq[simp]: "a' = a"  
                   and p'_eq: "p' = partition_index_map P i"  
                   and ai_in_L: "(a, i) \<in> L"
        by (simp_all add: in_br_conv)

      obtain im sm n where P_eq: "P = (im, sm, n)" by (metis prod.exhaust)

      show "i \<in> dom (fst P)"
        using ai_in_L invar
        unfolding Hopcroft_map_state_invar_def
        by (simp add: P_eq Ball_def)
       
      from abstr_invar have is_part_P': "is_partition (\<Q> \<A>) P'" and
                            L'_OK: "\<And>a p. (a, p) \<in> L' \<Longrightarrow> a \<in> \<Sigma> \<A>"
        unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def by auto
      define pre where "pre \<equiv> {q. \<exists>q'. q' \<in> p' \<and> (q, a, q') \<in> \<Delta> \<A>}"

      have "Hopcroft_map_step \<A> i a {q. \<exists>q'. q' \<in> partition_index_map P i \<and> (q, a, q') \<in> \<Delta> \<A>} P L
       \<le> \<Down> Hopcroft_map_state_rel
          (Hopcroft_precompute_step \<A> p' a' {q. \<exists>q'. q' \<in> p' \<and> (q, a', q') \<in> \<Delta> \<A>} P' L')" 
        apply (unfold pre_def[symmetric] p'_eq[symmetric] a'_eq)          
        apply (rule_tac Hopcroft_map_step_correct)
        apply (insert PL_OK, simp)[]
        apply (insert ai_in_L invar, simp add: Hopcroft_map_state_invar_def Ball_def) []
        apply (simp add: p'_eq)
        apply (simp add: is_part_P')
        apply (insert \<Delta>_consistent, auto simp add: pre_def)
      done
      also note Hopcroft_precompute_step_correct
      also note Hopcroft_set_step_correct
      finally show "Hopcroft_map_step \<A> i a
        {q. \<exists>q'. q' \<in> partition_index_map P i \<and> (q, a, q') \<in> \<Delta> \<A>} P L
       \<le> \<Down> Hopcroft_map_state_rel
          (SPEC (\<lambda>(P'', L'').
                    Hopcroft_update_splitters_pred \<A> p' a' P' L' L'' \<and>
                    P'' = Hopcroft_split \<A> p' a' {} P'))" 
        by (simp add: is_part_P' L'_OK is_partition_memb_finite[OF finite_\<Q> is_part_P'])
  qed
qed


definition partition_map_init where
  "partition_map_init \<A> =
   (if (\<Q> \<A> - \<F> \<A> = {}) then
      partition_map_sing (\<F> \<A>) (\<F> \<A>)
    else 
      (Map.empty (0 \<mapsto> (\<F> \<A>)) (1 \<mapsto> (\<Q> \<A> - \<F> \<A>)),
       (\<lambda>q. if (q \<in> \<F> \<A>) then Some 0 else
            if (q \<in> \<Q> \<A>) then Some 1 else None),
       2))"

lemma partition_map_init_correct :
assumes wf_A: "NFA \<A>"
    and f_neq_emp: "\<F> \<A> \<noteq> {}"
shows "partition_map_\<alpha> (partition_map_init \<A>) = Hopcroft_accepting_partition \<A> \<and>
       partition_map_invar (partition_map_init \<A>)"
proof (cases "\<Q> \<A> \<subseteq> \<F> \<A>")
  case True
    with f_neq_emp show ?thesis 
    unfolding partition_map_init_def Hopcroft_accepting_partition_alt_def[OF wf_A]
    by (auto simp add: partition_map_sing_correct)
next
  case False
  with f_neq_emp show ?thesis
    unfolding partition_map_init_def Hopcroft_accepting_partition_alt_def[OF wf_A]
    by auto
qed

lemma partition_map_init___index_0:
  "partition_index_map (partition_map_init \<A>) 0 = \<F> \<A>"
unfolding partition_map_init_def partition_index_map_def partition_map_sing_def
by auto

lemma partition_map_init___index_le:
  "0 < partition_free_index (partition_map_init \<A>)"
unfolding partition_map_init_def partition_index_map_def partition_map_sing_def
by auto

definition Hopcroft_map_init where
  "Hopcroft_map_init \<A> = (partition_map_init \<A>, {(a, 0) | a. a \<in> \<Sigma> \<A>})" 

definition Hopcroft_map where
  "Hopcroft_map \<A> = 
   (if (\<Q> \<A> = {}) then RETURN (partition_map_empty) else (
    if (\<F> \<A> = {}) then RETURN (partition_map_sing (\<Q> \<A>) (\<Q> \<A>)) else (
       do {
         (P, _) \<leftarrow> WHILEIT Hopcroft_map_state_invar (\<lambda>PL. (snd PL \<noteq> {}))
                          (Hopcroft_map_f \<A>) (Hopcroft_map_init \<A>);
         RETURN P
       })))" 

lemma (in DFA) Hopcroft_map_correct :                                                     
  "Hopcroft_map \<A> \<le> \<Down>(build_rel partition_map_\<alpha> partition_map_invar) (Hopcroft_abstract \<A>)"
unfolding Hopcroft_map_def Hopcroft_abstract_def
apply refine_rcg
apply (simp_all add: partition_map_empty_correct partition_map_sing_correct in_br_conv)
proof -
  assume "\<F> \<A> \<noteq> {}"
  thus "(Hopcroft_map_init \<A>, Hopcroft_abstract_init \<A>) \<in> Hopcroft_map_state_rel"
    unfolding Hopcroft_map_state_rel_def Hopcroft_abstract_init_def Hopcroft_map_init_def
    apply (simp add: in_br_conv Hopcroft_map_state_\<alpha>_def Hopcroft_map_state_invar_def
                     partition_map_init_correct[OF NFA_axioms] partition_map_init___index_le)
    apply (rule set_eqI)
    apply (simp add: image_iff partition_map_init___index_0)
    apply (auto)
  done
next
  fix PL and PL' :: "('q set set) \<times> ('a \<times> ('q set)) set"
  assume "(PL, PL') \<in> Hopcroft_map_state_rel"
  thus "(snd PL \<noteq> {}) = Hopcroft_abstract_b PL'"
     unfolding Hopcroft_abstract_b_def Hopcroft_map_state_rel_def
     by (cases PL, simp add: Hopcroft_map_state_\<alpha>_def in_br_conv)
next
  fix PL and PL' :: "('q set set) \<times> ('a \<times> ('q set)) set"
  assume "(PL, PL') \<in> Hopcroft_map_state_rel"
  thus "Hopcroft_map_f \<A> PL \<le> \<Down> Hopcroft_map_state_rel (Hopcroft_abstract_f \<A> PL')"
    by (rule Hopcroft_map_f_correct)
next
  fix P L P' and L' :: "('a \<times> ('q set)) set"
  assume "((P, L), (P', L')) \<in> Hopcroft_map_state_rel"
  thus "P' = partition_map_\<alpha> P \<and> partition_map_invar P"
    by (simp add: Hopcroft_map_state_rel_def Hopcroft_map_state_\<alpha>_def
                  Hopcroft_map_state_invar_def in_br_conv)
next
  fix PL :: "(((nat \<Rightarrow> ('q set) option) \<times> ('q \<Rightarrow> nat option) \<times> nat) \<times> ('a \<times> nat) set)"
  fix PL' :: "(('q set) set) \<times> (('a \<times> ('q set)) set)"
  assume "(PL, PL') \<in> Hopcroft_map_state_rel"
  thus "Hopcroft_map_state_invar PL"
    unfolding Hopcroft_map_state_rel_def by (simp add: in_br_conv)
qed

lemma (in DFA) Hopcroft_map_correct_full :
"Hopcroft_map \<A> \<le> SPEC (\<lambda>P. 
    (partition_map_\<alpha> P = Myhill_Nerode_partition \<A>) \<and>
    partition_map_invar P)"
proof -
  note Hopcroft_map_correct 
  also note Hopcroft_abstract_correct 
  finally show ?thesis by (simp add: pw_le_iff refine_pw_simps in_br_conv)
qed

text \<open> Using this encoding of the partition, it's even easier to construct a rename function \<close>
lemma partition_map_to_rename_fun_OK :
assumes invar: "partition_map_invar P"
   and part_map_OK: "partition_map_\<alpha> P = Myhill_Nerode_partition \<A>"
shows "dom (fst (snd P)) = \<Q> \<A>"
      "NFA_is_strong_equivalence_rename_fun \<A> (\<lambda>q. states_enumerate (the ((fst (snd P)) q)))"
proof -
  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  from invar have dom_i: "\<And>i Q. im i = Some Q \<Longrightarrow> i < n" by (auto simp add: dom_def)
  from invar have sm_eq: "\<And>q i. (sm q = Some i) = (\<exists>p. im i = Some p \<and> q \<in> p)" by simp

  from part_map_OK dom_i have 
    is_part: "is_partition (\<Q> \<A>) (partition_map_\<alpha> P)" and
    strong: "\<And>Q i. im i = Some Q \<Longrightarrow> is_strong_language_equiv_set \<A> Q"
    apply (simp_all add: is_strong_language_equiv_partition_fun_alt_def dom_def)
    apply metis
  done

  from is_part have Q_eq: "\<Q> \<A> = \<Union>{Q. \<exists>i<n. im i = Some Q}"
    unfolding is_partition_def by simp

  from invar
  show "dom (fst (snd P)) = \<Q> \<A>"
    by (auto simp add: dom_def Q_eq)

  show "NFA_is_strong_equivalence_rename_fun \<A> (\<lambda>q. states_enumerate (the ((fst (snd P)) q)))"
    unfolding NFA_is_strong_equivalence_rename_fun_def 
  proof (intro ballI)
    fix q q'
    assume "q \<in> \<Q> \<A>" "q' \<in> \<Q> \<A>"

    with Q_eq obtain i i' Q Q' where 
      iQ_props: "i < n" "i' < n" "im i = Some Q" "im i' = Some Q'" "q \<in> Q" "q' \<in> Q'"
      by auto
    with invar have sm_eq: "sm q = Some i" "sm q' = Some i'" by auto

    from invar iQ_props sm_eq
    have im_ii': "im i = im i' \<Longrightarrow> i = i'" 
      apply simp
      apply (subgoal_tac "sm q' = Some i")
      apply (simp add: sm_eq)
      apply auto
    done

    from iQ_props have "Q \<in> partition_map_\<alpha> P" "Q' \<in> partition_map_\<alpha> P" by auto
    with part_map_OK have 
       "Q \<in> Myhill_Nerode_partition \<A>"
       "Q' \<in> Myhill_Nerode_partition \<A>"
      by simp_all
    then obtain q1 q1' where 
       "Q = {q' \<in> \<Q> \<A>. \<L>_in_state \<A> q' = \<L>_in_state \<A> q1}" "q1 \<in> \<Q> \<A>" 
       "Q' = {q' \<in> \<Q> \<A>. \<L>_in_state \<A> q' = \<L>_in_state \<A> q1'}" "q1' \<in> \<Q> \<A>" 
    by (auto simp add: Myhill_Nerode_partition_alt_def)
    with iQ_props im_ii' have "(i = i') = (\<L>_in_state \<A> q = \<L>_in_state \<A> q')"
      apply (simp add: Myhill_Nerode_partition_alt_def)
      apply (rule iffI)
      apply (auto)
    done
    thus "((states_enumerate (the (fst (snd P) q)) = states_enumerate (the (fst (snd P) q')))) =
           (\<L>_in_state \<A> q = \<L>_in_state \<A> q')"
      by (simp add: sm_eq states_enumerate_eq)
  qed
qed

subsection \<open> Data Refinement 2 \<close>

lemma card_nat_segment : "card {i. l \<le> i \<and> i \<le> u} = Suc u - l"
    (is "card ?s = Suc u - l")
proof (cases "l \<le> u")
  case False thus ?thesis by auto
next
  case True note l_le_u = this
  have s_eq: "?s = {i. i \<le> u} - {i. i < l}" (is "_ = ?s1 - ?s2") by auto
  have fin_s2 : "finite ?s2" by (rule finite_Collect_less_nat)
  have s2_subset: "?s2 \<subseteq> ?s1" using l_le_u by auto

  from card_Diff_subset [OF fin_s2 s2_subset] s_eq
  show ?thesis by simp
qed


text\<open> Classes are represented as sets so far. The next refinement step introduces a bijection
between states and natural numbers. By maintaining this bijection, it is possible to represent
classes as intervals of natural numbers. The bijection is represented by two finite maps:
$\textit{pm}$ maps states to natural numbers; $\textit{pim}$ is the inverse map.\<close>

type_synonym 'q class_map = "('q \<Rightarrow> nat option) * (nat \<Rightarrow> 'q option)"
type_synonym 'q partition_map2 = "('q, nat \<times> nat) partition_map_gen"

definition class_map_\<alpha> :: "'q class_map \<Rightarrow> (nat \<times> nat) \<Rightarrow> 'q set" where
  "class_map_\<alpha> = (\<lambda>(pm, pim) (l, u). {the (pim i) | i. l \<le> i \<and> i \<le> u})"

lemma class_map_\<alpha>_alt_def :
  "class_map_\<alpha> (pm, pim) (l, u) = (\<lambda>i. the (pim i)) ` {i . l \<le> i \<and> i \<le> u}"
unfolding class_map_\<alpha>_def by auto

definition class_map_invar :: "'q set \<Rightarrow> 'q class_map \<Rightarrow> bool" where
  "class_map_invar Q = (\<lambda>(pm, pim).
   dom pm = Q \<and> dom pim = {i. i < card Q} \<and>
   (\<forall>q i. pm q = Some i \<longleftrightarrow> pim i = Some q))"

lemma class_map_invar___implies_finite_Q :
assumes invar: "class_map_invar Q (pm, pim)"
shows "finite Q"
proof (rule ccontr)
  assume not_fin_Q: "~ (finite Q)"

  hence "card Q = 0" by simp
  with invar have "dom pim = {}" unfolding class_map_invar_def by simp
  hence "\<And>i. pim i = None" by blast
  with invar have "\<And>q. pm q = None" unfolding class_map_invar_def by auto
  hence "dom pm = {}" by auto
  with invar have "Q = {}" unfolding class_map_invar_def by auto
  hence "finite Q" by simp

  with not_fin_Q show False ..
qed

lemma class_map_invar___pm_inj :
assumes invar: "class_map_invar Q (pm, pim)"
assumes pm_q1: "pm q1 = Some i"
assumes pm_q2: "pm q2 = Some i"
shows "q1 = q2"
proof -
  from invar pm_q1 pm_q2 have "pim i = Some q1" "pim i = Some q2" unfolding class_map_invar_def by auto
  thus "q1 = q2" by simp
qed

lemma class_map_invar___pim_inj :
assumes invar: "class_map_invar Q (pm, pim)"
assumes pim_i1: "pim i1 = Some q"
assumes pim_i2: "pim i2 = Some q"
shows "i1 = i2"
proof -
  from invar pim_i1 pim_i2 have "pm q = Some i1" "pm q = Some i2" unfolding class_map_invar_def by auto
  thus "i1 = i2" by simp
qed


definition partition_map2_\<alpha>_im :: "'q class_map \<Rightarrow> _ \<Rightarrow> _" where
  "partition_map2_\<alpha>_im cm im = (\<lambda>i. map_option (class_map_\<alpha> cm) (im i))"

definition partition_map2_\<alpha> :: "'q class_map \<Rightarrow> 'q partition_map2 \<Rightarrow> 'q partition_map" where
  "partition_map2_\<alpha> cm = (\<lambda>(im, sm, n). (partition_map2_\<alpha>_im cm im, sm, n))"

definition partition_map2_invar :: "nat \<Rightarrow> 'q partition_map2 \<Rightarrow> bool" where
  "partition_map2_invar m = (\<lambda>(im, sm, n).
   (\<forall>i l u. im i = Some (l, u) \<longrightarrow> (l \<le> u \<and> u < m)))"

definition Hopcroft_map2_state_\<alpha> where
"Hopcroft_map2_state_\<alpha> cm \<sigma> = (partition_map2_\<alpha> cm (fst \<sigma>), (snd \<sigma>))"

definition Hopcroft_map2_state_invar where
"Hopcroft_map2_state_invar Q cm \<sigma> \<longleftrightarrow>
   partition_map2_invar (card Q) (fst \<sigma>) \<and>
   class_map_invar Q cm"

definition Hopcroft_map2_state_rel where
  "Hopcroft_map2_state_rel cm Q = build_rel (Hopcroft_map2_state_\<alpha> cm) (Hopcroft_map2_state_invar Q cm)"

definition Hopcroft_map2_state_rel_full where
  "Hopcroft_map2_state_rel_full Q = build_rel (\<lambda>(PL, cm). Hopcroft_map2_state_\<alpha> cm PL) 
                                            (\<lambda>(PL, cm). Hopcroft_map2_state_invar Q cm PL)"

lemma Hopcroft_map2_state_rel_sv[refine] :
"single_valued (Hopcroft_map2_state_rel Q cm)"
unfolding Hopcroft_map2_state_rel_def
  by (rule br_sv)

definition partition_index_map2_full :: "'q class_map \<Rightarrow> 'q partition_map2 \<Rightarrow> (nat \<Rightarrow> 'q set)" where
  "partition_index_map2_full cm P i = class_map_\<alpha> cm (partition_index_map P i)"

definition Hopcroft_map2_step_invar where
"Hopcroft_map2_step_invar \<A> p a P L cm S \<sigma> \<longleftrightarrow> 
 Hopcroft_map_step_invar \<A> p a (partition_map2_\<alpha> cm P) L (fst ` S) (Hopcroft_map2_state_\<alpha> cm \<sigma>)"

fun partition_map2_split :: "'q class_map \<Rightarrow> 'q partition_map2 \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) => (nat \<times> nat) \<Rightarrow> 'q partition_map2" where
  "partition_map2_split cm (im, sm, n) i pmin pmax =
   (im (i \<mapsto> pmax) (n \<mapsto> pmin), 
    \<lambda>q. if (q \<in> (class_map_\<alpha> cm pmin)) then Some n else sm q,
    Suc n)"

definition Hopcroft_map2_step___iM_props where
   "Hopcroft_map2_step___iM_props \<A> cm pre P iM cm' \<longleftrightarrow>
    class_map_invar (\<Q> \<A>) cm' \<and>
    partition_map2_\<alpha> cm' P = partition_map2_\<alpha> cm P \<and> 
    (\<forall>i u s l. (iM i = Some s \<and> ((fst P) i = Some (l, u))) \<longrightarrow> (l < s \<and> s \<le> Suc u)) \<and>
    (\<forall>i u s l n q. (iM i = Some s \<and> ((fst P) i = Some (l, u)) \<and>
                   l \<le> n \<and> n \<le> u \<and> (snd cm') n = Some q) \<longrightarrow>
                       (q \<in> pre \<longleftrightarrow> n < s))"

lemma Hopcroft_map2_step___iM_propsI [intro!] :
   "\<lbrakk>class_map_invar (\<Q> \<A>) cm';
     partition_map2_\<alpha> cm' P = partition_map2_\<alpha> cm P; 
     \<And>i u s l. \<lbrakk>iM i = Some s; ((fst P) i = Some (l, u))\<rbrakk> \<Longrightarrow> (l < s \<and> s \<le> Suc u);
     \<And>i u s l n q. \<lbrakk>iM i = Some s; ((fst P) i = Some (l, u));
                   l \<le> n; n \<le> u; l < s; s \<le> Suc u; (snd cm') n = Some q\<rbrakk> \<Longrightarrow>
                       (q \<in> pre \<longleftrightarrow> n < s)\<rbrakk> \<Longrightarrow>
    Hopcroft_map2_step___iM_props \<A> cm pre P iM cm'"
unfolding Hopcroft_map2_step___iM_props_def by blast

definition Hopcroft_map2_step where
"Hopcroft_map2_step \<A> p a pre (P::'q partition_map2) L cm =
 (do { ASSERT (pre \<subseteq> dom (fst (snd P)) \<and> dom (fst (snd P)) \<subseteq> \<Q> \<A>); 
       (iM, cm') \<leftarrow> SPEC (\<lambda>(iM, cm'). 
          Hopcroft_map2_step___iM_props \<A> cm pre P iM cm' \<and>
          (dom iM \<subseteq> (partition_state_map P) ` pre) \<and>
          (\<forall>i \<in> (partition_state_map P) ` pre. 
                 split_language_equiv_partition_pred \<A> (partition_index_map2_full cm' P i) a 
                   (partition_index_map2_full cm' P p) \<longrightarrow> i \<in> dom iM));
       (P', L') \<leftarrow> FOREACHi (Hopcroft_map2_step_invar \<A> p a P L cm') {(p', s) . iM p' = Some s}
         (\<lambda>((p'::nat), (s::nat)) (P'::'q partition_map2, L'). do {
             ASSERT (p' \<in> dom (fst P'));
             let (pt', pct', pf', pcf') = 
                let (l, u) = partition_index_map P' p' in
                ((l, s - 1), (s - l), (s, u), Suc u - s) in
             if (pcf' = 0) then (RETURN (P', L')) else
             do {
               let (pmin, pmax) = (if (pcf' < pct') then (pf', pt') else (pt', pf'));
               ASSERT (\<forall>ai \<in> L'. snd ai < partition_free_index P');
               let L' = {(a, partition_free_index P') | a. a \<in> \<Sigma> \<A>} \<union> L';
               let P' = partition_map2_split cm' P' p' pmin pmax;
               RETURN (P', L')
             }             
          }) (P, L - {(a, p)});
       RETURN ((P', L'), cm')
     })"


lemma Hopcroft_map2_step_correct :
fixes P :: "'q partition_map2"
  and L :: "('a \<times> nat) set"
  and \<A> :: "('q, 'a, 'X) NFA_rec_scheme"
assumes PL_OK: "((P,L), (P', L)) \<in> Hopcroft_map2_state_rel cm (\<Q> \<A>)"
    and p_le: "p < partition_free_index P"
    and invar_P': "partition_map_invar P'"
    and pre'_OK: "pre' = pre"
    and L'_OK: "L' = L"
shows "Hopcroft_map2_step \<A> p a pre P L cm \<le> \<Down> {(((P, L), cm), (P', L')).
      ((P, L), (P', L')) \<in> Hopcroft_map2_state_rel cm (\<Q> \<A>)} 
      (Hopcroft_map_step \<A> p a pre' P' L')"
unfolding Hopcroft_map2_step_def Hopcroft_map_step_def pre'_OK L'_OK
using [[goals_limit = 14]]
apply refine_rcg
  apply (erule conjE)
defer
  apply (erule conjE)
defer
  apply (rule RELATESI_refspec [where R = "(br (\<lambda>(iM, _). dom iM) (\<lambda>(iM, cm'). Hopcroft_map2_step___iM_props \<A> cm pre P iM cm'))"])
  apply (simp add: RELATES_def)
  apply (intro RES_refine_sv br_sv)
  apply (simp, clarify)+
  apply (rename_tac iM pm pim)
  apply (simp add: Ball_def in_br_conv)
  apply (intro conjI allI impI)
defer
defer
  apply (subgoal_tac "inj_on fst {(p', s). x1 p' = Some s}")
  apply assumption
  apply (simp add: inj_on_def)
\<comment>\<open>goal solved\<close>
  apply (auto simp add: image_iff in_br_conv) []
\<comment>\<open>goal solved\<close>
  apply (subgoal_tac "((P, L - {(a, p)}), P', L - {(a, p)}) \<in> Hopcroft_map2_state_rel (snd x) (\<Q> \<A>)")
  apply assumption
  apply (insert PL_OK) []
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_invar_def
                   Hopcroft_map2_state_\<alpha>_def Hopcroft_map2_step___iM_props_def
                   partition_map2_invar_def in_br_conv)
\<comment>\<open>goal solved\<close>
  apply (simp add: in_br_conv, clarify)+
  apply (insert PL_OK) []
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def
                   Hopcroft_map2_step_invar_def Hopcroft_map2_step___iM_props_def in_br_conv)
\<comment>\<open>goal solved\<close>
  apply (simp add: in_br_conv)
  apply (auto simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def
                        partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def in_br_conv)[]
\<comment>\<open>goal solved\<close>
  prefer 2
  apply (simp split: prod.splits add: Let_def in_br_conv, clarify)+
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def 
                   Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def partition_index_map_def in_br_conv)
  apply clarify
  apply (simp add: in_br_conv)
  apply (rename_tac iM pm pim it im'' sm' n' L' l s u i s' pp)
defer
  apply (simp add: in_br_conv)
\<comment>\<open>goal solved\<close>
  prefer 3
  apply (simp add: in_br_conv)

  apply (simp split: prod.splits add: Let_def, clarify)+
  apply (simp add: partition_index_map_def Hopcroft_map2_state_rel_def
                   Hopcroft_map2_state_\<alpha>_def partition_map2_\<alpha>_def in_br_conv)
  apply auto[]
\<comment>\<open>goal solved\<close>
  apply (simp split: prod.splits add: Let_def in_br_conv, clarify)+
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def 
                   Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def partition_index_map_def in_br_conv
              cong: if_cong)
  apply clarify
  apply (simp)
  apply (rename_tac iM pm pim it im'' sm' n' L' l s u pmin pmax pmin_l pmin_u pmax_l pmax_u i s' pp)
  apply (intro conjI)
defer
defer
defer
(*  apply (simp add: Hopcroft_map2_state_rel_def single_valued_def Hopcroft_map2_state_\<alpha>_def 
                   Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def partition_index_map_def in_br_conv
              split: prod.splits)
        apply auto[]
  apply (metis fst_conv snd_conv)
\<comment>\<open>goal solved\<close>
  apply simp
\<comment>\<open>goal solved\<close> *)
using [[goals_limit = 10]]
proof -
  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)
  define im' where "im' \<equiv> partition_map2_\<alpha>_im cm im"

  have dom_im'_eq: "dom im' = dom im" unfolding im'_def dom_def partition_map2_\<alpha>_im_def by simp 

  from PL_OK have P'_eq[simp]: "P' = (im', sm, n)" and
                  im_props: "\<And>i l u. im i = Some (l, u) \<Longrightarrow> l \<le> u \<and> u < card (\<Q> \<A>)" and
                  invar_cm: "class_map_invar (\<Q> \<A>) cm" 
    by (simp_all add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def im'_def
                      Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def partition_map2_invar_def in_br_conv)

  assume "pre \<subseteq> dom (fst (snd P'))" "dom (fst (snd P')) \<subseteq> \<Q> \<A>"
  hence pre_subset: "pre \<subseteq> dom sm" "dom sm \<subseteq> \<Q> \<A>" by simp_all
  thus "pre \<subseteq> dom (fst (snd P))" "dom (fst (snd P)) \<subseteq> \<Q> \<A>"  by simp_all

  fix iM pm pim
  assume iM_props : "Hopcroft_map2_step___iM_props \<A> cm pre P iM (pm, pim)"

  from iM_props have invar_pm_pim: "class_map_invar (\<Q> \<A>) (pm, pim)"
                 and map2_\<alpha>_pm_pim_P: "partition_map2_\<alpha> (pm, pim) P = partition_map2_\<alpha> cm P"
                 and pim_pre_prop: "\<And>i u s l n q. \<lbrakk>iM i = Some s; im i = Some (l, u); 
                                                   l \<le> n; n \<le> u; pim n = Some q\<rbrakk> \<Longrightarrow>
                                                   (q \<in> pre) = (n < s)"
                 and iM_prop: "\<And>i u s l. \<lbrakk>iM i = Some s; im i = Some (l, u)\<rbrakk> \<Longrightarrow> (l < s) \<and> (s \<le> Suc u)"
    unfolding Hopcroft_map2_step___iM_props_def by (simp_all add: in_br_conv)
  
  from map2_\<alpha>_pm_pim_P have class_map_pm_pim_eq: "\<And>lu i. im i = Some lu \<Longrightarrow>
    class_map_\<alpha> cm lu = class_map_\<alpha> (pm, pim) lu" unfolding partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def
    apply (auto simp add: fun_eq_iff split: option.splits)
    apply (metis option.inject option.simps)+
    done

  { assume dom_subset: "dom iM \<subseteq> partition_state_map P ` pre"

    from dom_subset
    show "dom iM \<subseteq> partition_state_map P' ` pre"
      by (simp add: partition_state_map_def[abs_def])

    fix q 
    assume q_in_pre: "q \<in> pre"
       and equiv_pred_P': "split_language_equiv_partition_pred \<A>
        (partition_index_map P' (partition_state_map P' q)) a
        (partition_index_map P' p)"

    from q_in_pre pre_subset have "q \<in> dom sm" by blast
    then obtain qi where sm_q_eq[simp]: "sm q = Some qi" by blast

    from invar_P' have "qi \<in> dom im'" unfolding dom_def by simp (metis sm_q_eq)
    hence "qi \<in> dom im" by (simp add: dom_im'_eq)
    then obtain q_u q_l where im_q_eq[simp]: "im qi = Some (q_l, q_u)" by auto

    from p_le invar_P' have "p \<in> dom im'" by simp
    hence "p \<in> dom im" by (simp add: dom_im'_eq)
    then obtain p_u p_l where im_p_eq[simp]: "im p = Some (p_l, p_u)" by auto

    assume "\<forall>q. q \<in> pre \<longrightarrow>
           split_language_equiv_partition_pred \<A>
            (partition_index_map2_full (pm, pim) P (partition_state_map P q)) a
            (partition_index_map2_full (pm, pim) P p) \<longrightarrow>
           partition_state_map P q \<in> dom iM"
    with q_in_pre have
      "split_language_equiv_partition_pred \<A>
         (partition_index_map2_full (pm, pim) P (partition_state_map P q)) a
         (partition_index_map2_full (pm, pim) P p) \<Longrightarrow>
       partition_state_map P q \<in> dom iM" by simp
    with equiv_pred_P' class_map_pm_pim_eq[OF im_q_eq] 
         class_map_pm_pim_eq[OF im_p_eq] 
    have "partition_state_map P q \<in> dom iM"
      by (simp add: partition_index_map2_full_def partition_index_map_def partition_state_map_def
                       im'_def partition_map2_\<alpha>_im_def)

    thus "partition_state_map P' q \<in> dom iM"
      by (simp add: partition_state_map_def)
  }


  fix it i s im'' pp l u sm' n' L'
  assume it_subset: "it \<subseteq> {(p', s). iM p' = Some s}"
  assume is_in: "(i, s) \<in> it"
  assume "partition_map2_\<alpha>_im (pm, pim) im'' i = Some pp"
  assume im''_i_eq[simp]: "im'' i = Some (l, u)"
  assume invar_pm_pim: "class_map_invar (\<Q> \<A>) (pm, pim)"
  assume step_invar: "Hopcroft_map_step_invar \<A> p a P' L (fst ` it) ((partition_map2_\<alpha>_im (pm, pim) im'', sm', n'), L')"
  assume step_invar2: "Hopcroft_map2_step_invar \<A> p a P L (pm, pim) it ((im'', sm', n'), L')"
  assume invar2_cm'_P'': "partition_map2_invar (card (\<Q> \<A>)) (im'', sm', n')"
  assume "snd (snd P') \<le> n'" hence n_le_n': "n \<le> n'" by simp

  from invar_pm_pim have dom_pim: "dom pim = {i. i < card (\<Q> \<A>)}" 
    unfolding class_map_invar_def by simp

  from `partition_map2_\<alpha>_im (pm, pim) im'' i = Some pp` 
  have pp_eq: "class_map_\<alpha> (pm, pim) (l, u) = pp"
    by (simp add: partition_map2_\<alpha>_im_def)

  from invar2_cm'_P'' have lu_OK: "l \<le> u \<and> u < card (\<Q> \<A>)"
    unfolding partition_map2_invar_def by simp (metis im''_i_eq)

  assume "fst P' i = Some pp"
  hence im'_i_eq[simp]: "im' i = Some pp" by simp
  
  hence "i \<in> dom im'" by blast
  with invar_P' n_le_n' have i_le_n': "i < n'" by simp

  have im_i_eq[simp]: "im i = Some (l, u)"
  proof -
    from im'_i_eq
    obtain l' u' where 
      im_i_eq: "im i = Some (l', u')" and
      pp_eq2: "class_map_\<alpha> cm (l', u') = pp"  
      unfolding im'_def partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def
    by auto
    from im_props[OF im_i_eq] have lu'_OK: "l' \<le> u' \<and> u' < card (\<Q> \<A>)" .

    from pp_eq2 class_map_pm_pim_eq[OF im_i_eq]
    have pp_eq3: "class_map_\<alpha> (pm, pim) (l', u') = pp" by simp

    from dom_pim class_map_invar___pim_inj[OF invar_pm_pim]
    have pim_inj_on': "inj_on (\<lambda>i. the (pim i)) {i . i < card (\<Q> \<A>)}"
      unfolding inj_on_def dom_def set_eq_iff 
      by auto (metis option.sel)
    have pim_inj_on: "inj_on (\<lambda>i. the (pim i)) ({i . l \<le> i \<and> i \<le> u} \<union> {i . l' \<le> i \<and> i \<le> u'})" 
      using lu_OK lu'_OK
      apply (rule_tac subset_inj_on[OF pim_inj_on'])
      apply (simp add: subset_iff)
    done

    have "class_map_\<alpha> (pm, pim) (l', u') = class_map_\<alpha> (pm, pim) (l, u)" 
      using pp_eq pp_eq3 by simp
    hence "{i |i. l \<le> i \<and> i \<le> u} = {i |i. l' \<le> i \<and> i \<le> u'}"
      unfolding class_map_\<alpha>_alt_def 
      using inj_on_Un_image_eq_iff[OF pim_inj_on]
      by simp
    hence "l = l' \<and> u = u'" 
      apply (simp add: set_eq_iff) 
      apply (metis im_i_eq im_props le_trans linorder_linear order_antisym)
    done

    thus ?thesis by (simp add: im_i_eq)   
  qed

  from is_in it_subset have iM_i_eq[simp]: "iM i = Some s" by (simp add: subset_iff)
  from iM_prop [of i s l u] have s_OK: "l < s \<and> s \<le> Suc u" by simp

  { fix l' u'
    assume u'_le: "u' < card (\<Q> \<A>)" 

    with invar_pm_pim have subset_dom: "{i |i. l' \<le> i \<and> i \<le> u'} \<subseteq> dom pim" 
      by (simp add: class_map_invar_def subset_iff)

    have "card (class_map_\<alpha> (pm, pim) (l', u')) = card {i |i. l' \<le> i \<and> i \<le> u'}"
      apply (simp add: class_map_\<alpha>_alt_def)
      apply (intro card_image inj_onI class_map_invar___pim_inj [OF invar_pm_pim])
      apply (insert subset_dom)
      apply (auto simp add: subset_iff dom_def)
    done
    hence "card (class_map_\<alpha> (pm, pim) (l', u')) = Suc u' - l'"
      using card_nat_segment[of l' u'] by simp
  } note card_class_map = this
  
  have pim_pre_prop': "\<And>n. l \<le> n \<Longrightarrow> n \<le> u \<Longrightarrow> (the (pim n) \<in> pre) = (n < s)"  
  proof -
    fix n
    assume n_props: "l \<le> n" "n \<le> u"

    with dom_pim lu_OK have "n \<in> dom pim" by auto
    then obtain q where pim_n_eq: "pim n = Some q" by blast

    from pim_pre_prop[of i s l u n q] pim_n_eq n_props 
    show "(the (pim n) \<in> pre) = (n < s)" by simp
  qed

  from s_OK obtain s_pre where s_pre_intro: "s = Suc s_pre" 
    by (cases s) auto

  have pp_in_pre_eq: "{q \<in> pp. q \<in> pre} = class_map_\<alpha> (pm, pim) (l, s - Suc 0)" 
  proof -
    { fix x i
      from pim_pre_prop'[of i] s_OK
      have "(x = the (pim i) \<and> l \<le> i \<and> i \<le> u \<and> x \<in> pre) =
            (x = the (pim i) \<and> l \<le> i \<and> i < s)"
         by auto
    }
    with s_OK show ?thesis
      unfolding pp_eq[symmetric]
      apply (simp del: ex_simps add: s_pre_intro set_eq_iff class_map_\<alpha>_def ex_simps[symmetric])
      apply auto
    done
  qed

  have pp_nin_pre_eq: "{q \<in> pp. q \<notin> pre} = class_map_\<alpha> (pm, pim) (s, u)" 
  proof -
    { fix x i
      from pim_pre_prop'[of i] s_OK 
      have "(x = the (pim i) \<and> l \<le> i \<and> i \<le> u \<and> x \<notin> pre) =
            (x = the (pim i) \<and> s \<le> i \<and> i \<le> u)"
         by auto
    }
    thus ?thesis
      unfolding pp_eq[symmetric]
      by (simp del: ex_simps add: set_eq_iff class_map_\<alpha>_def ex_simps[symmetric])
  qed

  show "(Suc u \<le> s) = (card {q \<in> pp. q \<notin> pre} = 0)" 
    using card_class_map [of u s] s_OK lu_OK
    unfolding pp_nin_pre_eq by simp

  fix pmin pmax pmin_l pmin_u pmax_l pmax_u
  assume pminmax_eq: "(if card {q \<in> pp. q \<notin> pre} < card {q \<in> pp. q \<in> pre}
            then ({q \<in> pp. q \<notin> pre}, {q \<in> pp. q \<in> pre})
            else ({q \<in> pp. q \<in> pre}, {q \<in> pp. q \<notin> pre})) =
           (pmin, pmax)"
  assume pminmax_lu_eq:
    "(if Suc u - s < s - l then ((s, u), l, s - Suc 0) else ((l, s - Suc 0), s, u)) =
     ((pmin_l, pmin_u), (pmax_l, pmax_u))"
  assume "s < Suc u" hence s_le_u: "s \<le> u" by simp

  from card_class_map [of u s] card_class_map [of "s - Suc 0" l] s_OK lu_OK
  have card_eval: "card (class_map_\<alpha> (pm, pim) (s, u)) = Suc u - s"
                  "card (class_map_\<alpha> (pm, pim) (l, s - Suc 0)) = s - l" by auto

  from pminmax_eq have "pmin \<union> pmax = pp" by (auto split: if_splits)
  hence class_lu_minmax: "class_map_\<alpha> (pm, pim) (l, u) = pmin \<union> pmax" unfolding pp_eq by simp

  from pminmax_eq pminmax_lu_eq
  have pmin_eq: "class_map_\<alpha> (pm, pim) (pmin_l, pmin_u) = pmin" and
       pmax_eq: "class_map_\<alpha> (pm, pim) (pmax_l, pmax_u) = pmax"
      unfolding pp_in_pre_eq pp_nin_pre_eq card_eval
      by (auto split: if_splits)

  show "partition_map2_\<alpha>_im (pm, pim) im''(i \<mapsto> pmax, n' \<mapsto> pmin) =
        partition_map2_\<alpha>_im (pm, pim) (im''(i \<mapsto> (pmax_l, pmax_u), n' \<mapsto> (pmin_l, pmin_u)))"
    by (simp add: partition_map2_\<alpha>_im_def pmin_eq fun_eq_iff pmax_eq)

  show "(\<lambda>q. if q \<in> pmin then Some n' else sm' q) =
        (\<lambda>q. if q \<in> class_map_\<alpha> (pm, pim) (pmin_l, pmin_u) then Some n' else sm' q)"
    unfolding pmin_eq ..
 
  from pminmax_lu_eq[symmetric] lu_OK s_OK s_le_u have 
    pmin_lu_OK: "pmin_l \<le> pmin_u \<and> pmin_u < card (\<Q> \<A>)" and
    pmax_lu_OK: "pmax_l \<le> pmax_u \<and> pmax_u < card (\<Q> \<A>)"
    by (simp_all split: if_splits add: s_pre_intro)

  from invar2_cm'_P'' i_le_n'
  show "partition_map2_invar (card (\<Q> \<A>)) 
            (im''(i \<mapsto> (pmax_l, pmax_u), n' \<mapsto> (pmin_l, pmin_u)),
             \<lambda>q. if q \<in> class_map_\<alpha> (pm, pim) (pmin_l, pmin_u) then Some n'
                 else sm' q, Suc n')" 
    unfolding partition_map2_invar_def 
    by (simp add: pmin_lu_OK pmax_lu_OK)
qed

(* -- OLD PROOF --
unfolding Hopcroft_map2_step_def Hopcroft_map_step_def pre'_OK L'_OK
using [[goals_limit = 1]]
apply refine_rcg
  apply (erule conjE)
defer
  apply (erule conjE)
defer
  apply (rule RELATESI_refspec [where R = "(br (\<lambda>(iM, _). dom iM) (\<lambda>(iM, cm'). Hopcroft_map2_step___iM_props \<A> cm pre P iM cm'))"])
  apply (simp add: RELATES_def)
  apply (intro RES_refine_sv br_sv)
  apply (simp, clarify)+
  apply (rename_tac iM pm pim)
  apply (simp add: Ball_def)
  apply (intro conjI allI impI)
defer
defer
  apply (subgoal_tac "inj_on fst {(p', s). aa p' = Some s}")
  apply assumption
  apply (simp add: inj_on_def)
\<comment>\<open>goal solved\<close>
  apply (auto simp add: image_iff) []
\<comment>\<open>goal solved\<close>
  apply (subgoal_tac "((P, L - {(a, p)}), P', L - {(a, p)}) \<in> Hopcroft_map2_state_rel (snd x) (\<Q> \<A>)")
  apply assumption
  apply (insert PL_OK) []
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_invar_def
                   Hopcroft_map2_state_\<alpha>_def Hopcroft_map2_step___iM_props_def
                   partition_map2_invar_def)
\<comment>\<open>goal solved\<close>
  apply (simp, clarify)+
  apply (insert PL_OK) []
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def
                   Hopcroft_map2_step_invar_def Hopcroft_map2_step___iM_props_def)
\<comment>\<open>goal solved\<close>
  apply (auto simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def
                        partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def)[]
\<comment>\<open>goal solved\<close>
  apply (simp split: prod.splits add: Let_def, clarify)+
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def 
                   Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def partition_index_map_def)
  apply clarify
  apply simp
  apply (rename_tac iM pm pim it im'' sm' n' L' l s u i s' pp)
defer
  apply (simp)
\<comment>\<open>goal solved\<close>
  apply (simp)

  apply (simp split: prod.splits add: Let_def, clarify)+
  apply (simp add: partition_index_map_def Hopcroft_map2_state_rel_def
                   Hopcroft_map2_state_\<alpha>_def partition_map2_\<alpha>_def)
  apply auto[]
\<comment>\<open>goal solved\<close>
  apply (simp split: prod.splits add: Let_def, clarify)+
  apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def 
                   Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def partition_index_map_def
              cong: if_cong)
  apply clarify
  apply simp
  apply (rename_tac iM pm pim it im'' sm' n' L' l s u pmin pmax pmin_l pmin_u pmax_l pmax_u i s' pp)
  apply (intro conjI)
defer
defer
defer
  apply (simp add: Hopcroft_map2_state_rel_def single_valued_def) 
  apply (metis fst_conv snd_conv)
\<comment>\<open>goal solved\<close>
  apply simp
\<comment>\<open>goal solved\<close>
using [[goals_limit = 10]]
proof -
  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)
  def im' \<equiv> "partition_map2_\<alpha>_im cm im"

  have dom_im'_eq: "dom im' = dom im" unfolding im'_def dom_def partition_map2_\<alpha>_im_def by simp 

  from PL_OK have P'_eq[simp]: "P' = (im', sm, n)" and
                  im_props: "\<And>i l u. im i = Some (l, u) \<Longrightarrow> l \<le> u \<and> u < card (\<Q> \<A>)" and
                  invar_cm: "class_map_invar (\<Q> \<A>) cm" 
    by (simp_all add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def im'_def
                      Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def partition_map2_invar_def)

  assume "pre \<subseteq> dom (fst (snd P'))" "dom (fst (snd P')) \<subseteq> \<Q> \<A>"
  hence pre_subset: "pre \<subseteq> dom sm" "dom sm \<subseteq> \<Q> \<A>" by simp_all
  thus "pre \<subseteq> dom (fst (snd P))" "dom (fst (snd P)) \<subseteq> \<Q> \<A>"  by simp_all

  fix iM pm pim
  assume iM_props : "Hopcroft_map2_step___iM_props \<A> cm pre P iM (pm, pim)"

  from iM_props have invar_pm_pim: "class_map_invar (\<Q> \<A>) (pm, pim)"
                 and map2_\<alpha>_pm_pim_P: "partition_map2_\<alpha> (pm, pim) P = partition_map2_\<alpha> cm P"
                 and pim_pre_prop: "\<And>i u s l n q. \<lbrakk>iM i = Some s; im i = Some (l, u); 
                                                   l \<le> n; n \<le> u; pim n = Some q\<rbrakk> \<Longrightarrow>
                                                   (q \<in> pre) = (n < s)"
                 and iM_prop: "\<And>i u s l. \<lbrakk>iM i = Some s; im i = Some (l, u)\<rbrakk> \<Longrightarrow> (l < s) \<and> (s \<le> Suc u)"
    unfolding Hopcroft_map2_step___iM_props_def by simp_all metis+
  
  from map2_\<alpha>_pm_pim_P have class_map_pm_pim_eq: "\<And>lu i. im i = Some lu \<Longrightarrow>
    class_map_\<alpha> cm lu = class_map_\<alpha> (pm, pim) lu" unfolding partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def
    by (auto simp add: fun_eq_iff Option.map_def split: option.splits)

  { assume dom_subset: "dom iM \<subseteq> partition_state_map P ` pre"

    from dom_subset
    show "dom iM \<subseteq> partition_state_map P' ` pre"
      by (simp add: partition_state_map_def[abs_def])

    fix q 
    assume q_in_pre: "q \<in> pre"
       and equiv_pred_P': "split_language_equiv_partition_pred \<A>
        (partition_index_map P' (partition_state_map P' q)) a
        (partition_index_map P' p)"

    from q_in_pre pre_subset have "q \<in> dom sm" by blast
    then obtain qi where sm_q_eq[simp]: "sm q = Some qi" by blast

    from invar_P' have "qi \<in> dom im'" unfolding dom_def by simp (metis sm_q_eq)
    hence "qi \<in> dom im" by (simp add: dom_im'_eq)
    then obtain q_u q_l where im_q_eq[simp]: "im qi = Some (q_l, q_u)" by auto

    from p_le invar_P' have "p \<in> dom im'" by simp
    hence "p \<in> dom im" by (simp add: dom_im'_eq)
    then obtain p_u p_l where im_p_eq[simp]: "im p = Some (p_l, p_u)" by auto

    assume "\<forall>q. q \<in> pre \<longrightarrow>
           split_language_equiv_partition_pred \<A>
            (partition_index_map2_full (pm, pim) P (partition_state_map P q)) a
            (partition_index_map2_full (pm, pim) P p) \<longrightarrow>
           partition_state_map P q \<in> dom iM"
    with q_in_pre have
      "split_language_equiv_partition_pred \<A>
         (partition_index_map2_full (pm, pim) P (partition_state_map P q)) a
         (partition_index_map2_full (pm, pim) P p) \<Longrightarrow>
       partition_state_map P q \<in> dom iM" by simp
    with equiv_pred_P' class_map_pm_pim_eq[OF im_q_eq] 
         class_map_pm_pim_eq[OF im_p_eq] 
    have "partition_state_map P q \<in> dom iM"
      by (simp add: partition_index_map2_full_def partition_index_map_def partition_state_map_def
                       im'_def partition_map2_\<alpha>_im_def)

    thus "partition_state_map P' q \<in> dom iM"
      by (simp add: partition_state_map_def)
  }


  fix it i s im'' pp l u sm' n' L'
  assume it_subset: "it \<subseteq> {(p', s). iM p' = Some s}"
  assume is_in: "(i, s) \<in> it"
  assume "partition_map2_\<alpha>_im (pm, pim) im'' i = Some pp"
  assume im''_i_eq[simp]: "im'' i = Some (l, u)"
  assume invar_pm_pim: "class_map_invar (\<Q> \<A>) (pm, pim)"
  assume step_invar: "Hopcroft_map_step_invar \<A> p a P' L (fst ` it) ((partition_map2_\<alpha>_im (pm, pim) im'', sm', n'), L')"
  assume step_invar2: "Hopcroft_map2_step_invar \<A> p a P L (pm, pim) it ((im'', sm', n'), L')"
  assume invar2_cm'_P'': "partition_map2_invar (card (\<Q> \<A>)) (im'', sm', n')"
  assume "snd (snd P') \<le> n'" hence n_le_n': "n \<le> n'" by simp

  from invar_pm_pim have dom_pim: "dom pim = {i. i < card (\<Q> \<A>)}" 
    unfolding class_map_invar_def by simp

  from `partition_map2_\<alpha>_im (pm, pim) im'' i = Some pp` 
  have pp_eq: "class_map_\<alpha> (pm, pim) (l, u) = pp"
    by (simp add: partition_map2_\<alpha>_im_def)

  from invar2_cm'_P'' have lu_OK: "l \<le> u \<and> u < card (\<Q> \<A>)"
    unfolding partition_map2_invar_def by simp (metis im''_i_eq)

  assume "fst P' i = Some pp"
  hence im'_i_eq[simp]: "im' i = Some pp" by simp
  
  hence "i \<in> dom im'" by blast
  with invar_P' n_le_n' have i_le_n': "i < n'" by simp

  have im_i_eq[simp]: "im i = Some (l, u)"
  proof -
    from im'_i_eq
    obtain l' u' where 
      im_i_eq: "im i = Some (l', u')" and
      pp_eq2: "class_map_\<alpha> cm (l', u') = pp"  
      unfolding im'_def partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def
    by auto
    from im_props[OF im_i_eq] have lu'_OK: "l' \<le> u' \<and> u' < card (\<Q> \<A>)" .

    from pp_eq2 class_map_pm_pim_eq[OF im_i_eq]
    have pp_eq3: "class_map_\<alpha> (pm, pim) (l', u') = pp" by simp

    from dom_pim class_map_invar___pim_inj[OF invar_pm_pim]
    have pim_inj_on': "inj_on (\<lambda>i. the (pim i)) {i . i < card (\<Q> \<A>)}"
      unfolding inj_on_def dom_def set_eq_iff 
      by auto (metis the.simps)
    have pim_inj_on: "inj_on (\<lambda>i. the (pim i)) ({i . l \<le> i \<and> i \<le> u} \<union> {i . l' \<le> i \<and> i \<le> u'})" 
      using lu_OK lu'_OK
      apply (rule_tac subset_inj_on[OF pim_inj_on'])
      apply (simp add: subset_iff)
    done

    have "class_map_\<alpha> (pm, pim) (l', u') = class_map_\<alpha> (pm, pim) (l, u)" 
      using pp_eq pp_eq3 by simp
    hence "{i |i. l \<le> i \<and> i \<le> u} = {i |i. l' \<le> i \<and> i \<le> u'}"
      unfolding class_map_\<alpha>_alt_def 
      using inj_on_Un_image_eq_iff[OF pim_inj_on]
      by simp
    hence "l = l' \<and> u = u'" 
      apply (simp add: set_eq_iff) 
      apply (metis im_i_eq im_props le_trans linorder_linear order_antisym)
    done

    thus ?thesis by (simp add: im_i_eq)   
  qed

  from is_in it_subset have iM_i_eq[simp]: "iM i = Some s" by (simp add: subset_iff)
  from iM_prop [of i s l u] have s_OK: "l < s \<and> s \<le> Suc u" by simp

  { fix l' u'
    assume u'_le: "u' < card (\<Q> \<A>)" 

    with invar_pm_pim have subset_dom: "{i |i. l' \<le> i \<and> i \<le> u'} \<subseteq> dom pim" 
      by (simp add: class_map_invar_def subset_iff)

    have "card (class_map_\<alpha> (pm, pim) (l', u')) = card {i |i. l' \<le> i \<and> i \<le> u'}"
      apply (simp add: class_map_\<alpha>_alt_def)
      apply (intro card_image inj_onI class_map_invar___pim_inj [OF invar_pm_pim])
      apply (insert subset_dom)
      apply (auto simp add: subset_iff dom_def)
    done
    hence "card (class_map_\<alpha> (pm, pim) (l', u')) = Suc u' - l'"
      using card_nat_segment[of l' u'] by simp
  } note card_class_map = this
  
  have pim_pre_prop': "\<And>n. l \<le> n \<Longrightarrow> n \<le> u \<Longrightarrow> (the (pim n) \<in> pre) = (n < s)"  
  proof -
    fix n
    assume n_props: "l \<le> n" "n \<le> u"

    with dom_pim lu_OK have "n \<in> dom pim" by auto
    then obtain q where pim_n_eq: "pim n = Some q" by blast

    from pim_pre_prop[of i s l u n q] pim_n_eq n_props 
    show "(the (pim n) \<in> pre) = (n < s)" by simp
  qed

  from s_OK obtain s_pre where s_pre_intro: "s = Suc s_pre" 
    by (cases s) auto

  have pp_in_pre_eq: "{q \<in> pp. q \<in> pre} = class_map_\<alpha> (pm, pim) (l, s - Suc 0)" 
  proof -
    { fix x i
      from pim_pre_prop'[of i] s_OK
      have "(x = the (pim i) \<and> l \<le> i \<and> i \<le> u \<and> x \<in> pre) =
            (x = the (pim i) \<and> l \<le> i \<and> i < s)"
         by auto
    }
    with s_OK show ?thesis
      unfolding pp_eq[symmetric]
      apply (simp del: ex_simps add: s_pre_intro set_eq_iff class_map_\<alpha>_def ex_simps[symmetric])
      apply auto
    done
  qed

  have pp_nin_pre_eq: "{q \<in> pp. q \<notin> pre} = class_map_\<alpha> (pm, pim) (s, u)" 
  proof -
    { fix x i
      from pim_pre_prop'[of i] s_OK 
      have "(x = the (pim i) \<and> l \<le> i \<and> i \<le> u \<and> x \<notin> pre) =
            (x = the (pim i) \<and> s \<le> i \<and> i \<le> u)"
         by auto
    }
    thus ?thesis
      unfolding pp_eq[symmetric]
      by (simp del: ex_simps add: set_eq_iff class_map_\<alpha>_def ex_simps[symmetric])
  qed

  show "(Suc u \<le> s) = (card {q \<in> pp. q \<notin> pre} = 0)" 
    using card_class_map [of u s] s_OK lu_OK
    unfolding pp_nin_pre_eq by simp
   

  fix pmin pmax pmin_l pmin_u pmax_l pmax_u
  assume pminmax_eq: "(if card {q \<in> pp. q \<notin> pre} < card {q \<in> pp. q \<in> pre}
            then ({q \<in> pp. q \<notin> pre}, {q \<in> pp. q \<in> pre})
            else ({q \<in> pp. q \<in> pre}, {q \<in> pp. q \<notin> pre})) =
           (pmin, pmax)"
  assume pminmax_lu_eq:
    "(if Suc u - s < s - l then ((s, u), l, s - Suc 0) else ((l, s - Suc 0), s, u)) =
     ((pmin_l, pmin_u), (pmax_l, pmax_u))"
  assume "s < Suc u" hence s_le_u: "s \<le> u" by simp

  from card_class_map [of u s] card_class_map [of "s - Suc 0" l] s_OK lu_OK
  have card_eval: "card (class_map_\<alpha> (pm, pim) (s, u)) = Suc u - s"
                  "card (class_map_\<alpha> (pm, pim) (l, s - Suc 0)) = s - l" by auto

  from pminmax_eq have "pmin \<union> pmax = pp" by (auto split: if_splits)
  hence class_lu_minmax: "class_map_\<alpha> (pm, pim) (l, u) = pmin \<union> pmax" unfolding pp_eq by simp

  from pminmax_eq pminmax_lu_eq
  have pmin_eq: "class_map_\<alpha> (pm, pim) (pmin_l, pmin_u) = pmin" and
       pmax_eq: "class_map_\<alpha> (pm, pim) (pmax_l, pmax_u) = pmax"
      unfolding pp_in_pre_eq pp_nin_pre_eq card_eval
      by (auto split: if_splits)

  show "partition_map2_\<alpha>_im (pm, pim) im''(i \<mapsto> pmax, n' \<mapsto> pmin) =
        partition_map2_\<alpha>_im (pm, pim) (im''(i \<mapsto> (pmax_l, pmax_u), n' \<mapsto> (pmin_l, pmin_u)))"
    by (simp add: partition_map2_\<alpha>_im_def pmin_eq fun_eq_iff pmax_eq)

  show "(\<lambda>q. if q \<in> pmin then Some n' else sm' q) =
        (\<lambda>q. if q \<in> class_map_\<alpha> (pm, pim) (pmin_l, pmin_u) then Some n' else sm' q)"
    unfolding pmin_eq ..
 
  from pminmax_lu_eq[symmetric] lu_OK s_OK s_le_u have 
    pmin_lu_OK: "pmin_l \<le> pmin_u \<and> pmin_u < card (\<Q> \<A>)" and
    pmax_lu_OK: "pmax_l \<le> pmax_u \<and> pmax_u < card (\<Q> \<A>)"
    by (simp_all split: if_splits add: s_pre_intro)

  from invar2_cm'_P'' i_le_n'
  show "partition_map2_invar (card (\<Q> \<A>)) 
            (im''(i \<mapsto> (pmax_l, pmax_u), n' \<mapsto> (pmin_l, pmin_u)),
             \<lambda>q. if q \<in> class_map_\<alpha> (pm, pim) (pmin_l, pmin_u) then Some n'
                 else sm' q, Suc n')" 
    unfolding partition_map2_invar_def 
    by (simp add: pmin_lu_OK pmax_lu_OK)
qed

*)


definition Hopcroft_map2_step_compute_iM_invar where
  "Hopcroft_map2_step_compute_iM_invar \<A> cm pre P pre' = (\<lambda>(iM, cm').
   Hopcroft_map2_step___iM_props \<A> cm (pre - pre') P iM cm' \<and>
   (dom iM = (partition_state_map P) ` (pre - pre')))"

definition Hopcroft_map2_step_compute_iM where
"Hopcroft_map2_step_compute_iM \<A> (cm::'q class_map) (pre::'q set) P = 
 FOREACHi (Hopcroft_map2_step_compute_iM_invar \<A> cm pre P) pre (\<lambda>q (iM, (pm, pim)). do {
   ASSERT (q \<in> dom pm \<and> q \<in> dom (fst (snd P)));
   let i = (partition_state_map P) q;
   let s = (case (iM i) of Some s \<Rightarrow> s | None \<Rightarrow>
             (let (l, u) = (partition_index_map P) i in l));
   ASSERT (q \<in> dom pm \<and> s \<in> dom pim);
   let iq = the (pm q);
   let qs = the (pim s);
   let pm' = pm (q \<mapsto> s) (qs \<mapsto> iq);
   let pim' = pim (s \<mapsto> q) (iq \<mapsto> qs);
   RETURN (iM (i \<mapsto> (Suc s)), (pm', pim'))
 }) (Map.empty, cm)"

lemma Hopcroft_map2_step_compute_iM_correct :
assumes pre_subset: "pre \<subseteq> dom (fst (snd P))" "pre \<subseteq> \<Q> \<A>"
    and fin_P: "finite (dom (fst (snd P)))"
    and invar_cm: "class_map_invar (\<Q> \<A>) cm"
    and invar_P: "partition_map2_invar (card (\<Q> \<A>)) P"
    and invar_P': "partition_map_invar (partition_map2_\<alpha> cm P)"
    and is_part_P'': "is_partition (\<Q> \<A>) (partition_map_\<alpha> (partition_map2_\<alpha> cm P))"
shows "Hopcroft_map2_step_compute_iM \<A> cm pre P \<le> SPEC (\<lambda>(iM, cm'). 
          Hopcroft_map2_step___iM_props \<A> cm pre P iM cm' \<and>
          (dom iM = (partition_state_map P) ` pre))"
unfolding Hopcroft_map2_step_compute_iM_def
apply (rule refine_vcg)
-- "subgoals"
defer
  apply (simp add: Hopcroft_map2_step_compute_iM_invar_def Hopcroft_map2_step___iM_props_def
                   invar_cm)
-- "goal solved"
  apply (simp add: Let_def, clarify)
  apply (rename_tac q pre' iM pm' pim')
  apply (rule ASSERT_leI)
  apply (rule conjI)
defer
defer
  apply (erule conjE) 
  apply (rule ASSERT_leI)
  apply simp
defer
  apply (simp)
defer
  apply (simp split: prod.splits add: Hopcroft_map2_step_compute_iM_invar_def)
proof -
  from pre_subset fin_P show "finite pre" by (metis finite_subset)
next
  -- "first get manage assumptions and introduce abbriviations"
  fix q pre' iM pm' pim'
  assume "q \<in> pre'" "pre' \<subseteq> pre" and
         iM_invar: "Hopcroft_map2_step_compute_iM_invar \<A> cm pre P pre' (iM, pm', pim')"

  from `q \<in> pre'` `pre' \<subseteq> pre`
  have pre_diff_eq: "pre - (pre' - {q}) = insert q (pre - pre')" by auto

  def i \<equiv> "(partition_state_map P) q"
  def s \<equiv> "(case (iM i) of Some s \<Rightarrow> s | None \<Rightarrow>
             (let (l, u) = (partition_index_map P) i in l))"
  def iq \<equiv> "the (pm' q)"
  def qs \<equiv> "the (pim' s)"
  def pm'' \<equiv> "pm' (q \<mapsto> s) (qs \<mapsto> iq)"
  def pim'' \<equiv> "pim' (s \<mapsto> q) (iq \<mapsto> qs)"

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  -- "destruct assumptions into usefull facts"
  from iM_invar invar_P' is_part_P''
  have invar_P'_pm': "partition_map_invar (partition_map2_\<alpha> (pm', pim') P)"
    and is_part_P''_pm': "is_partition (\<Q> \<A>) (partition_map_\<alpha> (partition_map2_\<alpha> (pm', pim') P))"
    unfolding Hopcroft_map2_step_compute_iM_invar_def 
    by (simp_all add: Hopcroft_map2_step___iM_props_def)
 
  from invar_P'_pm' 
  have dom_im_eq: "dom im = {i. i < n}"
   and sm_eq_some: "\<And>q i. (sm q = Some i) = (\<exists>lu. im i = Some lu \<and> q \<in> class_map_\<alpha> (pm', pim') lu)" 
     apply (simp_all add: partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def)
     apply (simp add: dom_def)
     apply metis
  done

 from iM_invar 
  have dom_iM_eq: "dom iM = partition_state_map P ` (pre - pre')"
   and invar_pm': "class_map_invar (\<Q> \<A>) (pm', pim')"
   and map2_im_eq: "partition_map2_\<alpha>_im cm im = partition_map2_\<alpha>_im (pm', pim') im"
   and iM_prop1: "\<And>i u s l. \<lbrakk>iM i = Some s; im i = Some (l, u)\<rbrakk> \<Longrightarrow> l < s \<and> s \<le> Suc u"
   and iM_prop2: "\<And>i u s l n q.
          \<lbrakk>iM i = Some s; im i = Some (l, u); l \<le> n; n \<le> u; pim' n = Some q\<rbrakk> \<Longrightarrow>
          (q \<in> pre \<and> q \<notin> pre') = (n < s)"
     unfolding Hopcroft_map2_step_compute_iM_invar_def Hopcroft_map2_step___iM_props_def
     apply (simp_all add: i_def[symmetric] partition_map2_\<alpha>_def)
     apply blast+
  done

  from invar_pm' have 
    dom_pm'_eq: "dom pm' = \<Q> \<A>" and
    dom_pim'_eq: "dom pim' = {i. i < card (\<Q> \<A>)}"
    unfolding class_map_invar_def by simp_all

  from pre_subset `q \<in> pre'` `pre' \<subseteq> pre` 
  have "q \<in> dom sm" by auto
  hence sm_q_eq: "sm q = Some i" unfolding i_def partition_state_map_def by auto

  from `q \<in> dom sm` show "q \<in> dom (fst (snd P))"
    by (simp add: dom_pm'_eq subset_iff)

  from `q \<in> pre'` `pre' \<subseteq> pre` `pre \<subseteq> \<Q> \<A>`
  show "q \<in> dom pm'"
    by (simp add: dom_pm'_eq subset_iff)

  from sm_eq_some [of q i] sm_q_eq obtain l u where
     im_i_eq: "im i = Some (l, u)" and
     q_in_class: "q \<in> class_map_\<alpha> (pm', pim') (l, u)"
     by auto

  from invar_P im_i_eq have l_le_u: "l \<le> u" and u_less_card: "u < card (\<Q> \<A>)"
    unfolding partition_map2_invar_def by (simp_all)

  from im_i_eq have "i \<in> dom im" by blast
  with dom_im_eq have i_le_n: "i < n" by simp

  -- "if classes are not distinct, then they are equal"
  have class_map_inter_not_emp: "\<And>i1 i2 l1 l2 u1 u2.
       \<lbrakk>im i1 = Some (l1, u1); im i2 = Some (l2, u2);
        class_map_\<alpha> (pm', pim') (l1, u1) \<inter> class_map_\<alpha> (pm', pim') (l2, u2) \<noteq> {}\<rbrakk> \<Longrightarrow>
       (l1 = l2) \<and> (u1 = u2) \<and> (i1 = i2)"
  proof -
    fix i1 i2 l1 l2 u1 u2

    assume "im i1 = Some (l1, u1)" "im i2 = Some (l2, u2)"
           "class_map_\<alpha> (pm', pim') (l1, u1) \<inter> class_map_\<alpha> (pm', pim') (l2, u2) \<noteq> {}"  

    from `im i1 = Some (l1, u1)` `im i2 = Some (l2, u2)` dom_im_eq invar_P
    have ilu_facts: "i1 < n" "i2 < n" "l1 \<le> u1" "u1 < card (\<Q> \<A>)" "l2 \<le> u2" "u2 < card (\<Q> \<A>)" 
    unfolding partition_map2_invar_def
      by (simp_all) blast+

    from class_map_invar___pim_inj[OF invar_pm'] dom_pim'_eq
    have pim_inj_on': "inj_on (\<lambda>i. the (pim' i)) {i . i < card (\<Q> \<A>)}"
      unfolding inj_on_def dom_def set_eq_iff 
      by auto (metis the.simps)
    have pim_inj_on: "inj_on (\<lambda>i. the (pim' i)) ({i . l1 \<le> i \<and> i \<le> u1} \<union> {i . l2 \<le> i \<and> i \<le> u2})" 
      using ilu_facts
      apply (rule_tac subset_inj_on[OF pim_inj_on'])
      apply (simp add: subset_iff)
    done

    from ilu_facts is_part_P''_pm' `im i1 = Some (l1, u1)` `im i2 = Some (l2, u2)`
           `class_map_\<alpha> (pm', pim') (l1, u1) \<inter> class_map_\<alpha> (pm', pim') (l2, u2) \<noteq> {}`
    have "class_map_\<alpha> (pm', pim') (l1, u1) = class_map_\<alpha> (pm', pim') (l2, u2)"
      apply (simp_all add: partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def
                           is_partition_def)
      apply blast
    done
    hence "{i |i. l1 \<le> i \<and> i \<le> u1} = {i |i. l2 \<le> i \<and> i \<le> u2}"
      unfolding class_map_\<alpha>_alt_def 
      using inj_on_Un_image_eq_iff[OF pim_inj_on]
      by simp

    hence lu1_eq: "l1 = l2 \<and> u1 = u2" 
      apply (simp add: set_eq_iff) 
      apply (metis im_i_eq ilu_facts le_trans linorder_linear order_antisym)
    done

    from Hopcroft_Minimisation.partition_index_map_inj_on[OF invar_P', of "{i1, i2}"]
         `im i1 = Some (l1, u1)` `im i2 = Some (l2, u2)`
    have "i1 = i2"
      apply (simp add: partition_map2_\<alpha>_def partition_index_map_def image_iff Ball_def
                       partition_map2_\<alpha>_im_def lu1_eq)
      apply (metis ilu_facts(1,2))
    done
    with lu1_eq show "l1 = l2 \<and> u1 = u2 \<and> i1 = i2" by simp
  qed

  -- "properties of iq"
  from `q \<in> pre'` `pre' \<subseteq> pre` `pre \<subseteq> \<Q> \<A>` have "q \<in> \<Q> \<A>" by blast
  with invar_pm' have "q \<in> dom pm'" by (simp add: class_map_invar_def)
  hence pm'_q_eq: "pm' q = Some iq" unfolding iq_def by auto
  with invar_pm' have pim'_iq_eq: "pim' iq = Some q" 
    by (simp add: class_map_invar_def del: pm'_q_eq)
  from pim'_iq_eq invar_pm' have "iq < card (\<Q> \<A>)" 
    by (auto simp add: class_map_invar_def simp del: pim'_iq_eq)
  have pim'_q_simp: "\<And>x. pim' x = Some q \<longleftrightarrow> x = iq"
    using class_map_invar___pim_inj[OF invar_pm', OF pim'_iq_eq] 
    by (auto simp add: pim'_iq_eq)
  from dom_pim'_eq u_less_card q_in_class pim'_q_simp have iq_props: "l \<le> iq \<and> iq \<le> u"
    by (simp add: class_map_\<alpha>_def dom_def set_eq_iff) (metis the.simps xt1(7))

  -- "properties of s" 
  have "l \<le> s \<and> s \<le> iq \<and>
       (\<forall>n q. l \<le> n \<and> n \<le> u \<and> pim' n = Some q \<longrightarrow>
              (q \<in> pre \<and> q \<notin> pre') = (n < s))"
  proof (cases "iM i")
    case None note iM_i_eq = this
    hence s_eq: "s = l"
      by (simp add: s_def partition_index_map_def im_i_eq)

    from iM_i_eq have "i \<notin> dom iM" by blast
    with dom_iM_eq have "i \<notin> partition_state_map P ` (pre - pre')" by simp
    hence not_dom_iM: "\<And>q. the (sm q) = i \<Longrightarrow> q \<in> pre \<Longrightarrow> q \<in> pre'"
      by (auto simp add: image_iff Ball_def partition_state_map_def)

    have in_part_i: "\<And>n q. \<lbrakk>l \<le> n; n \<le> u; pim' n = Some q\<rbrakk> \<Longrightarrow> sm q = Some i" 
    proof -
      fix n q
      assume "l \<le> n" "n \<le> u" "pim' n = Some q"
      with sm_eq_some [of q i] 
      show "sm q = Some i"
        apply (simp add: im_i_eq class_map_\<alpha>_def)
        apply (metis the.simps)
      done
    qed

    from l_le_u s_eq in_part_i not_dom_iM iq_props show ?thesis
      apply simp
      apply (metis the.simps)
    done      
  next
    case (Some s')
    hence iM_i_eq: "iM i = Some s" 
      unfolding s_def by (simp add: s_def)

    from iM_prop2[of i s l u iq, OF iM_i_eq im_i_eq _ _ pim'_iq_eq] iq_props `q \<in> pre'`
    have "s \<le> iq" by (simp)

    with iM_prop1[of i s l u] iM_prop2[of i s l u] 
    show ?thesis by (simp add: iM_i_eq im_i_eq)
  qed
  with iq_props have s_props: "l \<le> s" "s \<le> iq" "s \<le> u" 
                 "\<And>n q. \<lbrakk>l \<le> n; n \<le> u; pim' n = Some q\<rbrakk> \<Longrightarrow>
                         (q \<in> pre \<and> q \<notin> pre') = (n < s)"
    by auto

  -- "properties of iq"
  from invar_pm' s_props(3) u_less_card have "s \<in> dom pim'"
    by (simp add: class_map_invar_def)
  hence pim'_s_eq: "pim' s = Some qs" using qs_def by auto
  with invar_pm' have pm'_qs_eq: "pm' qs = Some s" 
    by (simp add: class_map_invar_def del: pm'_q_eq)
  from pm'_qs_eq invar_pm' have "qs \<in> \<Q> \<A>" 
    by (auto simp add: class_map_invar_def dom_def set_eq_iff)
  have pim'_qs_simp: "\<And>x. pim' x = Some qs \<longleftrightarrow> x = s"
    using class_map_invar___pim_inj[OF invar_pm', OF pim'_s_eq] 
    by (auto simp add: pim'_s_eq)
  from pim'_iq_eq have q_def: "q = the (pim' iq)" by simp

  from `s \<in> dom pim'`
  show "(case iM (partition_state_map P q) of
        None \<Rightarrow> let (l, u) = partition_index_map P (partition_state_map P q) in l
        | Some s \<Rightarrow> s) \<in> dom pim'"
   unfolding i_def[symmetric] s_def[symmetric] by simp

  -- "start with main proof"
  have "Hopcroft_map2_step___iM_props \<A> cm (insert q (pre - pre')) P
       (iM(i \<mapsto> Suc s)) (pm'', pim'')"
  proof
    from `qs \<in> \<Q> \<A>` `q \<in> \<Q> \<A>`
    have Q_eq: "insert qs (insert q (\<Q> \<A>)) = \<Q> \<A>" by auto

    from `iq < card (\<Q> \<A>)` s_props(2) u_less_card
    have card_le_eq: "insert iq (insert s {i. i < card (\<Q> \<A>)}) = {i. i < card (\<Q> \<A>)}" by auto

    from invar_pm' show "class_map_invar (\<Q> \<A>) (pm'', pim'')"
      unfolding pm''_def pim''_def class_map_invar_def
      apply (simp add: all_conj_distrib Q_eq card_le_eq pim'_qs_simp
                       pim'_iq_eq pim'_s_eq pim'_q_simp)
      apply (rule_tac conjI)
      apply (auto simp add: iq_def pm'_qs_eq) []
      apply (auto simp add: qs_def pim'_iq_eq) []
    done
  next
    have map2_im_eq2: "partition_map2_\<alpha>_im (pm'', pim'') im = partition_map2_\<alpha>_im (pm', pim') im"
    proof
      fix ii
      show "partition_map2_\<alpha>_im (pm'', pim'') im ii =
            partition_map2_\<alpha>_im (pm', pim') im ii"
      proof (cases "im ii")
        case None thus ?thesis unfolding partition_map2_\<alpha>_im_def by simp
      next
        case (Some lu)
        then obtain l' u' where im_ii_eq: "im ii = Some (l', u')" by (metis prod.exhaust)

        have "class_map_\<alpha> (pm'(q \<mapsto> s, qs \<mapsto> iq), pim'(s \<mapsto> q, iq \<mapsto> qs)) (l', u') =
              class_map_\<alpha> (pm', pim') (l', u')"
        proof (rule set_eqI)
          fix qq
          show "qq \<in> class_map_\<alpha> (pm'(q \<mapsto> s, qs \<mapsto> iq), pim'(s \<mapsto> q, iq \<mapsto> qs)) (l', u') \<longleftrightarrow>
                qq \<in> class_map_\<alpha> (pm', pim') (l', u')"
          proof (cases "l' \<le> s \<and> s \<le> u' \<or> l' \<le> iq \<and> iq \<le> u'")
            case False thus ?thesis 
              apply (simp add: class_map_\<alpha>_def)
              apply (rule iffI)
              apply auto[]
              apply (erule exE)
              apply (rule_tac ?x=i in exI)
              apply simp
              apply (auto simp add: pim'_s_eq pim'_iq_eq)
            done
          next
            case True with s_props(1,3) iq_props
            have "q \<in> class_map_\<alpha> (pm', pim') (l', u') \<inter> class_map_\<alpha> (pm', pim') (l, u) \<or>
                 qs \<in> class_map_\<alpha> (pm', pim') (l', u') \<inter> class_map_\<alpha> (pm', pim') (l, u)"
              apply (simp add: class_map_\<alpha>_def q_def qs_def)
              apply auto
            done
            hence "class_map_\<alpha> (pm', pim') (l', u') \<inter> class_map_\<alpha> (pm', pim') (l, u) \<noteq> {}" by auto
            hence l'_eq: "l' = l" and u'_eq: "u' = u"
              using class_map_inter_not_emp[OF im_ii_eq im_i_eq] by simp_all

            from iq_props s_props(1,3)
            show ?thesis
              apply (simp add: l'_eq u'_eq class_map_\<alpha>_def q_def qs_def)
              apply (metis)
            done
          qed
        qed
        thus ?thesis
          unfolding partition_map2_\<alpha>_im_def pm''_def pim''_def im_ii_eq
          by simp    
      qed
    qed

    from map2_im_eq map2_im_eq2 show "partition_map2_\<alpha> (pm'', pim'') P = partition_map2_\<alpha> cm P"
      by (simp add: partition_map2_\<alpha>_def)
  next
    fix i' s' l' u'
    assume iM'_i'_eq: "(iM(i \<mapsto> Suc s)) i' = Some s'" and im_i'_eq: "fst P i' = Some (l', u')"
    show "l' < s' \<and> s' \<le> Suc u'"
    proof (cases "i' = i")
      case True 
      with iM'_i'_eq[symmetric] im_i'_eq[symmetric] s_props(1,3) show ?thesis
        by (simp add: im_i_eq)
    next
      case False note i'_neq_i = this
      with iM'_i'_eq have iM_i'_eq: "iM i' = Some s'" by simp
     
      from iM_prop1[OF iM_i'_eq, of l' u'] im_i'_eq
      show ?thesis by simp
    qed
  next
    fix i' s' l' u' n q'
    assume iM'_i'_eq: "(iM(i \<mapsto> Suc s)) i' = Some s'" and im_i'_eq: "fst P i' = Some (l', u')"
       and n_props: "l' \<le> n" "n \<le> u'"
       and pim''_n_eq: "snd (pm'', pim'') n = Some q'"

    show "(q' \<in> insert q (pre - pre')) = (n < s')"
    proof (cases "n = iq \<or> n = s")
      case False 
      hence "n \<noteq> iq" "n \<noteq> s" by simp_all
      hence pim'_n_eq: "pim' n = Some q'" using pim''_n_eq by (simp add: pim''_def)
      with `n \<noteq> iq` pim'_q_simp[of n] have "q' \<noteq> q" by simp

      show ?thesis
      proof (cases "i' = i")
        case True note i'_eq =this

        from i'_eq iM'_i'_eq have s'_eq: "s' = Suc s" by simp
        from s_props(4)[of n q'] n_props im_i'_eq[symmetric] `n \<noteq> s`
        show ?thesis by (auto simp add: i'_eq im_i_eq pim'_n_eq `q' \<noteq> q` s'_eq)
      next
        case False 
        with iM_prop2[of i' s' l' u' n q'] iM'_i'_eq im_i'_eq n_props pim'_n_eq `q' \<noteq> q`
        show ?thesis by simp
      qed
    next
      case True note n_eq_iq_or_s = this
      with s_props(1,3) n_props iq_props
      have "q \<in> class_map_\<alpha> (pm', pim') (l', u') \<inter> class_map_\<alpha> (pm', pim') (l, u) \<or>
            qs \<in> class_map_\<alpha> (pm', pim') (l', u') \<inter> class_map_\<alpha> (pm', pim') (l, u)"
        apply (simp add: class_map_\<alpha>_def q_def qs_def)
        apply auto
      done
      hence "class_map_\<alpha> (pm', pim') (l', u') \<inter> class_map_\<alpha> (pm', pim') (l, u) \<noteq> {}" by auto
      hence l'_eq: "l' = l" and u'_eq: "u' = u" and i'_eq: "i' = i"
        using class_map_inter_not_emp[OF _ im_i_eq, of i' l' u'] im_i'_eq by simp_all
 
      from iM'_i'_eq have s'_eq: "s' = Suc s" by (simp add: i'_eq)

      show ?thesis
      proof (cases "n = iq")
        case True note n_eq = this
        with pim''_n_eq have q'_eq: "q' = qs" by (simp add: pim''_def)

        from pim'_qs_simp[of iq, symmetric]
        have iqs_eq_simp: "iq = s \<longleftrightarrow> q = qs" by (simp add: pim'_iq_eq)
     
        from s_props(2) have "iq < Suc s \<longleftrightarrow> iq = s" by auto
        with s_props(4)[of s qs, symmetric]
        show ?thesis
          apply (simp add: q'_eq n_eq s'_eq iq_props pim'_s_eq s_props(1,2,3) iqs_eq_simp)
          apply metis
        done
      next
        case False note n_eq_iq = this
        with n_eq_iq_or_s have n_eq: "n = s" by simp

        with pim''_n_eq n_eq_iq have q'_eq: "q' = q" by (simp add: pim''_def)
        show ?thesis by (simp add: q'_eq s'_eq n_eq)
      qed
    qed
  qed
  hence "Hopcroft_map2_step_compute_iM_invar \<A> cm pre P (pre' - {q})
           (iM(i \<mapsto> Suc s), pm'', pim'') " 
     unfolding Hopcroft_map2_step_compute_iM_invar_def
     by (simp add: i_def[symmetric] dom_iM_eq pre_diff_eq del: P_eq)  
  thus "Hopcroft_map2_step_compute_iM_invar \<A> cm pre P (pre' - {q})
        (iM(partition_state_map P q \<mapsto>
         Suc (case iM (partition_state_map P q) of
              None \<Rightarrow>
                let (l, u) = partition_index_map P (partition_state_map P q) in l
              | Some s \<Rightarrow> s)),
         pm'(q \<mapsto>
         case iM (partition_state_map P q) of
         None \<Rightarrow> let (l, u) = partition_index_map P (partition_state_map P q) in l
         | Some s \<Rightarrow> s,
         the (pim' (case iM (partition_state_map P q) of
                    None \<Rightarrow>
                      let (l, u) = partition_index_map P (partition_state_map P q)
                      in l
                    | Some s \<Rightarrow> s)) 
         \<mapsto> the (pm' q)), pim'
         (case iM (partition_state_map P q) of
          None \<Rightarrow> let (l, u) = partition_index_map P (partition_state_map P q) in l
          | Some s \<Rightarrow> s 
         \<mapsto> q, the (pm' q) \<mapsto>
         the (pim' (case iM (partition_state_map P q) of
                    None \<Rightarrow>
                      let (l, u) = partition_index_map P (partition_state_map P q)
                      in l
                    | Some s \<Rightarrow> s))))"
     unfolding i_def[symmetric] s_def[symmetric] iq_def[symmetric] qs_def[symmetric]
               pm''_def[symmetric] pim''_def[symmetric] by simp
qed


definition Hopcroft_map2_step_compute_iM_swap_check where
"Hopcroft_map2_step_compute_iM_swap_check \<A> (cm::'q class_map) (pre::'q set) P = 
 FOREACHi (Hopcroft_map2_step_compute_iM_invar \<A> cm pre P) pre (\<lambda>q (iM, (pm, pim)). do {
   ASSERT (q \<in> dom pm \<and> q \<in> dom (fst (snd P)));
   let i = (partition_state_map P) q;
   let s = (case (iM i) of Some s \<Rightarrow> s | None \<Rightarrow>
             (let (l, u) = (partition_index_map P) i in l));
   ASSERT (q \<in> dom pm \<and> s \<in> dom pim);
   let iq = the (pm q);
   if (iq = s) then RETURN (iM (i \<mapsto> (Suc s)), (pm, pim)) else
   do {
     let qs = the (pim s);
     let pm' = pm (q \<mapsto> s) (qs \<mapsto> iq);
     let pim' = pim (s \<mapsto> q) (iq \<mapsto> qs);
     RETURN (iM (i \<mapsto> (Suc s)), (pm', pim'))
   }
 }) (empty, cm)"

lemma Hopcroft_map2_step_compute_iM_swap_check_correct :
assumes invar_cm: "class_map_invar (\<Q> \<A>) cm"
    and pre_subset: "pre \<subseteq> dom (fst (snd P))" "pre \<subseteq> \<Q> \<A>"
shows "Hopcroft_map2_step_compute_iM_swap_check \<A> cm pre P \<le> \<Down>Id (Hopcroft_map2_step_compute_iM \<A> cm pre P)"
unfolding Hopcroft_map2_step_compute_iM_def Hopcroft_map2_step_compute_iM_swap_check_def
using [[goals_limit = 10]]
apply refine_rcg
apply (rule inj_on_id)
apply (simp_all add: Let_def)
apply clarify
apply clarify
apply (simp add: Let_def split: option.split prod.split)
apply clarify
apply simp
apply (rename_tac q pre' iM pm' pim' iq i qs l u)
apply (intro impI conjI allI)
proof -
  fix q pre' iM pm' pim' iq i qs l u
  assume "q \<in> pre'" "pre' \<subseteq> pre"
     and iM_invar: "Hopcroft_map2_step_compute_iM_invar \<A> cm pre P pre' (iM, pm', pim')"
     and pm'_q_eq: "pm' q = Some iq"
     and i_eq: "fst (snd P) q = Some i"
     and qs_eq: "pim' (case iM (partition_state_map P q) of
             None \<Rightarrow>
               let (l, u) = partition_index_map P (partition_state_map P q) in l
             | Some s \<Rightarrow> s) =
          Some qs"
     and lu_eq: "partition_index_map P (partition_state_map P q) = (l, u)"

  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)

  from i_eq have sm_q_eq: "sm q = Some i" by (simp)

  from iM_invar have invar_cm': "class_map_invar (\<Q> \<A>) (pm', pim')" and
    map2_im_cm_cm'_eq: "partition_map2_\<alpha>_im (pm', pim') im = partition_map2_\<alpha>_im cm im" and
    dom_iM_eq: "dom iM = partition_state_map (im, sm, n) ` (pre - pre')"
    unfolding Hopcroft_map2_step_compute_iM_invar_def Hopcroft_map2_step___iM_props_def
    by (simp_all add: partition_map2_\<alpha>_def)

  { assume iM_i_eq: "iM (partition_state_map P q) = None"
       and iq_eq_l: "iq = l"

    from qs_eq iM_i_eq lu_eq have pim'_l_eq: "pim' l = Some qs"
      by (simp add: partition_state_map_def sm_q_eq partition_index_map_def)

    from invar_cm' pim'_l_eq 
    have pm'_qs_eq: "pm' qs = Some l" unfolding class_map_invar_def by simp

    show pm'_OK: "pm' = pm'(q \<mapsto> l, qs \<mapsto> l)" 
      apply (rule ext)
      apply (simp add: pm'_q_eq iq_eq_l pm'_qs_eq)
    done

    show "pim' = pim'(l \<mapsto> qs)"
      apply (rule ext)
      apply (simp add: pim'_l_eq)
    done
  }

  { assume iM_i_eq: "iM (partition_state_map P q) = Some iq"

    from qs_eq iM_i_eq lu_eq have pim'_iq_eq: "pim' iq = Some qs" by simp

    from invar_cm' pim'_iq_eq have pm'_qs_eq: "pm' qs = Some iq" unfolding class_map_invar_def by simp

    show pm'_OK: "pm' = pm'(q \<mapsto> iq, qs \<mapsto> iq)" 
      apply (rule ext)
      apply (simp add: pm'_q_eq pm'_qs_eq)
    done

    show "pim' = pim'(iq \<mapsto> qs)"
      apply (rule ext)
      apply (simp add: pim'_iq_eq)
    done
  }
qed

lemma Hopcroft_map2_step_compute_iM_swap_check_correct_full :
assumes pre_subset: "pre \<subseteq> dom (fst (snd P))" "pre \<subseteq> \<Q> \<A>"
    and fin_P: "finite (dom (fst (snd P)))"
    and invar_cm: "class_map_invar (\<Q> \<A>) cm"
    and invar_P: "partition_map2_invar (card (\<Q> \<A>)) P"
    and invar_P': "partition_map_invar (partition_map2_\<alpha> cm P)"
    and is_part_P'': "is_partition (\<Q> \<A>) (partition_map_\<alpha> (partition_map2_\<alpha> cm P))"
shows "Hopcroft_map2_step_compute_iM_swap_check \<A> cm pre P \<le> SPEC (\<lambda>(iM, cm').
             Hopcroft_map2_step___iM_props \<A> cm pre P iM cm' \<and>
             dom iM = partition_state_map P ` pre)"
proof -
  note Hopcroft_map2_step_compute_iM_swap_check_correct [OF invar_cm pre_subset]
  also note Hopcroft_map2_step_compute_iM_correct [OF pre_subset fin_P invar_cm invar_P 
     invar_P' is_part_P'']
  finally show ?thesis by simp
qed

text \<open> A version with caching and processing the elements in order. This does not really lead
 to an improvement, unluckily. It trades map lookup and updates with sorting a list. In OCaml
 code using red-black-trees this leads to a slight improvement, while it leads to a slight
 disadvantage in PolyML. In the end, it is probably not worth the efford, but it is currently
 kept, but deactivated. It needs further investigation. \<close>

definition Hopcroft_map2_step_compute_iM_cache___init_cache where
"Hopcroft_map2_step_compute_iM_cache___init_cache P q =
   (let i = (partition_state_map P) q in
    let (l::nat, u::nat) = (partition_index_map P) i in
    let s = l in (i, l, u, s))"
   thm partition_index_map_def

fun Hopcroft_map2_step_compute_iM_cache___invar_cache where
  "Hopcroft_map2_step_compute_iM_cache___invar_cache P it None = True"
| "Hopcroft_map2_step_compute_iM_cache___invar_cache P it (Some (i, l, u, s)) = 
   ((fst P) i = Some (l, u) \<and> l \<le> s \<and> (\<forall>q iq. (q, iq) \<in> it \<longrightarrow> s \<le> iq))"

lemma Hopcroft_map2_step_compute_iM_cache___invar_cache_I :
"Hopcroft_map2_step_compute_iM_cache___invar_cache P it None"
"\<lbrakk>(fst P) i = Some (l, u); l \<le> s; \<And>q iq. (q, iq) \<in> it \<Longrightarrow> s \<le> iq\<rbrakk> \<Longrightarrow>
  Hopcroft_map2_step_compute_iM_cache___invar_cache P it (Some (i, l, u, s))"
using assms by simp_all


fun Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache where
  "Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM None = iM"
| "Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM (Some (i, l, u, s)) = 
   (iM (i \<mapsto> s))"

definition Hopcroft_map2_step_compute_iM_invar_cache_add where
  "Hopcroft_map2_step_compute_iM_invar_cache_add \<A> cm pre P it = (\<lambda>(iM, cache, cm').
   let it' = fst ` it in
   let iM' = Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache in
   ((it = ((\<lambda>q. (q, the ((fst cm') q))) ` it')) \<and>
   (Hopcroft_map2_step_compute_iM_cache___invar_cache P it cache) \<and>
   (\<forall>i q iq. i \<in> dom iM \<longrightarrow> (q, iq) \<in> it \<longrightarrow> snd ((partition_index_map P) i) < iq)))"

definition Hopcroft_map2_step_compute_iM_invar_cache where
  "Hopcroft_map2_step_compute_iM_invar_cache \<A> cm pre P it = (\<lambda>(iM, cache, cm').
    Hopcroft_map2_step_compute_iM_invar \<A> cm pre P (fst ` it) (Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache, cm') \<and>
    Hopcroft_map2_step_compute_iM_invar_cache_add \<A> cm pre P it (iM, cache, cm'))"

lemma Hopcroft_map2_step_compute_iM_invar_cache_alt_def :
  "Hopcroft_map2_step_compute_iM_invar_cache \<A> cm pre P it (iM, cache, cm') =
   (let it' = fst ` it in
   let iM' = Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache in
   (Hopcroft_map2_step_compute_iM_invar \<A> cm pre P it' (iM', cm') \<and>
   (it = ((\<lambda>q. (q, the ((fst cm') q))) ` it')) \<and>
   (Hopcroft_map2_step_compute_iM_cache___invar_cache P it cache) \<and>
   (\<forall>i q iq. i \<in> dom iM \<longrightarrow> (q, iq) \<in> it \<longrightarrow> snd ((partition_index_map P) i) < iq)))"
by (simp add: Hopcroft_map2_step_compute_iM_invar_cache_def
              Hopcroft_map2_step_compute_iM_invar_cache_add_def Let_def)
 
lemma Hopcroft_map2_step_compute_iM_invar_cache_add_I :
assumes "\<And>q iq. (q, iq) \<in> it \<Longrightarrow> iq = the ((fst cm') q)"
    and "Hopcroft_map2_step_compute_iM_cache___invar_cache P it cache"
    and "\<And>i q iq. i \<in> dom iM \<Longrightarrow> (q, iq) \<in> it \<Longrightarrow> snd ((partition_index_map P) i) < iq"
shows "Hopcroft_map2_step_compute_iM_invar_cache_add \<A> cm pre P it (iM, cache, cm')"
unfolding Hopcroft_map2_step_compute_iM_invar_cache_add_def
apply (simp add: Let_def assms)
apply (insert assms(1))
apply (auto simp add: image_iff Bex_def)
done


definition Hopcroft_map2_step_compute_iM_update_cache where
  "Hopcroft_map2_step_compute_iM_update_cache P q iq iM cache =
   (case cache of None \<Rightarrow> (iM, Hopcroft_map2_step_compute_iM_cache___init_cache P q)
       | Some (i, l, u, s) \<Rightarrow> if (iq \<le> u) then (iM, (i, l, u, s)) else 
              (iM(i \<mapsto> s), Hopcroft_map2_step_compute_iM_cache___init_cache P q))"

definition Hopcroft_map2_step_compute_iM_cache_swap_check_loop where
"Hopcroft_map2_step_compute_iM_cache_swap_check_loop \<A> (cm::'q class_map) (pre::'q set) P =
    FOREACHoi (Hopcroft_map2_step_compute_iM_invar_cache \<A> cm pre P) 
      ((\<lambda>q. (q, the ((fst cm) q))) ` pre) (\<lambda>(q,iq) (q', iq'). iq \<le> iq')  
      (\<lambda>(q,iq) (iM, cache, (pm, pim)). 
      do {
        ASSERT (q \<in> dom pm \<and> q \<in> dom (fst (snd P)));
        let (iM, (i, l, u, s)) = Hopcroft_map2_step_compute_iM_update_cache P q iq iM cache;
        ASSERT (s \<in> dom pim);
        if (iq = s) then RETURN (iM, Some (i, l, u, Suc s), (pm, pim)) else
        do {
          let qs = the (pim s);
          let pm' = pm (q \<mapsto> s) (qs \<mapsto> iq);
          let pim' = pim (s \<mapsto> q) (iq \<mapsto> qs);
          RETURN (iM, Some (i, l, u, Suc s), (pm', pim'))
        }
      }) (empty, None, cm)"

definition Hopcroft_map2_step_compute_iM_cache_swap_check where
"Hopcroft_map2_step_compute_iM_cache_swap_check \<A> (cm::'q class_map) (pre::'q set) P = 
  do {
    (iM, cache, cm) \<leftarrow> Hopcroft_map2_step_compute_iM_cache_swap_check_loop \<A> 
        (cm::'q class_map) (pre::'q set) P;
    RETURN (Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache, cm)
  }"


lemma Hopcroft_map2_step_compute_iM_cache_swap_check_loop_correct :
assumes invar_cm: "class_map_invar (\<Q> \<A>) cm"
    and pre_subset: "pre \<subseteq> dom (fst (snd P))" "pre \<subseteq> \<Q> \<A>"
    and invar_P: "partition_map2_invar (card (\<Q> \<A>)) P"
    and invar_P': "partition_map_invar (partition_map2_\<alpha> cm P)"
defines "R \<equiv> {((iM, cache, cm), (iM', cm')). cm' = cm \<and>
   iM' = Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache}"
shows "Hopcroft_map2_step_compute_iM_cache_swap_check_loop \<A> cm pre P \<le> \<Down>R 
      (Hopcroft_map2_step_compute_iM_swap_check \<A> cm pre P)"
unfolding Hopcroft_map2_step_compute_iM_swap_check_def 
          Hopcroft_map2_step_compute_iM_cache_swap_check_loop_def
          FOREACHoi_def FOREACHi_def FOREACHci_def
using [[goals_limit = 1]]
apply (rule FOREACHoci_refine [where \<Phi>'' = "
  \<lambda>it cache _ _. Hopcroft_map2_step_compute_iM_invar_cache_add \<A> cm pre P it cache"])
-- "process subgoals"
  apply (subgoal_tac "inj_on fst ((\<lambda>q. (q, the (fst cm q))) ` pre)")
  apply assumption
defer
  apply (auto simp add: image_iff) []
-- "goal solved" 
  apply (simp add: R_def)
-- "goal solved" 
  apply (simp add: R_def single_valued_def)
-- "goal solved" 
  apply simp
-- "goal solved" 
  apply (simp add:  Hopcroft_map2_step_compute_iM_invar_cache_add_def image_image)
-- "goal solved" 
  apply simp
-- "goal solved" 
  apply (simp add: Hopcroft_map2_step_compute_iM_invar_cache_def R_def)
  apply clarify
-- "goal solved" 
  apply (clarify)
  apply (rule refine)+
  apply (simp add: R_def)
  apply (simp)
  apply (unfold fst_conv snd_conv)
  apply clarify
  apply (simp add: partition_state_map_def R_def)
  apply clarify
  apply simp
  apply (rename_tac iq it iM cache pm pim q iq' iq'' i)
  apply (case_tac "Hopcroft_map2_step_compute_iM_update_cache P q iq iM cache")
  apply (rename_tac iM' i' l' u' s')
  apply simp
defer
proof -
  obtain pm pim where cm_eq: "cm = (pm, pim)" by (rule prod.exhaust)
  show "inj_on fst ((\<lambda>q. (q, the (fst cm q))) ` pre)"
    using class_map_invar___pm_inj[OF invar_cm[unfolded cm_eq]]
    by (simp add: cm_eq inj_on_def)
next
  case goal2
  def it' \<equiv> "fst ` it"
  obtain im sm n where P_eq: "P = (im, sm, n)" by (metis prod.exhaust)
  from goal2(1) have iq_le: "\<And>q' iq'. (q', iq') \<in> it \<Longrightarrow> iq \<le> iq'" by auto
  note q_iq_in = goal2(2)
  note it_subset = goal2(3)
  note it'_subset = goal2(4)[folded it'_def]
  note invar = goal2(6)
  note invar_cache_add = goal2(7)
  note pm_q_eq = goal2(9)
  from goal2(10) have sm_q_eq: "sm q = Some i" by (simp add: P_eq)
  have part_state_map_q_eq[simp]: "partition_state_map P q = i" 
    unfolding partition_state_map_def P_eq by (simp add: sm_q_eq)
  note iM_cache'_eq = goal2(11)
  
  from invar have map2_\<alpha>_eq: "partition_map2_\<alpha> cm (im, sm, n) = partition_map2_\<alpha> (pm, pim) (im, sm, n)"
         and invar_pm_pim: "class_map_invar (\<Q> \<A>) (pm, pim)"
    by (simp_all add: P_eq Hopcroft_map2_step_compute_iM_invar_def Hopcroft_map2_step___iM_props_def)

  from invar_cache_add have it_eq: "it = (\<lambda>q. (q, the (pm q))) ` it'"
    unfolding  Hopcroft_map2_step_compute_iM_invar_cache_add_def
    by (simp add: it'_def[symmetric])

  { fix q iq
    assume q_iq_in: "(q, iq) \<in> it"
    with it_subset have "q \<in> pre" by auto
    with pre_subset have "q \<in> \<Q> \<A>" by auto
    with invar_pm_pim have q_in_dom: "q \<in> dom pm" unfolding class_map_invar_def by auto

    from q_iq_in it_eq have "iq = the (pm q)" by auto
    with q_in_dom have "pm q = Some iq" by auto
  } note in_it_prop = this

  from q_iq_in pm_q_eq have iq''_eq[simp]: "iq'' = iq" by (simp add: it_eq image_iff)
  from pm_q_eq invar_pm_pim have pim_iq_eq: "pim iq = Some q" unfolding class_map_invar_def by simp

  from invar_P'[unfolded map2_\<alpha>_eq P_eq] sm_q_eq 
    obtain l u where im_i_eq: "im i = Some (l, u)"
    by (auto simp add: P_eq partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def)

  from invar_P im_i_eq have "l \<le> u" "u < card (\<Q> \<A>)"
    unfolding partition_map2_invar_def P_eq
    by simp_all

  { fix q' iq'
    assume q'_iq'_in: "(q', iq') \<in> it - {(q, iq)}"
    hence pm_q'_eq: "pm q' = Some iq'" using in_it_prop [of q' iq'] by simp

    from q'_iq'_in have "(q', iq') \<noteq> (q, iq)" by simp
    with class_map_invar___pm_inj[OF invar_pm_pim, OF pm_q_eq, of q'] pm_q'_eq
    have iq'_neq_iq: "iq' \<noteq> iq" by auto

    from pm_q_eq pm_q'_eq iq'_neq_iq have "q' \<noteq> q" by auto

    from q'_iq'_in have "(q', iq') \<in> it" by simp
    
    note `(q', iq') \<in> it` `pm q' = Some iq'` `q' \<noteq> q` `iq' \<noteq> iq`
  } note in_it_diff_props = this

  {
    from invar_P'[unfolded map2_\<alpha>_eq P_eq] sm_q_eq 
       obtain iq' where iq'_props: "q = the (pim iq')" "l \<le> iq'" "iq' \<le> u"
       by (auto simp add: P_eq partition_map2_\<alpha>_def im_i_eq partition_map2_\<alpha>_im_def class_map_\<alpha>_def)

    from `iq' \<le> u` `u < card (\<Q> \<A>)` 
    have "iq' < card (\<Q> \<A>)" by simp
    with invar_pm_pim have "iq' \<in> dom pim" 
      unfolding class_map_invar_def by simp
    with `q = the (pim iq')` have pim_iq'_eq: "pim iq' = Some q" by auto

    from class_map_invar___pim_inj[OF invar_pm_pim, of iq' q iq]
    have "iq' = iq" by (simp add: pim_iq_eq pim_iq'_eq)
    with iq'_props have "l \<le> iq" "iq \<le> u" by simp_all
  } note iq_in_class = this

  from q_iq_in have "q \<in> it'" unfolding it'_def by (auto simp add: Bex_def image_iff)
  def s \<equiv> "(case Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache
               iM cache i of None \<Rightarrow> let (l, u) = partition_index_map P i in l
         | Some s \<Rightarrow> s)"

  from invar_cache_add have dom_iM_prop: "\<And>i q iq. i \<in> dom iM \<Longrightarrow>
         (q, iq) \<in> it \<Longrightarrow> snd (the (im i)) < iq"
    unfolding Hopcroft_map2_step_compute_iM_invar_cache_add_def 
    by (simp add: Let_def Ball_def partition_index_map_def P_eq)

  have invar_cache': 
      "Hopcroft_map2_step_compute_iM_invar_cache_add \<A> cm pre P (it-{(q, iq)})
         (iM', Some (i, l, u, Suc s), pm, pim) \<and> i' = i \<and> l' = l \<and> u' = u \<and> s' = s \<and>
       Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache (i \<mapsto> Suc s) = iM'(i \<mapsto> Suc s)"
  proof -
    { fix s'' iM''
      assume l_leq_Suc_s': "l \<le> Suc s'"
         and s'_le: "s' \<le> iq"
         and iM'_prop: "\<And>i q' iq'. \<lbrakk>i \<notin> dom iM; i \<in> dom iM'; (q', iq') \<in> it - {(q, iq)}\<rbrakk> \<Longrightarrow>
                               snd (the (im i)) < iq'"
         and [simp]: "iM'' = iM'" "s'' = s'"

      have "Hopcroft_map2_step_compute_iM_invar_cache_add \<A> cm pre P (it-{(q, iq)})
           (iM'', Some (i, l, u, Suc s''), pm, pim)"
      proof (intro conjI Hopcroft_map2_step_compute_iM_invar_cache_add_I refl
                       Hopcroft_map2_step_compute_iM_cache___invar_cache_I)
        fix q' iq'
        assume "(q', iq') \<in> it - {(q, iq)}"
        with in_it_prop[of q' iq']
        show "iq' = the (fst (pm, pim) q')"
          by simp
      next
        show "fst P i = Some (l, u)"
          unfolding P_eq by (simp add: im_i_eq)
      next
        show "l \<le> Suc s''" using l_leq_Suc_s' by simp
      next
        fix q' iq'
        assume q'_iq'_in: "(q', iq') \<in> it - {(q, iq)}"

          from in_it_diff_props[OF q'_iq'_in]
          have iq'_neq_iq: "iq' \<noteq> iq" by simp
        moreover
          from iq_le[of q' iq'] q'_iq'_in have "iq \<le> iq'" by simp
        moreover
          note `s' \<le> iq`
        ultimately show "Suc s'' \<le> iq'" by simp
      next
        fix i q' iq'
        assume "i \<in> dom iM''" "(q', iq') \<in> it - {(q, iq)}"

        show "snd (partition_index_map P i) < iq'"
        proof (cases "i \<in> dom iM")
          case True with dom_iM_prop[of i q' iq'] `(q', iq') \<in> it - {(q, iq)}`
          show "snd (partition_index_map P i) < iq'"
            by (simp add: P_eq partition_index_map_def)
        next
          case False note i_nin_dom_iM = this

          from `i \<in> dom iM''` have "i \<in> dom iM'" by simp
          from iM'_prop [OF i_nin_dom_iM `i \<in> dom iM'` `(q', iq') \<in> it - {(q, iq)}`]
          show "snd (partition_index_map P i) < iq'"
            by (simp add: P_eq partition_index_map_def)
        qed
      qed
    } note invar_cache_add'_intro = this

    from dom_iM_prop[of i q iq, OF _ q_iq_in] `iq \<le> u`
    have "i \<notin> dom iM" by (auto simp add: im_i_eq)

    show ?thesis
    proof (cases cache)
      case None note ch_eq[simp] = this
      from iM_cache'_eq have iM_cache'_rewrites[simp]: 
         "iM' = iM" "i' = i" "l' = l" "u' = u" "s' = l"
         by (simp_all add: Hopcroft_map2_step_compute_iM_update_cache_def 
                           Hopcroft_map2_step_compute_iM_cache___init_cache_def
                           P_eq partition_state_map_def sm_q_eq partition_index_map_def im_i_eq)

      have "s = l"
        using `i \<notin> dom iM`
        unfolding s_def ch_eq by (simp add: dom_def partition_index_map_def P_eq im_i_eq)

      show ?thesis unfolding iM_cache'_rewrites
      by (intro conjI invar_cache_add'_intro refl)
         (simp_all add:`l \<le> iq` `s = l`)
    next
      case (Some ch)
      then obtain i'' l'' u'' s'' where ch_eq: "cache = Some (i'', l'', u'', s'')" by (metis prod.exhaust)

      from invar_cache_add[unfolded ch_eq] q_iq_in have im_i''_eq: "im i'' = Some (l'', u'')" 
          and l''_le: "l'' \<le> s''" and s''_le: "s'' \<le> iq"
        by (simp_all add: Hopcroft_map2_step_compute_iM_invar_cache_add_def Ball_def it'_def[symmetric]
                          P_eq partition_index_map_def)

      have iq_le_u''_eq: "iq \<le> u'' \<longleftrightarrow> i'' = i"
      proof 
        assume "i'' = i"
        with im_i''_eq im_i_eq have "u'' = u" by simp
        with `iq \<le> u` show "iq \<le> u''" by simp
      next
        assume "iq \<le> u''"

        from im_i''_eq im_i_eq have "i \<in> dom im \<and> i'' \<in> dom im" by auto
        with invar_P'[unfolded P_eq map2_\<alpha>_eq] have i_i''_less_n: "i < n" "i'' < n"
          by (simp_all add: partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def dom_def)

        have "q \<in> class_map_\<alpha> (pm, pim) (l, u)"
          unfolding class_map_\<alpha>_def
          apply (simp) apply (rule exI[where x = iq])
          apply (simp add: pim_iq_eq `iq \<le> u` `l \<le> iq`)
        done
        moreover
        have "q \<in> class_map_\<alpha> (pm, pim) (l'', u'')"
          unfolding class_map_\<alpha>_def
          apply (simp) apply (rule exI[where x = iq])
          apply (insert l''_le s''_le)    
          apply (simp add: pim_iq_eq `iq \<le> u''`)
        done
        ultimately 
        have "class_map_\<alpha> (pm, pim) (l, u) \<inter> class_map_\<alpha> (pm, pim) (l'', u'') \<noteq> {}"
          by auto

        with partition_index_map_disj[OF invar_P'[unfolded P_eq map2_\<alpha>_eq], of i i'']
        show "i'' = i"
          by (simp add: partition_map2_\<alpha>_def partition_index_map_def  i_i''_less_n
                           partition_map2_\<alpha>_im_def im_i_eq im_i''_eq)
      qed
    
      show ?thesis
      proof (cases "i'' = i")
        case True note i''_eq = this
        with iq_le_u''_eq have iq_le_u'': "iq \<le> u''" by simp

        from i''_eq invar_cache_add have "l'' = l" "u'' = u" "l \<le> s''" and
             s''_le: "\<And>q iq. (q, iq) \<in> it \<Longrightarrow> s'' \<le> iq"
          unfolding ch_eq 
          by (simp_all add: Hopcroft_map2_step_compute_iM_invar_cache_add_def P_eq im_i_eq)
        with iM_cache'_eq iq_le_u'' have iM_cache'_rewrites[simp]: 
         "iM' = iM" "i' = i" "l' = l" "u' = u" "s' = s''"
         by (simp_all add: Hopcroft_map2_step_compute_iM_update_cache_def ch_eq iq_le_u'' i''_eq)

        have "s = s''" unfolding s_def ch_eq by (simp add: i''_eq)

        have ch_prop: "Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache (i \<mapsto> Suc s) = iM'(i \<mapsto> Suc s)"
          unfolding ch_eq by (simp add: i''_eq)

        show ?thesis unfolding iM_cache'_rewrites `s = s''`
        proof (intro conjI invar_cache_add'_intro)
          show "l \<le> Suc s'" using `l \<le> s''` by simp
        next
          from s''_le[of q iq] q_iq_in show "s' \<le> iq" by simp
        qed (simp_all add: ch_prop[unfolded `s = s''`])
      next
        case False note i''_neq_i = this

        with iq_le_u''_eq have iq_not_le_u'': "\<not>(iq \<le> u'')" by simp

        from iM_cache'_eq iq_not_le_u'' have iM_cache'_rewrites[simp]: 
         "iM' = iM(i'' \<mapsto> s'')" "i' = i" "l' = l" "u' = u" "s' = l"
         by (simp_all add: Hopcroft_map2_step_compute_iM_update_cache_def ch_eq
                           Hopcroft_map2_step_compute_iM_cache___init_cache_def
                           partition_index_map_def P_eq partition_state_map_def sm_q_eq im_i_eq )

        have "s = l" 
          using i''_neq_i `i \<notin> dom iM`
          unfolding s_def ch_eq by (simp add: dom_def partition_index_map_def P_eq im_i_eq)

        have ch_prop: "Hopcroft_map2_step_compute_iM_cache___\<alpha>_cache iM cache (i \<mapsto> Suc s) = iM'(i \<mapsto> Suc s)"
          unfolding ch_eq by simp

        show ?thesis unfolding iM_cache'_rewrites `s = l`
        proof (intro conjI invar_cache_add'_intro)
          fix i q' iq'
          assume i_in_dom: "i \<notin> dom iM" "i \<in> dom iM'"
             and "(q', iq') \<in> it - {(q, iq)}"
          from i_in_dom have "i = i''" by simp

            from iq_not_le_u'' have "u'' < iq" by simp
          moreover
            from iq_le [of q' iq'] `(q', iq') \<in> it - {(q, iq)}`
            have "iq \<le> iq'" by simp
          finally have "u'' < iq'" by simp
          thus "snd (the (im i)) < iq'" by (simp add: `i = i''` im_i''_eq)
        qed (simp_all add: `l \<le> iq` ch_prop[unfolded `s = l`])
      qed
    qed
  qed

  show ?case
    unfolding s_def[symmetric]
    apply (simp add: invar_cache')
    apply (refine_rcg)
    -- "process subgoals"
      apply (simp)
    -- "goal solved"
      apply simp
    -- "goal solved"
      apply (simp add: single_valued_def)
    -- "goal solved"
      apply (insert invar_cache') []
      apply (simp)
    -- "goal solved"
      apply simp
    -- "goal solved"
      apply simp
    -- "goal solved"
      apply (simp add: single_valued_def)
    -- "goal solved"
      apply (simp)
  proof -

    { fix q'
      assume "q' \<in> fst ` (it - {(q, iq)})"
      then obtain iq' where in_it_diff: "(q', iq') \<in> it - {(q, iq)}" by (simp add: image_iff Bex_def) metis

      with invar_cache' have "l \<le> Suc s" and "Suc s \<le> iq'"
        by (simp_all add: Hopcroft_map2_step_compute_iM_invar_cache_add_def)

      from in_it_diff_props[OF in_it_diff] have "q' \<noteq> q" "pm q' = Some iq'" by simp_all

      from invar_pm_pim `pm q' = Some iq'` 
      have pim_iq'_eq: "pim iq' = Some q'" and dom_pim: "dom pim = {i. i < card (\<Q> \<A>)} " 
         unfolding class_map_invar_def by simp_all

      from pim_iq'_eq dom_pim have "iq' < card (\<Q> \<A>)" by auto
      with `Suc s \<le> iq'` have "s \<in> dom pim" unfolding dom_pim by simp
      then obtain qs where pim_s_eq: "pim s = Some qs" by auto 
      
      from class_map_invar___pim_inj[OF invar_pm_pim, OF `pim iq' = Some q'`, of s] 
      have "q' \<noteq> qs" using `Suc s \<le> iq'`
         by (auto simp add: pim_s_eq)

      have "the (if q' = the (pim s) then Some iq else (pm(q \<mapsto> s)) q') = the (pm q')"
        by (simp add: `q' \<noteq> q` pim_s_eq `q' \<noteq> qs`)
    }
    hence "it - {(q, iq)} =
       (\<lambda>qa. (qa, the (if qa = the (pim s) then Some iq else (pm(q \<mapsto> s)) qa))) ` fst ` (it - {(q, iq)})" 
      apply (simp add: set_eq_iff image_iff)
      apply (auto simp add: it_eq Bex_def image_iff pm_q_eq)
    done

    with invar_cache'
    show "Hopcroft_map2_step_compute_iM_invar_cache_add \<A> cm pre
     P (it - {(q, iq)})
     (iM', Some (i, l, u, Suc s), pm(q \<mapsto> s, the (pim s) \<mapsto>
      iq), pim(s \<mapsto> q, iq \<mapsto> the (pim s)))" 
       by (simp add: Hopcroft_map2_step_compute_iM_invar_cache_add_def)
  qed
qed

lemma Hopcroft_map2_step_compute_iM_cache_swap_check_correct :
assumes invar_cm: "class_map_invar (\<Q> \<A>) cm"
    and pre_subset: "pre \<subseteq> dom (fst (snd P))" "pre \<subseteq> \<Q> \<A>"
    and invar_P: "partition_map2_invar (card (\<Q> \<A>)) P"
    and invar_P': "partition_map_invar (partition_map2_\<alpha> cm P)"
shows "Hopcroft_map2_step_compute_iM_cache_swap_check \<A> cm pre P \<le>  
      (Hopcroft_map2_step_compute_iM_swap_check \<A> cm pre P)"
proof -
  note loop_OK = Hopcroft_map2_step_compute_iM_cache_swap_check_loop_correct 
     [OF invar_cm pre_subset invar_P invar_P']

  have "Hopcroft_map2_step_compute_iM_cache_swap_check \<A> cm pre P \<le> \<Down>Id  
      ((Hopcroft_map2_step_compute_iM_swap_check \<A> cm pre P) \<guillemotright>= RETURN)"
    unfolding Hopcroft_map2_step_compute_iM_cache_swap_check_def
    apply (rule bind_refine)
    apply (rule loop_OK)
    apply auto
  done

  thus ?thesis by simp
qed


lemma Hopcroft_map2_step_compute_iM_cache_swap_check_correct_full :
assumes pre_subset: "pre \<subseteq> dom (fst (snd P))" "pre \<subseteq> \<Q> \<A>"
    and fin_P: "finite (dom (fst (snd P)))"
    and invar_cm: "class_map_invar (\<Q> \<A>) cm"
    and invar_P: "partition_map2_invar (card (\<Q> \<A>)) P"
    and invar_P': "partition_map_invar (partition_map2_\<alpha> cm P)"
    and is_part_P'': "is_partition (\<Q> \<A>) (partition_map_\<alpha> (partition_map2_\<alpha> cm P))"
shows "Hopcroft_map2_step_compute_iM_cache_swap_check \<A> cm pre P \<le> SPEC (\<lambda>(iM, cm').
             Hopcroft_map2_step___iM_props \<A> cm pre P iM cm' \<and>
             dom iM = partition_state_map P ` pre)"
proof -
  note Hopcroft_map2_step_compute_iM_cache_swap_check_correct[OF invar_cm pre_subset invar_P invar_P']
  also note Hopcroft_map2_step_compute_iM_swap_check_correct [OF invar_cm pre_subset]
  also note Hopcroft_map2_step_compute_iM_correct [OF pre_subset fin_P invar_cm invar_P 
     invar_P' is_part_P'']
  finally show ?thesis by simp
qed

definition Hopcroft_map2_step_no_spec where
"Hopcroft_map2_step_no_spec \<A> p a pre (P::'q partition_map2) L cm =
 (do { ASSERT (pre \<subseteq> dom (fst (snd P)) \<and> dom (fst (snd P)) \<subseteq> \<Q> \<A>); 
       (iM, cm') \<leftarrow> Hopcroft_map2_step_compute_iM_swap_check \<A> cm pre P;
       (P', L') \<leftarrow> FOREACHi (Hopcroft_map2_step_invar \<A> p a P L cm') {(p', s) . iM p' = Some s}
         (\<lambda>((p'::nat), (s::nat)) (P'::'q partition_map2, L'). do {
             ASSERT (p' \<in> dom (fst P'));
             let (pt', pct', pf', pcf') = 
                let (l, u) = partition_index_map P' p' in
                ((l, s - 1), (s - l), (s, u), Suc u - s) in
             if (pcf' = 0) then (RETURN (P', L')) else
             do {
               let (pmin, pmax) = (if (pcf' < pct') then (pf', pt') else (pt', pf'));
               ASSERT (\<forall>ai \<in> L'. snd ai < partition_free_index P');
               let L' = {(a, partition_free_index P') | a. a \<in> \<Sigma> \<A>} \<union> L';
               let P' = partition_map2_split cm' P' p' pmin pmax;
               RETURN (P', L')
             }             
          }) (P, L - {(a, p)});
       RETURN ((P', L'), cm')
     })"


lemma Hopcroft_map2_step_no_spec_correct :
fixes P :: "'q partition_map2"
  and L :: "('a \<times> nat) set"
  and \<A> :: "('q, 'a, 'X) NFA_rec_scheme"
assumes wf_A: "NFA \<A>"
    and PL_OK: "((P,L), (P', L)) \<in> Hopcroft_map2_state_rel cm (\<Q> \<A>)"
    and invar_P': "partition_map_invar P'"
    and is_part_P': "is_partition (\<Q> \<A>) (partition_map_\<alpha> P')"
shows "Hopcroft_map2_step_no_spec \<A> p a pre P L cm \<le> \<Down>Id
       (Hopcroft_map2_step \<A> p a pre P L cm)"
unfolding Hopcroft_map2_step_def Hopcroft_map2_step_no_spec_def
apply (rule ASSERT_refine_right)
apply (rule ASSERT_refine_left)
apply assumption

apply (rule bind_refine[where R'=Id])
defer
apply simp

apply (erule conjE)
apply (rule ref_two_step [where R=Id])
apply simp
apply (rule Hopcroft_map2_step_compute_iM_swap_check_correct_full)
apply (simp_all)

prefer 6
apply (simp add: subset_iff)
proof -
  obtain im sm n where P_eq[simp]: "P = (im, sm, n)" by (metis prod.exhaust)
  def im' \<equiv> "partition_map2_\<alpha>_im cm im"

  have dom_im'_eq: "dom im' = dom im" unfolding im'_def dom_def partition_map2_\<alpha>_im_def by simp 

  from PL_OK have P'_eq[simp]: "P' = (partition_map2_\<alpha> cm (im, sm, n))" and
                  map2_invar_P: "partition_map2_invar (card (\<Q> \<A>)) P" and
                  invar_cm: "class_map_invar (\<Q> \<A>) cm" 
    by (simp_all add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def im'_def
                      Hopcroft_map2_state_invar_def partition_map2_\<alpha>_def)

  from invar_cm show "class_map_invar (\<Q> \<A>) cm" .
  from map2_invar_P show "partition_map2_invar (card (\<Q> \<A>)) P" .
  from invar_P' show "partition_map_invar (partition_map2_\<alpha> cm P)" by simp
  from is_part_P' show "is_partition (\<Q> \<A>) (partition_map_\<alpha> (partition_map2_\<alpha> cm P))" by simp 
 
  assume "dom (fst (snd P)) \<subseteq> \<Q> \<A>"
  with FinSemiAutomaton.finite_\<Q>[of \<A>] wf_A
  show "finite (dom (fst (snd P)))" unfolding NFA_def by (metis finite_subset)
qed


definition Hopcroft_map2_f where
"Hopcroft_map2_f \<A> = 
 (\<lambda>((P, L), cm). do {
       ASSERT (Hopcroft_abstract_invar \<A> (Hopcroft_map_state_\<alpha> (Hopcroft_map2_state_\<alpha> cm (P, L))));
       ASSERT (L \<noteq> {});
       (a,i) \<leftarrow> SPEC (\<lambda>(a,i). (a,i) \<in> L);
       ASSERT (i \<in> dom (fst P));
       let pre = {q. \<exists>q'. q' \<in> class_map_\<alpha> cm (partition_index_map P i) \<and> (q, a, q') \<in> \<Delta> \<A>};
       (PL', cm') \<leftarrow> Hopcroft_map2_step_no_spec \<A> i a pre P L cm;
       RETURN (PL', cm')
     })"


lemma (in DFA) Hopcroft_map2_f_correct :
assumes PL_OK: "(PLc, PL') \<in> Hopcroft_map2_state_rel_full (\<Q> \<A>)"
    and invar_P': "partition_map_invar (fst PL')"
shows "Hopcroft_map2_f \<A> PLc \<le> \<Down>(Hopcroft_map2_state_rel_full (\<Q> \<A>)) (Hopcroft_map_f \<A> PL')"
proof -
  obtain P L cm where PLc_eq[simp]: "PLc = ((P, L), cm)" by (metis prod.exhaust)
  obtain P' L' where PL'_eq[simp]: "PL' = (P', L')" by (rule prod.exhaust)
  obtain im sm n where P_eq: "P = (im, sm, n)" by (metis prod.exhaust)

  from PL_OK have 
    PL_\<alpha>: "Hopcroft_map2_state_\<alpha> cm (P, L) = (P', L')" and
    PL_invar: "Hopcroft_map2_state_invar (\<Q> \<A>) cm (P, L)"
    unfolding Hopcroft_map2_state_rel_full_def
    by simp_all

  from PL_\<alpha> have L'_eq: "L' = L" and
                 P'_eq: "P' = partition_map2_\<alpha> cm P"
     unfolding Hopcroft_map2_state_\<alpha>_def
     by (simp_all)

  note Hopcroft_map2_step_no_spec_correct_full =
     conc_trans_additional(2) [OF Hopcroft_map2_step_no_spec_correct Hopcroft_map2_step_correct]

  show ?thesis
    using [[goals_limit = 1]]
    unfolding Hopcroft_map_f_def Hopcroft_map2_f_def
    apply simp
    apply (refine_rcg)
    -- "process goals"
      apply (simp only: PL_\<alpha>)
    -- "goal solved"
      apply (simp add: L'_eq)
    -- "goal solved"
      apply (subgoal_tac "RES L \<le> \<Down> Id (RES L')")
      apply assumption
      apply (simp add: L'_eq)
    -- "goal solved"
      apply simp apply clarify
      apply (simp add: P'_eq P_eq partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def)
      apply metis
    -- "goal solved"
      apply simp
      apply clarify
      apply simp
      apply (rename_tac a i p l u)
      apply (rule_tac Hopcroft_map2_step_no_spec_correct_full)
    -- "new subgoals"
      apply (simp add: NFA_axioms)
    -- "goal solved"    
      apply (simp add: Hopcroft_map2_state_rel_def Hopcroft_map2_state_\<alpha>_def P'_eq PL_invar)
    -- "goal solved"
      apply (insert invar_P')[]
      apply (simp add: P'_eq P_eq partition_map2_\<alpha>_def)
    -- "goal solved"
      apply (simp add: Hopcroft_abstract_invar_def Hopcroft_map_state_\<alpha>_def
                       is_weak_language_equiv_partition_def P_eq Hopcroft_map2_state_\<alpha>_def)
    -- "goal solved"    
      apply (insert PL_OK)[]
      apply (simp add: Hopcroft_map2_state_rel_full_def Hopcroft_map2_state_rel_def L'_eq)
    -- "goal solved"
      apply (insert invar_P') []
      apply (simp add: P_eq P'_eq partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def dom_def)
      apply auto[]
    -- "goal solved"   
      apply (insert invar_P') []
      apply simp
    -- "goal solved"   
      apply (simp add: P_eq P'_eq partition_index_map_def partition_map2_\<alpha>_def
                       partition_map2_\<alpha>_im_def)
    -- "goal solved"
      apply (simp add: L'_eq)    
    -- "goal solved"
      apply (unfold Hopcroft_map2_state_rel_full_def)
      apply (rule br_single_valued)
    -- "goal solved"
      apply (simp add: Hopcroft_map2_state_rel_def)
  done
qed

definition class_map_init_pred where
  "class_map_init_pred \<A> cm s m \<longleftrightarrow>
   (class_map_invar (\<Q> \<A>) cm \<and>
    s = card (\<Q> \<A> - \<F> \<A>) \<and>
    m = card (\<Q> \<A>) \<and>
    ((\<Q> \<A> \<noteq> {}) \<longrightarrow> 
      class_map_\<alpha> cm (s, card (\<Q> \<A>) - 1) = \<F> \<A> \<and>
      (0 < s \<longrightarrow> class_map_\<alpha> cm (0, s - 1) = \<Q> \<A> - \<F> \<A>)
    ))"

fun class_map_add_set_invar where
 "class_map_add_set_invar Q (pm, pim) m S = (\<lambda>((pm', pim'), m').
       (class_map_invar (Q \<union> S) (pm', pim')) \<and>
       (m' = card (Q \<union> S)) \<and>
       (\<forall>q \<in> Q. pm' q = pm q) \<and>
       (\<forall>n. n < m \<longrightarrow> pim' n = pim n))"

definition class_map_add_set ::
  "'q set \<Rightarrow> ('q class_map) \<Rightarrow> nat \<Rightarrow> 'q set \<Rightarrow> ('q class_map \<times> nat) nres" where
  "class_map_add_set Q cm m S = 
   FOREACHi (\<lambda>S'. class_map_add_set_invar Q cm m (S - S')) 
     S (\<lambda>q ((pm, pim), m). RETURN ((pm (q \<mapsto> m), pim (m \<mapsto> q)), Suc m)) (cm, m)"
   
lemma class_map_add_set_correct :
fixes pm pim m S
assumes fin_S: "finite S"
    and fin_Q: "finite Q"
    and m_eq: "m = card Q"
    and invar_cm: "class_map_invar Q (pm, pim)"
    and QS_dist: "Q \<inter> S = {}"
shows "class_map_add_set Q (pm, pim) m S \<le> SPEC (class_map_add_set_invar Q (pm, pim) m S)"
unfolding class_map_add_set_def
apply (rule FOREACHi_rule)
apply (simp add: fin_S)
apply (simp add: m_eq invar_cm)
defer
apply (simp, clarify)+
apply simp
apply (rename_tac q S' pm' pim')
apply (intro conjI)
proof -
  fix q S' pm' pim'
  assume "q \<in> S'" "S' \<subseteq> S"
     and invar_cm': "class_map_invar (Q \<union> (S - S')) (pm', pim')"
     and pm_eq: "\<forall>q\<in>Q. pm' q = pm q"
     and pim_eq: "\<forall>n<m. pim' n = pim n"
  let ?S1 = "Q \<union> (S - S')"
  let ?S2 = "Q \<union> (S - (S' - {q}))"
  let ?m' = "card (Q \<union> (S - S'))"

  from `q \<in> S'` `S' \<subseteq> S` have q_in_S: "q \<in> S" by blast
  with QS_dist have q_nin_Q: "q \<notin> Q" by auto

  from `q \<notin> Q` show "q \<in> Q \<longrightarrow> Some ?m' = pm q" by simp

  from card_Un_disjoint[OF fin_Q, of "S - S'"] fin_S QS_dist m_eq
  have m'_eq: "?m' = m + card (S - S')" by auto

  from m'_eq show "?m' < m \<longrightarrow> Some q = pim ?m'" by simp


  from q_in_S have S2_eq: "?S2 = insert q ?S1" by auto
  have fin_S1: "finite ?S1" by (intro finite_UnI fin_Q finite_Diff fin_S)
  have q_nin_S1: "q \<notin> ?S1" by (simp add: q_nin_Q `q \<in> S'`)

  from card_insert_disjoint[of ?S1 q, OF fin_S1 q_nin_S1]
  show card_S2_eq[symmetric]: "Suc (card ?S1) = card ?S2" unfolding S2_eq by simp

  from invar_cm' have "?m' \<notin> dom pim'"
    unfolding class_map_invar_def by auto
  hence pim'_m'_eq: "pim' ?m' = None" by blast

  have pim'_neq_q: "\<And>i. pim' i \<noteq> Some q"
  proof (rule notI)
    fix i 
    assume "pim' i = Some q"
    with invar_cm' have "pm' q = Some i"
      unfolding class_map_invar_def by simp
    hence "q \<in> dom pm'" by blast
    with invar_cm' have "q \<in> Q \<union> (S - S')"
      unfolding class_map_invar_def by simp
    thus False using q_nin_Q `q \<in> S'` by simp
  qed

  from invar_cm' card_S2_eq
  show "class_map_invar ?S2 (pm'(q \<mapsto> ?m'), pim'(?m' \<mapsto> q))"
    unfolding class_map_invar_def S2_eq
    by (auto simp add: pim'_m'_eq pim'_neq_q)
qed


definition class_map_init_pred_compute where
  "class_map_init_pred_compute QF F = do {
    (cm, s) \<leftarrow> class_map_add_set {} (empty, empty) 0 QF;
    (cm', m) \<leftarrow> class_map_add_set QF cm s F;
    RETURN (cm', s, m)
  }"

lemma (in DFA) class_map_init_pred_compute_correct :
  "class_map_init_pred_compute (\<Q> \<A> - \<F> \<A>) (\<F> \<A>) \<le>
   SPEC (\<lambda>(cm, s, m). class_map_init_pred \<A> cm s m)"
unfolding class_map_init_pred_compute_def
  apply (rule refine_vcg)+
  apply (rule conc_trans_additional(6) [OF class_map_add_set_correct])
    apply (simp add: finite_\<Q>)
    apply simp
    apply simp
    apply (simp add: class_map_invar_def)
    apply simp
  apply (simp add: subset_iff)
  apply (intro allI impI)
  apply (rename_tac pm pim)
  apply (rule refine_vcg)+
  apply (rule conc_trans_additional(6) [OF class_map_add_set_correct])
  apply (simp_all add: subset_iff Ball_def finite_\<Q> finite_\<F>)  
  apply auto[]
  apply clarify
  apply (rename_tac pm' pim')
proof -
  fix pm pim pm' pim'

  assume invar_cm': "class_map_invar (\<Q> \<A> \<union> \<F> \<A>) (pm', pim')"
     and invar_cm: "class_map_invar (\<Q> \<A> - \<F> \<A>) (pm, pim)"
     and pm_eq: "\<forall>x. x \<in> \<Q> \<A> \<and> x \<notin> \<F> \<A> \<longrightarrow> pm' x = pm x"
     and pim_eq: "\<forall>n<card (\<Q> \<A> - \<F> \<A>). pim' n = pim n"
  from \<F>_consistent have [simp]: "\<Q> \<A> \<union> \<F> \<A> = \<Q> \<A>" by auto

  from invar_cm have pm_pim_connected: "\<And>q i. (pm q = Some i) = (pim i = Some q)" 
                 and dom_pm_eq: "dom pm = \<Q> \<A> - \<F> \<A> "
                 and dom_pim_eq: "dom pim =  {i. i < card (\<Q> \<A> - \<F> \<A>)}"
    unfolding class_map_invar_def by simp_all

  from invar_cm' have pm'_pim'_connected: "\<And>q i. (pm' q = Some i) = (pim' i = Some q)" 
                  and dom_pm'_eq: "dom pm' = \<Q> \<A>"
                  and dom_pim'_eq: "dom pim' =  {i. i < card (\<Q> \<A>)}"
    unfolding class_map_invar_def by simp_all


  have part1: "0 < card (\<Q> \<A> - \<F> \<A>) \<Longrightarrow>
     class_map_\<alpha> (pm', pim') (0, card (\<Q> \<A> - \<F> \<A>) - Suc 0) = \<Q> \<A> - \<F> \<A>" 
  proof -
    assume "0 < card (\<Q> \<A> - \<F> \<A>)"

    hence dom_pim_eq_intro: "{i. 0 \<le> i \<and> i \<le> card (\<Q> \<A> - \<F> \<A>) - Suc 0} = dom pim"
      unfolding dom_pim_eq by auto

    from pim_eq dom_pim_eq 
    have image_dom_pim_eq: "(\<lambda>i. the (pim' i)) ` dom pim = (\<lambda>i. the (pim i)) ` dom pim"
      unfolding class_map_invar_def
      apply (rule_tac set_eqI)
      apply (simp add: image_iff Bex_def)
    done
    
    have image_dom_pim_eq2: "(\<lambda>i. the (pim i)) ` dom pim = {q . \<exists>i. pim i = Some q}"
      apply (intro set_eqI iffI)
      apply auto[]
      apply (simp add: image_iff Bex_def dom_def)
      apply (metis the.simps)
    done

    from pm_pim_connected[symmetric] dom_pm_eq
    have dom_pm_eq: "{q . \<exists>i. pim i = Some q} = \<Q> \<A> - \<F> \<A>"
      by (simp add: dom_def)

    show "class_map_\<alpha> (pm', pim') (0, card (\<Q> \<A> - \<F> \<A>) - Suc 0) = \<Q> \<A> - \<F> \<A>" 
      unfolding class_map_\<alpha>_alt_def dom_pim_eq_intro
      unfolding image_dom_pim_eq image_dom_pim_eq2 dom_pm_eq
      ..
  qed

  have part2: "\<Q> \<A> \<noteq> {} \<Longrightarrow>
    class_map_\<alpha> (pm', pim') (card (\<Q> \<A> - \<F> \<A>), card (\<Q> \<A>) - Suc 0) = \<F> \<A>" 
  proof -
    assume "\<Q> \<A> \<noteq> {}"
    hence less_card: "0 < card (\<Q> \<A>)" using finite_\<Q> by auto
    from less_card have less_eq_pre_card: "\<And>i. i \<le> card (\<Q> \<A>) - Suc 0 \<longleftrightarrow> i < card (\<Q> \<A>)" by auto


    from card_Diff_subset[OF finite_\<F> \<F>_consistent]
    have card_QF_le: "card (\<Q> \<A> - \<F> \<A>) \<le> card (\<Q> \<A>)" by simp

    def new_is \<equiv> "{i. card (\<Q> \<A> - \<F> \<A>) \<le> i \<and> i \<le> card (\<Q> \<A>) - Suc 0}"

    from dom_pim'_eq less_card have step1:
        "(\<lambda>i. the (pim' i)) ` new_is = {q . \<exists>i \<in> new_is. pim' i = Some q}"
      unfolding new_is_def 
      apply (simp add: set_eq_iff dom_def image_iff less_eq_pre_card)
      apply (metis the.simps)
    done

    have new_is_F_connection: "\<And>q i. pm' q = Some i \<Longrightarrow> (i \<in> new_is \<longleftrightarrow> q \<in> \<F> \<A>)"
    proof -
      fix q i
      assume pm'_q_eq: "pm' q = Some i"
      with pm'_pim'_connected[of q i] have pim'_i_eq: "pim' i = Some q" by simp

      from dom_pm'_eq[symmetric] have "q \<in> \<Q> \<A>" by (simp add: dom_def pm'_q_eq)

      from pm'_pim'_connected[of q i] have "i \<in> dom pim'" 
        by (simp add: dom_def pm'_q_eq)
      with dom_pim'_eq have "i < card (\<Q> \<A>)" by simp

      show "i \<in> new_is \<longleftrightarrow> q \<in> \<F> \<A>"
      proof (intro iffI)
        assume "i \<in> new_is"
        hence "i \<notin> dom pim"
          unfolding new_is_def dom_pim_eq by auto

        show "q \<in> \<F> \<A>"
        proof (rule ccontr)
          assume "q \<notin> \<F> \<A>"
          with `q \<in> \<Q> \<A>` pm_eq pm'_q_eq have "pm q = Some i"
            by simp
          with pm_pim_connected[of q i] have "pim i = Some q" by simp
          hence "i \<in> dom pim" by blast
          with `i \<notin> dom pim` show False ..
        qed
      next
        assume "q \<in> \<F> \<A>"
        hence "q \<notin> dom pm" unfolding dom_pm_eq by simp

        show "i \<in> new_is"
        proof (rule ccontr)
          assume "i \<notin> new_is"
          with `i < card (\<Q> \<A>)` have "i < card (\<Q> \<A> - \<F> \<A>)"
            unfolding new_is_def by auto
          with pim_eq pim'_i_eq have "pim i = Some q" by simp
          with pm_pim_connected[of q i] have "pm q = Some i" by simp
          hence "q \<in> dom pm" by blast
          with `q \<notin> dom pm` show False ..
        qed
      qed
    qed

    from invar_cm' have "\<And>q i. (pim' i = Some q) = (pm' q = Some i)"
      unfolding class_map_invar_def dom_def
      by simp
    hence step2: "{q . \<exists>i \<in> new_is. pim' i = Some q} = {q. \<exists>x. q \<in> \<F> \<A> \<and> pm' q = Some x}"
      apply (simp add: Bex_def)
      apply (auto simp add: new_is_F_connection)
    done
    
    have step3: "{q. \<exists>x. q \<in> \<F> \<A> \<and> pm' q = Some x} = (\<F> \<A>)"
      using dom_pm'_eq \<F>_consistent
      by auto

    show "class_map_\<alpha> (pm', pim') (card (\<Q> \<A> - \<F> \<A>), card (\<Q> \<A>) - Suc 0) = \<F> \<A>" 
      unfolding class_map_\<alpha>_alt_def new_is_def[symmetric] step1 step2 step3
      ..
  qed

  from invar_cm'
  show "class_map_init_pred \<A> (pm', pim') (card (\<Q> \<A> - \<F> \<A>)) (card (\<Q> \<A> \<union> \<F> \<A>))"
    by (simp add: class_map_init_pred_def part1 part2)
qed

definition partition_map2_init where
  "partition_map2_init \<A> s (m::nat) =   
   (if (s = 0) then
      (partition_map_sing (0, m - 1) (\<Q> \<A>))
    else 
      (empty (0 \<mapsto> (s, m - 1)) (1 \<mapsto> (0, s - 1)),
       (\<lambda>q. if (q \<in> \<F> \<A>) then Some 0 else
            if (q \<in> \<Q> \<A> - \<F> \<A>) then Some (1::nat) else None),
       (2::nat)))"

definition Hopcroft_map2_init where
  "Hopcroft_map2_init \<A> cm s m = ((partition_map2_init \<A> s m, {(a, 0) | a. a \<in> \<Sigma> \<A>}), cm)" 

definition Hopcroft_map2 where
  "Hopcroft_map2 \<A> = 
   do {
      (cm, card_QF, card_Q) \<leftarrow> SPEC (\<lambda>(cm, card_QF, card_Q). class_map_init_pred \<A> cm card_QF card_Q);
      (if (card_Q = 0) then RETURN (partition_map_empty, cm) else (
       if (card_Q = card_QF) then 
          RETURN (partition_map_sing (0, card_Q - 1) (\<Q> \<A>), cm) 
       else (
         do {
           ((P, _), cm') \<leftarrow> WHILEIT (\<lambda>(PL, cm). Hopcroft_map2_state_invar (\<Q> \<A>) cm PL \<and>
                                         Hopcroft_map_state_invar (Hopcroft_map2_state_\<alpha> cm PL))
                            (\<lambda>PL. (snd (fst PL) \<noteq> {}))
                            (Hopcroft_map2_f \<A>) (Hopcroft_map2_init \<A> cm card_QF card_Q);
           RETURN (P, cm')
         })))
    }" 

lemma (in DFA) Hopcroft_map2_correct :
shows  "Hopcroft_map2 \<A> \<le> \<Down>(br (\<lambda>(P, cm). partition_map2_\<alpha> cm P)
                                    (\<lambda>(P, cm). partition_map2_invar (card (\<Q> \<A>)) P)) (Hopcroft_map \<A>)"
unfolding Hopcroft_map_def Hopcroft_map2_def
apply (rule pw_bind_leI)
apply simp
apply refine_rcg
apply (simp_all del: br_def)
prefer 10
apply (rule Hopcroft_map2_f_correct)
prefer 8
apply (unfold Hopcroft_map2_state_rel_full_def)
apply (rule br_single_valued)
apply simp_all

apply (simp_all split: prod.splits add: Hopcroft_map2_state_rel_full_def Hopcroft_map2_state_\<alpha>_def
                Hopcroft_map2_state_invar_def del: br_def)
-- "process subgaols"
   apply clarify
   apply (simp add: Hopcroft_map_state_invar_def)
-- "goal solved"
   apply (simp add: class_map_init_pred_def finite_\<Q>)
-- "goal solved"
defer
   apply (clarify, simp)
   apply (rename_tac pm pim s m)
defer
   apply (clarify, simp)
   apply (rename_tac pm pim m)
defer
   apply (clarify, simp)
   apply (rename_tac pm pim s m sm im n L pm' pim')
defer
proof -
  fix cm :: "'q class_map"
  show "partition_map_empty = partition_map2_\<alpha> cm partition_map_empty \<and>
        partition_map2_invar 0 partition_map_empty"
     by (simp add: partition_map_empty_def partition_map2_\<alpha>_def
                   partition_map2_\<alpha>_im_def partition_map2_invar_def)
next
  fix pm pim s m
  assume "class_map_init_pred \<A> (pm, pim) s m" "0 < m"
  hence s_eq: "s = card (\<Q> \<A> - \<F> \<A>)" and m_eq: "m = card (\<Q> \<A>)"
    unfolding class_map_init_pred_def by simp_all

  from `0 < m` obtain m' where m_eq': "m = Suc m'" by (cases m, auto)

  from card_Diff_subset[OF finite_\<F> \<F>_consistent] m_eq s_eq
  have s_eq': "s = m - card (\<F> \<A>)" by simp

  show "(m = s) = (\<F> \<A> = {})"
  proof
    assume "\<F> \<A> = {}"
    with s_eq' show "m = s" by simp
  next
    assume "m = s"
    with s_eq' have "card (\<F> \<A>) = 0" 
      by (simp add: m_eq')
    with finite_\<F> show "\<F> \<A> = {}" by simp
  qed   
next
  fix pm pim m
  assume Q_neq_emp: "\<Q> \<A> \<noteq> {}"
     and F_eq_emp: "\<F> \<A> = {}"
     and pred_cm: "class_map_init_pred \<A> (pm, pim) m m"
  with finite_\<Q> have card_greater: "0 < card (\<Q> \<A>)" by auto

  from pred_cm have m_eq: "m = card (\<Q> \<A>)"
     by (simp add: class_map_init_pred_def class_map_\<alpha>_def 
              split: prod.splits)
  
  with pred_cm F_eq_emp Q_neq_emp card_greater 
  have Q_eq: "class_map_\<alpha> (pm, pim) (0, m - Suc 0) = \<Q> \<A>"
    by (simp add: class_map_init_pred_def)
 
  from card_greater
  show "partition_map_sing (\<Q> \<A>) (\<Q> \<A>) =
       partition_map2_\<alpha> (pm, pim) (partition_map_sing (0, m - Suc 0) (\<Q> \<A>)) \<and>
       partition_map2_invar (card (\<Q> \<A>)) (partition_map_sing (0, m - Suc 0) (\<Q> \<A>))" 
     apply (simp add: partition_map_sing_def partition_map2_\<alpha>_def
                   partition_map2_\<alpha>_im_def partition_map2_invar_def)
     apply (subst fun_eq_iff)
     apply (simp add: Q_eq m_eq[symmetric])
  done
next
  fix im :: "nat \<Rightarrow> (nat \<times> nat) option"
  fix sm :: "'q => nat option"
  fix n :: nat
  fix L :: "('a \<times> nat) set"
  fix pm :: "'q \<Rightarrow> nat option" 
  fix pim :: "nat \<Rightarrow> 'q option"
  fix pm' :: "'q \<Rightarrow> nat option" 
  fix pim' :: "nat \<Rightarrow> 'q option"
  fix s m

  assume QF_neq_emp: "\<Q> \<A> \<noteq> {}" "\<F> \<A> \<noteq> {}"
     and init_eq: "Hopcroft_map2_init \<A> (pm, pim) s m = (((im, sm, n), L), pm', pim')"
     and pred_cm: "class_map_init_pred \<A> (pm, pim) s m"
     and "0 < m"

  from finite_\<Q> finite_\<F> `\<Q> \<A> \<noteq> {}` `\<F> \<A> \<noteq> {}` 
  have card_greater: "0 < card (\<Q> \<A>)" "0 < card (\<F> \<A>)" by auto 

  from init_eq have 
     map2_init_eq: "partition_map2_init \<A> s m = (im, sm, n)" and
     L_eq[simp]: "L = {(a, 0) |a. a \<in> \<Sigma> \<A>}" and 
     cm_eq[simp]: "pm' = pm" "pim' = pim" 
  by (simp_all add: Hopcroft_map2_init_def)

  from pred_cm have 
     invar_cm: "class_map_invar (\<Q> \<A>) (pm, pim)" and
     s_eq: "s = card (\<Q> \<A>) - card (\<F> \<A>)" and
     m_eq: "m = card (\<Q> \<A>)" and
     Fc_eq[simp]: "class_map_\<alpha> (pm, pim) (s, m - Suc 0) = \<F> \<A>" and
     QFc_eq: "0 < s \<Longrightarrow> class_map_\<alpha> (pm, pim) (0, s - Suc 0) = \<Q> \<A> - \<F> \<A>"
    using card_Diff_subset[OF finite_\<F> \<F>_consistent] 
    apply (simp_all add: class_map_init_pred_def QF_neq_emp)
    apply auto
  done

  show "Hopcroft_map_init \<A> = (partition_map2_\<alpha> (pm', pim') (im, sm, n), L) \<and>
        partition_map2_invar (card (\<Q> \<A>)) (im, sm, n) \<and>
        class_map_invar (\<Q> \<A>) (pm', pim')"
  proof (cases "\<Q> \<A> - \<F> \<A> = {}")
    case True note QF_eq = this
    from QF_eq \<F>_consistent have F_eq[simp]: "\<F> \<A> = \<Q> \<A>" by simp
    with s_eq have s_eq_0[simp]: "s = 0" by simp

    from map2_init_eq[symmetric] have 
        im_eq: "im = [0 \<mapsto> (0, m - Suc 0)]" and
        sm_eq: "sm = (\<lambda>q. if q \<in> \<Q> \<A> then Some 0 else None)" and
        n_eq: "n = Suc 0"
      by (simp_all add: partition_map2_init_def partition_map_sing_def)
 
    from Fc_eq `0 < m`
    show ?thesis
      apply (simp add: invar_cm Hopcroft_map_init_def partition_map2_invar_def im_eq card_greater)
      apply (simp add: partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def
                       partition_map_init_def QF_eq partition_map_sing_def n_eq sm_eq)
      apply (simp add: fun_eq_iff m_eq[symmetric])
    done
  next
    case False note QF_eq = this

    from QF_eq finite_\<Q> have "card (\<Q> \<A> - \<F> \<A>) > 0" by auto
    with card_Diff_subset[OF finite_\<F> \<F>_consistent] s_eq QF_eq 
    have s_neq_0: "0 < s" by auto

    from s_eq card_greater have s_le: "s \<le> m - Suc 0" "s - Suc 0 < m" unfolding m_eq by auto
                                
    from s_neq_0 map2_init_eq[symmetric] have 
        im_eq: "im = [0 \<mapsto> (s, m - Suc 0), Suc 0 \<mapsto> (0, s - Suc 0)]" and
        sm_eq: "sm = (\<lambda>q. if q \<in> \<F> \<A> then Some 0 else if q \<in> \<Q> \<A> then Some 1 else None)" and
        n_eq: "n = 2"
      by (simp_all add: partition_map2_init_def cong: if_cong)
 
    from QFc_eq QF_eq `0 < m`
    show ?thesis
      apply (simp add: invar_cm Hopcroft_map_init_def partition_map2_invar_def im_eq card_greater
                       s_le s_neq_0 m_eq[symmetric])
      apply (simp add: partition_map2_\<alpha>_def partition_map2_\<alpha>_im_def
                       partition_map_init_def QF_eq partition_map_sing_def n_eq sm_eq)
      apply (simp add: fun_eq_iff)
    done    
  qed
qed

lemma (in DFA) Hopcroft_map2_correct_full :
shows "Hopcroft_map2 \<A> \<le> SPEC (\<lambda>(P, cm'). 
    (partition_map_\<alpha> (partition_map2_\<alpha> cm' P) = Myhill_Nerode_partition \<A>) \<and>
    partition_map_invar (partition_map2_\<alpha> cm' P))"
proof -
  note Hopcroft_map2_correct 
  also note Hopcroft_map_correct 
  also note Hopcroft_abstract_correct 
  finally show ?thesis by (simp add: pw_le_iff refine_pw_simps)
qed


subsection \<open> Code Generation \<close>

locale Hopcroft_impl_locale =
  s : StdSet s_ops +
  sm : StdMap sm_ops +
  im : StdMap im_ops +
  pm : StdMap pm_ops +
  pim : StdMap pim_ops +
  iM : StdMap iM_ops +
  sm_it :  set_iteratei "set_op_\<alpha> s_ops" "set_op_invar s_ops" sm_it +
  cm_it :  set_iteratei "set_op_\<alpha> s_ops" "set_op_invar s_ops" cm_it +
  pre_it :  set_iteratei s2_\<alpha> s2_invar pre_it +
  pre_it2 :  set_iteratei s2_\<alpha> s2_invar pre_it2 +
  iM_it :  map_iteratei "map_op_\<alpha> iM_ops" "map_op_invar iM_ops" iM_it
  for s_ops :: "('q, 'q_set, _) set_ops_scheme" 
  and s2_\<alpha> :: "'q_set2 \<Rightarrow> 'q set" and s2_invar
  and sm_ops :: "('q, nat, 'sm, _) map_ops_scheme" 
  and im_ops :: "(nat, nat \<times> nat, 'im, _) map_ops_scheme" 
  and pm_ops :: "('q, nat, 'pm, _) map_ops_scheme" 
  and pim_ops :: "(nat, 'q, 'pim, _) map_ops_scheme" 
  and iM_ops :: "(nat, nat, 'iM, _) map_ops_scheme" 
  and sm_it :: "'q_set \<Rightarrow> ('q, 'sm) set_iterator"
  and cm_it :: "'q_set \<Rightarrow> ('q, ('pm \<times> 'pim) \<times> nat) set_iterator"
  and pre_it :: "'q_set2 \<Rightarrow> ('q, 'iM \<times> 'pm \<times> 'pim) set_iterator"
  and pre_it2 :: "'q_set2 \<Rightarrow> ('q, ('q \<times> nat) list) set_iterator"
  and iM_it :: "'iM \<Rightarrow> (nat \<times> nat, ('im \<times> 'sm \<times> nat) \<times> ('a \<times> nat) list) set_iterator"
begin

definition "iM_rel \<equiv> build_rel iM.\<alpha> iM.invar"
lemma iM_RELEATES[refine_dref_RELATES]: 
  "RELATES iM_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued iM_rel" unfolding iM_rel_def by blast

definition "L_rel \<equiv> build_rel (set::(('a \<times> nat) list \<Rightarrow> ('a \<times> nat) set)) distinct"
lemma [simp]: "single_valued L_rel" unfolding L_rel_def by blast

definition "pm_rel \<equiv> build_rel pm.\<alpha> pm.invar"
lemma pm_RELEATES[refine_dref_RELATES]: 
  "RELATES pm_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued pm_rel" unfolding pm_rel_def by blast

definition "pim_rel \<equiv> build_rel pim.\<alpha> pim.invar"
lemma pim_RELEATES[refine_dref_RELATES]: 
  "RELATES pim_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued pim_rel" unfolding pim_rel_def by blast

definition "s_rel \<equiv> build_rel s.\<alpha> s.invar"
lemma s_RELEATES[refine_dref_RELATES]: 
  "RELATES s_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued s_rel" unfolding s_rel_def by blast

definition "s2_rel \<equiv> build_rel s2_\<alpha> s2_invar"
lemma s2_RELEATES[refine_dref_RELATES]: 
  "RELATES s2_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued s2_rel" unfolding s2_rel_def by blast

definition "sm_rel \<equiv> build_rel sm.\<alpha> sm.invar"
lemma sm_RELEATES[refine_dref_RELATES]: 
  "RELATES sm_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued sm_rel" unfolding sm_rel_def by blast

definition "im_rel \<equiv> build_rel im.\<alpha> im.invar"
lemma im_RELEATES[refine_dref_RELATES]: 
  "RELATES im_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued im_rel" unfolding im_rel_def by blast

definition "part_rel \<equiv> rprod im_rel (rprod sm_rel (Id::(nat \<times> nat) set))"
lemma part_rel_RELEATES[refine_dref_RELATES]: 
  "RELATES part_rel" by (simp add: RELATES_def)
lemma [simp]: "single_valued part_rel" unfolding part_rel_def 
by (intro rprod_sv) (simp_all)

definition partition_impl_empty where
  "partition_impl_empty = (\<lambda>_::unit. (im.empty(), sm.empty(), 0::nat))"

lemma partition_impl_empty_correct [refine] :
 "(partition_impl_empty (), partition_map_empty) \<in> part_rel"
  unfolding partition_impl_empty_def partition_map_empty_def part_rel_def
  by (simp add: sm.correct im.correct im_rel_def sm_rel_def refine_hsimp)


definition sm_update_init where
  "sm_update_init Q n sm = sm_it Q (\<lambda>_. True) (\<lambda>q sm. sm.update q n sm) sm"

lemma sm_update_init_correct :
assumes sm_OK: "(sm, sm') \<in> sm_rel"
    and Q_OK: "(Q, Q') \<in> s_rel"
    and n_OK: "n' = n"
shows "(sm_update_init Q n sm, \<lambda>q. if (q \<in> Q') then Some n' else sm' q) \<in> sm_rel"
unfolding sm_update_init_def sm_rel_def 
using assms
apply simp
apply (rule_tac sm_it.iteratei_rule_insert_P [where I = "\<lambda>Q \<sigma>.  sm.invar \<sigma> \<and> sm.\<alpha> \<sigma> = (\<lambda>q. if q \<in> Q then Some n else sm.\<alpha> sm q)"])
apply (auto simp add: sm.correct s_rel_def sm_rel_def)
done

fun sm_update where
   "sm_update n sm pim p (0::nat) = sm"
 | "sm_update n sm pim p m = 
    (let q = the (pim.lookup p pim) in
     let sm = sm.update q n sm in
     sm_update n sm pim (Suc p) (m - 1))"

lemma sm_update_correct :
assumes invar_sm: "sm.invar sm"
    and invar_pim: "pim.invar pim"
shows "(sm_update n sm pim l ((Suc u) - l), 
        \<lambda>q. if (q \<in> class_map_\<alpha> (pm, pim.\<alpha> pim) (l, u)) then Some n else sm.\<alpha> sm q) \<in> sm_rel"
using invar_sm
proof (induct "(Suc u) - l" arbitrary: l sm)
  case 0 
  note m_eq[symmetric] = 0(1)
  note invar_sm = 0(2)

  from m_eq
  show ?case
    apply (simp add: invar_sm class_map_\<alpha>_def sm_rel_def)
    apply (rule ext)
    apply auto
  done
next
  case (Suc m) 
  note suc_m_eq[symmetric] = Suc(2)

  hence m_eq: "m = Suc u - Suc l" by simp
  note ind_hyp = Suc(1)[OF m_eq]
  note invar_sm = Suc(3)

  def sm' \<equiv> "sm.update (the (pim.lookup l pim)) n sm"
  from invar_sm have invar_sm': "sm.invar sm'" unfolding sm'_def by (simp add: sm.correct)  

  { fix q
    have "(if q \<in> class_map_\<alpha> (pm, pim.\<alpha> pim) (Suc l, u) then Some n
             else map_op_\<alpha> sm_ops sm' q) =
          (if q \<in> class_map_\<alpha> (pm, pim.\<alpha> pim) (l, u) then Some n
             else map_op_\<alpha> sm_ops sm q)"
    proof (cases "q \<in> class_map_\<alpha> (pm, pim.\<alpha> pim) (Suc l, u)")
      case True note q_in_suc_l = this
      hence "q \<in> class_map_\<alpha> (pm, pim.\<alpha> pim) (l, u)"
        by (auto simp add: class_map_\<alpha>_def)
      thus ?thesis by (simp add: q_in_suc_l)
    next
      case False note q_nin_suc_l = this

      with suc_m_eq 
      have q_in_l_eq: "q \<in> class_map_\<alpha> (pm, map_op_\<alpha> pim_ops pim) (l, u) \<longleftrightarrow> 
                       q = the (map_op_\<alpha> pim_ops pim l)"
        apply (auto simp add: class_map_\<alpha>_def)
        apply (metis le_antisym not_less_eq_eq)
      done
         
      show ?thesis 
        by (simp add: q_nin_suc_l q_in_l_eq sm'_def sm.correct invar_sm 
                      pim.correct invar_pim)
    qed
  }
  with ind_hyp[OF invar_sm'] invar_sm' invar_sm
  show ?case
    by (simp add: suc_m_eq sm.correct m_eq sm'_def[symmetric])
qed

lemma sm_update_correctI :
assumes invar_sm: "sm.invar sm"
    and invar_pim: "pim.invar pim"
    and rs_eq: "\<exists>pm. \<forall>q. rs q = (if (q \<in> class_map_\<alpha> (pm, pim.\<alpha> pim) (l, u)) then Some n else sm.\<alpha> sm q)"
shows "(sm_update n sm pim l ((Suc u) - l), rs) \<in> sm_rel"
proof -
  from rs_eq obtain pm where
    rs_eq': "\<And>q. rs q = (if (q \<in> class_map_\<alpha> (pm, pim.\<alpha> pim) (l, u)) then Some n else sm.\<alpha> sm q)"
    by metis

  from sm_update_correct[OF invar_sm invar_pim, of n l u pm] 
  show ?thesis unfolding rs_eq'[symmetric] by simp
qed

definition class_map_add_set_impl ::
  "('pm \<times> 'pim) \<Rightarrow> nat \<Rightarrow> 'q_set \<Rightarrow> (('pm \<times> 'pim) \<times> nat) nres" where
  "class_map_add_set_impl cm m S = 
   FOREACH (s.\<alpha> S)
     (\<lambda>q ((pm, pim), m). RETURN ((pm.update q m pm, pim.update m q pim), Suc m)) (cm, m)"

lemma class_map_add_set_impl_correct [refine] :
assumes "m' = m"
    and "(S, S') \<in> s_rel"
    and "(cm, cm') \<in> rprod pm_rel pim_rel"
shows "class_map_add_set_impl cm m S \<le> \<Down> (rprod (rprod pm_rel pim_rel) Id) (class_map_add_set Q cm' m' S')"
unfolding class_map_add_set_impl_def class_map_add_set_def
using assms
  apply (refine_rcg)
  apply (rule inj_on_id)
  apply (simp_all split: prod.splits)
  apply (simp_all add: 
    s_rel_def pm_rel_def pim_rel_def pim.correct pm.correct refine_hsimp)
done

definition class_map_init_pred_impl where
  "class_map_init_pred_impl QF F = 
   do {
     ASSERT (s.invar QF \<and> s.invar F);
     (cm, s) \<leftarrow> class_map_add_set_impl (pm.empty (), pim.empty ()) 0 QF;
     (cm', m) \<leftarrow> class_map_add_set_impl cm s F;
     RETURN (cm', s, m)
   }"

lemma class_map_init_pred_impl_correct :
assumes "(QF, QF') \<in> s_rel"
    and "(F, F') \<in> s_rel"
shows "class_map_init_pred_impl QF F \<le> \<Down> (rprod (rprod pm_rel pim_rel) (rprod Id Id)) (class_map_init_pred_compute QF' F')"
unfolding class_map_init_pred_impl_def class_map_init_pred_compute_def
using assms
  apply (refine_rcg)
  apply (simp_all split: prod.splits)
  apply (simp_all add: pm_rel_def pim_rel_def s_rel_def 
    pim.correct pm.correct s.correct refine_hsimp)
done

definition partition_impl_sing :: "nat \<times> nat \<Rightarrow> 'q_set \<Rightarrow> ('im \<times> 'sm \<times> nat)" where
  "partition_impl_sing lu Q \<equiv> (im.sng 0 lu, sm_update_init Q 0 (sm.empty ()), 1)"

lemma partition_impl_sing_correct [refine] :
assumes "(Q, QQ) \<in> s_rel"
shows "(partition_impl_sing lu Q, partition_map_sing lu QQ) \<in> part_rel"
using assms  sm_update_init_correct [of "sm.empty ()" Map.empty Q QQ 0]
by (simp add: partition_impl_sing_def partition_map_sing_def part_rel_def
              s_rel_def sm.correct im_rel_def im.correct sm_rel_def
              refine_hsimp
         cong: if_cong)

definition partition_impl_init where
  "partition_impl_init Q QF F s m =
   ((if (s = 0) then partition_impl_sing (0, m - 1) Q else
    (im.update (Suc 0) (0, s - 1) (im.sng 0 (s, m - 1)), 
     sm_update_init F 0 (sm_update_init QF 1 (sm.empty ())), 2)))"

lemma partition_impl_init_correct :
assumes QF_in_rel: "(QF, \<Q> \<A> - \<F> \<A>) \<in> s_rel"
    and Q_in_rel: "(Q, \<Q> \<A>) \<in> s_rel"
    and F_in_rel: "(F, \<F> \<A>) \<in> s_rel"
shows "(partition_impl_init Q QF F s m, partition_map2_init \<A> s m) \<in> part_rel"
using partition_impl_sing_correct [OF Q_in_rel] Q_in_rel F_in_rel QF_in_rel
  apply (simp add: partition_impl_init_def Let_def s.correct partition_map2_init_def)
  apply (simp add: part_rel_def im_rel_def im.correct refine_hsimp)
  apply (rule impI)
  apply (rule_tac sm_update_init_correct)
  apply (rule_tac sm_update_init_correct)
  apply (simp_all add: s_rel_def sm_rel_def sm.correct)
done

lemma partition_impl_init_correctI [refine] :
assumes QF_in_rel: "(QF, \<Q> \<A> - \<F> \<A>) \<in> s_rel"
    and Q_in_rel: "(Q, \<Q> \<A>) \<in> s_rel"
    and F_in_rel: "(F, \<F> \<A>) \<in> s_rel"
    and rs_eq: "rs = partition_map2_init \<A> s m"
shows "(partition_impl_init Q QF F s m, rs) \<in> part_rel"
using partition_impl_init_correct[OF QF_in_rel Q_in_rel F_in_rel] rs_eq by simp

definition Hopcroft_impl_step_compute_iM_swap_check where
"Hopcroft_impl_step_compute_iM_swap_check cm pre = (\<lambda>(im, sm, n). 
 do {
   ASSERT (s2_invar pre);
   FOREACH (s2_\<alpha> pre) (\<lambda>q (iM, (pm, pim)). do {
     let i = the (sm.lookup q sm);
     let s = (case (iM.lookup i iM) of None \<Rightarrow> (let (l, u) = (the (im.lookup i im)) in l) | Some s \<Rightarrow> s);
     let iq = the (pm.lookup q pm);
     let iM' = iM.update i (Suc s) iM;
     if (iq = s) then RETURN (iM', (pm, pim)) else
     do {
       let qs = the (pim.lookup s pim);
       let pm' = pm.update qs iq (pm.update q s pm);
       let pim' = pim.update iq qs (pim.update s q pim);
       RETURN (iM', (pm', pim'))
     }
   }) (iM.empty (), cm)
 })"

lemma Hopcroft_impl_step_compute_iM_swap_check_correct :
assumes pre_OK: "(pre, pre') \<in> s2_rel"
    and im_OK: "(im, im') \<in> im_rel"
    and sm_OK: "(sm, sm') \<in> sm_rel"
    and cm_OK: "(cm, cm') \<in> (rprod pm_rel pim_rel)"
    and n_OK: "n' = n"
shows "Hopcroft_impl_step_compute_iM_swap_check cm pre (im, sm, n) \<le> \<Down> (rprod iM_rel (rprod pm_rel pim_rel))
      (Hopcroft_map2_step_compute_iM_swap_check \<A> cm' pre' (im', sm', n'))"
unfolding Hopcroft_map2_step_compute_iM_swap_check_def
          Hopcroft_impl_step_compute_iM_swap_check_def
          partition_state_map_def
using [[goals_limit = 1]]
using assms
apply refine_rcg
apply (simp add: s2_rel_def)
apply (rule inj_on_id)
apply (simp_all add: refine_hsimp)
apply (simp_all add: s2_rel_def iM_rel_def im_rel_def sm_rel_def pm_rel_def pim_rel_def
                     s.correct iM.correct im.correct sm.correct pm.correct pim.correct
                     partition_index_map_def
                split: option.split)
done


definition Hopcroft_impl_step_compute_iM_cache___init_cache where
"Hopcroft_impl_step_compute_iM_cache___init_cache im sm q =
   (let i = the (sm.lookup q sm) in
    let (l::nat, u::nat) = the (im.lookup i im) in
    (i, l, u, l))"

definition Hopcroft_impl_step_compute_iM_cache___\<alpha>_cache where
  "Hopcroft_impl_step_compute_iM_cache___\<alpha>_cache iM cache =
   (case cache of None \<Rightarrow> iM | (Some (i, l, u, s)) \<Rightarrow> (iM.update i s iM))"

definition Hopcroft_impl_step_compute_iM_update_cache where
  "Hopcroft_impl_step_compute_iM_update_cache im sm q iq iM cache =
   (case cache of None \<Rightarrow> (iM, Hopcroft_impl_step_compute_iM_cache___init_cache im sm q)
       | Some (i, l, u, s) \<Rightarrow> if (iq \<le> u) then (iM, (i, l, u, s)) else 
              (iM.update i s iM, Hopcroft_impl_step_compute_iM_cache___init_cache im sm q))"

definition Hopcroft_impl_step_compute_iM_cache_swap_check where
"Hopcroft_impl_step_compute_iM_cache_swap_check cm pre = (\<lambda>(im, sm, n). 
 do {
   ASSERT (s2_invar pre);
   (iM, cache, cm) \<leftarrow> FOREACHoi (\<lambda>_ _. True) ((\<lambda>q. (q, the (pm.lookup q (fst cm)))) ` s2_\<alpha> pre) (\<lambda>(q,iq) (q', iq'). iq \<le> iq') 
     (\<lambda>(q,iq) (iM, cache, (pm, pim)). do {
     let (iM', (i, l, u, s)) = Hopcroft_impl_step_compute_iM_update_cache im sm q iq iM cache;
     if (iq = s) then RETURN (iM', Some (i, l, u, Suc s), (pm, pim)) else
     do {
       let qs = the (pim.lookup s pim);
       let pm' = pm.update qs iq (pm.update q s pm);
       let pim' = pim.update iq qs (pim.update s q pim);
       RETURN (iM', Some (i, l, u, Suc s), (pm', pim'))
     }
   }) (iM.empty (), None, cm);
   RETURN (Hopcroft_impl_step_compute_iM_cache___\<alpha>_cache iM cache, cm)
 })"


lemma Hopcroft_impl_step_compute_iM_update_cache_correct :
assumes im_OK: "(im, im') \<in> im_rel"
    and sm_OK: "(sm, sm') \<in> sm_rel"
    and iM_OK: "(iM, iM') \<in> iM_rel"
    and impl_eq: "Hopcroft_impl_step_compute_iM_update_cache im sm q iq iM cache = (iM_new, cache_new)"
    and map2_eq: "Hopcroft_map2_step_compute_iM_update_cache (im', sm', n) q iq iM' cache = (iM_new', cache_new')"
shows "cache_new' = cache_new \<and> (iM_new, iM_new') \<in> iM_rel"
using assms
apply (simp add: Hopcroft_map2_step_compute_iM_update_cache_def 
                 Hopcroft_impl_step_compute_iM_update_cache_def)
apply (cases cache)
apply (simp add: Hopcroft_map2_step_compute_iM_cache___init_cache_def
                 Hopcroft_impl_step_compute_iM_cache___init_cache_def
                 Let_def partition_index_map_def partition_state_map_def 
                 sm_rel_def sm.correct im_rel_def im.correct)
apply (simp split: prod.splits)
apply (case_tac "iq \<le> ac")
apply (simp)
apply (simp add: Hopcroft_map2_step_compute_iM_cache___init_cache_def
                 Hopcroft_impl_step_compute_iM_cache___init_cache_def
                 Let_def partition_index_map_def partition_state_map_def 
                 sm_rel_def sm.correct im_rel_def im.correct)
apply clarify
apply (simp add: iM_rel_def iM.correct)
done


lemma Hopcroft_impl_step_compute_iM_cache_swap_check_correct :
assumes pre_OK: "(pre, pre') \<in> s2_rel"
    and im_OK: "(im, im') \<in> im_rel"
    and sm_OK: "(sm, sm') \<in> sm_rel"
    and cm_OK: "(cm, cm') \<in> (rprod pm_rel pim_rel)"
    and n_OK: "n' = n"
  notes refine_hsimp[simp]
shows "Hopcroft_impl_step_compute_iM_cache_swap_check cm pre (im, sm, n) \<le> \<Down> (rprod iM_rel (rprod pm_rel pim_rel))
      (Hopcroft_map2_step_compute_iM_cache_swap_check \<A> cm' pre' (im', sm', n'))"
unfolding Hopcroft_map2_step_compute_iM_cache_swap_check_def
          Hopcroft_impl_step_compute_iM_cache_swap_check_def
          Hopcroft_map2_step_compute_iM_cache_swap_check_loop_def
using [[goals_limit = 1]]
using assms
apply (simp del: rprod_def)
apply (rule_tac refine)
  apply (simp add: s2_rel_def)
apply (rule_tac refine)
apply (rule_tac refine)
  apply (rule inj_on_id)
  apply (simp split: prod.splits add: pm.correct pm_rel_def s2_rel_def
    refine_rel_defs)

  apply (subgoal_tac "((map_op_empty iM_ops (), None, cm), 
                      (Map.empty, None, cm')) \<in> rprod iM_rel (rprod Id (rprod pm_rel pim_rel))")
  apply assumption
  apply (simp add: iM_rel_def iM.correct)

  apply simp

  apply (intro rprod_sv)
  apply simp_all[4]

  apply simp

defer
  apply (refine_rcg)
  apply (simp_all ) [4]
  apply (simp add: Hopcroft_impl_step_compute_iM_cache___\<alpha>_cache_def iM_rel_def iM.correct
              split: option.splits)


  apply (simp del: rprod_def)
  apply clarify
  apply (simp del: rprod_def)

  apply (rename_tac q iq it iM cache pm pim iM' cache' pm' pim')
proof -
  case goal1
 
  from goal1(11) have cache'_eq: "cache' = cache" and 
    pm_OK: "(pm, pm') \<in> pm_rel" and pim_OK: "(pim, pim') \<in> pim_rel" and
    iM_OK: "(iM, iM') \<in> iM_rel" by (simp_all)

  obtain iM_new i l u s where 
     impl_eq: "Hopcroft_impl_step_compute_iM_update_cache im sm q iq iM cache = (iM_new, i, l, u, s)"
     by (metis prod.exhaust)

  obtain iM_new' i' l' u' s' where 
     map2_eq: "Hopcroft_map2_step_compute_iM_update_cache (im', sm', n) q iq iM' cache = (iM_new', i', l', u', s')"
     by (metis prod.exhaust)

  from Hopcroft_impl_step_compute_iM_update_cache_correct[OF im_OK sm_OK iM_OK impl_eq map2_eq]
  have cache_eq: "i' = i" "l' = l" "u' = u" "s'=s" and iM_new_OK: "(iM_new, iM_new') \<in> iM_rel" 
    by simp_all

  show ?case 
    unfolding impl_eq map2_eq cache'_eq cache_eq
    apply (simp del: rprod_def)
    apply (refine_rcg)
    apply (simp_all)
    apply (insert pm_OK pim_OK iM_new_OK)
    apply (simp_all add: pm_rel_def pm.correct pim_rel_def pim.correct)
  done
qed

definition partition_impl_split where
  "partition_impl_split = (\<lambda>(pm,pim) (im, sm, n) i (pmin_l, pmin_u) pmax.
   (im.update n (pmin_l, pmin_u) (im.update i pmax im), 
    sm_update n sm pim pmin_l (Suc pmin_u - pmin_l),
    Suc n))"

schematic_lemma partition_impl_split_correct :
assumes P_OK: "(P, P') \<in> part_rel"
    and i_OK: "i' = i"
    and pmin_OK: "pmin' = pmin"
    and pmax_OK: "pmax' = pmax"
    and cm_OK: "(cm, cm') \<in> rprod pm_rel pim_rel"
shows "(partition_impl_split cm P i pmin pmax, partition_map2_split cm' P' i' pmin' pmax') \<in>  part_rel"
using assms
  apply (cases pmin)
  apply (simp 
    split: prod.splits 
    add: part_rel_def im_rel_def im.correct partition_impl_split_def
         refine_rel_defs
  )
  apply clarify
  apply (simp add: refine_rel_defs)
  apply (rule_tac sm_update_correctI)
  apply (simp_all add: sm_rel_def pim_rel_def)
  apply blast
done
   
fun (in -) L_insert_impl where
   "L_insert_impl (i::nat) L [] = L"
 | "L_insert_impl i L (a # as) = 
    L_insert_impl i ((a, i)#L) as"

lemma L_insert_impl_correct :
assumes dist_L: "\<And>a. a \<in> set aL \<Longrightarrow> (a, i) \<notin> L'"
    and dist_aL: "distinct aL"
    and L_OK: "(L, L') \<in> L_rel"
shows "(L_insert_impl i L aL, {(a, i) | a. a \<in> set aL} \<union> L') \<in> L_rel"
using assms
proof (induct aL arbitrary: L L')
  case Nil thus ?case by simp 
next
  case (Cons a as)
  note dist_L = Cons(2)
  note dist_a_as = Cons(3)
  note L_OK = Cons(4)
  note ind_hyp = Cons(1)

  let ?L2 = "(a, i) # L"
  let ?L2' = "insert (a, i) L'"
 
  from L_OK dist_L dist_a_as
  have L2_OK: "(?L2, ?L2') \<in> L_rel" and dist_L2': "\<And>a. a \<in> set as \<Longrightarrow>(a, i) \<notin> ?L2'" and
       dist_as: "distinct as"
    by (auto simp add: L_rel_def)

  from ind_hyp[OF dist_L2' dist_as L2_OK]
  show ?case by (auto simp add: L_rel_def)
qed


lemma L_insert_impl_correctI :
assumes dist_L: "\<And>a. a \<in> set aL \<Longrightarrow> (a, i) \<notin> set L"
    and dist_aL: "distinct aL"
    and distinct_L: "distinct L"
    and L''_eq: "L'' = {(a, i) | a. a \<in> set aL} \<union> set L"
shows "(L_insert_impl i L aL, L'') \<in> L_rel"
using L_insert_impl_correct[OF dist_L dist_aL, of L] distinct_L
unfolding L''_eq by (simp add: L_rel_def)

definition Hopcroft_impl_step where
"Hopcroft_impl_step aL pre P L cm =
 (do { (iM, cm') \<leftarrow> Hopcroft_impl_step_compute_iM_swap_check cm pre P;
       ASSERT (iM.invar iM);
       (P', L') \<leftarrow> FOREACH (map_to_set (iM.\<alpha> iM))
         (\<lambda>((p'::nat), (s::nat)) ((im', sm', n'), L'). do {
             let (pt', pct', pf', pcf') = 
                let (l, u) = (the (im.lookup p' im')) in
                ((l, s - 1), (s - l), (s, u), Suc u - s) in
             if (pcf' = 0) then (RETURN ((im', sm', n'), L')) else
             do {
               let (pmin, pmax) = (if (pcf' < pct') then (pf', pt') else (pt', pf'));
               let L' = L_insert_impl n' L' aL;
               let P' = partition_impl_split cm' (im', sm', n') p' pmin pmax;
               RETURN (P', L')
             }             
          }) (P, L);
       RETURN ((P', L'), cm')
     })"


schematic_lemma Hopcroft_impl_step_correct :
assumes PL_OK: "(P, P') \<in> part_rel"
    and L_OK: "(L, L' - {(a, p)}) \<in> L_rel"
    and AL_OK: "distinct aL" "set aL = \<Sigma> \<A>"
    and pre_OK: "(pre, pre') \<in> s2_rel"
    and cm_OK: "(cm, cm') \<in> rprod pm_rel pim_rel"
    and [refine_dref_RELATES]: "RELATES L_rel"
notes refine_hsimp[simp]
shows "Hopcroft_impl_step aL pre P L cm  \<le> \<Down>?R
       (Hopcroft_map2_step_no_spec \<A> p a pre' P' L' cm')"
unfolding Hopcroft_impl_step_def Hopcroft_map2_step_no_spec_def
using [[goals_limit = 1]] assms
apply (cases P)
apply (cases P')
apply (simp add: part_rel_def iM_rel_def iM.correct s_rel_def s.correct im_rel_def im.correct
                     pm_rel_def pm.correct pim_rel_def pim.correct L_rel_def
                     partition_index_map_def
            split: prod.splits)
apply clarify
apply refine_rcg
apply (refine_dref_type)
apply (rule Hopcroft_impl_step_compute_iM_swap_check_correct)
apply (simp_all)
apply (simp_all add: s_rel_def im_rel_def sm_rel_def split: prod.splits)

apply (simp add: pim_rel_def pm_rel_def)
apply (simp add: iM_rel_def)
apply (rule inj_on_id) apply (simp)
apply (simp add: iM.correct iM_rel_def map_to_set_def)
apply (simp add: L_rel_def part_rel_def im_rel_def sm_rel_def)

apply (simp, clarify)
apply (simp add: im.correct im_rel_def part_rel_def)

apply clarify
apply (simp add: im_rel_def im.correct part_rel_def partition_impl_split_def)
apply (clarify, simp)+
apply (rule conjI)
  apply (rule sm_update_correctI)
  apply (simp add: sm_rel_def)
  apply (simp add: pim_rel_def)
  apply (simp add: pim_rel_def sm_rel_def) apply metis

  apply (rule L_insert_impl_correctI)
  apply (auto simp add: Ball_def L_rel_def)[]
  apply (simp add: AL_OK)
  apply (simp add: L_rel_def)
  apply (simp add: L_rel_def)
done

definition Hopcroft_impl_f where
"Hopcroft_impl_f pre_fun aL = (\<lambda>((P, L), (pm, pim)).
 do {
    let (a,i) = hd L;
    let pre = pre_fun a pim (the (im.lookup i (fst P)));
    (PL', cm') \<leftarrow> Hopcroft_impl_step aL pre P (tl L) (pm, pim);
    RETURN (PL', cm')
 })"

lemma Hopcroft_impl_f_correct :
assumes P_OK: "(P, P') \<in> part_rel"
    and L_OK: "(L, L') \<in> L_rel"
    and cm_OK: "(cm, cm') \<in> (rprod pm_rel pim_rel)"
    and AL_OK: "distinct AL" "set AL = \<Sigma> \<A>"
    and pre_fun_OK: "\<And>a pim u l. 
                      (s2_invar (pre_fun a pim (l, u)) \<and> (s2_\<alpha> (pre_fun a pim (l, u)) = 
                         {q . \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> {the (pim.lookup i pim) |i. l \<le> i \<and> i \<le> u}}))"
notes refine_hsimp[simp]
shows "(Hopcroft_impl_f pre_fun AL ((P,L), cm))  \<le> \<Down>(rprod (rprod part_rel L_rel) (rprod pm_rel pim_rel))
       (Hopcroft_map2_f \<A> ((P', L'), cm'))"
unfolding Hopcroft_impl_f_def Hopcroft_map2_f_def
using [[goals_limit = 1]]
apply (refine_rcg)
-- "preprocess goals"
  apply (insert L_OK)[]
  apply (simp add: L_rel_def)
-- "goal solved"
  apply (insert P_OK L_OK cm_OK)[]
  apply (clarify, simp)+
  apply (rule Hopcroft_impl_step_correct)
  apply (simp_all add: AL_OK RELATES_def)
  -- "process subgoals"
    apply (cases L)
    apply (simp_all add: L_rel_def)

    apply (simp add: s2_rel_def pre_fun_OK part_rel_def im_rel_def im.correct
                     partition_index_map_def class_map_\<alpha>_def pim.correct pim_rel_def)
    apply auto[]
done

lemma Hopcroft_impl_f_correct'[refine] :
assumes X_OK: "(X, X') \<in> rprod (rprod part_rel L_rel) (rprod pm_rel pim_rel)"
    and AL_OK: "distinct AL" "set AL = \<Sigma> \<A>"
    and pre_fun_OK: "\<And>a pim u l. 
                      (s2_invar (pre_fun a pim (l, u)) \<and> (s2_\<alpha> (pre_fun a pim (l, u)) = 
                         {q . \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> {the (pim.lookup i pim) |i. l \<le> i \<and> i \<le> u}}))"
shows "(Hopcroft_impl_f pre_fun AL X)  \<le> \<Down>(rprod (rprod part_rel L_rel) (rprod pm_rel pim_rel))
       (Hopcroft_map2_f \<A> X')"
using Hopcroft_impl_f_correct[of "fst (fst X)" "fst (fst X')" 
                                 "snd (fst X)" "snd (fst X')"
                                 "snd X" "snd X'", OF _ _ _ AL_OK pre_fun_OK] X_OK
by (simp split: prod.splits add: refine_rel_defs)

definition Hopcroft_impl where
  "Hopcroft_impl Q F aL pre_fun = 
   (let QF = s.diff Q F in
   do {
      (cm, card_QF, card_Q) \<leftarrow> class_map_init_pred_impl QF F;
      (if (card_Q = 0) then RETURN (partition_impl_empty (), cm) else (
       if (card_Q = card_QF) then 
          RETURN (partition_impl_sing (0, card_Q - 1) Q, cm) 
       else (
         do {
           ((P, _), cm') \<leftarrow> WHILET (\<lambda>PL. (snd (fst PL) \<noteq> []))
                            (Hopcroft_impl_f pre_fun aL) 
                            ((partition_impl_init Q QF F card_QF card_Q, 
                              L_insert_impl (0::nat) [] (aL::'a list)), cm);
           RETURN (P, cm')
         })))
    })" 

lemma Hopcroft_impl_correct :
assumes Q_in_rel: "(Q, \<Q> \<A>) \<in> s_rel"
    and F_in_rel: "(F, \<F> \<A>) \<in> s_rel"
    and wf_A: "DFA \<A>"
    and AL_OK: "distinct AL" "set AL = \<Sigma> \<A>"
    and pre_fun_OK: "\<And>a pim u l. 
                      (s2_invar (pre_fun a pim (l, u)) \<and> (s2_\<alpha> (pre_fun a pim (l, u)) = 
                         {q . \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> {the (pim.lookup i pim) |i. l \<le> i \<and> i \<le> u}}))"
notes refine_rel_defs[simp]
shows "Hopcroft_impl Q F AL pre_fun \<le> \<Down>(rprod part_rel (rprod pm_rel pim_rel)) (Hopcroft_map2 \<A>)"
unfolding Hopcroft_impl_def Hopcroft_map2_def
using [[goals_limit = 1]]
apply (simp only: Let_def)
apply (refine_rcg)
apply (refine_dref_type)
-- "preprocess goals"
  apply (rule_tac conc_trans_additional(1))
  apply (rule_tac class_map_init_pred_impl_correct)
  prefer 3
  apply (rule DFA.class_map_init_pred_compute_correct [OF wf_A])

  apply (insert Q_in_rel F_in_rel)
  apply (simp_all add: AL_OK s_rel_def s.correct partition_impl_empty_correct
                  split: prod.splits)
-- "remaining goals"
  apply (rule partition_impl_sing_correct)
  apply (simp add: s_rel_def)
-- "goal solved"
  apply (simp add: Hopcroft_map2_init_def refine_rel_defs)
  apply clarify apply simp
  apply (intro conjI)
    apply (rule partition_impl_init_correctI [where \<A> = \<A>])
    apply (simp add: s_rel_def s.correct)
    apply (simp add: s_rel_def s.correct)
    apply (simp add: s_rel_def s.correct)
    apply simp
defer
  apply (simp add: L_rel_def)
-- "goal solved"
  apply (simp add: pre_fun_OK)
-- "goal solved"
  apply (simp add: pre_fun_OK )
proof -
  from L_insert_impl_correct[of "AL" 0 "{}" "[]"] AL_OK
  show "(L_insert_impl 0 [] AL, {(a, 0) |a. a \<in> \<Sigma> \<A>}) \<in> L_rel"
    by (simp add: L_rel_def)
qed



subsection \<open> Remove Monad \<close>

schematic_lemma class_map_init_pred_code_correct_aux :
shows "RETURN ?code \<le> class_map_init_pred_impl QF F"
unfolding class_map_init_pred_impl_def class_map_add_set_impl_def 
apply (simp add: split_def)
apply (rule refine_transfer)+
apply (rule cm_it.iteratei_rule)
apply (simp)
apply (rule_tac refine_transfer)+
apply (rule cm_it.iteratei_rule)
apply simp
apply (rule_tac refine_transfer)+
done

definition class_map_init_pred_code where
  "class_map_init_pred_code QF F =
   (let cm0 = (map_op_empty pm_ops (), map_op_empty pim_ops ()); 
        (cm1, s) = cm_it QF (\<lambda>_. True)
                   (\<lambda>q ((pm', pim'), i). 
                      ((map_op_update pm_ops q i pm', map_op_update pim_ops i q pim'),
                        Suc i)) (cm0, 0);
        (cm2, m) = cm_it F (\<lambda>_. True)
                   (\<lambda>q ((pm', pim'), i). 
                      ((map_op_update pm_ops q i pm', map_op_update pim_ops i q pim'),
                        Suc i)) (cm1, s)
    in (cm2, s, m))"

lemma class_map_init_pred_code_correct [refine_transfer] :
shows "RETURN (class_map_init_pred_code QF F) \<le> class_map_init_pred_impl QF F"
unfolding class_map_add_set_impl_def 
apply (rule order_trans [OF _ class_map_init_pred_code_correct_aux])
apply (simp add: class_map_init_pred_code_def split_def)
done

schematic_lemma Hopcroft_code_step_compute_iM_swap_check_correct_aux :
shows "RETURN ?code \<le> Hopcroft_impl_step_compute_iM_swap_check cm pre P"
unfolding Hopcroft_impl_step_compute_iM_swap_check_def
apply (rule refine_transfer)+
apply (rule pre_it.iteratei_rule)
apply simp
apply (rule refine_transfer)+
done

definition Hopcroft_code_step_compute_iM_swap_check where
  "Hopcroft_code_step_compute_iM_swap_check cm pre =
   (\<lambda>(im, sm, n). 
    pre_it pre (\<lambda>_. True)
     (\<lambda>q (iM, pm, pim).
         let i = the (map_op_lookup sm_ops q sm);
             s = case map_op_lookup iM_ops i iM of
                    None \<Rightarrow> (let (l, u) = (the (map_op_lookup im_ops i im)) in l)
                  | Some s \<Rightarrow> s;
             iq = the (map_op_lookup pm_ops q pm);
             iM' = map_op_update iM_ops i (Suc s) iM
         in if iq = s then (iM', pm, pim)
            else let qs = the (map_op_lookup pim_ops s pim);
                     pim' = map_op_update pm_ops qs iq
                             (map_op_update pm_ops q s pm);
                     pm' =  map_op_update pim_ops iq qs
                              (map_op_update pim_ops s q pim)
                 in (iM', pim', pm'))
     (map_op_empty iM_ops (), cm))"

lemma Hopcroft_code_step_compute_iM_swap_check :
shows "RETURN (Hopcroft_code_step_compute_iM_swap_check cm pre P) \<le> 
          Hopcroft_impl_step_compute_iM_swap_check cm pre P"
apply (rule order_trans [OF _ Hopcroft_code_step_compute_iM_swap_check_correct_aux])
apply (cases P)
apply (simp add: Hopcroft_code_step_compute_iM_swap_check_def)
done

lemma sorted_pre_it_OK: 
assumes "s2_invar pre"
shows "set_iterator_genord
 (iterator_to_ordered_iterator_mergesort
   (\<lambda>(q, iq) (q', iq'). iq \<le> iq')
   (set_iterator_image
     (\<lambda>q. (q, the (map_op_lookup pm_ops q (fst cm))))
     (pre_it2 pre)))
 ((\<lambda>q. (q, the (map_op_lookup pm_ops q (fst cm)))) ` s2_\<alpha> pre)
 (\<lambda>(q, iq) (q', iq'). iq \<le> iq')"
      (is "set_iterator_genord _ (?f ` _) ?R")
proof -
  from pre_it2.iteratei_rule [OF assms]
  have it: "set_iterator (pre_it2 pre) (s2_\<alpha> pre)" .

  from set_iterator_image_correct[OF it, of ?f "?f ` (s2_\<alpha> pre)"]
  have it_image: "set_iterator (set_iterator_image ?f (pre_it2 pre))
        (?f ` s2_\<alpha> pre)" 
    by (simp add: inj_on_def)

  show ?thesis 
    apply (rule iterator_to_ordered_iterator_mergesort_correct [of ?R, OF _ _ it_image])
    apply auto
  done
qed


schematic_lemma Hopcroft_code_step_compute_iM_cache_swap_check_correct_aux :
shows "RETURN (?code cm pre P) \<le> Hopcroft_impl_step_compute_iM_cache_swap_check cm pre P"
unfolding Hopcroft_impl_step_compute_iM_cache_swap_check_def
          Hopcroft_impl_step_compute_iM_update_cache_def
          Hopcroft_impl_step_compute_iM_cache___init_cache_def
          Hopcroft_impl_step_compute_iM_cache___\<alpha>_cache_def
using sorted_pre_it_OK[refine]
by (refine_transfer)

concrete_definition Hopcroft_code_step_compute_iM_cache_swap_check for cm pre P uses Hopcroft_code_step_compute_iM_cache_swap_check_correct_aux

schematic_lemma Hopcroft_code_step_correct_aux :
shows "RETURN (?code aL pre P L cm) \<le> Hopcroft_impl_step aL pre P (L::('a \<times> nat) list) cm"
unfolding Hopcroft_impl_step_def partition_impl_split_def
by (refine_transfer Hopcroft_code_step_compute_iM_swap_check iM_it.iteratei_rule)

concrete_definition Hopcroft_code_step for aL pre P L cm uses Hopcroft_code_step_correct_aux

schematic_lemma Hopcroft_code_correct_aux :
shows "RETURN (?code Q F AL pre_fun) \<le> Hopcroft_impl Q F AL pre_fun"
unfolding Hopcroft_impl_def partition_impl_empty_def
          partition_impl_sing_def partition_impl_init_def 
          Hopcroft_impl_f_def sm_update_init_def
by (refine_transfer Hopcroft_code_step.refine)

concrete_definition Hopcroft_code for Q F AL pre_fun uses Hopcroft_code_correct_aux

lemma Hopcroft_code_correct_full :
fixes \<A> :: "('q, 'a, _) NFA_rec_scheme"
assumes Q_in_rel: "(Q, \<Q> \<A>) \<in> s_rel"
    and F_in_rel: "(F, \<F> \<A>) \<in> s_rel"
    and wf_A: "DFA \<A>"
    and AL_OK: "distinct AL" "set AL = \<Sigma> \<A>"
    and pre_fun_OK: "\<And>a pim u l. 
                      (s2_invar (pre_fun a pim (l, u)) \<and> (s2_\<alpha> (pre_fun a pim (l, u)) = 
                         {q . \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> {the (pim.lookup i pim) |i. l \<le> i \<and> i \<le> u}}))"
    and rs_eq: "Hopcroft_code Q F AL pre_fun = ((im, sm, n), (pm, pim))"
shows "map_op_invar im_ops im \<and>
       map_op_invar sm_ops sm \<and>
       map_op_invar pm_ops pm \<and>
       map_op_invar pim_ops pim \<and>
       partition_map_\<alpha>
         (partition_map2_\<alpha>_im (map_op_\<alpha> pm_ops pm, map_op_\<alpha> pim_ops pim)
         (map_op_\<alpha> im_ops im), map_op_\<alpha> sm_ops sm, n) =
       Myhill_Nerode_partition \<A> \<and>
       partition_map_invar
         (partition_map2_\<alpha>_im (map_op_\<alpha> pm_ops pm, map_op_\<alpha> pim_ops pim)
          (map_op_\<alpha> im_ops im), map_op_\<alpha> sm_ops sm, n)"
proof -
  def RR \<equiv> "(rprod part_rel (rprod pm_rel pim_rel))"
  def result \<equiv> "((im, sm, n), (pm, pim))"

  have RR_sv: "single_valued RR" unfolding RR_def
    by (intro rprod_sv, simp_all)

  note Hopcroft_code.refine
  also note Hopcroft_impl_correct[OF Q_in_rel F_in_rel wf_A AL_OK pre_fun_OK]
  also note DFA.Hopcroft_map2_correct_full[OF wf_A]
  finally have step1: "RETURN result  \<le> \<Down> RR
     (SPEC (\<lambda>(P, cm').
               partition_map_\<alpha> (partition_map2_\<alpha> cm' P) =
               Myhill_Nerode_partition \<A> \<and>
               partition_map_invar (partition_map2_\<alpha> cm' P))) "
  by (simp add: RR_def rs_eq result_def)

  thus ?thesis
    apply (simp add: pw_le_iff refine_pw_simps RR_sv refine_hsimp
                del: partition_map_\<alpha>.simps partition_map_invar.simps)
    apply (simp add: RR_def part_rel_def im_rel_def sm_rel_def pm_rel_def
                     pim_rel_def result_def  refine_hsimp
                del: partition_map_\<alpha>.simps partition_map_invar.simps)
    apply (simp add: partition_map2_\<alpha>_def refine_hsimp
                del: partition_map_\<alpha>.simps partition_map_invar.simps)
  done
qed


definition Hopcroft_code_rename_map where
"Hopcroft_code_rename_map Q F AL pre_fun = (fst (snd (fst (Hopcroft_code Q F AL pre_fun))))"

lemmas Hopcroft_code_rename_map_alt_def = Hopcroft_code_rename_map_def[unfolded Hopcroft_code_def]

lemma Hopcroft_code_correct_rename_fun :
fixes \<A> :: "('q, 'a, _) NFA_rec_scheme"
  and pre_fun AL F Q
defines "sm \<equiv> Hopcroft_code_rename_map Q F AL pre_fun"
assumes Q_in_rel: "(Q, \<Q> \<A>) \<in> s_rel"
    and F_in_rel: "(F, \<F> \<A>) \<in> s_rel"
    and wf_A: "DFA \<A>"
    and AL_OK: "distinct AL" "set AL = \<Sigma> \<A>"
    and pre_fun_OK: "\<And>a pim u l. 
                      (s2_invar (pre_fun a pim (l, u)) \<and> (s2_\<alpha> (pre_fun a pim (l, u)) = 
                         {q . \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> {the (pim.lookup i pim) |i. l \<le> i \<and> i \<le> u}}))"
shows "sm.invar sm"
      "dom (sm.\<alpha> sm) = \<Q> \<A>"
      "NFA_is_strong_equivalence_rename_fun \<A> (\<lambda>q. states_enumerate (the (sm.lookup q sm)))"
proof -
   obtain im n sm' pm pim where rs_eq: "Hopcroft_code Q F AL pre_fun = ((im, sm', n), (pm, pim))"  by (metis prod.exhaust)
    from rs_eq sm_def have sm'_eq: "sm' = sm"  unfolding Hopcroft_code_rename_map_def by simp

  def P' \<equiv> "(partition_map2_\<alpha>_im (map_op_\<alpha> pm_ops pm, map_op_\<alpha> pim_ops pim)
             (map_op_\<alpha> im_ops im), map_op_\<alpha> sm_ops sm, n)"

  from Hopcroft_code_correct_full [OF Q_in_rel F_in_rel wf_A AL_OK pre_fun_OK rs_eq] sm'_eq
  have invars: "map_op_invar im_ops im \<and>
        map_op_invar sm_ops sm \<and>
        map_op_invar pm_ops pm \<and>
        map_op_invar pim_ops pim" and
       strong_fun: "partition_map_\<alpha> P' = Myhill_Nerode_partition \<A>" and
       invar: "partition_map_invar P'" unfolding P'_def by simp_all

  from partition_map_to_rename_fun_OK[OF invar strong_fun] invars
  show "sm.invar sm"
       "dom (sm.\<alpha> sm) = \<Q> \<A>"
       "NFA_is_strong_equivalence_rename_fun \<A> (\<lambda>q. states_enumerate (the (sm.lookup q sm)))"
    unfolding P'_def
    by (simp_all add: sm.correct)
qed

end 

end

