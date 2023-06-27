theory Hopcroft_Thms
imports Main DFA Partition "HOL-Library.Discrete" "HOL-Combinatorics.List_Permutation"
begin

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

definition split_language_equiv_partition where
  "split_language_equiv_partition \<A> p1 a p2 = \<comment>\<open>split p1 with (a, p2).\<close>
   split_set (\<lambda>q. \<exists>q' \<in> p2. (q, a, q') \<in> \<Delta> \<A>) p1"

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

definition split_language_equiv_partition_pred ::
  "('q, 'a, 'x) NFA_rec_scheme \<Rightarrow> 'q set \<Rightarrow> 'a \<Rightarrow> 'q set \<Rightarrow> bool" where
  "split_language_equiv_partition_pred \<A> p1 a p2 \<equiv> \<comment>\<open>(a, p2) is a splitter of p1.\<close>
    (fst (split_language_equiv_partition \<A> p1 a p2) \<noteq> {}) \<and> 
    (snd (split_language_equiv_partition \<A> p1 a p2) \<noteq> {})"

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
           ('a \<times> 'q set) set \<Rightarrow> ('a \<times> 'q set) set \<Rightarrow> bool" where
 "Hopcroft_update_splitters_pred \<A> pp aa P L L' \<equiv>
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


definition Hopcroft_set_step_invar where
"Hopcroft_set_step_invar \<A> p a P L P' \<sigma> = 
 (Hopcroft_update_splitters_pred_aux (\<Sigma> \<A>) (Hopcroft_splitted \<A> p a {} (P - P')) P (L - {(a, p)}) (snd \<sigma>)
    \<and> fst \<sigma> = Hopcroft_split \<A> p a {} (P - P') \<union> P')" 
\<comment>\<open>Predicate for updating splitter and splitting partition\<close>

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
assumes invar: "Hopcroft_set_step_invar \<A> p a P L {} (P', L')"
shows "Hopcroft_update_splitters_pred_aux (\<Sigma> \<A>) (Hopcroft_splitted \<A> p a {} P) P
        (L - {(a, p)}) L' \<and>
       P' = Hopcroft_split \<A> p a {} P"
using invar
unfolding Hopcroft_set_step_invar_def
  by simp

lemma Hopcroft_splitted_aux:"(B, B', B'') \<in> Hopcroft_splitted \<A> C b {} P \<Longrightarrow>
  B \<in> P \<and> B = B' \<union> B'' \<and> B' \<inter> B'' = {} \<and> B' \<noteq> {} \<and> B'' \<noteq> {}"
  unfolding Hopcroft_splitted_def split_language_equiv_partition_def split_set_def
  by blast

lemma conj_commute1:
  "(P \<and> Q) \<Longrightarrow> (Q \<and> P)"
  by simp

lemma (in DFA) split_is_partition:
  assumes "Hopcroft_abstract_invar \<A> (P, L)" "a \<in> \<Sigma> \<A>" "(a, C) \<in> L"
  shows "is_partition (\<Q> \<A>) (Hopcroft_split \<A> C a {} P)"
proof-
  have "is_weak_language_equiv_partition \<A> ({} \<union> P)" "is_weak_language_equiv_set \<A> C" "a \<in> \<Sigma> \<A>" "{} \<inter> P = {}"
    using assms(2) unfolding Hopcroft_abstract_invar_def
       apply simp
    using assms
    unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def
       apply simp
    using assms
    unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def
      apply (metis (mono_tags, lifting) case_prodD snd_conv)
    apply (simp add: assms)+
    done
  note hyps=this
  from DFA.Hopcroft_split_correct(1)[OF DFA_axioms hyps]
  show ?thesis
    unfolding is_weak_language_equiv_partition_def
    by simp
qed

definition unique_pred where
  "unique_pred x P \<equiv> P x \<and> (\<forall>y. P y \<longrightarrow> y = x)"

lemma unique_pred_correct:"(unique_pred x P) \<longleftrightarrow> (\<exists>! y. P y \<and> x = (THE y. P y))"
  by (standard; metis the_equality unique_pred_def)+

lemma ex1_ex1I:"\<lbrakk>P x y; \<And>x' y'. P x' y' \<Longrightarrow> x = x' \<and> y = y'\<rbrakk> \<Longrightarrow> \<exists>! x. \<exists>! y. P x y"
  by (intro ex1I, blast+)

lemma discrete_log_ineq:"(a+b) * Discrete.log (x+y) \<ge> a * Discrete.log x + b * Discrete.log y"
proof-
  have "?thesis \<longleftrightarrow> a * Discrete.log(x+y) + b * Discrete.log(x+y) \<ge> a * Discrete.log x + b * Discrete.log y"
    by (simp add: algebra_simps)
  moreover have "Discrete.log(x+y) \<ge> Discrete.log x" "Discrete.log(x+y) \<ge> Discrete.log y"
    by (simp add: Discrete.log_le_iff)+
  ultimately show ?thesis
    by (simp add: add_mono)
qed

lemma discrete_log_ineqI:
  "\<lbrakk>A+B=AB; C+D=CD\<rbrakk> \<Longrightarrow> AB * Discrete.log CD \<ge> A * Discrete.log C + B * Discrete.log D"
  using discrete_log_ineq[of A C B D] by simp

lemma sum_list_conc_distr:"xs = ys @ zs \<Longrightarrow> (\<Sum>x\<leftarrow>xs. f x) = (\<Sum>x\<leftarrow>ys. f x) + (\<Sum>x\<leftarrow>zs. f x)"
  by (induction xs) simp+

lemma mset_eq_sum_list_eq: "mset xs = mset ys \<Longrightarrow> (\<Sum>x\<leftarrow>xs. (f::'a \<Rightarrow> 'b::comm_monoid_add) x) = (\<Sum>x\<leftarrow>ys. f x)"
  using mset_map[where f=f] sum_mset_sum_list by metis

lemma sum_fold_prod_aux:
  "(fold ((@) \<circ> (\<lambda>x. [fst (F x), snd (F x)])) xs []) <~~> ys \<Longrightarrow>
  (\<Sum>y\<leftarrow>ys. (f::'a \<Rightarrow> 'b::comm_monoid_add) y) = (\<Sum>x\<leftarrow>xs. f (fst (F x)) + f (snd (F x)))"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  from Cons.prems obtain ys' where ys'_def:"ys <~~> (fst (F x)) # (snd (F x)) # ys'"
  proof-
    have "(fold ((@) \<circ> (\<lambda>x. [fst (F x), snd (F x)])) (x # xs) []) = (fold ((@) \<circ> (\<lambda>x. [fst (F x), snd (F x)])) xs [fst (F x), snd (F x)])"
      by simp
    with Cons.prems have "\<exists> ys'. ys <~~> (fst (F x)) # (snd (F x)) # ys'"
      by (metis (no_types, lifting) append_Cons fold_append_concat_rev fold_map perm_append_swap)
    thus "(\<And>ys'. mset ys = mset (fst (F x) # snd (F x) # ys') \<Longrightarrow> thesis) \<Longrightarrow> thesis"
      by blast
  qed
  with mset_eq_sum_list_eq[OF this, of f]
  have "(\<Sum>y\<leftarrow>ys. f y) =  f (fst (F x)) + f (snd (F x)) + (\<Sum>y\<leftarrow>ys'. f y)"
    by (simp add: add.assoc)

  moreover from Cons.prems Cons.IH[of ys'] have "(\<Sum>y\<leftarrow>ys'. f y) = (\<Sum>x\<leftarrow>xs. f (fst (F x)) + f (snd (F x)))"
    by (smt (z3) Cons_eq_appendI ys'_def append_Nil append_assoc comp_apply fold_append_concat_rev fold_map fold_simps(2) perm_append1_eq perm_append_single perm_append_swap)

  ultimately show "(\<Sum>y\<leftarrow>ys. f y) = (\<Sum>x\<leftarrow>x#xs. f (fst (F x)) + f (snd (F x)))"
    by simp
qed simp

abbreviation (input) ls_perm :: \<open>'a list \<Rightarrow> 'a set \<Rightarrow> bool\<close>  (infixr \<open><~~~>\<close> 50)
  where \<open>xs <~~~> E \<equiv> (mset xs = mset_set E)\<close>

lemma ls_perm_nempty_perm_finite:"\<exists> xs. (xs <~~~> E) \<and> xs \<noteq> [] \<Longrightarrow> finite E"
proof-
  assume "\<exists> xs. (xs <~~~> E) \<and> xs \<noteq> []"
  then obtain xs where xs_def:"xs <~~~> E" "xs \<noteq> []"
    by blast

  then have "finite (set xs)"
    by blast

  {
    assume "\<not> finite E"
    then have "mset_set E = {#}" by simp

    with \<open>finite (set xs)\<close> xs_def obtain x where "x \<in># mset_set E" "\<not> (x \<in># mset xs)"
      by simp
    with xs_def(1) have False
      by presburger
  }
  then show ?thesis by blast
qed

lemma ls_perm_split_prop: "finite E \<Longrightarrow> \<exists> xs ys zs. xs <~~~> E \<and> xs = ys @ zs \<and> (\<forall>e \<in> set ys. P e) \<and> (\<forall>e \<in> set zs. \<not> P e)"
proof-
  assume finE:"finite E"
  obtain ys zs where yszs_def:"ys <~~~> {x \<in> E. P x}" "zs <~~~> {x \<in> E. \<not> P x}"
    using ex_mset by blast
  define xs where "xs \<equiv> ys @ zs"

  have "xs <~~~> E"
  proof-
    have "E = {x \<in> E. P x} \<union> {x \<in> E. \<not> P x}" "{x \<in> E. P x} \<inter> {x \<in> E. \<not> P x} = {}"
      by blast+

    with mset_set_Union[of "{x \<in> E. P x}" "{x \<in> E. \<not> P x}" ] finE finite_Un[of "{x \<in> E. P x}" "{x \<in> E. \<not> P x}", simplified this(1)[symmetric]]
    have "mset_set E = mset_set {x \<in> E. P x} + mset_set {x \<in> E. \<not> P x}"
      by fastforce

    moreover
    from xs_def have "mset xs = mset ys + mset zs" by simp

    moreover have "\<dots> = mset_set {x \<in> E. P x} + mset_set {x \<in> E. \<not> P x}"
      using yszs_def by argo

    ultimately show ?thesis
      by argo
  qed

  moreover from yszs_def have "e\<in>set ys \<Longrightarrow> P e" "e\<in>set zs \<Longrightarrow> \<not> P e" for e
     (* @TODO: find a better proof, this is easy *)
     apply (metis (no_types, lifting) count_mset_0_iff count_mset_set(3) mem_Collect_eq)+
    done
  
  ultimately show ?thesis
    using yszs_def xs_def by blast
qed

lemma ls_perm_set_eq:"finite E \<Longrightarrow> xs <~~~> E \<Longrightarrow> set xs = E"
  (* @TODO: find a better proof, this is easy *)
  apply standard
  apply (metis order_eq_iff finite_set_mset_mset_set set_mset_mset)+
  done

lemma perm_consI:"x \<in> set xs \<Longrightarrow> (\<exists> ys. (x#ys) <~~> xs)"
  using perm_remove[of x xs] by metis

lemma theI'':"\<exists>!(x, y). P x y \<Longrightarrow> P (fst (THE (x, y). P x y)) (snd (THE (x, y). P x y))"
  by (metis case_prod_beta' theI')

lemma fold_map_Un_eq:"set (fold ((@) \<circ> (\<lambda>x. (f::'a \<Rightarrow> 'b list) x)) xs res) = (set res) \<union> (\<Union> {set (f x) | x. x \<in> set xs})"
proof (induction xs arbitrary: res)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have "fold ((@) \<circ> f) (x # xs) res = fold ((@) \<circ> f) xs [] @ (f x @ res)"
    by (metis (no_types, lifting) append.right_neutral comp_apply fold_append_concat_rev fold_map fold_simps(2))
  with Cons have "set (fold ((@) \<circ> f) (x # xs) res) = set res \<union> \<Union> {set (f x) |x. x \<in> set xs} \<union> set (f x)"
    by fastforce
  moreover have "\<Union> {set (f y) |y. y \<in> set (x#xs)} = \<Union> {set (f x) |x. x \<in> set xs} \<union> set (f x)"
    by auto
  ultimately show ?case
    using Un_assoc[of "set res" "\<Union> {set (f x) |x. x \<in> set xs}" "set (f x)"]
    by argo
qed

lemma fold_map_distinct:"\<lbrakk>distinct xs; \<And>x. x \<in> set xs \<Longrightarrow> fst (f x) \<noteq> snd (f x) \<and> fst (fst (f x)) = fst (snd (f x)) \<and> is_partition (snd x) {snd (fst (f x)), snd (snd (f x))}\<rbrakk> \<Longrightarrow> distinct (fold ((@) \<circ> (\<lambda>x. [fst(f x), snd(f x)])) xs [])"
  sorry
end
