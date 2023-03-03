(*  Title:       Nondeterministic Finite Automata
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
                 Petra Dietrich <petra@ecs.vuw.ac.nz>

    using Peter Lammich <peter.lammich@uni-muenster.de> work on
    Finite state machines
*)

section\<open>Nondeterministic Finite Automata\<close>

theory NFA     
  imports Main LTS SemiAutomaton
          "HOL-Library.Nat_Bijection"
        "../Accessible"
begin

text \<open> This theory defines nondetermistic finite automata.
  These automata are represented as records containing a transtion relation, 
  a set of initial states and a set of final states.\<close>

record ('q,'a) NFA_rec =
  "('q, 'a) SemiAutomaton_rec" +
  \<F> :: "'q set"           \<comment>\<open>The set of final states\<close>

definition SemiAutomaton_to_NFA ::
  "('q, 'a, _) SemiAutomaton_rec_scheme \<Rightarrow> 'q set \<Rightarrow> ('q, 'a) NFA_rec" where
  "SemiAutomaton_to_NFA \<A> F =  \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = F \<rparr>"

lemma SemiAutomaton_to_NFA_\<Q>[simp]:
  "\<Q> (SemiAutomaton_to_NFA \<A> F) = \<Q> \<A>" unfolding SemiAutomaton_to_NFA_def by simp

lemma SemiAutomaton_to_NFA_\<Sigma>[simp]:
  "\<Sigma> (SemiAutomaton_to_NFA \<A> F) = \<Sigma> \<A>" unfolding SemiAutomaton_to_NFA_def by simp

lemma SemiAutomaton_to_NFA_\<I>[simp]:
  "\<I> (SemiAutomaton_to_NFA \<A> F) = \<I> \<A>" unfolding SemiAutomaton_to_NFA_def by simp

lemma SemiAutomaton_to_NFA_\<Delta>[simp]:
  "\<Delta> (SemiAutomaton_to_NFA \<A> F) = \<Delta> \<A>" unfolding SemiAutomaton_to_NFA_def by simp

lemma SemiAutomaton_to_NFA_\<delta>[simp]:
  "\<delta> (SemiAutomaton_to_NFA \<A> F) = \<delta> \<A>" unfolding \<delta>_def by simp

lemma SemiAutomaton_to_NFA_\<F>[simp]:
  "\<F> (SemiAutomaton_to_NFA \<A> F) = F" unfolding SemiAutomaton_to_NFA_def by simp

lemma SemiAutomaton_to_NFA_run[simp]:
  "SemiAutomaton_is_fin_run (SemiAutomaton_to_NFA \<A> F) =
   SemiAutomaton_is_fin_run \<A>"
by (simp add: fun_eq_iff SemiAutomaton_is_fin_run_def)

lemma SemiAutomaton_to_NFA_unreachable_states[simp]:
  "SemiAutomaton_unreachable_states (SemiAutomaton_to_NFA \<A> F) =
   SemiAutomaton_unreachable_states \<A>"
  unfolding SemiAutomaton_unreachable_states_def by simp

lemma SemiAutomaton_to_NFA_remove_states[simp]:
  "SemiAutomaton_remove_states (SemiAutomaton_to_NFA \<A> F) Q =
   SemiAutomaton_remove_states \<A> Q"
  unfolding SemiAutomaton_remove_states_def by simp

lemma SemiAutomaton_to_NFA_rename_states[simp]:
  "SemiAutomaton_rename_states (SemiAutomaton_to_NFA \<A> F) Q =
   SemiAutomaton_rename_states \<A> Q"
  unfolding SemiAutomaton_rename_states_ext_def by simp

lemma SemiAutomaton_to_NFA_initially_connected [simp]:
  "SemiAutomaton_is_initially_connected (SemiAutomaton_to_NFA \<A> F) =
   SemiAutomaton_is_initially_connected \<A>"
  unfolding SemiAutomaton_is_initially_connected_def by simp

lemma SemiAutomaton_to_NFA_complete_deterministic [simp]:
  "SemiAutomaton_is_complete_deterministic (SemiAutomaton_to_NFA \<A> F) =
   SemiAutomaton_is_complete_deterministic \<A>"
  unfolding SemiAutomaton_is_complete_deterministic_def by simp

lemma SemiAutomaton_to_NFA_deterministic [simp]:
  "SemiAutomaton_is_deterministic (SemiAutomaton_to_NFA \<A> F) =
   SemiAutomaton_is_deterministic \<A>"
  unfolding SemiAutomaton_is_deterministic_def by simp


text \<open> Using notions for labelled transition systems, it is easy to
  define the languages accepted by automata. \<close>

definition NFA_accept where
  "NFA_accept \<A> w = (\<exists> q\<in>(\<I> \<A>). \<exists> q'\<in>(\<F> \<A>). LTS_is_reachable (\<Delta> \<A>) q w q')"

lemma NFA_accept_run_def :
  "NFA_accept \<A> w = (\<exists>r. SemiAutomaton_is_fin_run \<A> w r \<and> last r \<in> \<F> \<A>)"
unfolding NFA_accept_def Bex_def LTS_is_reachable_alt_def SemiAutomaton_is_fin_run_def 
by auto

definition \<L> where "\<L> \<A> = {w. NFA_accept \<A> w}"
text \<open> It is also useful to define the language accepted in a state. \<close>
definition \<L>_in_state where
  "\<L>_in_state \<A> q = {w. (\<exists>q'\<in> (\<F> \<A>). LTS_is_reachable (\<Delta> \<A>) q w q')}"

abbreviation "\<L>_right \<equiv> \<L>_in_state"

lemma \<L>_in_state_alt_def :
  "\<L>_in_state \<A> q = \<L> \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = {q}, \<F> = \<F> \<A> \<rparr>"
unfolding \<L>_def \<L>_in_state_def 
by (auto simp add: NFA_accept_def)

definition \<L>_left where
  "\<L>_left \<A> q = {w. (\<exists> i \<in> (\<I> \<A>). LTS_is_reachable (\<Delta> \<A>) i w q)}"

lemma \<L>_left_alt_def :
  "\<L>_left \<A> q = \<L> \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = {q} \<rparr>"
unfolding \<L>_def \<L>_left_def by (auto simp add: NFA_accept_def)

lemma NFA_accept_alt_def : "NFA_accept \<A> w \<longleftrightarrow> w \<in> \<L> \<A>" by (simp add: \<L>_def)

lemma \<L>_alt_def :
  "\<L> \<A> = \<Union> ((\<L>_in_state \<A>) ` (\<I> \<A>))"
by (auto simp add: \<L>_def \<L>_in_state_def NFA_accept_def)

lemma in_\<L>_in_state_Nil [simp] : "[] \<in> \<L>_in_state \<A> q \<longleftrightarrow> (q \<in> \<F> \<A>)" by (simp add: \<L>_in_state_def)
lemma in_\<L>_in_state_Cons [simp] : "(\<sigma> # w) \<in> \<L>_in_state \<A> q \<longleftrightarrow> 
  (\<exists>q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<and> w \<in> \<L>_in_state \<A> q')" by (auto simp add: \<L>_in_state_def)

definition remove_prefix :: "'a list \<Rightarrow> ('a list) set \<Rightarrow> ('a list) set" where
  "remove_prefix pre L \<equiv> drop (length pre) ` (L \<inter> {pre @ w |w. True})"  

lemma remove_prefix_alt_def [simp] :
  "w \<in> remove_prefix pre L \<longleftrightarrow> (pre @ w \<in> L)"
by (auto simp add: remove_prefix_def image_iff Bex_def)

lemma remove_prefix_Nil [simp] :
   "remove_prefix [] L = L" by (simp add: set_eq_iff)

lemma remove_prefix_Combine [simp] :
   "remove_prefix p2 (remove_prefix p1 L) = 
    remove_prefix (p1 @ p2) L" 
by (rule set_eqI, simp)

lemma \<L>_in_state_remove_prefix : 
  "pre \<in> lists (\<Sigma> \<A>) \<Longrightarrow>
    (remove_prefix pre (\<L>_in_state \<A> q) = 
    \<Union> {\<L>_in_state \<A> q' | q'. LTS_is_reachable (\<Delta> \<A>) q pre q'})"
by (rule set_eqI, auto simp add: \<L>_in_state_def LTS_is_reachable_concat)

lemma \<L>_in_state___in_\<F> : 
assumes L_eq: "\<L>_in_state \<A> q = \<L>_in_state \<A> q'"
shows "(q \<in> \<F> \<A> \<longleftrightarrow> q' \<in> \<F> \<A>)"
proof -
  from L_eq have "([] \<in> \<L>_in_state \<A> q) = ([] \<in> \<L>_in_state \<A> q')" by simp
  thus ?thesis by simp
qed


text \<open> The following locale captures, whether a NFA  is well-formed. \<close>
locale NFA = FinSemiAutomaton \<A> 
  for \<A>::"('q,'a, 'NFA_more) NFA_rec_scheme" + 
  assumes \<F>_consistent: "\<F> \<A> \<subseteq> \<Q> \<A>"
  and finite_\<Sigma>: "finite (\<Sigma> \<A>)"

lemma NFA_alt_def :
  "NFA \<A> \<longleftrightarrow> FinSemiAutomaton \<A> \<and> \<F> \<A> \<subseteq> \<Q> \<A> \<and> finite (\<Sigma> \<A>)"
unfolding NFA_def NFA_axioms_def by simp

lemma NFA_full_def :
  "NFA \<A> \<longleftrightarrow> 
   ((\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow>
              q \<in> \<Q> \<A> \<and> \<sigma> \<in> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>) \<and>
    \<I> \<A> \<subseteq> \<Q> \<A> \<and> \<F> \<A> \<subseteq> \<Q> \<A> \<and>
    finite (\<Q> \<A>) \<and> finite (\<Delta> \<A>) \<and> finite (\<Sigma> \<A>))"
unfolding NFA_def FinSemiAutomaton_full_def NFA_axioms_def by auto

lemma (in NFA) finite_\<F> :
  "finite (\<F> \<A>)"
using \<F>_consistent finite_\<Q>
by (metis finite_subset)

lemma NFA_intro [intro!] :
  " \<lbrakk>\<And>q \<sigma> q'. (q,\<sigma>,q') \<in> \<Delta> \<A> \<Longrightarrow> (q \<in> \<Q> \<A>) \<and> (\<sigma> \<in> \<Sigma> \<A>) \<and> (q' \<in> \<Q> \<A>);
     \<I> \<A> \<subseteq> \<Q> \<A>; \<F> \<A> \<subseteq> \<Q> \<A>; finite (\<Q> \<A>); finite (\<Delta> \<A>); finite (\<Sigma> \<A>)\<rbrakk> \<Longrightarrow> NFA \<A>"
by (simp add: NFA_full_def)

definition dummy_NFA where
"dummy_NFA q a =
 \<lparr>\<Q> = {q}, \<Sigma> = {a}, \<Delta> = {(q, a, q)},
  \<I> = {q}, \<F> = {q} \<rparr>"

lemma dummy_NFA___is_NFA :
  "NFA (dummy_NFA q a)"
by (simp add: NFA_full_def dummy_NFA_def)


lemma (in NFA) NFA_accept_det_def :
  "NFA_accept \<A> w = (LTS_is_reachable_fun (\<Delta> \<A>) w (\<I> \<A>) \<inter> (\<F> \<A>) \<noteq> {})"
by (auto simp add: LTS_is_reachable_fun_alt_def NFA_accept_def)

lemma (in NFA) NFA_accept_wf_def :
  "NFA_accept \<A> w = (w \<in> lists (\<Sigma> \<A>) \<and> 
     (\<exists> q\<in>(\<I> \<A>). \<exists> q'\<in>(\<F> \<A>). LTS_is_reachable (\<Delta> \<A>) q w q'))"
unfolding NFA_accept_def by (metis LTS_is_reachable___labels)

lemma (in NFA) NFA_\<L>___lists_\<Sigma> :
  "\<L> \<A> \<subseteq> lists (\<Sigma> \<A>)"
by (simp add: \<L>_def NFA_accept_def subset_iff)
   (metis LTS_is_reachable___labels)

lemma (in NFA) NFA_is_empty_\<L> :
  assumes conn: "SemiAutomaton_is_initially_connected \<A>"
  shows "\<L> \<A> = {} \<longleftrightarrow> \<F> \<A> = {}"
proof 
  assume "\<F> \<A> = {}" thus "\<L> \<A> = {}"
    apply (rule_tac set_eqI)
    apply (simp add: \<L>_def NFA_accept_def)
  done
next
  assume L_eq: "\<L> \<A> = {}"
 
  show "\<F> \<A> = {}" 
  proof (rule ccontr)
    assume "\<F> \<A> \<noteq> {}"
    then obtain q where q_in_F: "q \<in> \<F> \<A>" by auto
    from \<F>_consistent q_in_F have q_in_Q: "q \<in> \<Q> \<A>" by auto

    from conn q_in_Q obtain i w where
      i_in:  "i \<in> \<I> \<A>" and 
      reach: "LTS_is_reachable (\<Delta> \<A>) i w q"
      unfolding SemiAutomaton_is_initially_connected_alt_def
    by auto

    have "w \<in> \<L> \<A>"
      apply (simp add: \<L>_def NFA_accept_def)
      apply (metis i_in q_in_F reach)
    done
    with L_eq show False by simp
  qed
qed


subsection \<open> Constructing from a list representation \<close>

fun construct_NFA_aux where 
   "construct_NFA_aux \<A> (q1, l, q2) =
    \<lparr> \<Q>=insert q1 (insert q2 (\<Q> \<A>)),
      \<Sigma>=\<Sigma> \<A> \<union> set l,
      \<Delta>=\<Delta> \<A> \<union> { (q1,a,q2) | a. a \<in> set l}, 
      \<I> = \<I> \<A>, \<F> = \<F> \<A>\<rparr>"

fun NFA_construct where
   "NFA_construct (Q, A, D, I, F) =
    (let \<A> = (SemiAutomaton_construct (Q, A, D, I)) in
     (SemiAutomaton_to_NFA \<A> (set F)) \<lparr> \<Q> := \<Q> \<A> \<union> set F \<rparr>)"
declare NFA_construct.simps [simp del]

lemma NFA_construct_fold_def :
   "NFA_construct (Q, A, D, I, F) =
    foldl construct_NFA_aux 
    \<lparr> \<Q>=set (Q @ I @ F), \<Sigma>=set A, \<Delta>={}, \<I> =set I, \<F> = set F\<rparr> D"
proof -
  have aux: "\<And>DD. 
    (let \<A> = foldl construct_SemiAutomaton_aux
              \<lparr>\<Q> = set (Q @ I), \<Sigma> = set A, \<Delta> = DD,
                 \<I> = set I\<rparr> D
     in SemiAutomaton_to_NFA \<A> (set F)\<lparr>\<Q> := \<Q> \<A> \<union> set F\<rparr>) =
    foldl construct_NFA_aux
     \<lparr>\<Q> = set (Q @ I @ F), \<Sigma> = set A, \<Delta> = DD, \<I> = set I,
        \<F> = set F\<rparr> D" 
  proof (induct D arbitrary: Q A)
    case Nil thus ?case
      by (auto simp add: SemiAutomaton_to_NFA_def)
  next
    case (Cons qaq' D') note indhyp = Cons(1)
    obtain q as q' where qaq'_eq[simp]: "qaq' = (q, as, q')"
      using prod_cases3 by blast

    from indhyp[of "q # q' # Q" "A @ as"]
    show ?case by simp
  qed

  from aux[of "{}"] show ?thesis
    by (simp add: NFA_construct.simps SemiAutomaton_construct.simps)
qed

lemma NFA_construct_alt_def :
  "NFA_construct (Q, A, D, I, F) =
   \<lparr> \<Q>=set Q \<union> set I \<union> set F \<union>
       set (map fst D) \<union>
       set (map (snd \<circ> snd) D), \<Sigma>=set A \<union> \<Union> (set (map (set \<circ> fst \<circ> snd) D)),
       \<Delta> = { (q1,a,q2) . (\<exists>l. (q1, l, q2) \<in> set D \<and> a \<in> set l)}, \<I> = set I, \<F> = set F\<rparr>"
unfolding NFA_construct.simps SemiAutomaton_to_NFA_def SemiAutomaton_construct_alt_def
by auto

fun NFA_construct_simple where
  "NFA_construct_simple (Q, A, D, I, F) =
   NFA_construct (Q, A, map (\<lambda>(q1, a, q2). (q1, [a], q2)) D, I, F)" 

lemma NFA_construct___is_well_formed :
  "NFA (NFA_construct l)"
proof -
  obtain Q A D I F where l_eq: "l = (Q, A, D, I, F)"
    using NFA_construct.cases by blast
  
  define SA where "SA \<equiv> SemiAutomaton_construct (Q, A, D, I)"
  have "FinSemiAutomaton SA" unfolding SA_def 
    by (simp add: SemiAutomaton_construct___is_well_formed)

  thus ?thesis
    unfolding NFA_construct.simps l_eq NFA_full_def
              FinSemiAutomaton_full_def
    by (simp add: subset_iff SA_def SemiAutomaton_construct_alt_def)
qed

lemma NFA_construct_exists :
fixes \<A> :: "('q, 'a) NFA_rec"
assumes wf_A: "NFA \<A>"
shows "\<exists>Q A D I F. \<A> = NFA_construct (Q, A, D, I, F)"
proof -
  interpret NFA_A: NFA \<A> by (fact wf_A)

  from NFA_A.finite_\<Sigma> have "finite (\<Sigma> (SemiAutomaton.truncate \<A>))"
    by (simp add: SemiAutomaton_rec.defs)
  with SemiAutomaton_construct_exists[of "SemiAutomaton.truncate \<A>"]
       NFA_A.FinSemiAutomaton_axioms 
  obtain Q A D I where SA_OK: 
     "SemiAutomaton_construct (Q, A, D, I) = SemiAutomaton_rec.truncate \<A>" by auto

  from finite_list[OF NFA_A.finite_\<F>] obtain F where "set F = \<F> \<A>" .. note set_F = this 

  from NFA_A.\<F>_consistent
  have "NFA_construct (Q, A, D, I, F) = \<A>"
    apply (cases \<A>)
    apply (auto simp add: NFA_construct.simps SA_OK Let_def SemiAutomaton_to_NFA_def
                          SemiAutomaton_rec.defs set_F )
  done
  thus ?thesis by blast
qed

subsection \<open> Removing states \<close>
  
definition NFA_remove_states :: "('q, 'a, _) NFA_rec_scheme \<Rightarrow> 'q set \<Rightarrow> ('q, 'a) NFA_rec" where
"NFA_remove_states \<A> S == 
 SemiAutomaton_to_NFA (SemiAutomaton_remove_states \<A> S) (\<F> \<A> - S)"

lemma NFA_remove_states_\<I> [simp] : "\<I> (NFA_remove_states \<A> S) = \<I> \<A> - S" by (simp add: NFA_remove_states_def)
lemma NFA_remove_states_\<Q> [simp] : "\<Q> (NFA_remove_states \<A> S) = \<Q> \<A> - S" by (simp add: NFA_remove_states_def)
lemma NFA_remove_states_\<F> [simp] : "\<F> (NFA_remove_states \<A> S) = \<F> \<A> - S" by (simp add: NFA_remove_states_def)
lemma NFA_remove_states_\<Sigma> [simp] : "\<Sigma> (NFA_remove_states \<A> S) = \<Sigma> \<A>" by (simp add: NFA_remove_states_def)
lemma NFA_remove_states_\<Delta> [simp] : "x \<in> \<Delta> (NFA_remove_states \<A> S) \<longleftrightarrow> 
                x \<in> \<Delta> \<A> \<and> fst x \<notin> S \<and> snd (snd x) \<notin> S" by (cases x, simp add: NFA_remove_states_def)

lemma NFA_remove_states_full_def :
  "NFA_remove_states \<A> S =  \<lparr>
       \<Q> = \<Q> \<A> - S, \<Sigma> = \<Sigma> \<A>,
       \<Delta> = {(s1, a, s2).
            (s1, a, s2) \<in> \<Delta> \<A> \<and> s1 \<notin> S \<and> s2 \<notin> S},
       \<I> = \<I> \<A> - S, \<F> = \<F> \<A> - S\<rparr>"
unfolding NFA_remove_states_def SemiAutomaton_remove_states_def SemiAutomaton_to_NFA_def
by simp

lemma NFA_remove_states___is_well_formed : 
  assumes wf: "NFA \<A>"
  shows "NFA (NFA_remove_states \<A> S)"
proof -
  interpret NFA \<A> by (fact wf)
  have "\<Delta> (NFA_remove_states \<A> S) \<subseteq> \<Delta> \<A>"
    unfolding NFA_remove_states_full_def
    by auto
  with rev_finite_subset finite_\<Delta> have "finite (\<Delta> (NFA_remove_states \<A> S))" .
  thus ?thesis
    using \<Delta>_consistent finite_\<Q> \<F>_consistent \<I>_consistent finite_\<Sigma>
    by unfold_locales auto
qed

lemma NFA_remove_states_empty [simp] : "NFA_remove_states \<A> {} = \<A>"
  by (rule NFA_rec.equality, simp_all add: set_eq_iff)

lemma NFA_remove_states_NFA_remove_states [simp] : "NFA_remove_states (NFA_remove_states \<A> S1) S2 = 
  NFA_remove_states \<A> (S1 \<union> S2)"
  by (rule NFA_rec.equality, auto simp add: NFA_remove_states_def)

lemma NFA_remove_states_\<L>_subset : "\<L> (NFA_remove_states \<A> S) \<subseteq> \<L> \<A>"
using SemiAutomaton_remove_states_fin_run_LTS_impl [of \<A> S]
by (auto simp add: \<L>_def NFA_accept_run_def NFA_remove_states_def
                   SemiAutomaton_is_fin_run_def)

lemma NFA_remove_states_\<L>_in_state_iff : 
assumes Q_unreach: "\<And>q'. q'\<in>Q \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) q q'"
shows "\<L>_in_state (NFA_remove_states \<A> Q) q = \<L>_in_state \<A> q"
using SemiAutomaton_remove_states_reachable_eq [of Q \<A>, OF Q_unreach]
apply (simp add: \<L>_in_state_def NFA_remove_states_def set_eq_iff Bex_def)
apply (metis LTS_is_unreachable_def Q_unreach)
done

lemma NFA_remove_states_\<L>_iff : 
assumes unreach_asm: "\<And>q q'. \<lbrakk>q \<in> \<I> \<A>; q' \<in> Q\<rbrakk> \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) q q'"
shows "\<L> (NFA_remove_states \<A> Q) = \<L> \<A>"
using SemiAutomaton_remove_states_reachable_eq [of Q \<A>]
apply (simp add: \<L>_def NFA_accept_def NFA_remove_states_def set_eq_iff Bex_def)
apply (metis LTS_is_unreachable_def LTS_is_unreachable_not_refl unreach_asm)
done

lemma NFA_remove_states_accept_iff : 
assumes unreach_asm: "\<And>q q'. \<lbrakk>q \<in> \<I> \<A>; q'\<in> Q\<rbrakk> \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) q q'"
shows "NFA_accept (NFA_remove_states \<A> Q) w = NFA_accept \<A> w"
using assms
by (simp add: NFA_accept_alt_def NFA_remove_states_\<L>_iff)

lemma NFA_unreachable_states_alt_def :
"SemiAutomaton_unreachable_states \<A> = {q. \<L>_left \<A> q = {}}"
by (simp add: SemiAutomaton_unreachable_states_def \<L>_left_def LTS_is_unreachable_def, auto)

definition NFA_remove_unreachable_states where
  "NFA_remove_unreachable_states \<A> = NFA_remove_states \<A> (SemiAutomaton_unreachable_states \<A>)"

lemma NFA_remove_unreachable_states_alt_def :
  "NFA_remove_unreachable_states \<A> = 
   SemiAutomaton_to_NFA
     (SemiAutomaton_remove_unreachable_states \<A>)
     (\<F> \<A> - SemiAutomaton_unreachable_states \<A>)"
unfolding NFA_remove_unreachable_states_def NFA_remove_states_def
          SemiAutomaton_remove_unreachable_states_def[symmetric] ..

lemma (in NFA) NFA_remove_unreachable_states_alt_def2 :
  "NFA_remove_unreachable_states \<A> = 
   SemiAutomaton_to_NFA
     (SemiAutomaton_remove_unreachable_states \<A>)
     (\<F> \<A> \<inter> SemiAutomaton_reachable_states \<A>)"
unfolding NFA_remove_unreachable_states_alt_def
using \<F>_consistent
by (simp add: set_eq_iff SemiAutomaton_not_in_unreachable_states_eq)

lemma NFA_remove_unreachable_states_no_change :
assumes wf_A: "NFA \<A>"
shows "NFA_remove_unreachable_states \<A> = \<A> \<longleftrightarrow>
       SemiAutomaton_is_initially_connected \<A>"
using wf_A SemiAutomaton.\<Delta>_consistent[of \<A>] SemiAutomaton.\<I>_consistent[of \<A>]
unfolding NFA_remove_unreachable_states_def NFA_remove_states_def SemiAutomaton_to_NFA_def
          SemiAutomaton_is_initially_connected_def NFA_alt_def FinSemiAutomaton_alt_def
apply (cases \<A>)
apply (auto simp add: set_eq_iff)
done

lemma NFA_remove_unreachable_states_\<L> [simp] :
  "\<L> (NFA_remove_unreachable_states \<A>) = \<L> \<A>"
apply (simp add: NFA_remove_unreachable_states_def)
apply (rule NFA_remove_states_\<L>_iff)
apply (simp add: SemiAutomaton_unreachable_states_def)
done

lemma NFA_remove_unreachable_states_\<L>_in_state [simp] :
assumes q_in_Q: "q \<in> \<Q> (NFA_remove_unreachable_states \<A>)"
shows "\<L>_in_state (NFA_remove_unreachable_states \<A>) q = \<L>_in_state \<A> q"
proof -
  from q_in_Q have "q \<notin> SemiAutomaton_unreachable_states \<A>"
    by (simp add: NFA_remove_unreachable_states_def)
  then obtain q0 w where 
    "q0 \<in> \<I> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) q0 w q"
    by (auto simp add: SemiAutomaton_unreachable_states_def LTS_is_unreachable_def)
  then have Q_OK: "\<And>q'. q' \<in> SemiAutomaton_unreachable_states \<A> \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) q q'"
    by (simp add: SemiAutomaton_unreachable_states_def,
        metis LTS_is_unreachable_reachable_start)

  note NFA_remove_states_\<L>_in_state_iff [where q = q and \<A> = \<A> and
     Q = "SemiAutomaton_unreachable_states \<A>", OF Q_OK]
  thus ?thesis by (simp add: NFA_remove_unreachable_states_def)
qed

lemma NFA_remove_unreachable_states_accept_iff [simp] : 
"NFA_accept (NFA_remove_unreachable_states \<A>) w = NFA_accept \<A> w"
by (simp add: NFA_accept_alt_def)

lemma NFA_remove_unreachable_states___is_well_formed [simp] : 
"NFA \<A> \<Longrightarrow> NFA (NFA_remove_unreachable_states \<A>)"
by (simp add: NFA_remove_unreachable_states_def NFA_remove_states___is_well_formed)

lemma NFA_remove_unreachable_states_\<I> [simp] :
  "\<I> (NFA_remove_unreachable_states \<A>) = \<I> \<A>"
by (simp add: NFA_remove_unreachable_states_alt_def)

lemma [simp] : "\<Sigma> (NFA_remove_unreachable_states \<A>) = \<Sigma> \<A>"
by (simp add: NFA_remove_unreachable_states_def)

lemma NFA_unreachable_states_NFA_remove_unreachable_states :
  "SemiAutomaton_unreachable_states (NFA_remove_unreachable_states \<A>) =
   SemiAutomaton_unreachable_states \<A>"
by (simp add: NFA_remove_unreachable_states_alt_def NFA_remove_states_def
              SemiAutomaton_unreachable_states_SemiAutomaton_remove_unreachable_states)

lemma NFA_remove_unreachable_states_NFA_remove_unreachable_states [simp] :
  "NFA_remove_unreachable_states (NFA_remove_unreachable_states \<A>) = NFA_remove_unreachable_states \<A>"
apply (simp add: NFA_remove_unreachable_states_def)
apply (simp add: NFA_remove_unreachable_states_def [symmetric]
                 NFA_unreachable_states_NFA_remove_unreachable_states)
done


subsection \<open> Rename States / Combining \<close>

definition NFA_rename_states :: 
"('q1, 'a, _) NFA_rec_scheme \<Rightarrow> ('q1 \<Rightarrow> 'q2) \<Rightarrow> ('q2, 'a) NFA_rec" where
"NFA_rename_states \<A> f \<equiv> 
 SemiAutomaton_rename_states_ext (\<lambda>f m. \<lparr>\<F> = f ` (\<F> m) \<rparr>) \<A> f"

lemma NFA_rename_states_\<I> [simp] : "\<I> (NFA_rename_states \<A> f) = f ` \<I> \<A>" by (simp add: NFA_rename_states_def)
lemma NFA_rename_states_\<Q> [simp] : "\<Q> (NFA_rename_states \<A> f) = f ` \<Q> \<A>" by (simp add: NFA_rename_states_def)
lemma NFA_rename_states_\<F> [simp] : "\<F> (NFA_rename_states \<A> f) = f ` \<F> \<A>" 
  by (simp add: NFA_rename_states_def SemiAutomaton_rename_states_ext_def)
lemma NFA_rename_states_\<Sigma> [simp] : "\<Sigma> (NFA_rename_states \<A> S) = \<Sigma> \<A>" by (simp add: NFA_rename_states_def)
lemma NFA_rename_states_\<Delta> [simp] : "(fq, \<sigma>, fq') \<in> \<Delta> (NFA_rename_states \<A> f) \<longleftrightarrow> 
                (\<exists>q q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<and> (fq = f q) \<and> (fq' = f q'))" 
  by (auto simp add: NFA_rename_states_def)

lemma NFA_rename_states_full_def :
"NFA_rename_states \<A> f = \<lparr>\<Q> = f ` \<Q> \<A>, \<Sigma> = \<Sigma> \<A>,
       \<Delta> = {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>},
       \<I> = f ` \<I> \<A>, \<F> = f ` \<F> \<A>\<rparr>"
unfolding NFA_rename_states_def SemiAutomaton_rename_states_ext_def by simp

lemma NFA_rename_states___is_well_formed :
  "NFA \<A> \<Longrightarrow> NFA (NFA_rename_states \<A> f)"
by (auto simp: NFA_full_def NFA_rename_states_full_def)

lemma NFA_rename_states_id [simp] : "NFA_rename_states \<A> id = \<A>" 
  unfolding NFA_rename_states_def
  by (cases \<A>) (simp)

lemma NFA_rename_states_NFA_rename_states [simp] : 
   "NFA_rename_states (NFA_rename_states \<A> f1) f2 = 
    NFA_rename_states \<A> (f2 \<circ> f1)" 
by (auto simp add: NFA_rename_states_def SemiAutomaton_rename_states_ext_def 
   set_eq_iff)

lemma (in NFA) NFA_rename_states_agree_on_Q :
assumes f12_agree: "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> f1 q = f2 q"
shows "NFA_rename_states \<A> f1 = NFA_rename_states \<A> f2"
unfolding NFA_rename_states_def
apply (rule SemiAutomaton_rename_states_ext_agree_on_Q[of f1 f2, OF f12_agree])
apply simp
apply (insert \<F>_consistent f12_agree)
apply (simp add: subset_iff set_eq_iff image_iff)
done

lemma \<L>_in_state_rename_subset1 :
   "\<L>_in_state \<A> q \<subseteq> \<L>_in_state (NFA_rename_states \<A> f) (f q)"
apply (simp add: \<L>_in_state_def subset_iff)
apply (simp add: NFA_rename_states_def)
apply (metis LTS_is_reachable___SemiAutomaton_rename_statesE)
done

definition NFA_is_equivalence_rename_fun where
"NFA_is_equivalence_rename_fun \<A> f = 
 (\<forall>q\<in>\<Q> \<A>. \<forall>q'\<in>\<Q> \<A>. (f q = f q') \<longrightarrow> (\<L>_in_state \<A> q = \<L>_in_state \<A> q'))"

definition NFA_is_strong_equivalence_rename_fun where
"NFA_is_strong_equivalence_rename_fun \<A> f = 
 (\<forall>q\<in>\<Q> \<A>. \<forall>q'\<in>\<Q> \<A>. ((f q = f q') \<longleftrightarrow> (\<L>_in_state \<A> q = \<L>_in_state \<A> q')))"

lemma NFA_is_strong_equivalence_rename_funE :
"\<lbrakk>NFA_is_strong_equivalence_rename_fun \<A> f;
  q \<in> \<Q> \<A>; q'\<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> 
  f q = f q' \<longleftrightarrow> (\<L>_in_state \<A> q = \<L>_in_state \<A> q')"
unfolding NFA_is_strong_equivalence_rename_fun_def by metis

lemma NFA_is_strong_equivalence_rename_fun___weaken :
  "NFA_is_strong_equivalence_rename_fun \<A> f \<Longrightarrow>
   NFA_is_equivalence_rename_fun \<A> f"
by (simp add: NFA_is_equivalence_rename_fun_def NFA_is_strong_equivalence_rename_fun_def)

lemma NFA_is_strong_equivalence_rename_fun_exists :
  "\<exists>f::('a \<Rightarrow> 'a). (NFA_is_strong_equivalence_rename_fun \<A> f \<and> (\<forall>q \<in> \<Q> \<A>. f q \<in> \<Q> \<A>))"
proof -
  define fe where "fe \<equiv> \<lambda>l. SOME q. q \<in> \<Q> \<A> \<and> \<L>_in_state \<A> q = l"
  define f where "f \<equiv> \<lambda>q. fe (\<L>_in_state \<A> q)"

  have f_lang : "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow>
      f q \<in> \<Q> \<A> \<and> 
      \<L>_in_state \<A> (f q) = \<L>_in_state \<A> q"
    by (simp add: fe_def f_def, rule_tac someI_ex, auto)
    
  have "NFA_is_strong_equivalence_rename_fun \<A> f"
    by (simp add: NFA_is_strong_equivalence_rename_fun_def,
           metis f_def f_lang)
  with f_lang show ?thesis by metis
qed

lemma NFA_is_strong_equivalence_rename_fun___isomorph :
fixes f1 :: "'a \<Rightarrow> 'b"
  and f2 :: "'a => 'c"
  and \<A> :: "('a, 'l, 'x) NFA_rec_scheme"
assumes f1_OK: "NFA_is_strong_equivalence_rename_fun \<A> f1"
    and f2_OK: "NFA_is_strong_equivalence_rename_fun \<A> f2"
shows "\<exists>f12. (\<forall>q\<in>\<Q> \<A>. f2 q = (f12 (f1 q))) \<and> inj_on f12 (f1 ` (\<Q> \<A>))"
proof -
  define f12 where "f12 \<equiv> \<lambda>q. f2 ((inv_into (\<Q> \<A>) f1) q)"

  have inj_f12: "inj_on f12 (f1 ` (\<Q> \<A>))"
  unfolding inj_on_def f12_def
  proof (intro ballI impI) 
    fix q1 q2 :: 'b
    assume q1_in_f1_Q: "q1 \<in> f1 ` \<Q> \<A>"
    assume q2_in_f1_Q: "q2 \<in> f1 ` \<Q> \<A>"
    assume f2_eq: "f2 (inv_into (\<Q> \<A>) f1 q1) = f2 (inv_into (\<Q> \<A>) f1 q2)"

    let ?q1' = "inv_into (\<Q> \<A>) f1 q1"
    let ?q2' = "inv_into (\<Q> \<A>) f1 q2"

    from inv_into_into[OF q1_in_f1_Q] have q1'_in_Q: "?q1' \<in> \<Q> \<A>" .
    from inv_into_into[OF q2_in_f1_Q] have q2'_in_Q: "?q2' \<in> \<Q> \<A>" .

    from f_inv_into_f[OF q1_in_f1_Q] have q1_eq: "f1 ?q1' = q1" by simp
    from f_inv_into_f[OF q2_in_f1_Q] have q2_eq: "f1 ?q2' = q2" by simp


    from NFA_is_strong_equivalence_rename_funE [OF f2_OK q1'_in_Q q2'_in_Q] f2_eq
    have q12'_equiv: "\<L>_in_state \<A> ?q1' = \<L>_in_state \<A> ?q2'"
      unfolding NFA_is_strong_equivalence_rename_fun_def
      by simp

    with NFA_is_strong_equivalence_rename_funE [OF f1_OK q1'_in_Q q2'_in_Q]
    show "q1 = q2"
      by (simp add: q1_eq q2_eq)
  qed

  have f2_eq: "(\<forall>q\<in>\<Q> \<A>. f2 q = f12 (f1 q))"
  proof (intro ballI)
    fix q
    assume q_in_Q: "q\<in>\<Q> \<A>"

    let ?q' = "inv_into (\<Q> \<A>) f1 (f1 q)"

    from q_in_Q have f1_q_in_f1_Q: "f1 q \<in> f1 ` (\<Q> \<A>)" by simp


    from inv_into_into [OF f1_q_in_f1_Q] 
    have q'_in_Q: "?q' \<in> \<Q> \<A>" by simp

    from f_inv_into_f[OF f1_q_in_f1_Q] have "f1 ?q' = f1 q" by simp
    with NFA_is_strong_equivalence_rename_funE [OF f1_OK q'_in_Q q_in_Q] 
    have q_q'_equiv: "\<L>_in_state \<A> ?q' = \<L>_in_state \<A> q"
      by simp

    from NFA_is_strong_equivalence_rename_funE [OF f2_OK q'_in_Q q_in_Q] q_q'_equiv
    have "f2 q = f2 ?q'" by simp

    thus "f2 q = f12 (f1 q)"
      unfolding f12_def
      by simp
  qed
    
  from f2_eq inj_f12 show ?thesis by blast
qed

lemma (in NFA) \<L>_in_state_rename_subset2 :
assumes equiv_f : "NFA_is_equivalence_rename_fun \<A> f" 
assumes q_in_Q  : "q \<in> \<Q> \<A>"
shows "\<L>_in_state (NFA_rename_states \<A> f) (f q) \<subseteq> \<L>_in_state \<A> q"
proof -
have "\<And>w q'. \<lbrakk>q' \<in> \<F> \<A>; LTS_is_reachable (\<Delta> (NFA_rename_states \<A> f)) (f q) w (f q')\<rbrakk> \<Longrightarrow>
              w \<in> \<L>_in_state \<A> q"
proof -
  {
    fix w q'
    assume q'_in_F: "q' \<in> \<F> \<A>"
    from q'_in_F have q'_in_Q: "q' \<in> \<Q> \<A>" using \<F>_consistent by (auto simp add: NFA_def)
    have "\<lbrakk>q \<in> \<Q> \<A>; LTS_is_reachable (\<Delta> (NFA_rename_states \<A> f)) (f q) w (f q')\<rbrakk> \<Longrightarrow>
           w \<in> \<L>_in_state \<A> q"
    proof (induct w arbitrary: q)
      case Nil
      note q_in_Q = Nil(1)
      from Nil(2) have "f q = f q'" by simp
      with equiv_f q_in_Q q'_in_Q have "\<L>_in_state \<A> q = \<L>_in_state \<A> q'" 
        by (metis NFA_is_equivalence_rename_fun_def) 
      with q'_in_F have "q \<in> \<F> \<A>" by (metis \<L>_in_state___in_\<F>)
      thus "[] \<in> \<L>_in_state \<A> q" by simp
    next
      case (Cons \<sigma> w)
      note ind_hyp = Cons(1) 
      note q_in_Q = Cons(2) 
      note is_reach_\<sigma>w' = Cons(3)
  
      from is_reach_\<sigma>w' obtain q'' q''' where
         f_q'''_eq: "f q''' = f q" and
         in_\<Delta>: "(q''', \<sigma>, q'') \<in> \<Delta> \<A>" and
         in_r\<Delta>: "(f q, \<sigma>, f q'') \<in>  (\<Delta> (NFA_rename_states \<A> f))" and
         is_reach_w': "LTS_is_reachable (\<Delta> (NFA_rename_states \<A> f)) (f q'') w (f q')"
      by (auto, metis) 
  
      from in_\<Delta> have q'''_in_Q : "q''' \<in> \<Q> \<A>" and
                     q''_in_Q: "q'' \<in> \<Q> \<A>"
        using \<Delta>_consistent by simp_all
  
      from q''_in_Q ind_hyp is_reach_w' have
         "w \<in> \<L>_in_state \<A> q''" by simp
      with in_\<Delta> have "(\<sigma> # w) \<in> \<L>_in_state \<A> q'''" by auto 
      with q_in_Q q'''_in_Q f_q'''_eq equiv_f show ?case
        by (metis NFA_is_equivalence_rename_fun_def)
    qed
  }
  then show "\<And>w q'. \<lbrakk>q' \<in> \<F> \<A>; LTS_is_reachable (\<Delta> (NFA_rename_states \<A> f)) (f q) w (f q')\<rbrakk> \<Longrightarrow> w \<in> \<L>_right \<A> q"
    using q_in_Q by blast
qed
thus ?thesis
  by (auto simp add: \<L>_in_state_def subset_iff)
qed

lemma (in NFA) \<L>_in_state_rename_iff :
assumes equiv_f : "NFA_is_equivalence_rename_fun \<A> f" 
assumes q_in_Q  : "q \<in> \<Q> \<A>"
shows "\<L>_in_state (NFA_rename_states \<A> f) (f q) = \<L>_in_state \<A> q"
using assms
by (metis \<L>_in_state_rename_subset1 \<L>_in_state_rename_subset2 set_eq_subset)

lemma (in NFA) \<L>_rename_iff :
assumes equiv_f : "NFA_is_equivalence_rename_fun \<A> f" 
shows "\<L> (NFA_rename_states \<A> f) = \<L> \<A>"
proof -
  have "\<And>q. q \<in> \<I> \<A> \<Longrightarrow> q \<in> \<Q> \<A>" using \<I>_consistent by auto
  thus ?thesis
    by (simp add: \<L>_alt_def set_eq_iff Bex_def,
        metis \<L>_in_state_rename_iff equiv_f)
qed

lemma (in NFA) \<L>_left_rename_iff :
assumes equiv_f : "NFA_is_equivalence_rename_fun \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = {q}\<rparr> f" 
    and q_in: "q \<in> \<Q> \<A>"
shows "\<L>_left (NFA_rename_states \<A> f) (f q) = \<L>_left \<A> q"
proof -
  obtain \<A>' where \<A>'_def: "\<A>' = \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = {q}\<rparr>"
    by blast

  from NFA_axioms \<A>'_def q_in have wf_\<A>': "NFA \<A>'"
    unfolding NFA_full_def by simp

  have left_A: "\<L>_left \<A> q = \<L> \<A>'" 
    unfolding \<L>_left_alt_def \<A>'_def ..

  have left_reA: "\<L>_left (NFA_rename_states \<A> f) (f q) = \<L>  (NFA_rename_states \<A>' f)"
    unfolding \<L>_left_alt_def \<A>'_def 
    by (simp add: NFA_rename_states_def SemiAutomaton_rename_states_ext_def SemiAutomaton_to_NFA_def)

  from equiv_f have equiv_f' : "NFA_is_equivalence_rename_fun \<A>' f"
     unfolding \<A>'_def
     by simp

  from NFA.\<L>_rename_iff [OF wf_\<A>' equiv_f']
       left_A left_reA
  show ?thesis by simp
qed

lemma (in NFA) \<L>_left_rename_iff_inj :
assumes inj_f : "inj_on f (\<Q> \<A>)" 
    and q_in: "q \<in> \<Q> \<A>"
shows "\<L>_left (NFA_rename_states \<A> f) (f q) = \<L>_left \<A> q"
proof -
  from inj_f have equiv_f : "NFA_is_equivalence_rename_fun \<lparr>\<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = {q}\<rparr> f" 
    unfolding NFA_is_equivalence_rename_fun_def inj_on_def
    by auto

  from \<L>_left_rename_iff [OF equiv_f q_in] 
  show ?thesis .
qed

lemma (in NFA) NFA_rename_states___accept :
assumes equiv_f : "NFA_is_equivalence_rename_fun \<A> f" 
shows "NFA_accept (NFA_rename_states \<A> f) w = NFA_accept \<A> w"
using assms
by (simp add: NFA_accept_alt_def \<L>_rename_iff)


text \<open> Renaming without combining states is fine. \<close>
lemma NFA_is_equivalence_rename_funI___inj_used : 
  "inj_on f (\<Q> \<A>) \<Longrightarrow> NFA_is_equivalence_rename_fun \<A> f"
by (auto simp add: inj_on_def NFA_is_equivalence_rename_fun_def)

text \<open> Combining without renaming is fine as well. \<close>  
lemma NFA_is_equivalence_rename_funI___intro2 :
"(\<forall>q \<in> \<Q> \<A>. ((f q \<in> \<Q> \<A>) \<and> (\<L>_in_state \<A> (f q) = \<L>_in_state \<A> q))) \<Longrightarrow> NFA_is_equivalence_rename_fun \<A> f"
by (simp add: inj_on_def NFA_is_equivalence_rename_fun_def, metis)


subsection \<open> Isomorphy \<close>

definition NFA_isomorphic where
  "NFA_isomorphic \<A>1 \<A>2 \<equiv>
   (\<exists>f. inj_on f (\<Q> \<A>1) \<and> \<A>2 = NFA_rename_states \<A>1 f)"

lemma NFA_isomorphic_alt_def :
  "NFA_isomorphic \<A>1 \<A>2 =
   SemiAutomaton_isomorphic_ext (\<lambda>f m. \<lparr>\<F> = f ` (\<F> m) \<rparr>) \<A>1 \<A>2"
unfolding NFA_isomorphic_def SemiAutomaton_isomorphic_ext_def NFA_rename_states_def 
by simp

lemma NFA_isomorphic_implies_SemiAutomaton_isomorphic :
  "NFA_isomorphic \<A>1 \<A>2 \<Longrightarrow>
   SemiAutomaton_isomorphic \<A>1 (SemiAutomaton.truncate \<A>2)"
unfolding NFA_isomorphic_alt_def
by (rule SemiAutomaton_isomorphic_ext_truncate2)

lemma NFA_isomorphic_refl :
  "NFA_isomorphic \<A> \<A>"
unfolding NFA_isomorphic_alt_def
apply (rule SemiAutomaton_isomorphic_ext_refl)
apply (cases \<A>, simp)
done

lemma NFA_isomorphic_bijections :
assumes wf_NFA1 : "NFA \<A>1"
    and iso_\<A>1_\<A>2: "NFA_isomorphic \<A>1 \<A>2"
shows "(\<exists>f1 f2. \<A>2 = NFA_rename_states \<A>1 f1 \<and>
                \<A>1 = NFA_rename_states \<A>2 f2 \<and>
                (\<forall>q \<in> \<Q> \<A>1. f2 (f1 q) = q) \<and>
                (\<forall>q \<in> \<Q> \<A>2. f1 (f2 q) = q) \<and>
                (inj_on f1 (\<Q> \<A>1)) \<and> (inj_on f2 (\<Q> \<A>2)))"
proof -
  from wf_NFA1 have wf': "SemiAutomaton \<A>1" 
    unfolding NFA_alt_def FinSemiAutomaton_def by simp

  show ?thesis
    unfolding NFA_rename_states_def
    apply (rule SemiAutomaton_isomorphic_ext_bijections[OF wf' iso_\<A>1_\<A>2[unfolded NFA_isomorphic_alt_def]])
    apply (case_tac \<A>)
    apply (case_tac \<A>1)
    apply (insert NFA.\<F>_consistent[OF wf_NFA1])
    apply (auto simp add: subset_iff image_iff)
  done
qed

lemma NFA_isomorphic_sym_impl :
assumes wf_NFA1 : "NFA \<A>1"
    and equiv_\<A>1_\<A>2: "NFA_isomorphic \<A>1 \<A>2"
shows "NFA_isomorphic \<A>2 \<A>1"
using NFA_isomorphic_bijections [OF wf_NFA1 equiv_\<A>1_\<A>2]
unfolding NFA_isomorphic_def by blast

lemma NFA_isomorphic_sym :
assumes wf_NFA1: "NFA \<A>1"
    and wf_NFA2: "NFA \<A>2"
shows "NFA_isomorphic \<A>1 \<A>2 \<longleftrightarrow> NFA_isomorphic \<A>2 \<A>1"
using assms
by (metis NFA_isomorphic_sym_impl)

lemma NFA_isomorphic___implies_well_formed :
assumes wf_NFA1: "NFA \<A>1"
    and equiv_\<A>1_\<A>2: "NFA_isomorphic \<A>1 \<A>2"
shows "NFA \<A>2"
using assms 
by (metis NFA_rename_states___is_well_formed NFA_isomorphic_def)

lemma NFA_isomorphic_trans :
assumes equiv_\<A>1_\<A>2: "NFA_isomorphic \<A>1 \<A>2"
    and equiv_\<A>2_\<A>3: "NFA_isomorphic \<A>2 \<A>3"
shows "NFA_isomorphic \<A>1 \<A>3"
using assms
unfolding NFA_isomorphic_alt_def
apply (rule SemiAutomaton_isomorphic_ext_trans)
apply (case_tac \<A>')
apply (auto)
done

text \<open> Normaly, one is interested in only well-formed automata. This simplifies
        reasoning about isomorphy. \<close>
definition NFA_isomorphic_wf where
  "NFA_isomorphic_wf \<A>1 \<A>2 \<equiv> NFA_isomorphic \<A>1 \<A>2 \<and> NFA \<A>1"

lemma NFA_isomorphic_wf_def___SemiAutomaton_isomorphic_wf_fin :
  "NFA_isomorphic_wf \<A>1 \<A>2 \<longleftrightarrow> SemiAutomaton_isomorphic_wf_fin_ext (\<lambda>f m. \<lparr>\<F> = f ` \<F> m\<rparr>) \<A>1 \<A>2 \<and>
                                NFA \<A>1"
unfolding NFA_isomorphic_wf_def NFA_isomorphic_alt_def SemiAutomaton_isomorphic_wf_fin_ext_def
          NFA_alt_def
by auto

lemma NFA_isomorphic_wf_def___SemiAutomaton_isomorphic_wf :
  "NFA_isomorphic_wf \<A>1 \<A>2 \<longleftrightarrow> SemiAutomaton_isomorphic_wf_ext (\<lambda>f m. \<lparr>\<F> = f ` \<F> m\<rparr>) \<A>1 \<A>2 \<and>
                                NFA \<A>1"
unfolding NFA_isomorphic_wf_def___SemiAutomaton_isomorphic_wf_fin
          NFA_alt_def FinSemiAutomaton_alt_def SemiAutomaton_isomorphic_wf_fin_ext_def
          SemiAutomaton_isomorphic_wf_ext_def
by auto

lemma NFA_isomorphic_wf_weaken :
  "NFA_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow>
   SemiAutomaton_isomorphic_wf_fin \<A>1 (SemiAutomaton.truncate \<A>2)"
unfolding NFA_isomorphic_wf_def___SemiAutomaton_isomorphic_wf_fin 
by (metis SemiAutomaton_isomorphic_ext_truncate2 SemiAutomaton_isomorphic_wf_fin_ext_def)

lemma NFA_isomorphic_wf_\<L> :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "\<L> \<A>1 = \<L> \<A>2"
proof -
  from equiv
  obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                 wf_\<A>1: "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  from inj_f have "NFA_is_equivalence_rename_fun \<A>1 f" by
    (simp add: NFA_is_equivalence_rename_funI___inj_used)

  note NFA.\<L>_rename_iff [OF wf_\<A>1 this]
  with \<A>2_eq show ?thesis by simp
qed

lemma NFA_isomorphic_wf_\<Sigma> :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "\<Sigma> \<A>1 = \<Sigma> \<A>2"
proof -
  from equiv
  obtain f where \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  with \<A>2_eq show ?thesis by simp
qed

lemma NFA_isomorphic_wf_accept :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_accept \<A>1 w = NFA_accept \<A>2 w"
using NFA_isomorphic_wf_\<L> [OF equiv]
by (simp add: set_eq_iff \<L>_def)

lemma NFA_isomorphic_wf_alt_def :
  "NFA_isomorphic_wf \<A>1 \<A>2 \<longleftrightarrow>
   NFA_isomorphic \<A>1 \<A>2 \<and> NFA \<A>1 \<and> NFA \<A>2"
unfolding NFA_isomorphic_wf_def
by (metis NFA_isomorphic___implies_well_formed)

lemma NFA_isomorphic_wf_sym :
  "NFA_isomorphic_wf \<A>1 \<A>2 = NFA_isomorphic_wf \<A>2 \<A>1"
unfolding NFA_isomorphic_wf_alt_def
by (metis NFA_isomorphic_sym)

lemma NFA_isomorphic_wf_trans :
  "\<lbrakk>NFA_isomorphic_wf \<A>1 \<A>2; NFA_isomorphic_wf \<A>2 \<A>3\<rbrakk> \<Longrightarrow>
   NFA_isomorphic_wf \<A>1 \<A>3"
unfolding NFA_isomorphic_wf_alt_def
by (metis NFA_isomorphic_trans)

lemma NFA_isomorphic_wf_refl :
  "NFA \<A>1 \<Longrightarrow> NFA_isomorphic_wf \<A>1 \<A>1"
unfolding NFA_isomorphic_wf_def
by (simp add: NFA_isomorphic_refl)

lemma NFA_isomorphic_wf_intro :
  "\<lbrakk>NFA \<A>1; NFA_isomorphic \<A>1 \<A>2\<rbrakk> \<Longrightarrow> NFA_isomorphic_wf \<A>1 \<A>2"
unfolding NFA_isomorphic_wf_def by simp

lemma NFA_isomorphic_wf_D :
  "NFA_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> NFA \<A>1"
  "NFA_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> NFA \<A>2"
  "NFA_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> NFA_isomorphic \<A>1 \<A>2"
  "NFA_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> NFA_isomorphic \<A>2 \<A>1"
unfolding NFA_isomorphic_wf_alt_def
by (simp_all, metis NFA_isomorphic_sym)
  
lemma NFA_isomorphic___NFA_rename_states :
"inj_on f (\<Q> \<A>) \<Longrightarrow> NFA_isomorphic \<A> (NFA_rename_states \<A> f)"
unfolding NFA_isomorphic_def
by blast

lemma NFA_isomorphic_wf___NFA_rename_states :
"\<lbrakk>inj_on f (\<Q> \<A>); NFA \<A>\<rbrakk> \<Longrightarrow> NFA_isomorphic_wf \<A> (NFA_rename_states \<A> f)"
unfolding NFA_isomorphic_def NFA_isomorphic_wf_def
by blast

lemma NFA_isomorphic_wf___rename_states_cong :
fixes \<A>1 :: "('q1, 'a) NFA_rec"
fixes \<A>2 :: "('q2, 'a) NFA_rec"
assumes inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
        inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
        equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (NFA_rename_states \<A>1 f1) (NFA_rename_states \<A>2 f2)"
proof -
  note wf_\<A>1 = NFA_isomorphic_wf_D(1)[OF equiv]
  note wf_\<A>2 = NFA_isomorphic_wf_D(2)[OF equiv]

  note eq_1 = NFA_isomorphic_wf___NFA_rename_states [OF inj_f1 wf_\<A>1]
  note eq_2 = NFA_isomorphic_wf___NFA_rename_states [OF inj_f2 wf_\<A>2]
  from eq_1 eq_2 equiv show ?thesis
    by (metis NFA_isomorphic_wf_trans NFA_isomorphic_wf_sym)
qed

lemma NFA_rename_states___NFA_remove_unreachable_states :
fixes \<A>1 :: "('q1, 'a) NFA_rec"
fixes \<A>2 :: "('q2, 'a) NFA_rec"
assumes \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f1" and
        \<A>1_eq: "\<A>1 = NFA_rename_states \<A>2 f2" and
        wf_\<A>1: "NFA \<A>1" and
        f2_f1: "\<And>q. q\<in>\<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q" 
shows "NFA_rename_states (NFA_remove_unreachable_states \<A>1) f1 = (NFA_remove_unreachable_states \<A>2)"
proof -
  note \<A>2_eq' = SemiAutomaton_rename_states_ext_truncate_sym[OF \<A>2_eq[unfolded NFA_rename_states_def]]
  note \<A>1_eq' = SemiAutomaton_rename_states_ext_truncate_sym[OF \<A>1_eq[unfolded NFA_rename_states_def]]

  from wf_\<A>1 have wf_\<A>1': "SemiAutomaton (SemiAutomaton.truncate \<A>1)"
    unfolding NFA_def FinSemiAutomaton_def by simp

  define S1 where "S1 \<equiv> SemiAutomaton_unreachable_states \<A>1"
  define S2 where "S2 \<equiv> SemiAutomaton_unreachable_states \<A>2"

  from SemiAutomaton_rename_states___SemiAutomaton_remove_unreachable_states 
         [OF \<A>2_eq' \<A>1_eq' wf_\<A>1', OF f2_f1]
  have sa_OK : "SemiAutomaton_rename_states
     (SemiAutomaton_remove_unreachable_states (SemiAutomaton_rec.truncate \<A>1)) f1 =
      SemiAutomaton_remove_unreachable_states (SemiAutomaton_rec.truncate \<A>2)"
    by (simp add: SemiAutomaton_rec.defs)

  from SemiAutomaton_rename_states___unreachable_states_iff 
         [OF \<A>2_eq' \<A>1_eq' wf_\<A>1', OF f2_f1]
  have sa_OK' : "\<And>q. q \<in> \<Q> (SemiAutomaton_rec.truncate \<A>1) \<Longrightarrow>
  (f1 q
   \<in> SemiAutomaton_unreachable_states
      (SemiAutomaton_rec.truncate \<A>2)) =
  (q \<in> SemiAutomaton_unreachable_states
         (SemiAutomaton_rec.truncate \<A>1) \<inter>
        \<Q> (SemiAutomaton_rec.truncate \<A>1))"
    by (simp add: SemiAutomaton_rec.defs)

  from NFA.\<F>_consistent[OF wf_\<A>1]
       \<A>2_eq
       S1_def[symmetric]
       S2_def[symmetric] sa_OK sa_OK'
  show ?thesis
    apply (cases \<A>1)
    apply (simp add: SemiAutomaton_rec.defs NFA_remove_unreachable_states_def 
                     SemiAutomaton_remove_unreachable_states_def
                     NFA_rename_states_def SemiAutomaton_rename_states_ext_def
                     SemiAutomaton_remove_states_def NFA_remove_states_def
                     SemiAutomaton_to_NFA_def SemiAutomaton_unreachable_states_def)
    apply clarify
    apply (auto simp add: set_eq_iff image_iff Bex_def subset_iff)
  done
qed

lemma NFA_isomorphic_wf___NFA_remove_unreachable_states :
fixes \<A>1 :: "('q1, 'a) NFA_rec"
fixes \<A>2 :: "('q2, 'a) NFA_rec"
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (NFA_remove_unreachable_states \<A>1) (NFA_remove_unreachable_states \<A>2)"
proof -
  from equiv
  obtain f1 f2 where 
     inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
     \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f1" and
     inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
     \<A>1_eq: "\<A>1 = NFA_rename_states \<A>2 f2" and
     wf_\<A>1: "NFA \<A>1" and
     wf_\<A>2: "NFA \<A>2" and
     f2_f1: "\<And>q. q\<in>\<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q" and
     f1_f2: "\<And>q. q\<in>\<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q"
    unfolding NFA_isomorphic_wf_alt_def 
    using NFA_isomorphic_bijections[of \<A>1 \<A>2]
    by blast

  have "\<Q> (NFA_remove_unreachable_states \<A>1) \<subseteq> \<Q> \<A>1"
    unfolding NFA_remove_unreachable_states_def by auto
  with inj_f1 have inj_f1' : "inj_on f1 (\<Q> (NFA_remove_unreachable_states \<A>1))"
    by (rule subset_inj_on)

  have \<A>2_eq' :
    "NFA_remove_unreachable_states \<A>2 = NFA_rename_states (NFA_remove_unreachable_states \<A>1) f1"
    using NFA_rename_states___NFA_remove_unreachable_states[OF \<A>2_eq \<A>1_eq wf_\<A>1] f2_f1
    by simp

  from inj_f1' \<A>2_eq' NFA_remove_unreachable_states___is_well_formed[OF wf_\<A>1]
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def
    by blast
qed
  

lemma SemiAutomaton_is_initially_connected___NFA_rename_states :
assumes connected: "SemiAutomaton_is_initially_connected \<A>"
shows "SemiAutomaton_is_initially_connected (NFA_rename_states \<A> f)"
unfolding NFA_rename_states_def
by (rule SemiAutomaton_is_initially_connected___SemiAutomaton_rename_states[OF connected])

lemma SemiAutomaton_is_initially_connected___NFA_remove_unreachable_states :
  "SemiAutomaton_is_initially_connected (NFA_remove_unreachable_states \<A>)"
using SemiAutomaton_remove_unreachable_states___SemiAutomaton_is_initially_connected[of \<A>]
by (simp add: NFA_remove_unreachable_states_def NFA_remove_states_def
              SemiAutomaton_remove_unreachable_states_def)

lemma SemiAutomaton_is_initially_connected___NFA_isomorphic :
assumes equiv: "NFA_isomorphic \<A>1 \<A>2"
    and connected_A1: "SemiAutomaton_is_initially_connected \<A>1"
shows "SemiAutomaton_is_initially_connected \<A>2"
by (metis equiv connected_A1 NFA_isomorphic_def SemiAutomaton_is_initially_connected___NFA_rename_states)

lemma SemiAutomaton_is_initially_connected___NFA_isomorphic_wf :
fixes \<A>1 :: "('q1, 'a) NFA_rec"
fixes \<A>2 :: "('q2, 'a) NFA_rec"
assumes iso: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "SemiAutomaton_is_initially_connected \<A>1 = SemiAutomaton_is_initially_connected \<A>2"
using assms
by (metis SemiAutomaton_is_initially_connected___NFA_isomorphic
          NFA_isomorphic_wf_sym NFA_isomorphic_wf_def)


subsection \<open> Renaming letters (i.e. elements of the alphabet) \<close>

lemma [simp] : "\<F> (SemiAutomaton_rename_labels \<A> f) = \<F> \<A>" 
  apply (cases \<A>)
  apply (simp add: SemiAutomaton_rename_labels_def)
done

lemma (in NFA) NFA_rename_labels___is_well_formed :
"NFA (SemiAutomaton_rename_labels \<A> f)"
proof -
  have "\<Delta> (SemiAutomaton_rename_labels \<A> f) = (\<lambda>(q,a,q').(q,f a,q')) ` \<Delta> \<A>"
    by (fastforce split: prod.split)
  with finite_\<Delta> have "finite (\<Delta> (SemiAutomaton_rename_labels \<A> f))"
    by simp
  with NFA_axioms show ?thesis
    by (auto simp add: NFA_full_def)
qed

lemma NFA_accept___NFA_rename_labels :
  assumes "NFA_accept \<A> w"
  shows "NFA_accept (SemiAutomaton_rename_labels \<A> f) (map f w)"
using assms LTS_is_reachable___SemiAutomaton_rename_labels unfolding NFA_accept_def
by (auto, fast)

lemma NFA_accept___NFA_rename_labelsE :
  "NFA_accept (SemiAutomaton_rename_labels \<A> f) w \<Longrightarrow> \<exists> w'. w = (map f w') \<and> NFA_accept \<A> w'"
unfolding NFA_accept_def
by simp (metis LTS_is_reachable___SemiAutomaton_rename_labelsE)

lemma NFA_accept___NFA_rename_labels_iff :
  "NFA_accept (SemiAutomaton_rename_labels \<A> f) w \<longleftrightarrow> (\<exists> w'. w = (map f w') \<and> NFA_accept \<A> w')"
by (metis NFA_accept___NFA_rename_labels NFA_accept___NFA_rename_labelsE)

lemma \<L>_NFA_rename_labels [simp] :
  "\<L> (SemiAutomaton_rename_labels \<A> f) = (map f) ` \<L> \<A>"
by (simp add: set_eq_iff \<L>_def NFA_accept___NFA_rename_labels_iff image_iff, blast)

lemma NFA_isomorphic_wf___NFA_rename_labels_cong :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (SemiAutomaton_rename_labels \<A>1 fl) (SemiAutomaton_rename_labels \<A>2 fl)"
proof -
  from equiv
  obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                 wf_\<A>1: "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  note wf_rename = NFA.NFA_rename_labels___is_well_formed [OF wf_\<A>1, of fl]

  have "SemiAutomaton_rename_labels \<A>2 fl = NFA_rename_states (SemiAutomaton_rename_labels \<A>1 fl) f"
    unfolding \<A>2_eq SemiAutomaton_rename_labels_def NFA_rename_states_def
              SemiAutomaton_rename_states_ext_def
    by (cases \<A>1, auto, metis)
  with wf_rename inj_f show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def 
    by auto
qed

subsection \<open> Normalise states \<close>

definition NFA_normalise_states :: "('q, 'a, _) NFA_rec_scheme \<Rightarrow> ('q2::{automaton_states}, 'a) NFA_rec" where
  "NFA_normalise_states \<A> = (NFA_rename_states \<A> (SOME (f::'q \<Rightarrow> 'q2). inj_on f (\<Q> \<A>)))"

lemma NFA_isomorphic_wf_normalise_states :
fixes \<A>:: "('q, 'a, _) NFA_rec_scheme"
assumes wf_A: "NFA \<A>"
shows "NFA_isomorphic_wf \<A> ((NFA_normalise_states \<A>)::('q2::{automaton_states},'a) NFA_rec)"
proof -
  interpret NFA \<A> by fact
  have ex_f: "\<exists>f::('q \<Rightarrow> 'q2). inj_on f (\<Q> \<A>)"
    apply (rule ex_inj_on_finite)
    apply (simp_all add: not_finite_automaton_states_UNIV finite_\<Q>)
  done
  from someI_ex[OF ex_f] have inj_SOME: "inj_on (SOME f::('q \<Rightarrow> 'q2). inj_on f (\<Q> \<A>)) (\<Q> \<A>)" . 

  from NFA_isomorphic_wf___NFA_rename_states [OF inj_SOME wf_A]
  show ?thesis unfolding NFA_normalise_states_def .
qed

lemma NFA_isomorphic_wf___NFA_normalise_states :
"NFA_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> NFA_isomorphic_wf \<A>1 (NFA_normalise_states \<A>2)"
by (metis NFA_isomorphic_wf_alt_def NFA_isomorphic_wf_normalise_states NFA_isomorphic_wf_trans)

lemma NFA_isomorphic_wf___NFA_normalise_states_cong :
fixes \<A>1::"('q1, 'a) NFA_rec"
  and \<A>2::"('q2, 'a) NFA_rec"
shows "NFA_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> 
 NFA_isomorphic_wf (NFA_normalise_states \<A>1) (NFA_normalise_states \<A>2)"
unfolding NFA_normalise_states_def
  apply (rule NFA.NFA_isomorphic_wf___rename_states_cong [of _ \<A>1])
  apply (rule someI_ex [where P = "\<lambda>f. inj_on f (\<Q> \<A>1)"])
  apply (rule ex_inj_on_finite)
  defer 
  apply (rule FinSemiAutomaton.finite_\<Q>)
  defer
  apply (rule someI_ex [where P = "\<lambda>f. inj_on f (\<Q> \<A>2)"])
  apply (rule ex_inj_on_finite)
  defer 
  apply (rule FinSemiAutomaton.finite_\<Q>)
  defer
  apply (simp_all add: not_finite_automaton_states_UNIV NFA_def NFA_isomorphic_wf_alt_def)
done

lemma NFA_normalise_states_\<Sigma> [simp] :
"\<Sigma> (NFA_normalise_states \<A>) = \<Sigma> \<A>"
unfolding NFA_normalise_states_def by simp

lemma NFA_normalise_states_\<L> [simp] :
"NFA \<A> \<Longrightarrow> \<L> (NFA_normalise_states \<A>) = \<L> \<A>"
using NFA_isomorphic_wf_normalise_states[of \<A>]
by (metis NFA_isomorphic_wf_\<L>)

lemma NFA_normalise_states_accept [simp] :
"NFA \<A> \<Longrightarrow> NFA_accept (NFA_normalise_states \<A>) w = NFA_accept \<A> w"
using NFA_normalise_states_\<L> [of \<A>]
by (auto simp add: \<L>_def)

lemma SemiAutomaton_is_initially_connected___normalise_states :
assumes connected: "SemiAutomaton_is_initially_connected \<A>"
shows "SemiAutomaton_is_initially_connected (NFA_normalise_states \<A>)"
unfolding NFA_normalise_states_def
by (intro connected SemiAutomaton_is_initially_connected___NFA_rename_states)


subsection \<open> Product automata \<close>

text \<open> The following definition is an abstraction of
  product automata. It only becomes interesting for deterministic automata.
  For nondeterministic ones, only product automata are used. \<close>

definition bool_comb_NFA :: 
  "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> ('q1, 'a, 'x1) NFA_rec_scheme \<Rightarrow> 
   ('q2, 'a, 'x2) NFA_rec_scheme \<Rightarrow> ('q1 \<times> 'q2, 'a) NFA_rec" where
"bool_comb_NFA bc \<A>1 \<A>2 == 
  SemiAutomaton_to_NFA (product_SemiAutomaton \<A>1 \<A>2)
   {q. q \<in> \<Q> \<A>1 \<times> \<Q> \<A>2 \<and> bc (fst q \<in> \<F> \<A>1) (snd q \<in> \<F> \<A>2)}"

lemma [simp] : "\<I> (bool_comb_NFA bc \<A>1 \<A>2) = \<I> \<A>1 \<times> \<I> \<A>2" by (simp add: bool_comb_NFA_def)
lemma [simp] : "\<Q> (bool_comb_NFA bc \<A>1 \<A>2) = \<Q> \<A>1 \<times> \<Q> \<A>2" by (simp add: bool_comb_NFA_def)
lemma [simp] : "\<F> (bool_comb_NFA bc \<A>1 \<A>2) = {q. q \<in> \<Q> \<A>1 \<times> \<Q> \<A>2 \<and> bc (fst q \<in> \<F> \<A>1) (snd q \<in> \<F> \<A>2)}" by (simp add: bool_comb_NFA_def)
lemma [simp] : "\<Sigma> (bool_comb_NFA bc \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2" by (simp add: bool_comb_NFA_def)
lemma [simp] : "\<Delta> (bool_comb_NFA bc \<A>1 \<A>2) = LTS_product (\<Delta> \<A>1) (\<Delta> \<A>2)" by (simp add: bool_comb_NFA_def)

definition product_NFA where "product_NFA \<A>1 \<A>2 \<equiv> bool_comb_NFA HOL.conj \<A>1 \<A>2"

lemma accept_product_NFA :
assumes wf1: "NFA \<A>1" and wf2: "NFA \<A>2" 
shows "NFA_accept (product_NFA \<A>1 \<A>2) w = ((NFA_accept \<A>1 w) \<and> (NFA_accept \<A>2 w))"
using NFA.\<F>_consistent [OF wf1] NFA.\<F>_consistent [OF wf2]
apply (auto simp add: NFA_accept_def LTS_is_reachable_product product_NFA_def subset_iff Bex_def)
apply blast
done

lemma \<L>_product_NFA :
  "\<lbrakk>NFA \<A>1; NFA \<A>2\<rbrakk>  \<Longrightarrow> \<L> (product_NFA \<A>1 \<A>2) = \<L> \<A>1 \<inter> \<L> \<A>2"
unfolding \<L>_def using accept_product_NFA by auto

lemma bool_comb_NFA___is_well_formed :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2\<rbrakk> \<Longrightarrow> NFA (bool_comb_NFA bc \<A>1 \<A>2)"
unfolding NFA_full_def 
by (auto simp add: bool_comb_NFA_def LTS_product_finite)

lemma product_NFA___is_well_formed :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2 \<rbrakk> \<Longrightarrow> NFA (product_NFA \<A>1 \<A>2)"
unfolding NFA_full_def by (auto simp add: product_NFA_def LTS_product_finite)

definition efficient_bool_comb_NFA where
  "efficient_bool_comb_NFA bc \<A>1 \<A>2 = 
   NFA_remove_unreachable_states (bool_comb_NFA bc \<A>1 \<A>2)"

definition efficient_product_NFA where
  "efficient_product_NFA \<A>1 \<A>2 = NFA_remove_unreachable_states (product_NFA \<A>1 \<A>2)"

lemma efficient_product_NFA_alt_def:
  "efficient_product_NFA \<A>1 \<A>2 = efficient_bool_comb_NFA HOL.conj \<A>1 \<A>2"
unfolding efficient_product_NFA_def efficient_bool_comb_NFA_def product_NFA_def
..

lemma efficient_bool_comb_NFA_\<Sigma> [simp] :
  "\<Sigma> (efficient_bool_comb_NFA bc \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2"
unfolding efficient_bool_comb_NFA_def
by simp

lemma accept_efficient_product_NFA :
  "\<lbrakk>NFA \<A>1;  NFA \<A>2\<rbrakk> \<Longrightarrow> NFA_accept (efficient_product_NFA \<A>1 \<A>2) w = 
   (NFA_accept \<A>1 w \<and> NFA_accept \<A>2 w)" 
by (simp add: efficient_product_NFA_def accept_product_NFA)

lemma \<L>_efficient_product_NFA :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2\<rbrakk> \<Longrightarrow> \<L> (efficient_product_NFA \<A>1 \<A>2) = \<L> \<A>1 \<inter> \<L> \<A>2"
unfolding \<L>_def
by (auto simp add: accept_efficient_product_NFA)

lemma efficient_bool_comb_NFA___is_well_formed :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2 \<rbrakk> \<Longrightarrow> NFA (efficient_bool_comb_NFA bc \<A>1 \<A>2)"
unfolding efficient_bool_comb_NFA_def
by (simp add: bool_comb_NFA___is_well_formed)

lemma efficient_product_NFA___is_well_formed :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2 \<rbrakk> \<Longrightarrow> NFA (efficient_product_NFA \<A>1 \<A>2)"
unfolding efficient_product_NFA_alt_def
by (rule efficient_bool_comb_NFA___is_well_formed)

lemma NFA_isomorphic_bool_comb_NFA :
assumes equiv_1: "NFA_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "NFA_isomorphic_wf \<A>2 \<A>2'"
shows "NFA_isomorphic_wf (bool_comb_NFA bc \<A>1 \<A>2) (bool_comb_NFA bc \<A>1' \<A>2')"
proof -
  from equiv_1 obtain f1 where inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
                 \<A>1'_eq: "\<A>1' = NFA_rename_states \<A>1 f1" and
                 wf_\<A>1 : "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  from equiv_2 obtain f2 where inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
                 \<A>2'_eq: "\<A>2' = NFA_rename_states \<A>2 f2" and
                 wf_\<A>2: "NFA \<A>2" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  define f where "f \<equiv> \<lambda>(q1, q2). (f1 q1, f2 q2)"
  with inj_f1 inj_f2 have inj_f : "inj_on f (\<Q> (bool_comb_NFA bc \<A>1 \<A>2))"
    by (simp add: inj_on_def)

  have f_image: "\<And>S1 S2. f ` (S1 \<times> S2) = (f1 ` S1) \<times> (f2 ` S2)"
    unfolding f_def by auto

  have "\<F> (bool_comb_NFA bc \<A>1' \<A>2') = f ` (\<F> (bool_comb_NFA bc \<A>1 \<A>2))"
  proof -
    { fix q
      have "q \<in> {q \<in> f1 ` \<Q> \<A>1 \<times> f2 ` \<Q> \<A>2. bc (fst q \<in> f1 ` \<F> \<A>1) (snd q \<in> f2 ` \<F> \<A>2)} \<longleftrightarrow>
            q \<in> f ` {q \<in> \<Q> \<A>1 \<times> \<Q> \<A>2. bc (fst q \<in> \<F> \<A>1) (snd q \<in> \<F> \<A>2)}"
      proof -
        obtain q1 q2 where q_eq: "q = (q1, q2)" by (cases q, blast)

        have fact1 : "\<And>y. y \<in> \<Q> \<A>1 \<Longrightarrow> (\<exists>x. x \<in> \<F> \<A>1 \<and> f1 y = f1 x) \<longleftrightarrow> (y \<in> \<F> \<A>1)"
          by (metis inj_f1 [unfolded inj_on_def] 
                    NFA.\<F>_consistent [OF wf_\<A>1, unfolded subset_iff])

        have fact2 : "\<And>y. y \<in> \<Q> \<A>2 \<Longrightarrow> (\<exists>x. x \<in> \<F> \<A>2 \<and> f2 y = f2 x) \<longleftrightarrow> (y \<in> \<F> \<A>2)"
          by (metis inj_f2 [unfolded inj_on_def] 
                    NFA.\<F>_consistent [OF wf_\<A>2, unfolded subset_iff])

        show ?thesis 
          apply (simp del: ex_simps add: image_iff Bex_def ex_simps[symmetric] q_eq f_def)
          apply (insert fact1 fact2)
          apply (auto, metis+)
        done
      qed
    } 
    thus ?thesis
      unfolding \<A>1'_eq \<A>2'_eq bool_comb_NFA_def 
      by simp
  qed

  hence prod_eq': "bool_comb_NFA bc \<A>1' \<A>2' = NFA_rename_states (bool_comb_NFA bc \<A>1 \<A>2) f"
    unfolding \<A>1'_eq \<A>2'_eq bool_comb_NFA_def 
    apply (rule_tac NFA_rec.equality)
    apply (simp_all add: f_image)
    apply (simp del: ex_simps add: NFA_rename_states_def set_eq_iff ex_simps[symmetric] f_def)
    apply (blast)
  done

  from inj_f prod_eq' 
       bool_comb_NFA___is_well_formed [OF wf_\<A>1 wf_\<A>2, of bc]
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast
qed

lemma NFA_isomorphic_efficient_bool_comb_NFA :
assumes equiv_1: "NFA_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "NFA_isomorphic_wf \<A>2 \<A>2'"
shows "NFA_isomorphic_wf (efficient_bool_comb_NFA bc \<A>1 \<A>2) (efficient_bool_comb_NFA bc \<A>1' \<A>2')"
unfolding efficient_bool_comb_NFA_def
apply (rule NFA_isomorphic_wf___NFA_remove_unreachable_states)
apply (rule_tac NFA_isomorphic_bool_comb_NFA)
apply (simp_all add: equiv_1 equiv_2)
done

definition NFA_bool_comb :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 
  ('q::{automaton_states}, 'a, _) NFA_rec_scheme \<Rightarrow> ('q, 'a, _) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec" where
  "NFA_bool_comb bc \<A>1 \<A>2 = NFA_normalise_states (efficient_bool_comb_NFA bc \<A>1 \<A>2)"

lemma NFA_bool_comb___isomorphic_wf :
"NFA \<A>1 \<Longrightarrow> NFA \<A>2 \<Longrightarrow>
 NFA_isomorphic_wf (efficient_bool_comb_NFA bc \<A>1 \<A>2) 
                   (NFA_bool_comb bc \<A>1 \<A>2)"
unfolding NFA_isomorphic_def NFA_bool_comb_def
apply (rule NFA_isomorphic_wf_normalise_states)
apply (simp add: efficient_bool_comb_NFA___is_well_formed)
done

lemma NFA_isomorphic_efficient_NFA_bool_comb :
assumes equiv_1: "NFA_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "NFA_isomorphic_wf \<A>2 \<A>2'"
shows "NFA_isomorphic_wf (NFA_bool_comb bc \<A>1 \<A>2) (NFA_bool_comb bc \<A>1' \<A>2')"
unfolding NFA_bool_comb_def efficient_bool_comb_NFA_def
apply (rule NFA_isomorphic_wf___NFA_normalise_states_cong)
apply (rule NFA_isomorphic_wf___NFA_remove_unreachable_states)
apply (rule_tac NFA_isomorphic_bool_comb_NFA)
apply (simp_all add: equiv_1 equiv_2)
done

lemma NFA_bool_comb_NFA___\<Sigma> [simp] :
  "\<Sigma> (NFA_bool_comb bc \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2"
unfolding NFA_bool_comb_def
by simp


definition NFA_product where "NFA_product \<A>1 \<A>2 = NFA_bool_comb HOL.conj \<A>1 \<A>2"

lemma NFA_product_accept :
assumes wf1: "NFA \<A>1" and wf2: "NFA \<A>2" 
shows "NFA_accept (NFA_product \<A>1 \<A>2) w = ((NFA_accept \<A>1 w) \<and> (NFA_accept \<A>2 w))"
proof -
  let ?A1 = "bool_comb_NFA HOL.conj \<A>1 \<A>2"
  let ?A2 = "NFA_remove_unreachable_states ?A1"
  let ?A3 = "NFA_normalise_states ?A2"

  have nfa_A1: "NFA ?A1" using bool_comb_NFA___is_well_formed[OF wf1 wf2] .
  have nfa_A2: "NFA ?A2" using NFA_remove_unreachable_states___is_well_formed[OF nfa_A1] .

  note accept1 = accept_product_NFA[OF wf1 wf2, of w, unfolded product_NFA_def]
  note accept2 = NFA_remove_unreachable_states_accept_iff [of ?A1 w]
  note accept3 = NFA_normalise_states_accept[OF nfa_A2, of w]

  show ?thesis
    unfolding NFA_product_def NFA_bool_comb_def efficient_bool_comb_NFA_def
    by (simp add: accept3 accept2 accept1)
qed

lemma NFA_product_\<L> :
  "\<lbrakk>NFA \<A>1; NFA \<A>2\<rbrakk>  \<Longrightarrow> \<L> (NFA_product \<A>1 \<A>2) = \<L> \<A>1 \<inter> \<L> \<A>2"
unfolding \<L>_def using NFA_product_accept by auto


subsection \<open> Composition of automata \<close>

definition comb_NFA :: 
  "('q1, 'a, 'x1) NFA_rec_scheme \<Rightarrow> 
   ('q2, 'a, 'x2) NFA_rec_scheme \<Rightarrow> ('q1 + 'q2, 'a) NFA_rec" where
"comb_NFA \<A>1 \<A>2 == SemiAutomaton_to_NFA (comb_SemiAutomaton \<A>1 \<A>2)
   ((\<F> \<A>1) <+> (\<F> \<A>2))"

lemma [simp] : "\<I> (comb_NFA \<A>1 \<A>2) = \<I> \<A>1 <+> \<I> \<A>2" by (simp add: comb_NFA_def)
lemma [simp] : "\<Q> (comb_NFA \<A>1 \<A>2) = \<Q> \<A>1 <+> \<Q> \<A>2" by (simp add: comb_NFA_def)
lemma [simp] : "\<F> (comb_NFA \<A>1 \<A>2) =  \<F> \<A>1 <+> \<F> \<A>2" by (simp add: comb_NFA_def)
lemma [simp] : "\<Sigma> (comb_NFA \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2" by (simp add: comb_NFA_def)
lemma [simp] : "\<Delta> (comb_NFA \<A>1 \<A>2) = LTS_comb (\<Delta> \<A>1) (\<Delta> \<A>2)" by (simp add: comb_NFA_def)

lemma accept_comb_NFA :
assumes wf1: "NFA \<A>1" and wf2: "NFA \<A>2"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2" 
shows "NFA_accept (comb_NFA \<A>1 \<A>2) w = ((NFA_accept \<A>1 w) \<or> (NFA_accept \<A>2 w))"
using NFA.\<F>_consistent [OF wf1] NFA.\<F>_consistent [OF wf2]
apply (simp add: NFA_accept_def LTS_is_reachable_comb comb_NFA_def \<Sigma>_eq)
apply blast
done

lemma \<L>_comb_NFA :
  "\<lbrakk>NFA \<A>1; NFA \<A>2; \<Sigma> \<A>1 = \<Sigma> \<A>2\<rbrakk>  \<Longrightarrow> \<L> (comb_NFA \<A>1 \<A>2) = \<L> \<A>1 \<union> \<L> \<A>2"
unfolding \<L>_def using accept_comb_NFA by auto

lemma comb_NFA___is_well_formed :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2; \<Sigma> \<A>1 = \<Sigma> \<A>2\<rbrakk> \<Longrightarrow> NFA (comb_NFA \<A>1 \<A>2)"
unfolding NFA_full_def by (auto simp add: comb_NFA_def LTS_comb_alt2_def LTS_comb_finite)

definition efficient_comb_NFA where
  "efficient_comb_NFA \<A>1 \<A>2 = 
   NFA_remove_unreachable_states (comb_NFA \<A>1 \<A>2)"

lemma efficient_comb_NFA_\<Sigma> [simp] :
  "\<Sigma> (efficient_comb_NFA \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2"
unfolding efficient_comb_NFA_def
by simp

lemma accept_efficient_comb_NFA :
  "\<lbrakk>NFA \<A>1;  NFA \<A>2; \<Sigma> \<A>1 = \<Sigma> \<A>2\<rbrakk> \<Longrightarrow> NFA_accept (efficient_comb_NFA \<A>1 \<A>2) w = 
   (NFA_accept \<A>1 w \<or> NFA_accept \<A>2 w)" 
by (simp add: efficient_comb_NFA_def accept_comb_NFA)

lemma \<L>_efficient_comb_NFA :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2; \<Sigma> \<A>1 = \<Sigma> \<A>2\<rbrakk> \<Longrightarrow> \<L> (efficient_comb_NFA \<A>1 \<A>2) = \<L> \<A>1 \<union> \<L> \<A>2"
unfolding \<L>_def
by (auto simp add: accept_efficient_comb_NFA)

lemma efficient_comb_NFA___is_well_formed :
  "\<lbrakk> NFA \<A>1;  NFA \<A>2; \<Sigma> \<A>1 = \<Sigma> \<A>2\<rbrakk> \<Longrightarrow> NFA (efficient_comb_NFA \<A>1 \<A>2)"
unfolding efficient_comb_NFA_def
by (simp add: comb_NFA___is_well_formed)

lemma NFA_isomorphic_comb_NFA :
assumes equiv_1: "NFA_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "NFA_isomorphic_wf \<A>2 \<A>2'"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2"
shows "NFA_isomorphic_wf (comb_NFA \<A>1 \<A>2) (comb_NFA \<A>1' \<A>2')"
proof -
  from equiv_1 obtain f1 where inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
                 \<A>1'_eq: "\<A>1' = NFA_rename_states \<A>1 f1" and
                 wf_\<A>1 : "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  from equiv_2 obtain f2 where inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
                 \<A>2'_eq: "\<A>2' = NFA_rename_states \<A>2 f2" and
                 wf_\<A>2: "NFA \<A>2" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  define f where "f \<equiv> \<lambda>q. case q of (Inl q1) \<Rightarrow> Inl (f1 q1) | Inr q2 \<Rightarrow> Inr (f2 q2)"
  with inj_f1 inj_f2 have inj_f : "inj_on f (\<Q> (comb_NFA \<A>1 \<A>2))"
    by (auto simp add: inj_on_def Ball_def)

  have f_image: "\<And>S1 S2. f ` (S1 <+> S2) = (f1 ` S1) <+> (f2 ` S2)"
    unfolding f_def 
      apply (auto simp add: image_iff Bex_def)
      apply auto
    done

  have "\<F> (comb_NFA \<A>1' \<A>2') = f ` (\<F> (comb_NFA \<A>1 \<A>2))"
      apply (auto simp add: Plus_def comb_NFA_def image_iff Bex_def \<A>1'_eq \<A>2'_eq)
      apply (simp_all del: ex_simps add: ex_simps[symmetric] conj_disj_distribR)
      apply (simp_all add: ex_disj_distrib f_def)
      apply auto
  done

  with inj_f1 inj_f2
  have prod_eq': "comb_NFA \<A>1' \<A>2' = NFA_rename_states (comb_NFA \<A>1 \<A>2) f"
    unfolding \<A>1'_eq \<A>2'_eq bool_comb_NFA_def 
    apply (rule_tac NFA_rec.equality)
    apply (simp_all add: f_image)
    apply (simp del: ex_simps add: NFA_rename_states_def set_eq_iff ex_simps[symmetric] f_def
                LTS_comb_alt2_def)
    apply (intro allI iffI)
    apply auto[]
    apply (rule_tac x="Inl q" in exI)
    apply simp
    apply (rule_tac x="Inl q'" in exI)
    apply simp
    apply (rule_tac x="Inr q" in exI)
    apply simp
    apply (rule_tac x="Inr q'" in exI)
    apply simp
    apply auto[]
  done

  from inj_f prod_eq' comb_NFA___is_well_formed [OF wf_\<A>1 wf_\<A>2 \<Sigma>_eq]
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast
qed

lemma NFA_isomorphic_efficient_comb_NFA :
assumes equiv_1: "NFA_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "NFA_isomorphic_wf \<A>2 \<A>2'"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2"
shows "NFA_isomorphic_wf (efficient_comb_NFA \<A>1 \<A>2) (efficient_comb_NFA \<A>1' \<A>2')"
unfolding efficient_comb_NFA_def
apply (rule NFA_isomorphic_wf___NFA_remove_unreachable_states)
apply (rule_tac NFA_isomorphic_comb_NFA)
apply (simp_all add: equiv_1 equiv_2 \<Sigma>_eq)
done

definition NFA_comb :: " 
  ('q::{automaton_states}, 'a, _) NFA_rec_scheme \<Rightarrow> ('q, 'a, _) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec" where
  "NFA_comb \<A>1 \<A>2 = NFA_normalise_states (efficient_comb_NFA \<A>1 \<A>2)"

lemma NFA_comb___isomorphic_wf :
"NFA \<A>1 \<Longrightarrow> NFA \<A>2 \<Longrightarrow> \<Sigma> \<A>1 = \<Sigma> \<A>2 \<Longrightarrow>
 NFA_isomorphic_wf (efficient_comb_NFA \<A>1 \<A>2) 
                   (NFA_comb \<A>1 \<A>2)"
unfolding NFA_isomorphic_def NFA_comb_def
apply (rule NFA_isomorphic_wf_normalise_states)
apply (simp add: efficient_comb_NFA___is_well_formed)
done

lemma NFA_isomorphic_efficient_NFA_comb :
assumes equiv_1: "NFA_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "NFA_isomorphic_wf \<A>2 \<A>2'"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2"
shows "NFA_isomorphic_wf (NFA_comb \<A>1 \<A>2) (NFA_comb \<A>1' \<A>2')"
unfolding NFA_comb_def efficient_comb_NFA_def
apply (rule NFA_isomorphic_wf___NFA_normalise_states_cong)
apply (rule NFA_isomorphic_wf___NFA_remove_unreachable_states)
apply (rule_tac NFA_isomorphic_comb_NFA)
apply (simp_all add: equiv_1 equiv_2 \<Sigma>_eq)
done

lemma NFA_comb_NFA___\<Sigma> [simp] :
  "\<Sigma> (NFA_comb \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2"
unfolding NFA_comb_def
by simp


subsection \<open> Reversal \<close>
definition NFA_reverse :: "('q, 'a, 'x) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec" where
  "NFA_reverse \<A> = \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = { (q,\<sigma>,p). (p,\<sigma>,q) \<in> \<Delta> \<A> }, \<I> = \<F> \<A>, \<F> = \<I> \<A> \<rparr>"

lemma [simp] : "\<Q> (NFA_reverse \<A>) = \<Q> \<A>" by (simp add: NFA_reverse_def)
lemma [simp] : "\<Sigma> (NFA_reverse \<A>) = \<Sigma> \<A>" by (simp add: NFA_reverse_def)
lemma [simp] : "\<I> (NFA_reverse \<A>) = \<F> \<A>" by (simp add: NFA_reverse_def)
lemma [simp] : "\<F> (NFA_reverse \<A>) = \<I> \<A>" by (simp add: NFA_reverse_def)

lemma [simp] : "p\<sigma>q \<in> \<Delta> (NFA_reverse \<A>) \<longleftrightarrow> ((snd (snd p\<sigma>q)), (fst (snd p\<sigma>q)), (fst p\<sigma>q)) \<in> \<Delta> \<A>"
by (cases p\<sigma>q, simp add: NFA_reverse_def)

lemma NFA_reverse___is_well_formed :
  assumes "NFA \<A>" 
  shows "NFA (NFA_reverse \<A>)"
proof -
  from assms interpret NFA \<A> .
  have "\<Delta> (NFA_reverse \<A>) = (\<lambda>(q,a,q'). (q',a,q)) ` \<Delta> \<A>"
    unfolding NFA_reverse_def by (fastforce split: prod.split)
  with finite_\<Delta> have "finite (\<Delta> (NFA_reverse \<A>))" by simp
  with assms show ?thesis by (simp add: NFA_full_def NFA_reverse_def)
qed

lemma NFA_reverse_NFA_reverse :
  "NFA_reverse (NFA_reverse \<A>) = \<A>"
proof -
  have "\<Delta> \<A> = {(q, \<sigma>, p) |q \<sigma> p. (q, \<sigma>, p) \<in> \<Delta> \<A>}" by auto
  thus ?thesis by (simp add: NFA_reverse_def)
qed

lemma NFA_reverse___LTS_is_reachable :
  "LTS_is_reachable (\<Delta> (NFA_reverse \<A>)) p w q \<longleftrightarrow> LTS_is_reachable (\<Delta> \<A>) q (rev w) p"
by (induct w arbitrary: p q, auto)

lemma NFA_reverse___accept :
  "NFA_accept (NFA_reverse \<A>) w \<longleftrightarrow> NFA_accept \<A> (rev w)"
by (simp add: NFA_accept_def NFA_reverse___LTS_is_reachable, auto) 

lemma NFA_reverse___\<L> :
  "\<L> (NFA_reverse \<A>) = {rev w | w. w \<in> \<L> \<A>}"
unfolding \<L>_def using NFA_reverse___accept by force

lemma NFA_reverse___\<L>_in_state :
  "\<L>_in_state (NFA_reverse \<A>) q = {rev w | w. w \<in> \<L>_left \<A> q}"
by (auto simp add: \<L>_in_state_def \<L>_left_def NFA_reverse___LTS_is_reachable lists_eq_set,
    metis rev_rev_ident)

lemma NFA_reverse___\<L>_left :
  "\<L>_left (NFA_reverse \<A>) q = {rev w | w. w \<in> \<L>_in_state \<A> q}"
by (auto simp add: \<L>_in_state_def \<L>_left_def NFA_reverse___LTS_is_reachable lists_eq_set,
    metis rev_rev_ident)

lemma unreachable_states_NFA_reverse_def :
  "SemiAutomaton_unreachable_states \<A> = {q. \<L>_in_state (NFA_reverse \<A>) q = {}}"
by (simp add: NFA_reverse___\<L>_in_state NFA_unreachable_states_alt_def)

lemma NFA_isomorphic_wf___NFA_reverse_cong :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (NFA_reverse \<A>1) (NFA_reverse \<A>2)"
proof -
  from equiv obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                 wf_\<A>1: "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  with inj_f have inj_f' : "inj_on f (\<Q> (NFA_reverse \<A>1))"
    by simp

  have \<A>2_eq': "NFA_reverse \<A>2 = NFA_rename_states (NFA_reverse \<A>1) f"
    unfolding NFA_reverse_def \<A>2_eq NFA_rename_states_def SemiAutomaton_rename_states_ext_def
    apply simp
    apply auto 
  done

  from inj_f' \<A>2_eq' NFA_reverse___is_well_formed [OF wf_\<A>1] show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast
qed

subsection \<open> Right quotient \<close>

definition NFA_right_quotient :: "('q, 'a, 'x) NFA_rec_scheme \<Rightarrow> ('a list) set \<Rightarrow> ('q, 'a) NFA_rec" where
  "NFA_right_quotient \<A> L = 
     \<lparr> \<Q> = \<Q> \<A>, 
       \<Sigma> = \<Sigma> \<A>, 
       \<Delta> = \<Delta> \<A>, 
       \<I> = \<I> \<A>, 
       \<F> = {q. q \<in> \<Q> \<A> \<and> \<L>_in_state \<A> q \<inter> L \<noteq> {}} \<rparr>"

lemma [simp] : "\<Q> (NFA_right_quotient \<A> L) = \<Q> \<A>" by (simp add: NFA_right_quotient_def)
lemma [simp] : "\<Sigma> (NFA_right_quotient \<A> L) = \<Sigma> \<A>" by (simp add: NFA_right_quotient_def)
lemma [simp] : "\<I> (NFA_right_quotient \<A> L) = \<I> \<A>" by (simp add: NFA_right_quotient_def)
lemma [simp] : "\<Delta> (NFA_right_quotient \<A> L) = \<Delta> \<A>" by (simp add: NFA_right_quotient_def)
lemma [simp] : "\<F> (NFA_right_quotient \<A> L) = {q. q \<in> \<Q> \<A> \<and> \<L>_in_state \<A> q \<inter> L \<noteq> {}}" by (simp add: NFA_right_quotient_def)

lemma NFA_right_quotient_alt_def :
  "NFA_right_quotient \<A> L = SemiAutomaton_to_NFA \<A> {q. q \<in> \<Q> \<A> \<and> \<L>_in_state \<A> q \<inter> L \<noteq> {}}"
unfolding NFA_right_quotient_def SemiAutomaton_to_NFA_def by simp

lemma NFA_right_quotient___is_well_formed :
  "NFA \<A> \<Longrightarrow> NFA (NFA_right_quotient \<A> L)"
unfolding NFA_full_def NFA_right_quotient_def
by auto

lemma (in NFA) NFA_right_quotient___accepts :
  "NFA_accept (NFA_right_quotient \<A> L) w \<longleftrightarrow>
   (\<exists>w2 \<in> L. NFA_accept \<A> (w @ w2))"
unfolding NFA_def NFA_right_quotient_def
using SemiAutomaton_\<Delta>_cons___LTS_is_reachable \<I>_consistent
by (simp add: NFA_accept_def Bex_def LTS_is_reachable_concat subset_iff
              ex_simps[symmetric] \<L>_in_state_def ex_in_conv [symmetric]
         del: ex_simps )
    metis

lemma NFA_right_quotient___alt_def :
  "NFA_right_quotient \<A> L = 
     \<lparr> \<Q> = \<Q> \<A>, 
       \<Sigma> = \<Sigma> \<A>, 
       \<Delta> = \<Delta> \<A>, 
       \<I> = \<I> \<A>, 
       \<F> = {q' . \<exists>q w. q' \<in> \<Q> \<A> \<and> q \<in> \<F> \<A> \<and> w \<in> rev ` L \<and>
                 LTS_is_reachable {(q, \<sigma>, p) . (p, \<sigma>, q) \<in> \<Delta> \<A>} q w q'} \<rparr>"
proof -
  have "\<And>q. (\<L>_in_state \<A> q \<inter> L) = rev ` (\<L>_left (NFA_reverse \<A>) q \<inter> rev ` L)"
   apply (simp add: NFA_reverse___\<L>_left image_Int)
   apply (simp add: set_eq_iff image_iff ex_simps[symmetric] del: ex_simps)
  done
  hence "\<And>q. \<L>_in_state \<A> q \<inter> L \<noteq> {} \<longleftrightarrow> (\<L>_left (NFA_reverse \<A>) q \<inter> rev ` L) \<noteq> {}"
    by simp
  thus ?thesis 
    apply (simp add: NFA_right_quotient_def \<L>_left_def set_eq_iff)
    apply (simp del: ex_simps add: ex_simps[symmetric] image_iff Bex_def NFA_reverse_def)
    apply blast
  done
qed

lemma NFA_isomorphic_right_quotient :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (NFA_right_quotient \<A>1 L) (NFA_right_quotient \<A>2 L)"
proof -
  from equiv obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                 wf_\<A>1: "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  with inj_f have inj_f' : "inj_on f (\<Q> (NFA_right_quotient \<A>1 L))"
    by simp
  note equiv_f = NFA_is_equivalence_rename_funI___inj_used [OF inj_f]

  from NFA.\<L>_in_state_rename_iff [OF wf_\<A>1 equiv_f]
  have F_eq: "{q \<in> f ` \<Q> \<A>1. \<L>_in_state (NFA_rename_states \<A>1 f) q \<inter> L \<noteq> {}} =
        f ` {q \<in> \<Q> \<A>1. \<L>_in_state \<A>1 q \<inter> L \<noteq> {}}"
    by auto

  have \<A>2_eq': "NFA_right_quotient \<A>2 L = NFA_rename_states (NFA_right_quotient \<A>1 L) f"
    unfolding NFA_right_quotient_def \<A>2_eq 
    apply (rule NFA_rec.equality)
    apply (simp_all)
    apply (simp add: NFA_rename_states_def SemiAutomaton_rename_states_ext_def)
    apply (simp add: F_eq)
  done

  from inj_f' \<A>2_eq' NFA_right_quotient___is_well_formed [OF wf_\<A>1, of L]
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast
qed


text \<open> Code will just be generated for a simpler version, which is very easy to implement: \<close>
abbreviation "NFA_right_quotient_lists \<A> Q \<equiv> NFA_right_quotient \<A> (lists Q)"

lemma (in NFA) NFA_right_quotient_lists_inter :
shows "NFA_right_quotient_lists \<A> Q = NFA_right_quotient_lists \<A> (Q \<inter> (\<Sigma> \<A>))"
unfolding NFA_right_quotient_def
apply (simp add: set_eq_iff lists_inter ex_simps[symmetric] del: ex_simps)
apply (intro allI iff_exI iffI)
apply (simp_all)
apply (simp add: \<L>_in_state_def)
apply (metis LTS_is_reachable___labels)
done

lemma (in NFA) NFA_right_quotient_lists_alt_def :
shows "NFA_right_quotient_lists \<A> Q =
     \<lparr> \<Q> = \<Q> \<A>, 
       \<Sigma> = \<Sigma> \<A>, 
       \<Delta> = \<Delta> \<A>, 
       \<I> = \<I> \<A>, 
       \<F> = accessible {(q,p) . \<exists>\<sigma>. (p, \<sigma>, q) \<in> \<Delta> \<A> \<and> \<sigma> \<in> Q} (\<F> \<A>) \<rparr>"
unfolding NFA_right_quotient___alt_def 
proof (intro NFA_rec.equality conjI refl, simp_all)
  show "{q' \<in> \<Q> \<A>. \<exists>q. q \<in> \<F> \<A> \<and>
         (\<exists>w. w \<in> lists Q \<and>
              LTS_is_reachable {(q, \<sigma>, p). (p, \<sigma>, q) \<in> \<Delta> \<A>}
               q w q')} =
    accessible {(q, p). \<exists>\<sigma>. (p, \<sigma>, q) \<in> \<Delta> \<A> \<and> \<sigma> \<in> Q} (\<F> \<A>)"
    (is "?ls = ?rs")
  proof -
    have "{(q, p). \<exists>\<sigma>. (p, \<sigma>, q) \<in> \<Delta> \<A> \<and> \<sigma> \<in> Q} =
          LTS_forget_labels_pred (\<lambda>\<sigma>. \<sigma> \<in> Q) {(q, \<sigma>, p). (p, \<sigma>, q) \<in> \<Delta> \<A>}"
      unfolding LTS_forget_labels_pred_def by simp
    hence rs_eq: "?rs = {q'. \<exists>q\<in>\<F> \<A>. \<exists>w. LTS_is_reachable (\<Delta> (NFA_reverse \<A>)) q w q' \<and> w \<in> lists Q}"
      by (simp add: accessible_def rtrancl_LTS_forget_labels_pred NFA_reverse_def)
    
    interpret revA : NFA "NFA_reverse \<A>" by (rule NFA_reverse___is_well_formed [OF NFA_axioms])

    show ?thesis 
    proof (intro iffI set_eqI)
      fix q'
      assume "q' \<in> ?ls"
      thus "q' \<in> ?rs" unfolding rs_eq NFA_reverse_def by auto
    next
      fix q'
      assume "q' \<in> ?rs"
      with rs_eq obtain q w where 
        q_in_F: "q\<in>\<F> \<A>" and reach: "LTS_is_reachable (\<Delta> (NFA_reverse \<A>)) q w q'" and w_in_Q: "w \<in> lists Q" by blast

      from q_in_F \<F>_consistent have q_in_Q: "q \<in> \<Q> \<A>" by auto
      with reach SemiAutomaton.SemiAutomaton_\<Delta>_cons___LTS_is_reachable[OF revA.SemiAutomaton_axioms] 
      have q'_in_Q: "q' \<in> \<Q> \<A>" and w_in_A: "w \<in> lists (\<Sigma> \<A>)" by simp_all

      show "q' \<in> ?ls" 
        apply (simp add: q'_in_Q del: ex_simps add: ex_simps[symmetric])
        apply (rule exI [where x=q])
        apply (rule exI [where x=w])
        apply (insert reach)
        apply (simp add: q_in_F w_in_Q w_in_A NFA_reverse_def)
      done
    qed
  qed
qed

end
