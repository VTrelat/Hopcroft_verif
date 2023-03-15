(*  Title:       Deterministic Finite Automata
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
                 Petra Dietrich <petra@ecs.vuw.ac.nz>

    using Peter Lammich <peter.lammich@uni-muenster.de> work on
    Finite state machines
*)

section \<open> Deterministic Finite Automata \<close>

theory DFA
imports Main LTS NFA
begin

subsection \<open> Basic Definitions \<close>

lemma dummy_NFA___SemiAutomaton_is_complete_deterministic :
  "SemiAutomaton_is_complete_deterministic (dummy_NFA q a)"
by (simp add: SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def 
              LTS_is_deterministic_def LTS_is_complete_def dummy_NFA_def)

locale DFA = NFA \<A> +
             DetFinSemiAutomaton \<A>
  for \<A>::"('q,'a, 'DFA_more) NFA_rec_scheme"

lemma DFA_alt_def : "DFA \<A> \<longleftrightarrow> NFA \<A> \<and> SemiAutomaton_is_complete_deterministic \<A>"
  unfolding DFA_def DetFinSemiAutomaton_def DetSemiAutomaton_alt_def FinSemiAutomaton_alt_def NFA_alt_def by metis

lemma DFA_alt_def2 : "DFA \<A> \<longleftrightarrow> NFA \<A> \<and> DetFinSemiAutomaton \<A>"
  unfolding DFA_def DetFinSemiAutomaton_alt_def NFA_alt_def by auto

lemma DFA_alt_def3 : "DFA \<A> \<longleftrightarrow> NFA \<A> \<and> DetSemiAutomaton \<A>"
  unfolding DFA_def DetFinSemiAutomaton_alt_def NFA_alt_def 
            DetSemiAutomaton_alt_def FinSemiAutomaton_def by auto

lemma DFA_implies_NFA[simp] :
  "DFA \<A> \<Longrightarrow> NFA \<A>" unfolding DFA_alt_def by simp

lemma dummy_NFA___is_DFA :
  "DFA (dummy_NFA q a)"
by (simp add: DFA_alt_def dummy_NFA___is_NFA dummy_NFA___SemiAutomaton_is_complete_deterministic)

lemma (in DFA) \<L>_in_state_\<i> : "\<L>_in_state \<A> (\<i> \<A>) = \<L> \<A>" using \<L>_alt_def by force

subsection \<open> Lemmas about deterministic automata \<close>

lemma (in DFA) DFA_left_languages___pairwise_disjoint :
assumes p_in_Q : "p \<in> \<Q> \<A>"
    and q_in_Q : "q \<in> \<Q> \<A>"
    and p_neq_Q: "p \<noteq> q"
shows "\<L>_left \<A> p \<inter> \<L>_left \<A> q = {}"
proof (rule ccontr)
  assume "\<L>_left \<A> p \<inter> \<L>_left \<A> q \<noteq> {}"
  then obtain w where "w \<in> \<L>_left \<A> p" and "w \<in> \<L>_left \<A> q" by auto
  then have "LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w p" and "LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w q"
    unfolding \<L>_left_def by auto
  with `p \<noteq> q` show "False" by (simp add: DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp)
qed

lemma (in DFA) DFA_accept_alt_def :
  "NFA_accept \<A> w = 
   (case (DLTS_reach (\<delta> \<A>) (\<i> \<A>) w) of None \<Rightarrow> False | Some q' \<Rightarrow> q' \<in> \<F> \<A>)"
by (simp add: NFA_accept_def Bex_def DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp
         split: option.split)

lemma \<L>_in_state___DFA___eq_reachable_step :
assumes DFA_\<A>: "DFA \<A>"
    and DFA_\<A>': "DFA \<A>'"
    and in_D1: "(q1, \<sigma>, q1') \<in> \<Delta> \<A>"
    and in_D2: "(q2, \<sigma>, q2') \<in> \<Delta> \<A>'"
    and lang_eq : "\<L>_in_state \<A> q1 = \<L>_in_state \<A>' q2"
shows "\<L>_in_state \<A> q1' = \<L>_in_state \<A>' q2'"
proof -
  interpret DFA1 : DFA \<A> by (fact DFA_\<A>)    
  interpret DFA2 : DFA \<A>' by (fact DFA_\<A>')    

  from DFA1.deterministic_LTS in_D1 have q1'_unique: 
     "\<And>q1''. (q1, \<sigma>, q1'') \<in> \<Delta> \<A> = (q1'' = q1')"
     by (auto simp add: LTS_is_deterministic_def)

  from DFA2.deterministic_LTS in_D2 have q2'_unique: 
     "\<And>q2''. (q2, \<sigma>, q2'') \<in> \<Delta> \<A>' = (q2'' = q2')"
     by (auto simp add: LTS_is_deterministic_def)

  from DFA1.\<Delta>_consistent DFA2.\<Delta>_consistent in_D1 in_D2 have
    \<sigma>_in_\<Sigma>: "\<sigma> \<in> (\<Sigma> \<A> \<inter> \<Sigma> \<A>')" by simp

  from lang_eq 
    have "remove_prefix [\<sigma>] (\<L>_in_state \<A> q1) = remove_prefix [\<sigma>] (\<L>_in_state \<A>' q2)" by simp
  with \<sigma>_in_\<Sigma> 
  have "\<Union>{\<L>_in_state \<A> q' |q'. (q1, \<sigma>, q') \<in> \<Delta> \<A>} =
        \<Union>{\<L>_in_state \<A>' q' |q'. (q2, \<sigma>, q') \<in> \<Delta> \<A>'}" 
    by (simp add: \<L>_in_state_remove_prefix)
  with q1'_unique q2'_unique show "\<L>_in_state \<A> q1' = \<L>_in_state \<A>' q2'" by simp
qed

lemma \<L>_in_state___DFA___eq_DLTS_reachable :
assumes DFA_\<A>: "DFA \<A>"
    and DFA_\<A>': "DFA \<A>'"
    and DLTS_reach_1: "LTS_is_reachable (\<Delta> \<A>) q1 w q1'"
    and DLTS_reach_2: "LTS_is_reachable (\<Delta> \<A>') q2 w q2'"
    and lang_eq : "\<L>_in_state \<A> q1 = \<L>_in_state \<A>' q2"
shows "\<L>_in_state \<A> q1' = \<L>_in_state \<A>' q2'"
using DLTS_reach_1 DLTS_reach_2 lang_eq
proof (induct w arbitrary: q1 q2)
  case Nil thus ?thesis by simp
next
  case (Cons \<sigma> w)
  note ind_hyp = Cons (1)
  note DLTS_reach_1 = Cons (2)
  note DLTS_reach_2 = Cons (3)
  note lang_eq = Cons (4)

  from DLTS_reach_1 obtain q1'' where in_D1 : "(q1, \<sigma>, q1'') \<in> (\<Delta> \<A>)" and
                                 DLTS_reach_1' : "LTS_is_reachable (\<Delta> \<A>) q1'' w q1'" 
    by auto
  from DLTS_reach_2 obtain q2'' where in_D2 : "(q2, \<sigma>, q2'') \<in> (\<Delta> \<A>')" and
                                 DLTS_reach_2' : "LTS_is_reachable (\<Delta> \<A>') q2'' w q2'" 
    by auto
 
  have lang_eq' : "\<L>_in_state \<A> q1'' = \<L>_in_state \<A>' q2''"
    by (fact \<L>_in_state___DFA___eq_reachable_step 
              [OF DFA_\<A> DFA_\<A>' in_D1 in_D2 lang_eq])

  note ind_hyp [OF DLTS_reach_1' DLTS_reach_2' lang_eq']
  thus ?thesis by assumption
qed

lemma DFA___inj_rename :
assumes DFA_\<A>: "DFA \<A>"
    and inj_f: "inj_on f (\<Q> \<A>)"
shows "DFA (NFA_rename_states \<A> f)"
proof -
  interpret det_A: DFA \<A> by fact

  from NFA_rename_states___is_well_formed[OF det_A.NFA_axioms, of f]
  have nfa: "NFA (NFA_rename_states \<A> f)" .

  have det: "SemiAutomaton_is_complete_deterministic (NFA_rename_states \<A> f)"
    unfolding NFA_rename_states_def 
    by (simp add: det_A.SemiAutomaton_is_complete_deterministic___inj_rename [OF inj_f])

  from nfa det show ?thesis 
    unfolding DFA_alt_def by simp
qed

lemma NFA_isomorphic___is_well_formed_DFA :
assumes wf_A1: "DFA \<A>1"
    and eq_A12: "NFA_isomorphic \<A>1 \<A>2"
shows "DFA \<A>2"
proof -
  from eq_A12 obtain f where
    inj_f: "inj_on f (\<Q> \<A>1)" and
    A2_eq: "\<A>2 = NFA_rename_states \<A>1 f"
    unfolding NFA_isomorphic_def by blast

  from A2_eq DFA___inj_rename [OF wf_A1 inj_f]
  show "DFA \<A>2" by simp
qed

lemma NFA_isomorphic_wf___DFA :
fixes \<A>1 :: "('q1, 'a) NFA_rec" and \<A>2 :: "('q2, 'a) NFA_rec"
assumes iso: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "DFA \<A>1 \<longleftrightarrow> DFA \<A>2"
using assms
by (metis NFA_isomorphic_wf_sym NFA_isomorphic_wf_def NFA_isomorphic___is_well_formed_DFA)

lemma NFA_normalise_states_DFA [simp] :
assumes wf_A: "DFA \<A>" 
shows "DFA (NFA_normalise_states \<A>)"
by (metis NFA_isomorphic_wf_normalise_states[unfolded NFA_isomorphic_wf_def] 
    NFA_isomorphic___is_well_formed_DFA DFA_alt_def assms)


subsection \<open> Determinisation \<close>

definition determinise_NFA where
  "determinise_NFA \<A> = SemiAutomaton_to_NFA (powerset_SemiAutomaton \<A>)
     {fs. (fs \<subseteq> (\<Q> \<A>)) \<and> (fs \<inter> \<F> \<A>) \<noteq> {}}"

lemma determinise_NFA_full_def :
  "determinise_NFA \<A> = \<lparr>\<Q> = {q. q \<subseteq> \<Q> \<A>}, \<Sigma> = \<Sigma> \<A>,
       \<Delta> = {(Q, \<sigma>, {q'. \<exists>q\<in>Q. (q, \<sigma>, q') \<in> \<Delta> \<A>}) |Q \<sigma>.
            Q \<subseteq> \<Q> \<A> \<and> \<sigma> \<in> \<Sigma> \<A>},
       \<I> = {\<I> \<A>}, \<F> = {fs. fs \<subseteq> \<Q> \<A> \<and> fs \<inter> \<F> \<A> \<noteq> {}}\<rparr>"
unfolding determinise_NFA_def SemiAutomaton_to_NFA_def powerset_SemiAutomaton_def
by simp

lemma determinise_NFA_\<I> [simp] : "\<I> (determinise_NFA \<A>) = {\<I> \<A>}" by (simp add: determinise_NFA_def)
lemma determinise_NFA_\<Q> [simp] : "(q \<in> \<Q> (determinise_NFA \<A>)) \<longleftrightarrow> q \<subseteq> \<Q> \<A>" by (simp add: determinise_NFA_def)
lemma determinise_NFA_\<Sigma> [simp] : "\<Sigma> (determinise_NFA \<A>) = \<Sigma> \<A>" by (simp add: determinise_NFA_def)
lemma determinise_NFA_\<F> [simp] : "q \<in> \<F> (determinise_NFA \<A>) \<longleftrightarrow> (q \<subseteq> (\<Q> \<A>)) \<and> q \<inter> \<F> \<A> \<noteq> {}" by (simp add: determinise_NFA_def)

lemma determinise_NFA_\<Delta> [simp] : "Q\<sigma>Q' \<in> \<Delta> (determinise_NFA \<A>) \<longleftrightarrow> 
  ((snd (snd Q\<sigma>Q') = {q'. \<exists>q\<in>(fst Q\<sigma>Q'). (q, fst (snd Q\<sigma>Q'), q') \<in> \<Delta> \<A>}) \<and>
   (fst Q\<sigma>Q' \<subseteq> \<Q> \<A>) \<and> ((fst (snd Q\<sigma>Q')) \<in> \<Sigma> \<A>))" 
by (cases Q\<sigma>Q', simp add: determinise_NFA_def)

lemma determinise_NFA_is_det :
  "SemiAutomaton_is_deterministic (determinise_NFA \<A>)"
unfolding determinise_NFA_def
by (simp) (rule powerset_SemiAutomaton_is_deterministic)

lemma (in NFA) determinise_NFA_is_complete_determistic :
  "SemiAutomaton_is_complete_deterministic (determinise_NFA \<A>)"
unfolding determinise_NFA_def
by (simp add: powerset_SemiAutomaton_is_complete_determistic)

lemma determinise_NFA___is_well_formed :
  assumes "NFA \<A>"
  shows "NFA (determinise_NFA \<A>)"
proof -
  from assms interpret NFA \<A> .
  from finite_\<Sigma> have "finite (\<Delta> (powerset_SemiAutomaton \<A>))"
    using powerset_SemiAutomaton__finite_\<Delta>
    by simp
  with assms show ?thesis
    by (auto simp add: NFA_full_def determinise_NFA_def powerset_SemiAutomaton_def)
qed

lemma determinise_NFA___DFA :
  "NFA \<A> \<Longrightarrow> DFA (determinise_NFA \<A>)"
by (simp add: determinise_NFA___is_well_formed DFA_alt_def
              NFA.determinise_NFA_is_complete_determistic)

lemma (in NFA) determinise_NFA___DLTS_reach :
shows "Q \<subseteq> \<Q> \<A> \<Longrightarrow>
  DLTS_reach (\<delta> (determinise_NFA \<A>)) Q w = 
  (if (w \<in> lists (\<Sigma> \<A>)) then Some {q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'} else None)"
unfolding determinise_NFA_def
using powerset_SemiAutomaton___DLTS_reach[of Q w]
by simp

lemma (in NFA) determinise_NFA___LTS_is_reachable :
shows "Q \<subseteq> \<Q> \<A> \<Longrightarrow>
  LTS_is_reachable (\<Delta> (determinise_NFA \<A>)) Q w Q' \<longleftrightarrow> 
  (w \<in> lists (\<Sigma> \<A>)) \<and> Q' = {q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'}"
unfolding determinise_NFA_def
using powerset_SemiAutomaton___LTS_is_reachable[of Q w Q']
by simp

lemma (in NFA) determinise_NFA___\<L>_in_state :
  assumes Q_subset: "Q \<subseteq> \<Q> \<A>"
  shows "\<L>_in_state (determinise_NFA \<A>) Q = \<Union> {\<L>_in_state \<A> q | q. q \<in> Q}"
        (is "?s1 = ?s2")
proof (intro set_eqI)
  fix w
  show "w \<in> ?s1 \<longleftrightarrow> w \<in> ?s2"
  proof -
    interpret DFA_detA: DFA "(determinise_NFA \<A>)" using determinise_NFA___DFA [OF NFA_axioms]
      by assumption

    from LTS_is_reachable___labels[of _ w]
    have in_s1_eq: "w \<in> ?s1 = 
      ({q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'} \<subseteq> \<Q> \<A> \<and>
       {q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'} \<inter> \<F> \<A> \<noteq> {})"
      apply (simp add: \<L>_in_state_def DFA_detA.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp)
      apply (auto simp add: determinise_NFA___DLTS_reach Q_subset)
    done

    have in_s1_eq2: "({q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'} \<inter> \<F> \<A> \<noteq> {}) =
                     (\<exists>q q'. q \<in> Q \<and> q' \<in> (\<F> \<A>) \<and> LTS_is_reachable (\<Delta> \<A>) q w q')"
      by auto

    from Q_subset SemiAutomaton_\<Delta>_cons___LTS_is_reachable [where w = w]
    have in_s1_eq1: "{q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'} \<subseteq> \<Q> \<A>" by auto

    have in_s2_eq: 
    "w \<in> ?s2 = (\<exists>q q'. q \<in> Q \<and> q' \<in> (\<F> \<A>) \<and> LTS_is_reachable (\<Delta> \<A>) q w q')"
      by (auto simp add: \<L>_in_state_def)
    
    show ?thesis unfolding in_s2_eq in_s1_eq in_s1_eq2 
      by (simp add: in_s1_eq1)
  qed
qed

lemma (in NFA) determinise_NFA_\<L> [simp] :
"\<L> (determinise_NFA \<A>) = \<L> \<A>"
proof -
  from \<I>_consistent have "\<I> \<A> \<in> \<Q> (determinise_NFA \<A>)" by (simp add: NFA_def)

  thus ?thesis
    by (auto simp add: \<L>_alt_def determinise_NFA___\<L>_in_state)
qed

lemma (in NFA) determinise_NFA_accept [simp] :
  "NFA_accept (determinise_NFA \<A>) w = NFA_accept \<A> w"
by (simp add: NFA_accept_alt_def)

definition efficient_determinise_NFA where
  "efficient_determinise_NFA \<A> = NFA_remove_unreachable_states (determinise_NFA \<A>)"

lemma SemiAutomaton_is_complete_deterministic___NFA_remove_unreachable_states :
  "SemiAutomaton_is_complete_deterministic \<A> \<Longrightarrow>
   SemiAutomaton_is_complete_deterministic (NFA_remove_unreachable_states \<A>)"
using SemiAutomaton_is_complete_deterministic___SemiAutomaton_remove_unreachable_states[of \<A>]
unfolding NFA_remove_unreachable_states_def NFA_remove_states_def
          SemiAutomaton_remove_unreachable_states_def
by simp

lemma DFA___NFA_remove_unreachable_states :
  "DFA \<A> \<Longrightarrow> DFA (NFA_remove_unreachable_states \<A>)"
unfolding DFA_alt_def
by (metis SemiAutomaton_is_complete_deterministic___NFA_remove_unreachable_states
          NFA_remove_unreachable_states___is_well_formed)

lemma (in NFA) efficient_determinise_SemiAutomaton_is_complete_deterministic :
  "SemiAutomaton_is_complete_deterministic (efficient_determinise_NFA \<A>)"
unfolding efficient_determinise_NFA_def
apply (rule SemiAutomaton_is_complete_deterministic___NFA_remove_unreachable_states)
apply (rule determinise_NFA_is_complete_determistic)
done

lemma efficient_determinise_NFA_is_DFA :
assumes wf_A: "NFA \<A>"
shows "DFA (efficient_determinise_NFA \<A>)"
unfolding DFA_alt_def 
proof
  show "SemiAutomaton_is_complete_deterministic (efficient_determinise_NFA \<A>)" 
    by (rule NFA.efficient_determinise_SemiAutomaton_is_complete_deterministic[OF wf_A])
next
  show "NFA (efficient_determinise_NFA \<A>)"
    unfolding efficient_determinise_NFA_def
    apply (rule NFA_remove_unreachable_states___is_well_formed)
    apply (rule determinise_NFA___is_well_formed)
    apply (fact wf_A)
  done
qed

lemma efficient_determinise_NFA_\<Sigma> [simp] :
  "\<Sigma> (efficient_determinise_NFA \<A>) = \<Sigma> \<A>"
unfolding efficient_determinise_NFA_def by simp

lemma (in NFA) efficient_determinise_NFA_accept [simp] :
  "NFA_accept (efficient_determinise_NFA \<A>) w = NFA_accept \<A> w"
unfolding efficient_determinise_NFA_def
by simp

lemma (in NFA) efficient_determinise_NFA_\<L> [simp] :
"\<L> (efficient_determinise_NFA \<A>) = \<L> \<A>"
unfolding efficient_determinise_NFA_def
by simp

lemma efficient_determinise_NFA___is_initially_connected :
  "SemiAutomaton_is_initially_connected (efficient_determinise_NFA \<A>)"
unfolding efficient_determinise_NFA_def 
by (simp add: SemiAutomaton_is_initially_connected___NFA_remove_unreachable_states)

lemma efficient_determinise_NFA_already_det :
assumes dfa_A : "DFA \<A>"
    and conn: "SemiAutomaton_is_initially_connected \<A>"
shows "NFA_isomorphic_wf \<A> (efficient_determinise_NFA \<A>)"
proof -
  from dfa_A have nfa_A: "NFA \<A>"
              and det_A: "SemiAutomaton_is_complete_deterministic \<A>"
              and sa_A: "SemiAutomaton \<A>"
              and dsa_A: "DetSemiAutomaton \<A>"
    unfolding DFA_alt_def NFA_alt_def FinSemiAutomaton_def DetSemiAutomaton_alt_def by simp_all


  interpret det_A': DFA "determinise_NFA \<A>" by (rule determinise_NFA___DFA[OF nfa_A])
  interpret det_A: DFA \<A> by fact

  have det_trans: "LTS_is_deterministic (\<Delta> (determinise_NFA \<A>))" 
    by (metis SemiAutomaton_is_deterministic_def determinise_NFA_is_det)

  let ?f = "\<lambda>q. {q}"
  have inj_f: "\<And>Q. inj_on ?f Q"
    unfolding inj_on_def by simp

  have reachable_states_eq: "SemiAutomaton_reachable_states (determinise_NFA \<A>) = (\<lambda>q. {q}) ` \<Q> \<A>"
    using det_A.determinise_NFA___LTS_is_reachable[of "{\<i> \<A>}"] det_A.\<i>_is_state
    unfolding det_A'.SemiAutomaton_reachable_states_reachable 
              det_A.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp
    apply (simp)
    apply (rule set_eqI)
    apply (simp add: image_iff Bex_def)
    apply (intro iffI)
  proof -
    fix Q'
    assume "\<exists>w. w \<in> lists (\<Sigma> \<A>) \<and>
                Q' = {q'. DLTS_reach (\<delta> \<A>) (\<i> \<A>) w = Some q'}"
    then obtain w where
      w_in: "w \<in> lists (\<Sigma> \<A>)" and Q'_eq: "Q' = {q'. DLTS_reach (\<delta> \<A>) (\<i> \<A>) w = Some q'}" by blast

    from det_A CLTS_is_reachable_exists[of "\<Q> \<A>" "\<Sigma> \<A>" "\<Delta> \<A>" w "\<i> \<A>"] det_A.\<i>_is_state w_in
    obtain q' where reach_w_simp: "DLTS_reach (\<delta> \<A>) (\<i> \<A>) w = Some q'"
      unfolding SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def
                det_A.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp
      by simp blast

    from reach_w_simp have q'_in: "q' \<in> \<Q> \<A>" 
      using det_A.DetSemiAutomaton_DLTS_reach_wf[OF det_A.\<i>_is_state, of w q'] by simp

    show "\<exists>q'. q' \<in> \<Q> \<A> \<and> Q' = {q'}"
      apply (rule exI[where x = q'])
      apply (simp add: Q'_eq reach_w_simp q'_in)
    done
  next
    fix Q'
    assume "\<exists>q'. q' \<in> \<Q> \<A> \<and> Q' = {q'}"
    then obtain q' where q'_in: "q' \<in> \<Q> \<A>" and Q'_eq: "Q' = {q'}" by blast


    from q'_in conn obtain w where 
      reach_w_simp: "DLTS_reach (\<delta> \<A>) (\<i> \<A>) w = Some q'"
      unfolding SemiAutomaton_is_initially_connected_def SemiAutomaton_unreachable_states_def
              LTS_is_unreachable_def
              det_A.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp
      by auto

    from reach_w_simp have w_in: "w \<in> lists (\<Sigma> \<A>)" 
      using det_A.DetSemiAutomaton_DLTS_reach_wf[OF det_A.\<i>_is_state, of w q'] by simp

    show "\<exists>w. w \<in> lists (\<Sigma> \<A>) \<and>
                Q' = {q'. DLTS_reach (\<delta> \<A>) (\<i> \<A>) w = Some q'}"
      apply (rule exI[where x=w])
      apply (simp add: Q'_eq w_in reach_w_simp)
    done
  qed
   
  show ?thesis
    unfolding NFA_isomorphic_wf_def  NFA_isomorphic_def 
    apply (simp add: nfa_A)
    apply (rule exI[where x = ?f])
    apply (simp add: inj_f efficient_determinise_NFA_def SemiAutomaton_to_NFA_def
      det_A'.NFA_remove_unreachable_states_alt_def2
      det_A'.SemiAutomaton_remove_unreachable_states_alt_def
      NFA_rename_states_full_def reachable_states_eq)
    apply (insert det_A.\<Delta>_consistent det_A.\<F>_consistent)
    apply (intro conjI set_eqI)
    apply (auto simp add: image_iff det_A.\<i>_is_state)
    apply (metis LTS_is_deterministic_def det_A.deterministic_LTS)
  done
qed

lemma NFA_isomorphic_wf___NFA_determinise_cong :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (determinise_NFA \<A>1) (determinise_NFA \<A>2)"
proof -
  from equiv obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                            \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                            wf_\<A>1: "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  obtain F where F_def : "F = (\<lambda>S. f ` S)" by blast

  have F_elim: "\<And>Q1 Q2. \<lbrakk>Q1 \<subseteq> \<Q> \<A>1; Q2 \<subseteq> \<Q> \<A>1\<rbrakk> \<Longrightarrow> (F Q1 = F Q2) \<longleftrightarrow> Q1 = Q2"
  proof -
    fix Q1 Q2    
    assume "Q1 \<subseteq> \<Q> \<A>1" "Q2 \<subseteq> \<Q> \<A>1"
    hence "Q1 \<union> Q2 \<subseteq> \<Q> \<A>1" by simp
    with inj_f have "inj_on f (Q1 \<union> Q2)" by (rule subset_inj_on)

    thus "(F Q1 = F Q2) \<longleftrightarrow> Q1 = Q2"
      using inj_on_Un_image_eq_iff [of f Q1 Q2] F_def
      by simp
  qed

  from F_elim have inj_F : "inj_on F (\<Q> (determinise_NFA \<A>1))"
    unfolding determinise_NFA_def inj_on_def
    by simp

  have \<A>2_eq' : "determinise_NFA \<A>2 = NFA_rename_states (determinise_NFA \<A>1) F"
    unfolding determinise_NFA_def \<A>2_eq NFA_rename_states_def SemiAutomaton_rename_states_ext_def
              powerset_SemiAutomaton_def SemiAutomaton_to_NFA_def 
    apply simp
  proof (intro conjI)
    show "f ` \<I> \<A>1 = F (\<I> \<A>1)" unfolding F_def by simp
  next
    show "{q. q \<subseteq> f ` \<Q> \<A>1} = F ` {q. q \<subseteq> \<Q> \<A>1}"
      apply (rule set_eqI)
      apply (simp add: subset_image_iff F_def image_iff)
    done
  next
    have "\<And>Q. Q \<subseteq> (\<Q> \<A>1) \<Longrightarrow> (f ` Q \<inter> (f ` (\<F> \<A>1)) \<noteq> {}) = (Q \<inter> \<F> \<A>1 \<noteq> {})"
    proof -
      fix Q
      assume Q_sub: "Q \<subseteq> (\<Q> \<A>1)"
      
      from NFA.\<F>_consistent [OF wf_\<A>1] 
      have F_sub: "\<F> \<A>1 \<subseteq> \<Q> \<A>1" .

      from inj_on_image_Int [OF inj_f Q_sub F_sub, symmetric]
      show "(f ` Q \<inter> (f ` (\<F> \<A>1)) \<noteq> {}) = (Q \<inter> \<F> \<A>1 \<noteq> {})"
        by simp
    qed
    thus "{fs. fs \<subseteq> f ` \<Q> \<A>1 \<and> fs \<inter> f ` \<F> \<A>1 \<noteq> {}} = F ` {fs. fs \<subseteq> \<Q> \<A>1 \<and> fs \<inter> \<F> \<A>1 \<noteq> {}}"
      apply (rule_tac set_eqI)
      apply (simp add: subset_image_iff F_def image_iff)
      apply metis
    done
  next
    from inj_f SemiAutomaton.\<Delta>_consistent[of \<A>1] wf_\<A>1
    have lem: "\<And>\<sigma> Q. \<lbrakk>Q \<subseteq> \<Q> \<A>1; \<sigma> \<in> \<Sigma> \<A>1\<rbrakk> \<Longrightarrow>
        {q'. \<exists>q\<in>Q. \<exists>s1 s2. f q = f s1 \<and> q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1} =
        f ` {q'. \<exists>q\<in>Q. (q, \<sigma>, q') \<in> \<Delta> \<A>1}" 
      apply (rule_tac set_eqI)
      apply (simp add: image_iff inj_on_def subset_iff Bex_def NFA_alt_def FinSemiAutomaton_def)
      apply auto
      apply metis
    done

    show "{(Q, \<sigma>, {q'. \<exists>q\<in>Q. \<exists>s1. q = f s1 \<and> (\<exists>s2. q' = f s2 \<and> (s1, \<sigma>, s2) \<in> \<Delta> \<A>1)}) |Q \<sigma>.
     Q \<subseteq> f ` \<Q> \<A>1 \<and> \<sigma> \<in> \<Sigma> \<A>1} =
    {(F s1, a, F {q'. \<exists>q\<in>s1. (q, a, q') \<in> \<Delta> \<A>1}) |s1 a. s1 \<subseteq> \<Q> \<A>1 \<and> a \<in> \<Sigma> \<A>1}"

      apply (rule_tac set_eqI)
      apply (simp add: subset_image_iff F_def image_iff)
      apply (simp del: ex_simps add: ex_simps[symmetric])
      apply auto
        apply (insert lem, auto)
        apply (insert lem[symmetric], auto)
    done
  qed

  from inj_F \<A>2_eq' determinise_NFA___is_well_formed [OF wf_\<A>1]
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast
qed

lemma NFA_isomorphic_efficient_determinise :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (efficient_determinise_NFA \<A>1) (efficient_determinise_NFA \<A>2)"
unfolding efficient_determinise_NFA_def
by (intro NFA_isomorphic_wf___NFA_remove_unreachable_states 
          NFA_isomorphic_wf___NFA_determinise_cong equiv)

definition NFA_determinise :: "('q::{automaton_states}, 'a, _) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec" where
  "NFA_determinise \<A> = NFA_normalise_states (efficient_determinise_NFA \<A>)"

lemma NFA_determinise_isomorphic_wf :
assumes wf_A: "NFA \<A>"
shows  "NFA_isomorphic_wf (efficient_determinise_NFA \<A>) 
                          (NFA_determinise \<A>)"
unfolding NFA_determinise_def
apply (rule NFA_isomorphic_wf_normalise_states)
apply (rule efficient_determinise_NFA_is_DFA [OF wf_A, THEN DFA_implies_NFA])
done

lemma NFA_determinise_already_det :
assumes dfa_A : "DFA \<A>"
    and conn: "SemiAutomaton_is_initially_connected \<A>"
shows "NFA_isomorphic_wf \<A> (NFA_determinise \<A>)"
using NFA_isomorphic_wf_trans[OF 
   efficient_determinise_NFA_already_det[OF dfa_A conn]
   NFA_determinise_isomorphic_wf[of \<A>]] dfa_A
by (simp add: DFA_alt_def)
  
lemma NFA_determinise_\<Sigma> [simp] :
  "\<Sigma> (NFA_determinise \<A>) = \<Sigma> \<A>"
unfolding NFA_determinise_def by simp

lemma NFA_determinise_is_DFA :
assumes wf_A : "NFA \<A>"
shows "DFA (NFA_determinise \<A>)"
proof -
  note step1 = efficient_determinise_NFA_is_DFA [OF wf_A]
  note step2 = NFA_determinise_isomorphic_wf [OF wf_A]
  note step3 = NFA_isomorphic___is_well_formed_DFA [OF step1 NFA_isomorphic_wf_D(3)[OF step2]]
  thus ?thesis .
qed

lemma NFA_determinise_NFA_accept :
assumes wf_A : "NFA \<A>"
shows  "NFA_accept (NFA_determinise \<A>) w = NFA_accept \<A> w"
proof -
  note iso = NFA_determinise_isomorphic_wf [OF wf_A]
  from NFA_isomorphic_wf_accept [OF iso] NFA.efficient_determinise_NFA_accept [OF wf_A]
  show ?thesis by auto
qed

lemma NFA_determinise_\<L> :
"NFA \<A> \<Longrightarrow> \<L> (NFA_determinise \<A>) = \<L> \<A>"
by (simp add: \<L>_def NFA_determinise_NFA_accept)


subsection \<open> Right quotient \<close>

lemma NFA_right_quotient___is_well_formed_DFA :
  "DFA \<A> \<Longrightarrow> DFA (NFA_right_quotient \<A> L)"
unfolding DFA_alt_def SemiAutomaton_is_complete_deterministic_def
by (simp add: NFA_right_quotient___is_well_formed)


subsection \<open> Complement \<close>
definition DFA_complement :: "('q, 'a, 'x) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec" where
  "DFA_complement \<A> = \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = \<Q> \<A> - \<F> \<A> \<rparr>"

lemma [simp] : "\<Q> (DFA_complement \<A>) = \<Q> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<Sigma> (DFA_complement \<A>) = \<Sigma> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<Delta> (DFA_complement \<A>) = \<Delta> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<I> (DFA_complement \<A>) = \<I> \<A>" by (simp add: DFA_complement_def)
lemma [simp] : "\<F> (DFA_complement \<A>) = \<Q> \<A> - \<F> \<A>" by (simp add: DFA_complement_def)

lemma [simp] : "\<delta> (DFA_complement \<A>) = \<delta> \<A>" by (simp add: DFA_complement_def \<delta>_def)
lemma [simp] : "\<i> (DFA_complement \<A>) = \<i> \<A>" by (simp add: DFA_complement_def \<i>_def)

lemma DFA_complement_alt_def :
  "DFA_complement \<A> = SemiAutomaton_to_NFA \<A> (\<Q> \<A> - \<F> \<A>)"
unfolding DFA_complement_def SemiAutomaton_to_NFA_def by simp
  
lemma DFA_complement___is_well_formed : "NFA \<A> \<Longrightarrow> NFA (DFA_complement \<A>)"
unfolding NFA_full_def by auto

lemma DFA_complement_of_DFA_is_DFA :
  "DFA \<A> \<Longrightarrow> DFA (DFA_complement \<A>)"
unfolding DFA_alt_def NFA_full_def SemiAutomaton_is_complete_deterministic_def by auto

lemma DFA_complement___DLTS_reach :
  "DLTS_reach (\<delta> (DFA_complement \<A>)) q w = DLTS_reach (\<delta> \<A>) q w" by simp

lemma DFA_complement_DFA_complement [simp] :
  "NFA \<A> \<Longrightarrow> DFA_complement (DFA_complement \<A>) = \<A>"
proof -
  assume a: "NFA \<A>"
  then have "\<Q> \<A> - (\<Q> \<A> - \<F> \<A>) = \<F> \<A>" using NFA.\<F>_consistent by auto
  thus ?thesis unfolding DFA_complement_def by simp
qed

lemma DFA_complement_word :
  assumes wf_A: "DFA \<A>" and w_in_\<Sigma>: "w \<in> lists (\<Sigma> \<A>)"
  shows "NFA_accept (DFA_complement \<A>) w \<longleftrightarrow> \<not> NFA_accept \<A> w"
proof -
  let ?c\<A> = "DFA_complement \<A>"

  interpret DFA_A: DFA \<A> by (fact wf_A)
  interpret DFA_cA: DFA ?c\<A> by (simp add: DFA_complement_of_DFA_is_DFA wf_A)

  from w_in_\<Sigma> DFA_A.\<i>_is_state
  have "~(DLTS_reach (\<delta> \<A>) (\<i> \<A>) w = None)" 
    by (simp add: DFA_A.DetSemiAutomaton_DLTS_reach_is_some)
  then obtain q' where DLTS_reach_eq_q': "DLTS_reach (\<delta> \<A>) (\<i> \<A>) w = Some q'" by auto
   
  from DLTS_reach_eq_q' DFA_A.\<i>_is_state have
   "q' \<in> \<Q> \<A>" by (metis DFA_A.DetSemiAutomaton_DLTS_reach_wf)

  with DLTS_reach_eq_q' show ?thesis
    by (simp add: NFA_accept_def Bex_def w_in_\<Sigma>
           DFA_A.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp
           DFA_cA.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp)
qed

lemma (in DFA) DFA_complement_\<L>___lists_\<Sigma> :
  "\<L> (DFA_complement \<A>) \<subseteq> lists (\<Sigma> \<A>)"
by (simp add: DFA_complement_def \<L>_def NFA_accept_def subset_iff)
   (metis LTS_is_reachable___labels)

lemma (in DFA) DFA_complement_\<L> [simp] : 
shows "\<L> (DFA_complement \<A>) = lists (\<Sigma> \<A>) - \<L> \<A>"
proof (intro set_eqI)
  fix w
  show "(w \<in> \<L> (DFA_complement \<A>)) \<longleftrightarrow> w \<in> (lists (\<Sigma> \<A>) - \<L> \<A>)"
  proof (cases "w \<in> lists (\<Sigma> \<A>)")
    case False with DFA_complement_\<L>___lists_\<Sigma> show ?thesis 
      by auto
  next
    case True 
    note w_in_\<Sigma> = this
    note DFA_complement_w = DFA_complement_word [OF DFA_axioms w_in_\<Sigma>]

    from DFA_complement_w w_in_\<Sigma> show ?thesis by (simp add: \<L>_def)
  qed
qed

lemma NFA_isomorphic_wf___DFA_complement_cong :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (DFA_complement \<A>1) (DFA_complement \<A>2)"
proof -
  from equiv obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = NFA_rename_states \<A>1 f" and
                 wf_\<A>1: "NFA \<A>1" 
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by auto

  with inj_f have inj_f' : "inj_on f (\<Q> (DFA_complement \<A>1))"
    by simp

  have \<A>2_eq': "DFA_complement \<A>2 = NFA_rename_states (DFA_complement \<A>1) f"
    unfolding DFA_complement_def \<A>2_eq 
    apply (rule NFA_rec.equality)
    apply (simp_all)
    apply (simp add: NFA_rename_states_def SemiAutomaton_rename_states_ext_def)
    apply (insert inj_on_image_set_diff [of f "\<Q> \<A>1" "\<Q> \<A>1" "\<F> \<A>1"])
    apply (insert NFA.\<F>_consistent[OF wf_\<A>1])
    apply (simp add: inj_f)
  done

  from inj_f' \<A>2_eq' DFA_complement___is_well_formed [OF wf_\<A>1] 
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast
qed

subsection \<open> Boolean Combinations of NFAs \<close>

lemma bool_comb_DFA___is_well_formed :
assumes DFA_\<A>1 : "DFA \<A>1"
    and DFA_\<A>2 : "DFA \<A>2"
shows "DFA (bool_comb_NFA f \<A>1 \<A>2)"
proof -
  from DFA_\<A>1 DFA_\<A>2 bool_comb_NFA___is_well_formed [of \<A>1 \<A>2]
  have NFA_ok: "NFA (bool_comb_NFA f \<A>1 \<A>2)"
    unfolding DFA_def by auto

  from DFA_\<A>1 DFA_\<A>2 product_SemiAutomaton___is_well_formed_det[of \<A>1 \<A>2]
  have det_ok: "SemiAutomaton_is_complete_deterministic (bool_comb_NFA f \<A>1 \<A>2)"
    unfolding DFA_alt_def3 by (simp add: bool_comb_NFA_def DetSemiAutomaton_alt_def)

  from NFA_ok det_ok show ?thesis
    unfolding DFA_alt_def by simp
qed

lemma efficient_bool_comb_DFA___is_well_formed :
assumes DFA_\<A>1 : "DFA \<A>1"
    and DFA_\<A>2 : "DFA \<A>2"
shows "DFA (efficient_bool_comb_NFA f \<A>1 \<A>2)"
using bool_comb_DFA___is_well_formed [OF DFA_\<A>1 DFA_\<A>2, of f]
unfolding efficient_bool_comb_NFA_def
by (rule DFA___NFA_remove_unreachable_states)

lemma bool_comb_DFA_NFA_accept :
assumes DFA_\<A>1 : "DFA \<A>1"
    and DFA_\<A>2 : "DFA \<A>2"
shows "NFA_accept (bool_comb_NFA f \<A>1 \<A>2) w = 
       (w \<in> lists (\<Sigma> \<A>1) \<inter> lists (\<Sigma> \<A>2) \<and> f (NFA_accept \<A>1 w) (NFA_accept \<A>2 w))"
proof -
  interpret DFA1 : DFA \<A>1 by (fact DFA_\<A>1)
  interpret DFA2 : DFA \<A>2 by (fact DFA_\<A>2)
  interpret DFA12: DFA "(bool_comb_NFA f \<A>1 \<A>2)" by (rule bool_comb_DFA___is_well_formed, fact+)

  show ?thesis
  proof (cases "w \<in> lists (\<Sigma> \<A>1) \<inter> lists (\<Sigma> \<A>2)")
    case False thus ?thesis 
      by (simp add: DFA12.NFA_accept_wf_def, auto)
  next
    case True note w_in_lists = this
    then obtain q1 q2 where DLTS_reach_is_some:
      "(DLTS_reach (\<delta> \<A>1) (\<i> \<A>1) w = Some q1) \<and>
       (DLTS_reach (\<delta> \<A>2) (\<i> \<A>2) w = Some q2)"
    using DFA1.DetSemiAutomaton_reach_is_none_iff [where w = w and q = "\<i> \<A>1"]
          DFA2.DetSemiAutomaton_reach_is_none_iff [where w = w and q = "\<i> \<A>2"]
    by (simp add: DFA1.\<i>_is_state DFA2.\<i>_is_state, auto)

    from DLTS_reach_is_some 
      have q12_in_Q: "q1 \<in> \<Q> \<A>1 \<and> q2 \<in> \<Q> \<A>2"
    using DFA1.DetSemiAutomaton_DLTS_reach_wf [where w = w and q = "\<i> \<A>1" and q' = q1]
          DFA2.DetSemiAutomaton_DLTS_reach_wf [where w = w and q = "\<i> \<A>2" and q' = q2]
          DFA1.\<i>_is_state DFA2.\<i>_is_state
    by simp

    from q12_in_Q DLTS_reach_is_some w_in_lists show ?thesis
      by (simp add: bool_comb_NFA_def NFA_accept_def
                    LTS_is_reachable_product Bex_def lists_inter
                    DFA1.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp DFA1.\<i>_is_state
                    DFA2.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp DFA2.\<i>_is_state)
  qed
qed

lemma efficient_bool_comb_DFA_accept :
assumes DFA_\<A>1 : "DFA \<A>1"
    and DFA_\<A>2 : "DFA \<A>2"
shows "NFA_accept (efficient_bool_comb_NFA f \<A>1 \<A>2) w = 
       (w \<in> lists (\<Sigma> \<A>1) \<inter> lists (\<Sigma> \<A>2) \<and> f (NFA_accept \<A>1 w) (NFA_accept \<A>2 w))"
using assms
unfolding efficient_bool_comb_NFA_def
by (simp add: bool_comb_DFA_NFA_accept)

lemma NFA_bool_comb_DFA___is_well_formed :
assumes DFA_\<A>1 : "DFA \<A>1"
    and DFA_\<A>2 : "DFA \<A>2"
shows "DFA (NFA_bool_comb f \<A>1 \<A>2)"
proof -
  from  DFA_\<A>1 DFA_\<A>2 have NFA_\<A>12: "NFA \<A>1" "NFA \<A>2"
    unfolding DFA_alt_def by simp_all

  note step1 = efficient_bool_comb_DFA___is_well_formed [OF DFA_\<A>1 DFA_\<A>2, of f]
  note iso = NFA_isomorphic_wf_D(3) [OF NFA_bool_comb___isomorphic_wf [OF NFA_\<A>12]]
  note step3 = NFA_isomorphic___is_well_formed_DFA [OF step1 iso]
  thus ?thesis .
qed

lemma NFA_bool_comb_DFA___NFA_accept :
assumes DFA_\<A>1 : "DFA \<A>1"
    and DFA_\<A>2 : "DFA \<A>2"
shows "NFA_accept (NFA_bool_comb f \<A>1 \<A>2) w = 
       (w \<in> lists (\<Sigma> \<A>1) \<inter> lists (\<Sigma> \<A>2) \<and> f (NFA_accept \<A>1 w) (NFA_accept \<A>2 w))"
proof -
  from  DFA_\<A>1 DFA_\<A>2 have NFA_\<A>12: "NFA \<A>1" "NFA \<A>2"
    unfolding DFA_alt_def by simp_all

  note step1 = efficient_bool_comb_DFA_accept [OF DFA_\<A>1 DFA_\<A>2, of f]
  note iso = NFA_bool_comb___isomorphic_wf [OF NFA_\<A>12]
  note step2 = NFA_isomorphic_wf_\<L> [OF iso, of f]

  from step1 step2
  show ?thesis by (auto simp add: NFA_accept_alt_def)
qed


subsection \<open> Minimisation \<close>

definition DFA_is_smaller_equiv where
  "DFA_is_smaller_equiv \<A> \<A>' \<equiv>
   DFA \<A>' \<and> (\<Sigma> \<A> = \<Sigma> \<A>') \<and> (\<L> \<A> = \<L> \<A>') \<and> (card (\<Q> \<A>') < card (\<Q> \<A>))"

definition DFA_is_minimal where
  "DFA_is_minimal \<A> \<equiv> DFA (\<A>::('q, 'a, 'X) NFA_rec_scheme) \<and> 
     (\<forall>\<A>'::('q, 'a) NFA_rec. \<not>(DFA_is_smaller_equiv \<A> \<A>'))"

text \<open> The definition of minimal automata considers only automata that use the same type of states and no extra information.
  This is useful, because otherwise the right hand side would contain type variables that do not occur on the left side of the definition.
  However, the property holds in general. \<close>  

lemma NFA_accept_truncate [simp] : 
  "NFA_accept (NFA_rec.truncate \<A>) = NFA_accept \<A>"
by (simp add: fun_eq_iff NFA_accept_def NFA_rec.truncate_def)

lemma \<L>_truncate [simp] : 
  "\<L> (NFA_rec.truncate \<A>) = \<L> \<A>"
by (simp add: \<L>_def)

lemma NFA_truncate [simp] :
  "NFA (NFA_rec.truncate \<A>) = NFA \<A>"
unfolding NFA_full_def
by (simp add: NFA_rec.truncate_def)

lemma SemiAutomaton_is_complete_deterministic_truncate [simp] :
  "SemiAutomaton_is_complete_deterministic (NFA_rec.truncate \<A>) = SemiAutomaton_is_complete_deterministic \<A>"
unfolding SemiAutomaton_is_complete_deterministic_def
by (simp add: NFA_rec.truncate_def)

lemma SemiAutomaton_is_deterministic_truncate [simp] :
  "SemiAutomaton_is_deterministic (NFA_rec.truncate \<A>) = SemiAutomaton_is_deterministic \<A>"
unfolding SemiAutomaton_is_deterministic_def
by (simp add: NFA_rec.truncate_def)

lemma DFA_truncate [simp] :
  "DFA (NFA_rec.truncate \<A>) = DFA \<A>"
unfolding DFA_alt_def
by simp

lemma DFA_is_smaller_equiv_truncate [simp] : "DFA_is_smaller_equiv \<A> (NFA_rec.truncate \<A>') \<longleftrightarrow> DFA_is_smaller_equiv \<A> \<A>'"
unfolding DFA_is_smaller_equiv_def
by (simp, simp add: NFA_rec.truncate_def)


lemma DFA_is_minimal_gen_def :
fixes \<A>:: "('q, 'a, 'X) NFA_rec_scheme"
shows "DFA_is_minimal \<A> \<longleftrightarrow> DFA \<A> \<and> (\<forall>\<A>'::('q, 'a, 'X2) NFA_rec_scheme. \<not>(DFA_is_smaller_equiv \<A> \<A>'))"
unfolding DFA_is_minimal_def
proof (intro iffI allI conjI) 
  fix \<A>' :: "('q, 'a, 'X2) NFA_rec_scheme"
  assume "DFA \<A> \<and> (\<forall>\<A>'::('q, 'a) NFA_rec. \<not>(DFA_is_smaller_equiv \<A> \<A>'))"
  hence "\<not> DFA_is_smaller_equiv \<A> (NFA_rec.truncate \<A>')"
    by blast
  thus "\<not> DFA_is_smaller_equiv \<A> \<A>'" by simp
next
  fix \<A>' :: "('q, 'a) NFA_rec"
  assume "DFA \<A> \<and>
          (\<forall>\<A>'::('q, 'a, 'X2) NFA_rec_scheme. \<not> DFA_is_smaller_equiv \<A> \<A>')"
  hence "\<not> DFA_is_smaller_equiv \<A> (NFA_rec.extend \<A>' (ARB::'X2))"
    by blast
  hence "\<not> DFA_is_smaller_equiv \<A> (NFA_rec.truncate (NFA_rec.extend \<A>' (ARB::'X2)))" by simp
  hence "\<not> DFA_is_smaller_equiv \<A> (NFA_rec.truncate \<A>')"
    by (simp add: NFA_rec.defs)
  thus "\<not> DFA_is_smaller_equiv \<A> \<A>'" by simp
qed simp_all

locale minDFA = DFA \<A> for \<A> +
  assumes minimal_DFA: "DFA_is_minimal \<A>"

lemma minDFA_alt_def :
  "minDFA \<A> = DFA_is_minimal \<A>"
by (simp add: minDFA_def minDFA_axioms_def DFA_is_minimal_def)

lemma (in minDFA) wf_minDFA :
  "minDFA \<A>" by (simp add: minDFA_alt_def minimal_DFA)

lemma (in minDFA) DFA_is_minimal___DLTS_reachable :
  "q \<in> \<Q> \<A> \<Longrightarrow> q \<notin> SemiAutomaton_unreachable_states \<A>"
proof 
  let ?\<A>' = "NFA_remove_unreachable_states \<A>"
  from complete_deterministic_SemiAutomaton have det_A': "SemiAutomaton_is_complete_deterministic ?\<A>'"
    by (simp add: SemiAutomaton_is_complete_deterministic___NFA_remove_unreachable_states)

  have \<Sigma>_A': "\<Sigma> ?\<A>' = \<Sigma> \<A>" by (simp add: NFA_remove_unreachable_states_def)
  have L_A': "\<L> ?\<A>' = \<L> \<A>" by simp
  from NFA_axioms have wf_A': "NFA ?\<A>'" using NFA_remove_states___is_well_formed
    unfolding NFA_remove_unreachable_states_def by metis
  with det_A' have "DFA ?\<A>'" unfolding DFA_alt_def by fast

  assume "q \<in> \<Q> \<A>" "q \<in> SemiAutomaton_unreachable_states \<A>"
  hence "\<Q> ?\<A>' \<subset> \<Q> \<A>" by (auto simp add: NFA_remove_unreachable_states_def)
  hence card_A': "card (\<Q> ?\<A>') < card (\<Q> \<A>)"
    by (metis psubset_card_mono NFA_full_def NFA_axioms)

  from `DFA ?\<A>'` \<Sigma>_A' L_A' card_A' 
  have "DFA_is_smaller_equiv \<A> ?\<A>'"
    unfolding DFA_is_smaller_equiv_def
    by simp
  hence not_min_A: "\<not> DFA_is_minimal \<A>"
    by (metis DFA_is_minimal_def)

  from not_min_A minimal_DFA show "False" by auto
qed

lemma (in minDFA) DFA_is_minimal___initially_connected :
  "SemiAutomaton_is_initially_connected \<A>"
using DFA_is_minimal___DLTS_reachable
unfolding SemiAutomaton_is_initially_connected_def
by auto

lemma (in DFA) SemiAutomaton_is_complete_deterministic___combine_equiv_states :
assumes equiv_f: "NFA_is_strong_equivalence_rename_fun \<A> f"
shows "SemiAutomaton_is_complete_deterministic (NFA_rename_states \<A> f)"
proof -
  have comdet_\<Delta>: "LTS_is_complete_deterministic (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>)"
    by (simp add: complete_deterministic_LTS)
  hence det_\<Delta>: "LTS_is_deterministic (\<Delta> \<A>)" 
    by (simp add: LTS_is_complete_deterministic_def)

  have part1:
   "\<And>q1 q2 q1' q2' \<sigma>.
      \<lbrakk>(q1, \<sigma>, q1') \<in> \<Delta> \<A>; (q2, \<sigma>, q2') \<in> \<Delta> \<A>; f q1 = f q2\<rbrakk> \<Longrightarrow> (f q1' = f q2')"
  proof -
    fix q1 q2 q1' q2' \<sigma>
    assume in_\<Delta>1 : "(q1, \<sigma>, q1') \<in> \<Delta> \<A>"
    assume in_\<Delta>2 : "(q2, \<sigma>, q2') \<in> \<Delta> \<A>"
    assume f_eq : "f q1 = f q2"

    from in_\<Delta>1 in_\<Delta>2 \<Delta>_consistent have "q1 \<in> \<Q> \<A> \<and> q2 \<in> \<Q> \<A>" by simp
    with f_eq equiv_f have \<L>_eq: "\<L>_in_state \<A> q1 = \<L>_in_state \<A> q2"
      by (simp add: NFA_is_strong_equivalence_rename_fun_def)

    have \<L>'_eq: "\<L>_in_state \<A> q1' = \<L>_in_state \<A> q2'"
      by (fact \<L>_in_state___DFA___eq_reachable_step [OF DFA_axioms DFA_axioms in_\<Delta>1 in_\<Delta>2 \<L>_eq])

    from in_\<Delta>1 in_\<Delta>2 \<Delta>_consistent have "q1' \<in> \<Q> \<A> \<and> q2' \<in> \<Q> \<A>" by simp
    with \<L>'_eq equiv_f show f'_eq: "f q1' = f q2'"
      by (simp add: NFA_is_strong_equivalence_rename_fun_def)
  qed

  have part2:
    "\<And>q \<sigma>. \<lbrakk>q \<in> \<Q> \<A>; \<sigma> \<in> \<Sigma> \<A>\<rbrakk> \<Longrightarrow> \<exists>q1 q1'. f q = f q1 \<and> (q1, \<sigma>, q1') \<in> \<Delta> \<A>" 
  proof -
    fix q \<sigma>
    assume "q \<in> \<Q> \<A>" "\<sigma> \<in> \<Sigma> \<A>"
    with comdet_\<Delta> obtain q' where q'_intro: "(q, \<sigma>, q') \<in> \<Delta> \<A>"
      by (auto simp add: LTS_is_complete_deterministic_def LTS_is_complete_def)

    from q'_intro show "\<exists>q1 q1'. f q = f q1 \<and> (q1, \<sigma>, q1') \<in> \<Delta> \<A>" by blast
  qed

  show ?thesis
    apply (simp add: SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def 
                  LTS_is_deterministic_def LTS_is_complete_def Bex_def Ball_def image_iff)
    apply (simp del: all_simps ex_simps add: ex_simps[symmetric] all_simps[symmetric])
    apply (simp)
    apply (rule conjI)
    apply (metis part1)
    apply (metis part2 \<Delta>_consistent)
  done
qed


lemma DFA___combine_equiv_states :
assumes DFA_\<A>: "DFA \<A>"
    and equiv_f: "NFA_is_strong_equivalence_rename_fun \<A> f"
shows "DFA (NFA_rename_states \<A> f)"
using DFA_\<A> DFA.SemiAutomaton_is_complete_deterministic___combine_equiv_states [OF DFA_\<A> equiv_f]
unfolding DFA_alt_def
by (simp add: NFA_rename_states___is_well_formed)


lemma (in minDFA) \<L>_in_state_inj :
  assumes q: "q \<in> \<Q> \<A>" and q': "q' \<in> \<Q> \<A>" and q_not_q': "q \<noteq> q'"
  shows "\<L>_in_state \<A> q \<noteq> \<L>_in_state \<A> q'"
proof
  obtain f where f_is_serf: "NFA_is_strong_equivalence_rename_fun \<A> (f::'a \<Rightarrow> 'a)"
    using NFA_is_strong_equivalence_rename_fun_exists by metis
  let ?\<A>' = "NFA_rename_states \<A> f"

  have "DFA ?\<A>'" by
     (fact DFA___combine_equiv_states [OF DFA_axioms f_is_serf])
  moreover
  note \<L>_rename_iff [OF NFA_is_strong_equivalence_rename_fun___weaken [OF f_is_serf]]
  hence "\<L> \<A> = \<L> ?\<A>'" by simp 
  moreover
  assume "\<L>_in_state \<A> q = \<L>_in_state \<A> q'"
  with f_is_serf q q' q_not_q' have not_inj: "\<not> inj_on f (\<Q> \<A>)"
    unfolding inj_on_def NFA_is_strong_equivalence_rename_fun_def by auto
  from finite_\<Q> not_inj have not_eq: "card (\<Q> ?\<A>') \<noteq> card (\<Q> \<A>)" using eq_card_imp_inj_on
    unfolding NFA_rename_states_def by auto
  from finite_\<Q> have "card (\<Q> ?\<A>') \<le> card (\<Q> \<A>)"
    using card_image_le unfolding NFA_rename_states_def by auto
  with not_eq have "card (\<Q> ?\<A>') < card (\<Q> \<A>)" by simp
  ultimately have "DFA_is_smaller_equiv \<A> (NFA_rename_states \<A> f)" 
    unfolding DFA_is_smaller_equiv_def by simp
  hence "\<not> DFA_is_minimal \<A>" by (metis DFA_is_minimal_def)
  with minimal_DFA show "False" by simp
qed

lemma (in DFA) DFA_is_minimal_intro :
  assumes
    connected: "SemiAutomaton_is_initially_connected \<A>" and
    no_equivalant_states: "inj_on (\<L>_in_state \<A>) (\<Q> \<A>)"
  shows "DFA_is_minimal \<A>"
proof (rule ccontr)
  assume "\<not> DFA_is_minimal \<A>"
  then obtain \<A>'::"('q, 'a) NFA_rec" where
    dfa_A': "DFA \<A>'" and
    same_\<Sigma>: "\<Sigma> \<A> = \<Sigma> \<A>'" and
    same_\<L>: "\<L> \<A> = \<L> \<A>'" and
    smaller: "card (\<Q> \<A>') < card (\<Q> \<A>)"
    unfolding DFA_is_minimal_def DFA_is_smaller_equiv_def by (auto simp add: DFA_axioms)

  interpret DFA_A' : DFA \<A>' by (fact dfa_A')

  have "\<not> (\<L>_in_state \<A>) ` (\<Q> \<A>) \<subseteq> (\<L>_in_state \<A>') ` (\<Q> \<A>')"
  proof -
    note DFA_A'.finite_\<Q>
    hence fin_L_A': "finite ((\<L>_in_state \<A>') ` (\<Q> \<A>'))" by (metis finite_imageI)
    from `finite (\<Q> \<A>')` have "card ((\<L>_in_state \<A>') ` (\<Q> \<A>')) \<le> card (\<Q> \<A>')" by (metis card_image_le)
    moreover
    from no_equivalant_states have "card ((\<L>_in_state \<A>) ` (\<Q> \<A>)) = card (\<Q> \<A>)" by (metis card_image)
    ultimately
    have "\<not> card ((\<L>_in_state \<A>) ` (\<Q> \<A>)) \<le> card ((\<L>_in_state \<A>') ` (\<Q> \<A>'))" using smaller by simp
    then show ?thesis by (metis card_mono fin_L_A')
  qed
  then obtain q where q_in_Q: "q \<in> \<Q> \<A> " and
    \<L>_q: "\<L>_in_state \<A> q \<notin> (\<L>_in_state \<A>') ` (\<Q> \<A>')" by auto
  from q_in_Q connected obtain w where DLTS_reach_\<A>: "LTS_is_reachable (\<Delta> \<A>) (\<i> \<A>) w q"
    unfolding SemiAutomaton_is_initially_connected_alt_def 
    by auto
  hence w_word: "w \<in> lists (\<Sigma> \<A>)" using LTS_is_reachable___labels by fast
  with same_\<Sigma> have "w \<in> lists (\<Sigma> \<A>')" by simp
  hence "\<not>(DLTS_reach (\<delta> \<A>') (\<i> \<A>') w = None)" unfolding DFA_A'.DetSemiAutomaton_reach_is_none_iff
    by (simp add: DFA_A'.\<i>_is_state)
  then obtain q' where DLTS_reach_\<A>': "LTS_is_reachable (\<Delta> \<A>') (\<i> \<A>') w q'"
    by (auto simp add: DFA_A'.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp)
  hence "q' \<in> \<Q> \<A>'"
    using DFA_A'.SemiAutomaton_\<Delta>_cons___LTS_is_reachable DFA_A'.\<i>_is_state 
    by simp
  with \<L>_q have \<L>_q_q'_neq: "\<L>_in_state \<A>' q' \<noteq> \<L>_in_state \<A> q" by blast
  show "False"
    using same_\<L> \<L>_q_q'_neq \<L>_in_state_\<i> DFA_A'.\<L>_in_state_\<i> 
         \<L>_in_state___DFA___eq_DLTS_reachable [OF DFA_axioms dfa_A'
            DLTS_reach_\<A> DLTS_reach_\<A>']
    by simp
qed

theorem (in DFA) DFA_is_minimal_alt_def :
  "DFA_is_minimal \<A> \<longleftrightarrow>
    (SemiAutomaton_is_initially_connected \<A> \<and>
     inj_on (\<L>_in_state \<A>) (\<Q> \<A>))"
   (is "_ = (?P1 \<and> ?P2)")
proof 
  assume "DFA_is_minimal \<A>"
  then interpret minDFA_A: minDFA \<A> by (simp add: minDFA_alt_def)

  show "?P1 \<and> ?P2"
  proof 
    show ?P1 by (auto simp add: minDFA_A.DFA_is_minimal___initially_connected)
  next
    show ?P2 by (auto simp add: inj_on_def, metis minDFA_A.\<L>_in_state_inj)
  qed
next
  assume "?P1 \<and> ?P2"
  with DFA_axioms show "DFA_is_minimal \<A>" 
    by (simp add: DFA_is_minimal_intro)
qed

lemma DFA_is_minimal_alt_DFA_def :
  "DFA_is_minimal \<A> \<longleftrightarrow>
    (DFA \<A> \<and> SemiAutomaton_is_initially_connected \<A> \<and>
     inj_on (\<L>_in_state \<A>) (\<Q> \<A>))"
   (is "_ = (?P1 \<and> ?P2)")
apply (cases "DFA \<A>")
  apply (simp add: DFA.DFA_is_minimal_alt_def)
apply (simp add: DFA_is_minimal_def)
done
 
lemma NFA_isomorphic___DFA_is_minimal :
fixes \<A>1 :: "('q1, 'a, 'X) NFA_rec_scheme"
fixes \<A>2 :: "('q2, 'a) NFA_rec"
assumes eq_A12: "NFA_isomorphic \<A>1 \<A>2"
    and min_A1: "DFA_is_minimal \<A>1"
shows "DFA_is_minimal \<A>2"
proof (rule ccontr)
  assume not_min_A2: "\<not>(DFA_is_minimal \<A>2)"

  from eq_A12 obtain f where
    inj_f: "inj_on f (\<Q> \<A>1)" and
    A2_eq: "\<A>2 = NFA_rename_states \<A>1 f"
    unfolding NFA_isomorphic_def by blast

  from min_A1 have wf_A1: "DFA \<A>1"
    unfolding DFA_is_minimal_def by fast

  from NFA_isomorphic___is_well_formed_DFA [OF wf_A1 eq_A12]
  have wf_A2: "DFA \<A>2" .

  from not_min_A2 obtain \<A>2' :: "('q2, 'a) NFA_rec" 
    where A2'_smaller: "DFA_is_smaller_equiv \<A>2 \<A>2'"
    by (auto simp add: DFA_is_minimal_def wf_A2)

  have wf_A2': "DFA \<A>2'"
    using A2'_smaller 
    unfolding DFA_is_smaller_equiv_def by simp

  have fin_QA2' : "finite (\<Q> \<A>2')"
    using wf_A2' [unfolded DFA_alt_def NFA_alt_def] FinSemiAutomaton.finite_\<Q>
    by blast
  have fin_QA1 : "finite (\<Q> \<A>1)"
    using wf_A1 [unfolded DFA_alt_def NFA_alt_def] FinSemiAutomaton.finite_\<Q>
    by blast

  from A2'_smaller have "card (\<Q> \<A>2') < card (\<Q> \<A>2)" 
    unfolding DFA_is_smaller_equiv_def by fast
  hence "card (\<Q> \<A>2') < card (\<Q> \<A>1)"
    unfolding A2_eq
    by (simp add: inj_f card_image)
  then obtain f' :: "'q2 \<Rightarrow> 'q1" where inj_f': "inj_on f' (\<Q> \<A>2')"
    using inj_on_iff_card_le [OF fin_QA2' fin_QA1]
    by auto

  have equiv_f': "NFA_is_equivalence_rename_fun \<A>2' f'"
    using inj_f' 
    unfolding NFA_is_equivalence_rename_fun_def inj_on_def
    by auto

  have equiv_f: "NFA_is_equivalence_rename_fun \<A>1 f"
    using inj_f
    unfolding NFA_is_equivalence_rename_fun_def inj_on_def
    by auto

  from A2'_smaller wf_A1 have
    A1_smaller: "DFA_is_smaller_equiv \<A>1 (NFA_rename_states \<A>2' f')"
    unfolding DFA_is_smaller_equiv_def A2_eq
    apply (simp add: inj_f inj_f' card_image DFA___inj_rename)
    apply (simp add: DFA_alt_def equiv_f' NFA.\<L>_rename_iff equiv_f)
  done

  from A1_smaller have "\<not>(DFA_is_minimal \<A>1)"
    unfolding DFA_is_minimal_def by auto
  with min_A1 show "False" by fast
qed

lemma DFA_is_minimal___equiv_states_injection_exists :
fixes \<A>1 :: "('q1, 'a, 'X1) NFA_rec_scheme"
fixes \<A>2 :: "('q2, 'a, 'X2) NFA_rec_scheme"
assumes L_eq: "\<L> \<A>1 = \<L> \<A>2"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2"
    and min_A1: "DFA_is_minimal \<A>1"
    and min_A2: "DFA_is_minimal \<A>2"
shows "\<exists>f. inj_on f (\<Q> \<A>1) \<and>
           (\<forall>q\<in>\<Q> \<A>1. (f q) \<in> \<Q> \<A>2 \<and> \<L>_in_state \<A>2 (f q) = \<L>_in_state \<A>1 q)"
proof -
  from min_A1 have wf_A1: "DFA \<A>1"
    by (simp add: DFA_is_minimal_alt_DFA_def)
  from min_A2 have wf_A2: "DFA \<A>2"
    by (simp add: DFA_is_minimal_alt_DFA_def)

  interpret DFA1 : DFA \<A>1 by (fact wf_A1)    
  interpret DFA2 : DFA \<A>2 by (fact wf_A2)    

  let ?states_equiv = "\<lambda>q1 q2. q2 \<in> \<Q> \<A>2 \<and> \<L>_in_state \<A>2 q2 = \<L>_in_state \<A>1 q1"
  have "\<forall>q1 \<in> \<Q> \<A>1. \<exists>q2. ?states_equiv q1 q2"
  proof 
    fix q1
    assume q1_in: "q1 \<in> \<Q> \<A>1"

    from min_A1 have "SemiAutomaton_is_initially_connected \<A>1" by (simp add: DFA_is_minimal_alt_DFA_def)
    then obtain w where DLTS_reach_q1: "LTS_is_reachable (\<Delta> \<A>1) (\<i> \<A>1) w q1"
      unfolding SemiAutomaton_is_initially_connected_alt_def 
      using q1_in by auto

    from DFA1.LTS_is_reachable___labels[OF DLTS_reach_q1] 
    have w_in_\<Sigma>1: "w \<in> lists (\<Sigma> \<A>1)" by simp
    from  w_in_\<Sigma>1 \<Sigma>_eq have w_in_\<Sigma>2: "w \<in> lists (\<Sigma> \<A>2)" by fast

    from DFA2.DetSemiAutomaton_DLTS_reach_is_some [OF DFA2.\<i>_is_state w_in_\<Sigma>2] 
    obtain q2 where "DLTS_reach (\<delta> \<A>2) (\<i> \<A>2) w = Some q2" by auto
    hence DLTS_reach_q2: "LTS_is_reachable (\<Delta> \<A>2) (\<i> \<A>2) w q2"
      by (simp add: DFA2.DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp)
    
    from DFA2.SemiAutomaton_\<Delta>_cons___LTS_is_reachable [OF DLTS_reach_q2] 
    have q2_in: "q2 \<in> \<Q> \<A>2" by (simp add: DFA2.\<i>_is_state)

    from L_eq have initial_equiv: "\<L>_in_state \<A>1 (\<i> \<A>1) = \<L>_in_state \<A>2 (\<i> \<A>2)"
      unfolding \<L>_alt_def by simp

    from \<L>_in_state___DFA___eq_DLTS_reachable [OF wf_A1 wf_A2 DLTS_reach_q1 DLTS_reach_q2 initial_equiv]
    have q12_equiv: "\<L>_in_state \<A>1 q1 = \<L>_in_state \<A>2 q2" .

    from q12_equiv q2_in show "\<exists>q2. ?states_equiv q1 q2" by blast
  qed
  from bchoice[OF this] obtain f where "\<forall>x\<in>\<Q> \<A>1. f x \<in> \<Q> \<A>2 \<and> \<L>_right \<A>2 (f x) = \<L>_right \<A>1 x" .. note f_prop = this

  have inj_f : "inj_on f (\<Q> \<A>1)"
  unfolding inj_on_def
  proof (intro ballI impI)
    fix q q'
    assume q1_in: "q \<in> \<Q> \<A>1"
       and q2_in: "q' \<in> \<Q> \<A>1"
       and f_qq'_eq: "f q = f q'"
    with f_prop have L_qq'_eq: "\<L>_in_state \<A>1 q = \<L>_in_state \<A>1 q'" by metis

    from q1_in q2_in L_qq'_eq min_A1 
    show "q = q'"
      unfolding DFA_is_minimal_alt_DFA_def inj_on_def
      by simp
  qed

  from f_prop inj_f show ?thesis by blast
qed

lemma DFA_is_minimal___equiv_states_bijection_exists :
fixes \<A>1 :: "('q1, 'a, 'X1) NFA_rec_scheme"
fixes \<A>2 :: "('q2, 'a, 'X2) NFA_rec_scheme"
assumes L_eq: "\<L> \<A>1 = \<L> \<A>2"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2"
    and min_A1: "DFA_is_minimal \<A>1"
    and min_A2: "DFA_is_minimal \<A>2"
shows "\<exists>f. bij_betw f (\<Q> \<A>1) (\<Q> \<A>2) \<and>
           (\<forall>q\<in>\<Q> \<A>1. \<L>_in_state \<A>2 (f q) = \<L>_in_state \<A>1 q)"
proof -
  from DFA_is_minimal___equiv_states_injection_exists 
    [OF L_eq \<Sigma>_eq min_A1 min_A2]
  obtain f1 where "inj_on f1 (\<Q> \<A>1) \<and> (\<forall>q\<in>\<Q> \<A>1. f1 q \<in> \<Q> \<A>2 \<and> \<L>_right \<A>2 (f1 q) = \<L>_right \<A>1 q)" .. note f1_props = this
  
  from DFA_is_minimal___equiv_states_injection_exists 
    [OF L_eq[symmetric] \<Sigma>_eq[symmetric] min_A2 min_A1]
  obtain f2 where "inj_on f2 (\<Q> \<A>2) \<and> (\<forall>q\<in>\<Q> \<A>2. f2 q \<in> \<Q> \<A>1 \<and> \<L>_right \<A>1 (f2 q) = \<L>_right \<A>2 q)" .. note f2_props = this

  have A2_eq: "f1 ` \<Q> \<A>1 = \<Q> \<A>2"
  proof
    from f1_props show "f1 ` \<Q> \<A>1 \<subseteq> \<Q> \<A>2" by auto
  next
    show "\<Q> \<A>2 \<subseteq> f1 ` \<Q> \<A>1"
    proof 
      fix q2
      assume q2_in: "q2 \<in> \<Q> \<A>2"
      let ?q1 = "f2 q2"
      let ?q2' = "f1 ?q1"

      from q2_in f2_props
      have q1_in: "?q1 \<in> \<Q> \<A>1" and
           q1_q2_equiv: "\<L>_in_state \<A>1 ?q1 = \<L>_in_state \<A>2 q2"
        by simp_all

      from f1_props q1_in 
      have q2'_in: "?q2' \<in> \<Q> \<A>2" and
           q2'_q1_equiv: "\<L>_in_state \<A>2 ?q2' = \<L>_in_state \<A>1 ?q1"
        by simp_all

      from q1_q2_equiv q2'_q1_equiv have
        q2_q2'_equiv: "\<L>_in_state \<A>2 ?q2' = \<L>_in_state \<A>2 q2"
        by simp

      from min_A2 q2_in q2'_in q2_q2'_equiv 
      have q2'_eq: "?q2' = q2"
        unfolding DFA_is_minimal_alt_DFA_def inj_on_def by simp

      from q2'_eq q1_in show "q2 \<in> f1 ` \<Q> \<A>1"
        by (simp add: image_iff) metis
    qed
  qed
  from f1_props A2_eq show ?thesis 
    apply (rule_tac exI [where x = f1])
    apply (simp add: bij_betw_def)
  done
qed

lemma DFA_is_minimal___isomorph_wf :
fixes \<A>1 :: "('q1, 'a, 'X) NFA_rec_scheme"
fixes \<A>2 :: "('q2, 'a) NFA_rec"
assumes min_A1: "DFA_is_minimal \<A>1"
    and min_A2: "DFA_is_minimal \<A>2"
    and L_eq: "\<L> \<A>1 = \<L> \<A>2"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2"
shows "NFA_isomorphic_wf \<A>1 \<A>2"
proof -
  from min_A1 have wf_A1: "DFA \<A>1"
    by (simp add: DFA_is_minimal_alt_DFA_def)
  from min_A2 have wf_A2: "DFA \<A>2"
    by (simp add: DFA_is_minimal_alt_DFA_def)

  interpret DFA1 : DFA \<A>1 by (fact wf_A1)    
  interpret DFA2 : DFA \<A>2 by (fact wf_A2)    

  from DFA_is_minimal___equiv_states_bijection_exists 
    [OF L_eq \<Sigma>_eq min_A1 min_A2]
  obtain f where "bij_betw f (\<Q> \<A>1) (\<Q> \<A>2) \<and> (\<forall>q\<in>\<Q> \<A>1. \<L>_right \<A>2 (f q) = \<L>_right \<A>1 q)" .. note f_props = this
  hence bij_f: "bij_betw f (\<Q> \<A>1) (\<Q> \<A>2)"
    and f_equiv: "\<And>q1. q1\<in>\<Q> \<A>1 \<Longrightarrow> \<L>_in_state \<A>2 (f q1) = \<L>_in_state \<A>1 q1"
    by simp_all

  from bij_f have f_is_state: "\<And>q1. q1\<in>\<Q> \<A>1 \<Longrightarrow> f q1 \<in> \<Q> \<A>2"
     unfolding bij_betw_def by auto

  from bij_f have inj_f: "inj_on f (\<Q> \<A>1)"
     unfolding bij_betw_def by fast

  have A2_eq: "\<A>2 = NFA_rename_states \<A>1 f" 
  unfolding NFA_rename_states_def SemiAutomaton_rename_states_ext_def
  proof (intro NFA_rec.equality, simp_all)
    show "\<Sigma> \<A>2 = \<Sigma> \<A>1" by (simp add: \<Sigma>_eq)
  next
    show "\<Q> \<A>2 = f ` \<Q> \<A>1"
      using bij_f unfolding bij_betw_def 
      by simp
  next
    from f_equiv [OF DFA1.\<i>_is_state] L_eq
    have "\<L>_in_state \<A>2 (f (\<i> \<A>1)) = \<L>_in_state \<A>2 (\<i> \<A>2)"
      unfolding \<L>_alt_def by simp
    with min_A2 DFA2.\<i>_is_state f_is_state [OF DFA1.\<i>_is_state]
    show "\<i> \<A>2 = f (\<i> \<A>1)"
      unfolding DFA_is_minimal_alt_DFA_def inj_on_def
      by simp
  next
    show "\<F> \<A>2 = f ` \<F> \<A>1"
    proof (intro set_eqI iffI)
      fix q2 
      assume "q2 \<in> f ` (\<F> \<A>1)"
      then obtain q1 where q1_in_F: "q1 \<in> \<F> \<A>1" and
                           q2_eq: "q2 = f q1" by auto

      from DFA1.\<F>_consistent q1_in_F 
      have q1_in_Q: "q1 \<in> \<Q> \<A>1" by blast

      from f_equiv[OF q1_in_Q] q2_eq q1_in_F
      show "q2 \<in> \<F> \<A>2"
      by (simp add: in_\<L>_in_state_Nil [symmetric]
               del: in_\<L>_in_state_Nil)
    next
      fix q2 
      assume q2_in_F: "q2 \<in> \<F> \<A>2"

      from DFA2.\<F>_consistent q2_in_F 
      have q2_in_Q: "q2 \<in> \<Q> \<A>2" by blast

      with bij_f obtain q1 where q1_in_Q: "q1 \<in> \<Q> \<A>1" and
                        q2_eq: "q2 = f q1" 
        unfolding bij_betw_def
        by auto

      from f_equiv[OF q1_in_Q] q2_eq q2_in_F
      have q1_in_F: "q1 \<in> \<F> \<A>1"
        by (simp add: in_\<L>_in_state_Nil [symmetric]
                 del: in_\<L>_in_state_Nil)
      
      show "q2 \<in> f ` (\<F> \<A>1)"
        unfolding q2_eq
        using q1_in_F
        by auto
    qed
  next
    show "\<Delta> \<A>2 = {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>1}"
    proof (intro set_eqI)
      fix q2aq2' :: "'q2 \<times> 'a \<times> 'q2"
      obtain q2 a q2' where q2aq2'_eq [simp]: "q2aq2' = (q2, a, q2')"
        by (cases q2aq2', blast)
 
      show "q2aq2' \<in> \<Delta> \<A>2 \<longleftrightarrow> q2aq2' \<in> {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>1}"
      proof (cases "q2 \<in> \<Q> \<A>2 \<and> a \<in> \<Sigma> \<A>2 \<and> q2' \<in> \<Q> \<A>2")
        case False note q2aq2'_not_wf = this

        from q2aq2'_not_wf have q2aq2'_nin_ls: "q2aq2' \<notin> \<Delta> \<A>2"
          using DFA2.\<Delta>_consistent
          by auto

        have q2aq2'_nin_rs: "q2aq2' \<notin> {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>1}"
        proof (rule notI)
           assume "q2aq2' \<in> {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>1}"
           then obtain q1 q1' where 
              q2_eq:  "q2 = f q1" and 
              q2'_eq: "q2' = f q1'" and
              q1aq1'_in: "(q1, a, q1') \<in> \<Delta> \<A>1"
              by auto
           with DFA1.\<Delta>_consistent f_is_state q2aq2'_not_wf \<Sigma>_eq
           show "False" by metis
        qed
        from q2aq2'_nin_rs q2aq2'_nin_ls show ?thesis by simp
      next
        case True
        hence q2_in: "q2 \<in> \<Q> \<A>2"
          and a_in2: "a \<in> \<Sigma> \<A>2"
          and q2'_in: "q2' \<in> \<Q> \<A>2"
        by simp_all
        from a_in2 \<Sigma>_eq have a_in1: "a \<in> \<Sigma> \<A>1" by fast

        from bij_f q2_in 
          obtain q1 where q1_in: "q1 \<in> \<Q> \<A>1"
                      and q2_eq: "q2 = f q1"
          unfolding bij_betw_def by auto

        from DFA1.DetSemiAutomaton_\<delta>_is_some [OF q1_in a_in1]
        obtain q1'' where \<delta>_q1a: "(\<delta> \<A>1) (q1, a) = Some q1''" by auto
        from DFA1.\<delta>_wf[OF \<delta>_q1a] have q1''_in: "q1'' \<in> \<Q> \<A>1" by fast
   
        from DFA2.DetSemiAutomaton_\<delta>_is_some [OF q2_in a_in2]
        obtain q2'' where \<delta>_q2a: "(\<delta> \<A>2) (q2, a) = Some q2''" by auto
        from DFA2.\<delta>_wf[OF \<delta>_q2a] have q2''_in: "q2'' \<in> \<Q> \<A>2" by fast

        from \<L>_in_state___DFA___eq_reachable_step [OF wf_A1 wf_A2, 
           of q1 a q1'' q2 q2'']  \<delta>_q1a  \<delta>_q2a f_equiv[OF q1_in]
        have q1''_q2''_equiv: "\<L>_in_state \<A>1 q1'' = \<L>_in_state \<A>2 q2''"
          by (simp add: q2_eq DFA1.\<delta>_in_\<Delta>_iff [symmetric] 
                        DFA2.\<delta>_in_\<Delta>_iff [symmetric])

        from q1''_q2''_equiv f_equiv[OF q1''_in]
        have "\<L>_in_state \<A>2 q2'' = \<L>_in_state \<A>2 (f q1'')" by simp
        hence q2''_eq: "q2'' = f q1''" 
          using min_A2 q2''_in f_is_state[OF q1''_in]
          unfolding DFA_is_minimal_alt_DFA_def inj_on_def
          by simp

        from DFA1.\<delta>_wf inj_f \<delta>_q1a
        have q2aq2'_in_rs_eq: "q2aq2' \<in> {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>1} \<longleftrightarrow> q2' = f q1''"
           unfolding inj_on_def
           by (simp add: q2_eq DFA1.\<delta>_in_\<Delta>_iff)
              (metis option.inject)
        show ?thesis
          unfolding q2aq2'_in_rs_eq
          by (simp add: q2''_eq DFA2.\<delta>_in_\<Delta>_iff \<delta>_q2a) blast
      qed
    qed
  qed

  from wf_A1 inj_f A2_eq
  show ?thesis
    unfolding NFA_isomorphic_wf_def NFA_isomorphic_def
    apply (simp add: DFA_alt_def)
    apply (rule exI [where x = f])
    apply simp
  done
qed


subsection\<open> Brzozowski's Algorithm \<close>

text \<open> Brzozowski's algorithm for minimisation applies powerset
  construction to the reverse and repeats this to obtain a minimal automaton. \<close>

definition Brzozowski_halfway
where "Brzozowski_halfway \<A> \<equiv> efficient_determinise_NFA (NFA_reverse \<A>)"

definition Brzozowski
where "Brzozowski \<A> \<equiv> Brzozowski_halfway (Brzozowski_halfway \<A>)"

lemma Brzozowski_halfway___well_formed :
  "NFA \<A> \<Longrightarrow> NFA (Brzozowski_halfway \<A>)"
unfolding Brzozowski_halfway_def efficient_determinise_NFA_def
by (metis determinise_NFA___is_well_formed NFA_reverse___is_well_formed
          NFA_remove_unreachable_states___is_well_formed)

lemma Brzozowski___well_formed :
  "NFA \<A> \<Longrightarrow> NFA (Brzozowski \<A>)"
unfolding Brzozowski_def 
by (metis Brzozowski_halfway___well_formed)

lemma Brzozowski_\<Sigma> [simp] :
  "\<Sigma> (Brzozowski \<A>) = \<Sigma> \<A>"
unfolding Brzozowski_def Brzozowski_halfway_def efficient_determinise_NFA_def
by simp

lemma Brzozowski_halfway_yields_DFA :
  assumes "NFA \<A>"
  shows "DFA (Brzozowski_halfway \<A>)"
unfolding DFA_alt_def 
using assms
by (simp add: Brzozowski_halfway___well_formed,
    simp add: SemiAutomaton_is_complete_deterministic___NFA_remove_unreachable_states
              efficient_determinise_NFA_def
              Brzozowski_halfway_def NFA_reverse___is_well_formed
              NFA.determinise_NFA_is_complete_determistic)

lemma Brzozowski_yields_DFA :
  assumes "NFA \<A>"
  shows "DFA (Brzozowski \<A>)"
unfolding Brzozowski_def
using assms
by (metis DFA_alt_def Brzozowski_halfway_yields_DFA)


lemma (in NFA) Brzozowski_halfway___\<L> :
  shows "\<L> (Brzozowski_halfway \<A>) = {rev w |w. w \<in> \<L> \<A>}"
using NFA_reverse___\<L> NFA.determinise_NFA_\<L> [OF NFA_reverse___is_well_formed [OF NFA_axioms]]
by (simp add: Brzozowski_halfway_def efficient_determinise_NFA_def)

text \<open> Finally we show that Brzozowski's algorithm preserves the language of the automaton. \<close>

theorem (in NFA) Brzozowski___\<L> :
  "\<L> (Brzozowski \<A>) = \<L> \<A>"
unfolding Brzozowski_def
using Brzozowski_halfway___\<L>
using NFA.Brzozowski_halfway___\<L> [OF Brzozowski_halfway___well_formed [OF NFA_axioms]]
by (simp add: set_eq_iff del: ex_simps add: ex_simps[symmetric])

theorem (in NFA) Brzozowski___NFA_accept :
  "NFA_accept (Brzozowski \<A>) w = NFA_accept \<A> w"
using Brzozowski___\<L> 
by (simp add: \<L>_def set_eq_iff)

lemma (in DFA) Brzozowski_halfway___minimal :
assumes connected: "SemiAutomaton_is_initially_connected \<A>"
shows "DFA_is_minimal (Brzozowski_halfway \<A>)"
proof -
  let ?BH = "Brzozowski_halfway \<A>"
  interpret DFA_BH: DFA ?BH 
    using Brzozowski_halfway_yields_DFA [OF NFA_axioms] .

  show "DFA_is_minimal ?BH"
  proof (rule DFA_BH.DFA_is_minimal_intro)
    show "SemiAutomaton_is_initially_connected ?BH"
      by (simp add: Brzozowski_halfway_def efficient_determinise_NFA_def 
                    SemiAutomaton_is_initially_connected___NFA_remove_unreachable_states)
  next
    let ?DR = "determinise_NFA (NFA_reverse \<A>)"

    have wf_reverse_A: "NFA (NFA_reverse \<A>)"
      using NFA_reverse___is_well_formed [OF NFA_axioms] .

    have "\<And>Q1 Q2. \<lbrakk>Q1 \<in> \<Q> ?DR; Q2 \<in> \<Q> ?DR;
                   \<L>_in_state ?DR Q1 = \<L>_in_state ?DR Q2\<rbrakk> \<Longrightarrow> (Q1 = Q2)"
    proof -
      fix Q1 Q2
      assume "Q1 \<in> \<Q> ?DR" hence Q1_Q : "Q1 \<subseteq> \<Q> \<A>" by simp
      assume "Q2 \<in> \<Q> ?DR" hence Q2_Q : "Q2 \<subseteq> \<Q> \<A>" by simp
      assume \<L>_eq : "\<L>_in_state ?DR Q1 = \<L>_in_state ?DR Q2"
 
      have \<L>_left_not_empty :
        "\<And>q. q \<in> Q1 \<union> Q2 \<Longrightarrow> \<exists>w. w \<in> \<L>_left \<A> q"
      proof -
        fix q
        assume "q \<in> Q1 \<union> Q2"
        with Q1_Q Q2_Q have "q \<in> \<Q> \<A>" by auto
        with connected have "q \<notin> SemiAutomaton_unreachable_states \<A>" unfolding SemiAutomaton_is_initially_connected_def by auto
        hence "\<L>_left \<A> q \<noteq> {}" by (simp add: NFA_unreachable_states_alt_def)
        thus "\<exists>w. w \<in> \<L>_left \<A> q"
          by (metis ex_in_conv)
      qed

      note DFA_left_languages___pairwise_disjoint
      with Q1_Q Q2_Q have \<L>_left_unique: "\<And>q1 q2 w. \<lbrakk>q1 \<in> Q1; q2 \<in> Q2; 
           w \<in> \<L>_left \<A> q1; w \<in> \<L>_left \<A> q2\<rbrakk> \<Longrightarrow> (q1 = q2)"
        by (simp add: set_eq_iff subset_iff, metis)
     
      obtain QQ where QQ_def: "QQ = (\<lambda>Q. \<Union>{{rev w |w. w \<in> \<L>_left \<A> q} |q. q \<in> Q})" by auto
      have QQ_in: "\<And>w Q. rev w \<in> QQ Q = (\<exists>q \<in> Q. w \<in> \<L>_left \<A> q)"
        by (auto simp add: QQ_def)

      note NFA.determinise_NFA___\<L>_in_state [OF wf_reverse_A]
      with Q1_Q Q2_Q \<L>_eq have "QQ Q1 = QQ Q2"
        by (simp add: NFA_reverse___\<L>_in_state QQ_def)
      hence "\<And>w. (rev w \<in> QQ Q1) = (rev w \<in> QQ Q2)" by simp
      hence "\<And>w. (\<exists>q \<in> Q1. w \<in> \<L>_left \<A> q) \<longleftrightarrow> (\<exists>q \<in> Q2. w \<in> \<L>_left \<A> q)" 
        by (simp add: QQ_in)
      with \<L>_left_unique \<L>_left_not_empty have "\<And>q. q \<in> Q1 \<longleftrightarrow> q \<in> Q2"
        by (simp, metis)
      thus "Q1 = Q2" by auto
    qed
    hence "\<And>q1 q2. \<lbrakk>q1 \<in> \<Q> ?BH; q2 \<in> \<Q> ?BH;
                   \<L>_in_state ?BH q1 = \<L>_in_state ?BH q2\<rbrakk> \<Longrightarrow> (q1 = q2)"
      apply (simp add: Brzozowski_halfway_def efficient_determinise_NFA_def)
      apply (simp add: NFA_remove_unreachable_states_def)
    done

    thus "inj_on (\<L>_in_state ?BH) (\<Q> ?BH)"
      by (simp add: inj_on_def)
  qed
qed

theorem (in NFA) Brzozowski___minimal :
 "DFA_is_minimal (Brzozowski \<A>)"
unfolding Brzozowski_def
proof (rule DFA.Brzozowski_halfway___minimal)
  let ?BH = "Brzozowski_halfway \<A>"

  show "DFA ?BH" 
    using Brzozowski_halfway_yields_DFA [OF NFA_axioms] .

  show "SemiAutomaton_is_initially_connected ?BH"
    by (simp add: Brzozowski_halfway_def efficient_determinise_NFA_def
                  SemiAutomaton_is_initially_connected___NFA_remove_unreachable_states)
qed

lemma NFA_isomorphic_Brzozowski_halfway :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (Brzozowski_halfway \<A>1) (Brzozowski_halfway \<A>2)"
proof -
  note equiv_1 = NFA_isomorphic_wf___NFA_reverse_cong [OF equiv]
  note equiv_2 = NFA_isomorphic_wf___NFA_determinise_cong [OF equiv_1]
  note equiv_3 = NFA_isomorphic_wf___NFA_remove_unreachable_states [OF equiv_2]
  thus ?thesis unfolding Brzozowski_halfway_def efficient_determinise_NFA_def .
qed

lemma NFA_isomorphic_Brzozowski :
assumes equiv: "NFA_isomorphic_wf \<A>1 \<A>2"
shows "NFA_isomorphic_wf (Brzozowski \<A>1) (Brzozowski \<A>2)"
proof -
  note equiv_1 = NFA_isomorphic_Brzozowski_halfway [OF equiv]
  note equiv_2 = NFA_isomorphic_Brzozowski_halfway [OF equiv_1]
  thus ?thesis unfolding Brzozowski_def .
qed


subsection \<open> Abstract Minimisation Function \<close>

text \<open> Above, it is shown that all minimal automata that accept the same language are
isomorphic. Let's use Brzozwski minisation and this property in order to define a
minisation function that is later used for specification. \<close>

consts NFA_minimise :: "('q::{automaton_states}, 'a, 'X) NFA_rec_scheme \<Rightarrow> ('q, 'a) NFA_rec"

specification (NFA_minimise) NFA_minimise_spec_aux: 
"\<forall>\<A>. NFA \<A> \<longrightarrow>    
   \<L>(NFA_minimise \<A>) = \<L> \<A> \<and>
   \<Sigma>(NFA_minimise \<A>) = \<Sigma> \<A> \<and>
   DFA_is_minimal (NFA_minimise \<A>)"
apply (rule exI [where x = "\<lambda>\<A>. NFA_normalise_states (Brzozowski \<A>)"])
apply (simp add: Brzozowski___well_formed NFA.Brzozowski___\<L>)
apply (metis Brzozowski___well_formed NFA.Brzozowski___minimal NFA_isomorphic_wf_D(3) 
          NFA_isomorphic_wf_normalise_states NFA_isomorphic___DFA_is_minimal)
done

lemma NFA_minimise_spec: 
  "NFA \<A> \<Longrightarrow> \<L>(NFA_minimise \<A>) = \<L> \<A>"
  "NFA \<A> \<Longrightarrow> \<Sigma>(NFA_minimise \<A>) = \<Sigma> \<A>"
  "NFA \<A> \<Longrightarrow> DFA_is_minimal (NFA_minimise \<A>)"
by (simp_all add: NFA_minimise_spec_aux)

lemma NFA_isomorphic_wf___minimise :
fixes \<A>1 :: "('q1::{automaton_states}, 'a, _) NFA_rec_scheme"
  and \<A>2 :: "('q2, 'a) NFA_rec"
assumes wf_\<A>1: "NFA \<A>1"
shows "NFA_isomorphic_wf \<A>2 (NFA_minimise \<A>1) \<longleftrightarrow>
       \<L> \<A>2 = \<L> \<A>1 \<and> \<Sigma> \<A>2 = \<Sigma> \<A>1 \<and> DFA_is_minimal \<A>2"
using NFA_minimise_spec[OF wf_\<A>1]
      DFA_is_minimal___isomorph_wf [of \<A>2 "NFA_minimise \<A>1"]
      NFA_isomorphic___DFA_is_minimal [of "NFA_minimise \<A>1" \<A>2]
by (simp, metis NFA_isomorphic_wf_D(4) NFA_isomorphic_wf_\<L> NFA_isomorphic_wf_\<Sigma>)


lemma NFA_isomorphic_wf___minimise_cong :
assumes pre: "NFA_isomorphic_wf \<A>1 \<A>2" 
shows "NFA_isomorphic_wf (NFA_minimise \<A>1) (NFA_minimise \<A>2)"
proof -
  from pre have "NFA \<A>1" "NFA \<A>2"
    by (simp_all add: NFA_isomorphic_wf_alt_def)

  from `NFA \<A>2` NFA_minimise_spec[OF `NFA \<A>1`] pre
  show ?thesis 
    by (simp add: NFA_isomorphic_wf___minimise NFA_isomorphic_wf_\<L> NFA_isomorphic_wf_\<Sigma>)
qed

lemma Brzozowski___minimise :
  "NFA \<A> \<Longrightarrow> NFA_isomorphic_wf (Brzozowski \<A>) (NFA_minimise \<A>)"
by (simp add: NFA_isomorphic_wf___minimise NFA.Brzozowski___\<L> NFA.Brzozowski___minimal)

end
