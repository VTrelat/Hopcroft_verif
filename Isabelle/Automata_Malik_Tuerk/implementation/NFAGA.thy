theory NFAGA
imports NFASpec
begin



subsection {* Construction hierarchie *}

lemma nfa_dfa_construct_default :
assumes label_set_OK: "nfa_dfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar (\<lambda>x. {x}) (\<lambda>_. True) construct"
shows "nfa_dfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar construct"
proof (intro nfa_dfa_construct.intro nfa_dfa_construct_axioms.intro)
  from label_set_OK show "nfa \<alpha> invar" unfolding nfa_dfa_construct_label_sets_def by simp
next
  case goal2 note assms = this
  note label_set_rule = nfa_dfa_construct_label_sets.nfa_dfa_construct_label_sets_correct[OF label_set_OK,
     where DS_q = "\<lambda>q. {({a}, q') | a q'. (q, a, q') \<in> \<Delta> \<A>}"]
  note label_set_rule' = label_set_rule [of \<A> det f ff I A FP D_it, OF assms(1-9)]

  show ?case
  proof (rule label_set_rule')
    fix q
    assume pre: "q2_invar q" "q2_\<alpha> q \<in> \<Q> \<A>"

    from assms(10)[OF pre] show "FP q = (q2_\<alpha> q \<in> \<F> \<A>)" by simp

    from assms(11)[OF pre]
    obtain lc where lc_props: "\<forall>(a, y)\<in>set lc. q2_invar y"
         "distinct (map (\<lambda>(a, q'). (a, q2_\<alpha> q')) lc)"
         "{(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>} = (\<lambda>(a, q'). (a, q2_\<alpha> q')) ` set lc"
         "D_it q = foldli lc"
      by (auto simp add: set_iterator_abs_def set_iterator_abs_genord_def)
    show "set_iterator_abs (\<lambda>(as, q). ({as}, q2_\<alpha> q))
           (\<lambda>(as, q). True \<and> q2_invar q) (D_it q)
           {({a}, q') |a q'. (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}" 
      unfolding set_iterator_abs_def set_iterator_abs_genord_def
      proof (rule_tac exI [where x = lc], intro conjI)
        from lc_props(2)
        show "distinct (map (\<lambda>(as, q). ({as}, q2_\<alpha> q)) lc)"
          by (simp add: distinct_map inj_on_def Ball_def)
      next
        from lc_props(3)
        show "{({a}, q') |a q'. (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>} =
              set (map (\<lambda>(as, q). ({as}, q2_\<alpha> q)) lc)"
          unfolding set_eq_iff
          apply (simp add: image_iff Bex_def del: ex_simps add: ex_simps[symmetric])
          apply metis
        done
    qed (simp_all add: lc_props)
  qed auto
qed

lemma nfa_construct_default :
assumes label_set_OK: "nfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar (\<lambda>x. {x}) (\<lambda>_. True) construct"
shows "nfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar construct"
proof (intro nfa_construct.intro nfa_construct_axioms.intro)
  from label_set_OK show "nfa \<alpha> invar" unfolding nfa_construct_label_sets_def by simp
next
  case goal2 note assms = this
  note label_set_rule = nfa_construct_label_sets.nfa_construct_label_sets_correct[OF label_set_OK,
     where DS_q = "\<lambda>q. {({a}, q') | a q'. (q, a, q') \<in> \<Delta> \<A>}"]
  note label_set_rule' = label_set_rule [of \<A> f ff I A FP D_it, OF assms(1-9)]

  show ?case
  proof (rule label_set_rule')
    fix q
    assume "q2_invar q" "q2_\<alpha> q \<in> \<Q> \<A>"

    from assms(10)[OF this]
    obtain lc where lc_props: "\<forall>(a, y)\<in>set lc. q2_invar y"
         "distinct (map (\<lambda>(a, q'). (a, q2_\<alpha> q')) lc)"
         "{(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>} = (\<lambda>(a, q'). (a, q2_\<alpha> q')) ` set lc"
         "D_it q = foldli lc"
      by (auto simp add: set_iterator_abs_def set_iterator_abs_genord_def)
    show "set_iterator_abs (\<lambda>(as, q). ({as}, q2_\<alpha> q))
           (\<lambda>(as, q). True \<and> q2_invar q) (D_it q)
           {({a}, q') |a q'. (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}" 
      unfolding set_iterator_abs_def set_iterator_abs_genord_def
      proof (rule_tac exI [where x = lc], intro conjI)
        from lc_props(2)
        show "distinct (map (\<lambda>(as, q). ({as}, q2_\<alpha> q)) lc)"
          by (simp add: distinct_map inj_on_def Ball_def)
      next
        from lc_props(3)
        show "{({a}, q') |a q'. (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>} =
              set (map (\<lambda>(as, q). ({as}, q2_\<alpha> q)) lc)"
          unfolding set_eq_iff
          apply (simp add: image_iff Bex_def del: ex_simps add: ex_simps[symmetric])
          apply metis
        done
    qed (simp_all add: lc_props)
  qed auto
qed

lemma dfa_construct_default :
assumes label_set_OK: "dfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar (\<lambda>x. {x}) (\<lambda>_. True) construct"
shows "dfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar construct"
proof (intro dfa_construct.intro dfa_construct_axioms.intro)
  from label_set_OK show "nfa \<alpha> invar" unfolding dfa_construct_label_sets_def by simp
next
  case goal2 note assms = this
  note label_set_rule = dfa_construct_label_sets.dfa_construct_label_sets_correct[OF label_set_OK,
     where DS_q = "\<lambda>q. {({a}, q') | a q'. (q, a, q') \<in> \<Delta> \<A>}"]
  note label_set_rule' = label_set_rule [of \<A> f ff I A FP D_it, OF assms(1-9)]

  show ?case
  proof (rule label_set_rule')
    fix q
    assume "q2_invar q" "q2_\<alpha> q \<in> \<Q> \<A>"

    from assms(10)[OF this]
    obtain lc where lc_props: "\<forall>(a, y)\<in>set lc. q2_invar y"
         "distinct (map (\<lambda>(a, q'). (a, q2_\<alpha> q')) lc)"
         "{(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>} = (\<lambda>(a, q'). (a, q2_\<alpha> q')) ` set lc"
         "D_it q = foldli lc"
      by (auto simp add: set_iterator_abs_def set_iterator_abs_genord_def)
    show "set_iterator_abs (\<lambda>(as, q). ({as}, q2_\<alpha> q))
           (\<lambda>(as, q). True \<and> q2_invar q) (D_it q)
           {({a}, q') |a q'. (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}" 
      unfolding set_iterator_abs_def set_iterator_abs_genord_def
      proof (rule_tac exI [where x = lc], intro conjI)
        from lc_props(2)
        show "distinct (map (\<lambda>(as, q). ({as}, q2_\<alpha> q)) lc)"
          by (simp add: distinct_map inj_on_def Ball_def)
      next
        from lc_props(3)
        show "{({a}, q') |a q'. (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>} =
              set (map (\<lambda>(as, q). ({as}, q2_\<alpha> q)) lc)"
          unfolding set_eq_iff
          apply (simp add: image_iff Bex_def del: ex_simps add: ex_simps[symmetric])
          apply metis
        done
    qed (simp_all add: lc_props)
  qed auto
qed

lemma nfa_dfa_construct_no_enc_default :
  "nfa_dfa_construct \<alpha> invar \<alpha>_s invar_s id (\<lambda>_. True) construct \<Longrightarrow>
   nfa_dfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s construct"
by (simp add: nfa_dfa_construct_def nfa_dfa_construct_no_enc_def nfa_dfa_construct_no_enc_axioms_def
                nfa_dfa_construct_axioms_def)

lemma nfa_construct_no_enc_default :
  "nfa_construct \<alpha> invar \<alpha>_s invar_s id (\<lambda>_. True) construct \<Longrightarrow>
   nfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s construct"
by (simp add: nfa_construct_def nfa_construct_no_enc_def nfa_construct_no_enc_axioms_def
                nfa_construct_axioms_def)

lemma dfa_construct_no_enc_default :
  "dfa_construct \<alpha> invar \<alpha>_s invar_s id (\<lambda>_. True) construct \<Longrightarrow>
   dfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s construct"
 by (simp add: dfa_construct_def dfa_construct_no_enc_def dfa_construct_no_enc_axioms_def
               dfa_construct_axioms_def)
   
lemma dfa_construct_no_enc_fun_default :
  "dfa_construct_fun \<alpha> invar \<alpha>_s invar_s id (\<lambda>_. True) construct \<Longrightarrow>
   dfa_construct_no_enc_fun \<alpha> invar \<alpha>_s invar_s construct"
  by (simp add: dfa_construct_fun_def dfa_construct_no_enc_fun_def 
                dfa_construct_no_enc_fun_axioms_def
                dfa_construct_fun_axioms_def)


subsection {* Construct with functions *}

definition construct_by_fun ::
  "('q2_rep,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct \<Rightarrow>
   ('a_set \<Rightarrow> ('a,'\<sigma>) set_iterator) \<Rightarrow> 
   ('q2_rep,'i,'a,'a_set,'nfa) nfa_construct_fun" where
  "construct_by_fun const it_A ff I A FP D_fun =
   const ff [I] A FP 
   (\<lambda>q. set_iterator_image (\<lambda>a. (a, D_fun q a)) (it_A A))"

lemma construct_by_fun_alt_def :
  "construct_by_fun const it_A ff I A FP D_fun =
   const ff [I] A FP (\<lambda>q c f. it_A A c (\<lambda>x. f (x, D_fun q x)))"
   unfolding construct_by_fun_def[abs_def] set_iterator_image_alt_def 
by simp

lemma construct_by_fun_correct :
fixes const :: "('q2_rep,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct"
  and \<alpha> :: "'nfa \<Rightarrow> ('q, 'a) NFA_rec" 
  and q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2"
assumes const_OK: "dfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar const"
    and it_A: "set_iteratei \<alpha>_s invar_s it_A"
shows "dfa_construct_fun \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar (construct_by_fun const it_A)"
proof (intro dfa_construct_fun.intro dfa_construct_fun_axioms.intro)
  from const_OK show "nfa \<alpha> invar" unfolding dfa_construct_def by simp

  fix \<A> :: "('q2, 'a) NFA_rec" and 
      f :: "'q2 \<Rightarrow> 'i" and ff I A FP D_fun
  assume wf_A: "DFA \<A>"
     and inj_f: "inj_on f (\<Q> \<A>)"
     and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = f (q2_\<alpha> q)"
     and invar_I: "q2_invar I"
     and I_in: "q2_\<alpha> I \<in> \<I> \<A>"
     and invar_A: "invar_s A"
     and A_OK: "\<alpha>_s A = \<Sigma> \<A>"
     and FP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> FP q = (q2_\<alpha> q \<in> \<F> \<A>)"
     and D_fun_OK: "\<And>q a. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> a \<in> \<Sigma> \<A> \<Longrightarrow> 
                (q2_\<alpha> q, a, q2_\<alpha> (D_fun q a)) \<in> \<Delta> \<A> \<and> q2_invar (D_fun q a)"

  interpret DFA \<A> by fact
  note const_rule = dfa_construct.dfa_construct_correct [OF const_OK wf_A inj_f, of ff "[I]",
        OF ff_OK _ _ _ invar_A A_OK FP_OK]

  show "invar (construct_by_fun const it_A ff I A FP D_fun) \<and>
       NFA_isomorphic_wf (\<alpha> (construct_by_fun const it_A ff I A FP D_fun)) (NFA_remove_unreachable_states \<A>)" 
    unfolding construct_by_fun_def
  proof (rule const_rule)
    from I_in \<I>_is_set_\<i> show "q2_\<alpha> ` set [I] = \<I> \<A>" by auto
  next
    fix q
    assume invar_q: "q2_invar q" and q_in_Q: "q2_\<alpha> q \<in> \<Q> \<A>"
    
    with D_fun_OK[of q] have 
      D_fun_in_D: "\<And>a. a \<in> \<Sigma> \<A> \<Longrightarrow> (q2_\<alpha> q, a, q2_\<alpha> (D_fun q a)) \<in> \<Delta> \<A>" and
      D_fun_invar: "\<And>a. a \<in> \<Sigma> \<A> \<Longrightarrow> q2_invar (D_fun q a)" by simp_all

    let ?DS_q = "{(a,  D_fun q a) |a. a \<in> \<Sigma> \<A>}"

    from set_iteratei.iteratei_rule[OF it_A, OF invar_A] have 
      it_A_OK': "set_iterator (it_A A) (\<alpha>_s A)" .

    from set_iterator_image_correct [OF it_A_OK', of "\<lambda>a. (a, D_fun q a)"]
    have "set_iterator (set_iterator_image (\<lambda>a. (a, D_fun q a)) (it_A A))
           ((\<lambda>a. (a, D_fun q a)) ` \<alpha>_s A)" by (simp add: inj_on_def)
    moreover have "((\<lambda>a. (a, D_fun q a)) ` \<alpha>_s A) = {(a,  D_fun q a) |a. a \<in> \<Sigma> \<A>}" 
      unfolding A_OK by auto
    ultimately have it_OK: 
        "set_iterator (set_iterator_image (\<lambda>a. (a, D_fun q a)) (it_A A)) ?DS_q"
        by simp

    show "set_iterator_abs (\<lambda>(a, q'). (a, q2_\<alpha> q'))
         (\<lambda>(a, q'). q2_invar q')
         (set_iterator_image (\<lambda>a. (a, D_fun q a)) (it_A A))
         {(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}" 
      apply (rule set_iterator_abs_I2)
      apply (rule it_OK)
      apply (auto simp add: it_OK D_fun_invar image_iff D_fun_in_D \<Delta>_consistent)
      apply (metis D_fun_in_D \<Delta>_consistent LTS_is_deterministic_def deterministic_LTS)
    done
  qed (simp_all add: invar_I)
qed


subsection{* Brzozowski *}

definition Brzozowski_impl :: "('nfa \<Rightarrow> 'nfa) \<Rightarrow> ('nfa \<Rightarrow> 'nfa) \<Rightarrow> 'nfa \<Rightarrow> 'nfa" where
  "Brzozowski_impl r d A = d (r (d (r A)))"

lemma Brzozowski_impl_correct :
assumes r_OK: "nfa_reverse \<alpha> invar \<alpha> invar r"
    and d_OK: "nfa_determinise \<alpha> invar \<alpha> invar d"
shows "nfa_minimise \<alpha> invar \<alpha> invar (Brzozowski_impl r d)"
unfolding Brzozowski_impl_def[abs_def]
proof (intro nfa_minimise.intro nfa_minimise_axioms.intro conjI)
  from r_OK show nfa_OK: "nfa \<alpha> invar" and "nfa \<alpha> invar" unfolding nfa_reverse_def by simp_all

  note nfa_correct = nfa.nfa_is_wellformed [OF nfa_OK]
  note r_correct = nfa_reverse.reverse_correct___isomorphic [OF r_OK]
  note d_correct = nfa_determinise.determinise_correct___isomorphic [OF d_OK]

  fix n
  assume invar_n: "invar n"
  hence wf_n: "NFA (\<alpha> n)" by (simp add: nfa_correct)

  show "invar (d (r (d (r n))))"
    by (intro d_correct(1) r_correct(1) invar_n)

  have "NFA_isomorphic_wf (\<alpha> (d (r (d (r n))))) (Brzozowski (\<alpha> n))"
    unfolding Brzozowski_def Brzozowski_halfway_def
    by (intro d_correct r_correct invar_n NFA_isomorphic_wf_refl wf_n)
  with Brzozowski___minimise[OF wf_n]
  show "NFA_isomorphic_wf (\<alpha> (d (r (d (r n))))) (NFA_minimise (\<alpha> n))"
    by (metis NFA_isomorphic_wf_trans)
qed



subsection{* Minimisation combined with determinisation *}

lemma NFAGA_minimisation_with_determinisation :
fixes \<alpha>1::"'nfa1 \<Rightarrow> ('q1::{automaton_states}, 'a) NFA_rec"
  and \<alpha>2::"'nfa2 \<Rightarrow> ('q2::{automaton_states}, 'a) NFA_rec"
  and \<alpha>3::"'nfa3 \<Rightarrow> ('q3, 'a) NFA_rec"
assumes d_OK: "nfa_determinise \<alpha>1 invar1 \<alpha>2 invar2 d"
    and m_OK: "dfa_minimise \<alpha>2 invar2 \<alpha>3 invar3 m"
shows "nfa_minimise \<alpha>1 invar1 \<alpha>3 invar3 (m \<circ> d)"
proof (intro nfa_minimise.intro nfa_minimise_axioms.intro conjI)
  from d_OK show nfa1_OK: "nfa \<alpha>1 invar1" unfolding nfa_determinise_def by simp
  from m_OK show "nfa \<alpha>3 invar3" unfolding dfa_minimise_def by simp

  fix a
  assume invar_a: "invar1 a"

  from nfa1_OK invar_a have NFA_a: "NFA (\<alpha>1 a)" unfolding nfa_def by simp

  let ?da = "NFA_determinise (\<alpha>1 a)"

  from nfa_determinise.determinise_correct___same [OF d_OK, OF invar_a]
  have invar_da: "invar2 (d a)" and
       iso_da: "NFA_isomorphic_wf (\<alpha>2 (d a)) ?da"
    by (simp_all add: NFA_isomorphic_wf___NFA_normalise_states_cong)

  have DFA_da : "DFA ?da" by (simp add: NFA_determinise_is_DFA NFA_a)
  have con_da: "SemiAutomaton_is_initially_connected ?da"
    unfolding NFA_determinise_def
    by (intro SemiAutomaton_is_initially_connected___normalise_states
              efficient_determinise_NFA___is_initially_connected)
 
  from dfa_minimise.dfa_minimise_correct___isomorphic 
         [OF m_OK, OF invar_da, OF DFA_da con_da iso_da]
  have invar_mda: "invar3 ((m \<circ> d) a)" and
       iso_mda: "NFA_isomorphic_wf (\<alpha>3 ((m \<circ> d) a)) (NFA_minimise ?da)" 
    by simp_all

  from invar_mda show "invar3 ((m \<circ> d) a)" .

  from iso_mda NFA_a DFA_da DFA_implies_NFA[OF DFA_da]
  show "NFA_isomorphic_wf (\<alpha>3 ((m \<circ> d) a)) (NFA_minimise (\<alpha>1 a))"
    by (simp add: NFA_isomorphic_wf___minimise DFA_alt_def 
                  NFA_determinise_\<L>)
qed


subsection{* Language Operations *}

definition NFAGA_language_is_univ :: "('nfa \<Rightarrow> 'nfa) \<Rightarrow> ('nfa \<Rightarrow> 'nfa) \<Rightarrow> ('nfa \<Rightarrow> bool) \<Rightarrow> 'nfa \<Rightarrow> bool" where
  "NFAGA_language_is_univ d c is_emp A =  is_emp (c (d A))"

lemma NFAGA_language_is_univ_correct :
assumes c_OK: "nfa_complement \<alpha> invar c"
    and d_OK: "nfa_determinise \<alpha> invar \<alpha> invar d"
    and is_emp_OK: "nfa_language_is_empty \<alpha> invar is_emp"
shows "nfa_language_is_univ \<alpha> invar (NFAGA_language_is_univ d c is_emp)"
proof (intro nfa_language_is_univ.intro nfa_language_is_univ_axioms.intro)
  from c_OK show nfa_OK: "nfa \<alpha> invar" unfolding nfa_complement_def by simp_all

  fix n
  assume invar_n: "invar n"

  from invar_n nfa_OK have NFA_n: "NFA (\<alpha> n)" 
    unfolding nfa_def by simp

  from nfa_determinise.determinise_correct___same[OF d_OK, OF invar_n]
  have invar_dn: "invar (d n)" and
       iso_dn: "NFA_isomorphic_wf (\<alpha> (d n)) (NFA_determinise (\<alpha> n))" by simp_all
 
  from nfa_complement.complement_correct___isomorphic[OF c_OK, OF invar_dn] iso_dn
  have invar_cdn: "invar (c (d n))" and
       iso_cdn: "NFA_isomorphic_wf (\<alpha> (c (d n))) (DFA_complement (NFA_determinise (\<alpha> n)))" by simp_all

  from nfa_language_is_empty.language_is_empty_correct [OF is_emp_OK, OF invar_cdn]
  have emp_eq: "is_emp (c (d n)) = (\<L> (\<alpha> (c (d n))) = {})" by simp

  from iso_cdn have "\<L> (\<alpha> (c (d n))) = \<L> (DFA_complement (NFA_determinise (\<alpha> n)))"
    by (metis NFA_isomorphic_wf_\<L>)
  hence L_cdn_eq: "\<L> (\<alpha> (c (d n))) = lists (\<Sigma> (\<alpha> n)) - \<L> (\<alpha> n)"
    using  DFA.DFA_complement_\<L>[OF NFA_determinise_is_DFA[OF NFA_n]]
           NFA_determinise_\<L>[OF NFA_n]
    by simp

   have L_n_subset: "\<L> (\<alpha> n) \<subseteq> lists (\<Sigma> (\<alpha> n))"
     using NFA.NFA_\<L>___lists_\<Sigma>[OF NFA_n] by simp

  show "NFAGA_language_is_univ d c is_emp n =
        (\<L> (\<alpha> n) = lists (\<Sigma> (\<alpha> n)))" 
    unfolding NFAGA_language_is_univ_def emp_eq L_cdn_eq
    using L_n_subset by auto
qed


definition NFAGA_language_is_subset :: "('nfa \<Rightarrow> 'nfa) \<Rightarrow> ('nfa \<Rightarrow> 'nfa) \<Rightarrow> ('nfa \<Rightarrow> 'nfa \<Rightarrow> 'nfa) \<Rightarrow> ('nfa \<Rightarrow> bool) \<Rightarrow> 'nfa \<Rightarrow> 'nfa \<Rightarrow> bool" where
  "NFAGA_language_is_subset d c p is_emp A1 A2 = 
   is_emp (p A1 (c (d A2)))"

lemma NFAGA_language_is_subset_correct :
assumes c_OK: "nfa_complement \<alpha> invar c"
    and d_OK: "nfa_determinise \<alpha> invar \<alpha> invar d"
    and bc_OK: "nfa_bool_comb_same \<alpha> invar bc"
    and is_emp_OK: "nfa_language_is_empty \<alpha> invar is_emp"
shows "nfa_language_is_subset \<alpha> invar (NFAGA_language_is_subset d c (bc (op \<and>)) is_emp)"
proof (intro nfa_language_is_subset.intro nfa_language_is_subset_axioms.intro)
  from c_OK show nfa_OK: "nfa \<alpha> invar" unfolding nfa_complement_def by simp_all

  fix n1 n2
  assume invar_n1: "invar n1"
     and invar_n2: "invar n2"
     and \<Sigma>_eq: "\<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2)"

  from invar_n1 nfa_OK have NFA_n1: "NFA (\<alpha> n1)" 
    unfolding nfa_def by simp

  from invar_n2 nfa_OK have NFA_n2: "NFA (\<alpha> n2)" 
    unfolding nfa_def by simp

  from nfa_determinise.determinise_correct___same[OF d_OK, OF invar_n2]
  have invar_dn2: "invar (d n2)" and
       iso_dn: "NFA_isomorphic_wf (\<alpha> (d n2)) (NFA_determinise (\<alpha> n2))" by simp_all
 
  from nfa_complement.complement_correct___isomorphic[OF c_OK, OF invar_dn2] iso_dn
  have invar_cdn2: "invar (c (d n2))" and
       iso_cdn2: "NFA_isomorphic_wf (\<alpha> (c (d n2))) (DFA_complement (NFA_determinise (\<alpha> n2)))" by simp_all

  have \<Sigma>_eq': "\<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> (c (d n2)))"
    using NFA_isomorphic_wf_\<Sigma>[OF iso_cdn2] \<Sigma>_eq
    by simp

  note bc_props_aux = nfa_bool_comb_same.bool_comb_correct___same_isomorphic[OF bc_OK, OF invar_n1 invar_cdn2 \<Sigma>_eq',
    where ?bc = "op \<and>"]

  from bc_props_aux(1) bc_props_aux(2)[OF NFA_isomorphic_wf_refl[OF NFA_n1] iso_cdn2]
  have invar_res: "invar (bc op \<and> n1 (c (d n2)))"
   and iso_res: "NFA_isomorphic_wf (\<alpha> (bc op \<and> n1 (c (d n2))))
     (NFA_product (\<alpha> n1) (DFA_complement (NFA_determinise (\<alpha> n2))))"
        unfolding NFA_product_def by simp_all

  have L_cdn2_eq: "\<L> (DFA_complement (NFA_determinise (\<alpha> n2))) = lists (\<Sigma> (\<alpha> n2)) - \<L> (\<alpha> n2)"
    using  DFA.DFA_complement_\<L>[OF NFA_determinise_is_DFA[OF NFA_n2]]
           NFA_determinise_\<L>[OF NFA_n2]
    by simp

  from iso_cdn2 have NFA_cdn2: "NFA (DFA_complement (NFA_determinise (\<alpha> n2)))"
    unfolding NFA_isomorphic_wf_alt_def by simp

  have "\<L> (\<alpha> (bc op \<and> n1 (c (d n2)))) = \<L> (NFA_product (\<alpha> n1) (DFA_complement (NFA_determinise (\<alpha> n2))))"
    using NFA_isomorphic_wf_\<L>[OF iso_res] .
  with NFA_product_\<L> [OF NFA_n1 NFA_cdn2] L_cdn2_eq
  have L_res_eq: "\<L> (\<alpha> (bc op \<and> n1 (c (d n2)))) = \<L> (\<alpha> n1) \<inter> (lists (\<Sigma> (\<alpha> n2)) - \<L> (\<alpha> n2))" by simp
 
  from nfa_language_is_empty.language_is_empty_correct [OF is_emp_OK, OF invar_res]
  have emp_eq: "is_emp (bc op \<and> n1 (c (d n2))) = (\<L> (\<alpha> (bc op \<and> n1 (c (d n2)))) = {})" by simp

  have L_n1_subset: "\<L> (\<alpha> n1) \<subseteq> lists (\<Sigma> (\<alpha> n1))"
     using NFA.NFA_\<L>___lists_\<Sigma>[OF NFA_n1] by simp
  have L_n2_subset: "\<L> (\<alpha> n2) \<subseteq> lists (\<Sigma> (\<alpha> n2))"
     using NFA.NFA_\<L>___lists_\<Sigma>[OF NFA_n2] by simp

  show "NFAGA_language_is_subset d c (bc op \<and>) is_emp n1 n2 =
       (\<L> (\<alpha> n1) \<subseteq> \<L> (\<alpha> n2))" 
    using L_n2_subset L_n1_subset
    unfolding NFAGA_language_is_subset_def emp_eq L_res_eq \<Sigma>_eq
    by auto
qed

definition NFAGA_language_is_eq :: "('nfa \<Rightarrow> 'nfa \<Rightarrow> bool) \<Rightarrow> 'nfa \<Rightarrow> 'nfa \<Rightarrow> bool" where
  "NFAGA_language_is_eq is_sub A1 A2 = (is_sub A1 A2 \<and> is_sub A2 A1)"

lemma NFAGA_language_is_eq_correct :
assumes is_sub_OK: "nfa_language_is_subset \<alpha> invar is_sub"
shows "nfa_language_is_eq \<alpha> invar (NFAGA_language_is_eq is_sub)"
using assms
unfolding nfa_language_is_subset_def nfa_language_is_subset_axioms_def
          nfa_language_is_eq_def nfa_language_is_eq_axioms_def
          NFAGA_language_is_eq_def by auto

end
