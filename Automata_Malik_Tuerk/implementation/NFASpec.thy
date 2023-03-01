*** TODO: Port to new Collection Framework
header "Interface for NFAs and DFAs"
theory NFASpec
imports Main "../../Collections/ICF/Collections"
  "../../Collections/Iterator/SetAbstractionIterator"
  "../NFA" "../DFA"

begin
  type_synonym ('q,'a,'nfa) nfa_\<alpha> = "'nfa \<Rightarrow> ('q, 'a) NFA_rec"
  locale nfa =
    fixes \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes invar :: "'nfa \<Rightarrow> bool"
    assumes nfa_is_wellformed: "invar n \<Longrightarrow> NFA (\<alpha> n)"

  locale dfa =
    fixes \<alpha> :: "('q,'a,'dfa) nfa_\<alpha>"
    fixes invar :: "'dfa \<Rightarrow> bool"
    assumes dfa_is_wellformed: "invar n \<Longrightarrow> DFA (\<alpha> n)"

  type_synonym ('q,'a,'nfa) nfa_from_list = 
    "('q list \<times> 'a list \<times> ('q \<times> 'a list \<times> 'q) list \<times> 'q list \<times> 'q list) \<Rightarrow> 'nfa"
  locale nfa_from_list = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes from_list :: "('q,'a,'nfa) nfa_from_list"
    assumes nfa_from_list_correct:
      "invar (from_list l)"
      "\<alpha> (from_list l) = NFA_construct l"
  begin
    lemma nfa_from_list_correct___isomorphic :
      "invar (from_list l)"
      "NFA_isomorphic_wf (\<alpha> (from_list l)) (NFA_construct l)"
    by (simp_all add: nfa_from_list_correct NFA_isomorphic_wf_def NFA_isomorphic_refl
                      NFA_construct___is_well_formed)
  end

  locale dfa_from_list = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes from_list :: "('q,'a,'nfa) nfa_from_list"
    assumes dfa_from_list_correct:
      "DFA (NFA_construct l) \<Longrightarrow> invar (from_list l)"
      "DFA (NFA_construct l) \<Longrightarrow> \<alpha> (from_list l) = NFA_construct l"
  begin
    lemma dfa_from_list_correct___isomorphic :
      "DFA (NFA_construct l) \<Longrightarrow> invar (from_list l)"
      "DFA (NFA_construct l) \<Longrightarrow> NFA_isomorphic_wf (\<alpha> (from_list l)) (NFA_construct l)"
    by (simp_all add: dfa_from_list_correct NFA_isomorphic_wf_def NFA_isomorphic_refl
                      NFA_construct___is_well_formed)
  end

  type_synonym ('q,'a,'nfa) nfa_to_list = 
    "'nfa \<Rightarrow> ('q list \<times> 'a list \<times> ('q \<times> 'a list \<times> 'q) list \<times> 'q list \<times> 'q list)"
  locale nfa_to_list = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes to_list :: "('q,'a,'nfa) nfa_to_list"
    assumes to_list_correct:
      "invar n \<Longrightarrow> NFA_construct (to_list n) = \<alpha> n"
  begin
    lemma to_list_correct___isomorphic :
      "invar n \<Longrightarrow>  NFA_isomorphic_wf (\<alpha> n) (NFA_construct (to_list n))"
    using to_list_correct[of n]
      apply (simp add: NFA_isomorphic_wf_def NFA_isomorphic_refl)
      apply (metis NFA_construct___is_well_formed)
    done
  end

  type_synonym ('q,'a,'nfa) nfa_to_list_simple = 
    "'nfa \<Rightarrow> ('q list \<times> 'a list \<times> ('q \<times> 'a \<times> 'q) list \<times> 'q list \<times> 'q list)"
  locale nfa_to_list_simple = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes to_list_simple :: "('q,'a,'nfa) nfa_to_list_simple"
    assumes to_list_simple_correct:
      "invar n \<Longrightarrow> NFA_construct_simple (to_list_simple n) = \<alpha> n"
  begin
    lemma to_list_simple_correct___isomorphic :
      "invar n \<Longrightarrow>  NFA_isomorphic_wf (\<alpha> n) (NFA_construct_simple (to_list_simple n))"
    using to_list_simple_correct[of n]
      apply (cases "to_list_simple n")
      apply (simp add: NFA_isomorphic_wf_def NFA_isomorphic_refl)
      apply (metis NFA_construct___is_well_formed)
    done
  end

  locale nfa_stats = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes states_no :: "'nfa \<Rightarrow> nat"
    fixes labels_no :: "'nfa \<Rightarrow> nat"
    fixes trans_no :: "'nfa \<Rightarrow> nat"
    fixes initial_no :: "'nfa \<Rightarrow> nat"
    fixes final_no :: "'nfa \<Rightarrow> nat"
    assumes stats_correct:
      "invar n \<Longrightarrow> states_no n = card (\<Q> (\<alpha> n))"
      "invar n \<Longrightarrow> labels_no n = card (\<Sigma> (\<alpha> n))"
      "invar n \<Longrightarrow> trans_no n = card (\<Delta> (\<alpha> n))"
      "invar n \<Longrightarrow> initial_no n = card (\<I> (\<alpha> n))"
      "invar n \<Longrightarrow> final_no n = card (\<F> (\<alpha> n))"
  begin
    lemma stats_correct___isomorphic :
    fixes \<A> :: "('q2, 'a, _) NFA_rec_scheme"
    shows
      "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> n) \<A> \<Longrightarrow> states_no n = card (\<Q> \<A>)"
      "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> n) \<A> \<Longrightarrow> labels_no n = card (\<Sigma> \<A>)"
      "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> n) \<A> \<Longrightarrow> trans_no n = card (\<Delta> \<A>)"
      "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> n) \<A> \<Longrightarrow> initial_no n = card (\<I> \<A>)"
      "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> n) \<A> \<Longrightarrow> final_no n = card (\<F> \<A>)"
    proof -
      fix n and \<A>:: "('q2, 'a, _) NFA_rec_scheme"
      assume invar_n: "invar n" and iso_\<A>: "NFA_isomorphic_wf (\<alpha> n) \<A>"

      note [simp] = stats_correct [OF invar_n]
      from iso_\<A> obtain f where inj_f: "inj_on f (\<Q> (\<alpha> n))"
                            and \<A>_eq[simp]: "\<A> = NFA_rename_states (\<alpha> n) f"
                            and wf: "NFA (\<alpha> n)"
        unfolding NFA_isomorphic_wf_def NFA_isomorphic_def by blast

      from wf have wf': "SemiAutomaton (\<alpha> n)" unfolding NFA_alt_def FinSemiAutomaton_def by simp

      show "states_no n = card (\<Q> \<A>)" by (simp add: card_image inj_f)
      show "labels_no n = card (\<Sigma> \<A>)" by simp

      from wf' [THEN SemiAutomaton.\<I>_consistent, THEN subset_inj_on[OF inj_f]]
      show "initial_no n = card (\<I> \<A>)" by (simp add: card_image inj_f)

      from wf [THEN NFA.\<F>_consistent, THEN subset_inj_on[OF inj_f]]
      show "final_no n = card (\<F> \<A>)" by (simp add: card_image inj_f)

      show "trans_no n = card (\<Delta> \<A>)" 
      proof -
        have "{(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> (\<alpha> n)} =
              (\<lambda>(s1, a, s2). (f s1, a, f s2)) ` (\<Delta> (\<alpha> n))" 
          by (auto simp add: image_iff Bex_def, metis)
        moreover
          have "inj_on (\<lambda>(s1, a, s2). (f s1, a, f s2)) (\<Delta> (\<alpha> n))"
            using inj_f wf'[THEN SemiAutomaton.\<Delta>_consistent]
            by (simp add: inj_on_def Ball_def)
        ultimately show ?thesis 
          by (simp add: NFA_rename_states_full_def card_image)
      qed
    qed
  end

  lemma (in nfa_from_list) \<alpha>_exists :
    "NFA \<A> \<Longrightarrow> \<exists>AA. invar AA \<and> \<A> = \<alpha> AA"
  by (metis NFA_construct_exists nfa_from_list_correct)

  type_synonym ('q,'a,'nfa) nfa_accept = 
    "'nfa \<Rightarrow> 'a list \<Rightarrow> bool"
  locale nfa_accept = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes accept :: "'nfa \<Rightarrow> 'a list \<Rightarrow> bool"
    assumes accept_correct:
      "invar n \<Longrightarrow> (accept n w = NFA_accept (\<alpha> n) w)"
  begin
    lemma accept_correct___isomorphic :
      assumes invar: "invar n"
          and iso: "NFA_isomorphic_wf (\<alpha> n) (\<A> :: ('q2, 'a) NFA_rec)"
      shows "accept n w = NFA_accept \<A> w"
    using assms
    by (metis NFA_isomorphic_wf_accept accept_correct)
  end

  locale dfa_accept = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes accept :: "'nfa \<Rightarrow> 'a list \<Rightarrow> bool"
    assumes accept_correct:
      "invar n \<Longrightarrow> DFA (\<alpha> n) \<Longrightarrow> (accept n w = NFA_accept (\<alpha> n) w)"

  locale nfa_remove_states = nfa \<alpha> invar + set \<alpha>_s invar_s 
    for \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" and invar
    and \<alpha>_s :: "'q_set \<Rightarrow> 'q set" and invar_s +
    fixes remove_states :: "'nfa \<Rightarrow> 'q_set \<Rightarrow> 'nfa"
    assumes remove_states_correct:
      "invar n \<Longrightarrow> invar_s S \<Longrightarrow> (invar (remove_states n S))"
      "invar n \<Longrightarrow> invar_s S \<Longrightarrow> 
       (\<alpha> (remove_states n S) = NFA_remove_states (\<alpha> n) (\<alpha>_s S))"

  locale nfa_rename_states = nfa \<alpha>1 invar1 + nfa \<alpha>2 invar2  
    for \<alpha>1 :: "('q1,'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes rename_states :: "'nfa1 \<Rightarrow> ('q1 \<Rightarrow> 'q2) \<Rightarrow> 'nfa2"
    assumes nfa_rename_states_correct:
      "invar1 n \<Longrightarrow> (invar2 (rename_states n f))"
      "invar1 n \<Longrightarrow> (\<alpha>2 (rename_states n f) = NFA_rename_states (\<alpha>1 n) f)"

  locale dfa_rename_states = nfa \<alpha>1 invar1 + nfa \<alpha>2 invar2  
    for \<alpha>1 :: "('q1,'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes rename_states :: "'nfa1 \<Rightarrow> ('q1 \<Rightarrow> 'q2) \<Rightarrow> 'nfa2"
    assumes dfa_rename_states_correct:
      "invar1 n \<Longrightarrow> DFA (NFA_rename_states (\<alpha>1 n) f) \<Longrightarrow> (invar2 (rename_states n f))"
      "invar1 n \<Longrightarrow> DFA (NFA_rename_states (\<alpha>1 n) f) \<Longrightarrow> (\<alpha>2 (rename_states n f) = NFA_rename_states (\<alpha>1 n) f)"

  type_synonym ('a1,'a2,'nfa1,'nfa2) nfa_rename_labels = "'nfa1 \<Rightarrow> ('a1 \<Rightarrow> 'a2) \<Rightarrow> 'nfa2"
  locale nfa_rename_labels = n1:nfa \<alpha>1 invar1 + n2:nfa \<alpha>2 invar2  
    for \<alpha>1 :: "('q,'a1,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q,'a2,'nfa2) nfa_\<alpha>" and invar2 +
    fixes rename_labels :: "('a1,'a2,'nfa1,'nfa2) nfa_rename_labels"
    assumes rename_labels_correct:
      "invar1 n \<Longrightarrow> (invar2 (rename_labels n f))"
      "invar1 n \<Longrightarrow> (\<alpha>2 (rename_labels n f) = SemiAutomaton_rename_labels (\<alpha>1 n) f)"
  begin
    lemma rename_labels_correct___isomorphic :
      "invar1 n \<Longrightarrow> (invar2 (rename_labels n f))"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> 
                    NFA_isomorphic_wf (\<alpha>2 (rename_labels n f)) (SemiAutomaton_rename_labels \<A> f)"
    using rename_labels_correct[of n f] n2.nfa_is_wellformed
          NFA_isomorphic_wf___NFA_rename_labels_cong [of "\<alpha>1 n" \<A> f]
      by simp_all
  end

  type_synonym ('a1,'a2,'a_set,'nfa1,'nfa2) nfa_rename_labels_gen = "'nfa1 \<Rightarrow> 'a_set \<Rightarrow> ('a1 \<Rightarrow> 'a2) \<Rightarrow> 'nfa2"
  locale nfa_rename_labels_gen = n1: nfa \<alpha>1 invar1 + n2: nfa \<alpha>2 invar2 + set \<alpha>3 invar3  
    for \<alpha>1 :: "('q,'a1,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q,'a2,'nfa2) nfa_\<alpha>" and invar2 and
        \<alpha>3 :: "'a_set \<Rightarrow> 'a2 set" and invar3 +
    fixes rename_labels_gen :: "('a1,'a2,'a_set,'nfa1,'nfa2) nfa_rename_labels_gen"
    assumes rename_labels_gen_correct:
      "invar1 n \<Longrightarrow> invar3 A \<Longrightarrow> \<alpha>3 A = f ` (\<Sigma> (\<alpha>1 n)) \<Longrightarrow> (invar2 (rename_labels_gen n A f))"
      "invar1 n \<Longrightarrow> invar3 A \<Longrightarrow> \<alpha>3 A = f ` (\<Sigma> (\<alpha>1 n)) \<Longrightarrow> (\<alpha>2 (rename_labels_gen n A f) = SemiAutomaton_rename_labels (\<alpha>1 n) f)"
  begin
    lemma rename_labels_gen_correct___isomorphic :
      "invar1 n \<Longrightarrow> invar3 A \<Longrightarrow> \<alpha>3 A = f ` (\<Sigma> (\<alpha>1 n)) \<Longrightarrow> (invar2 (rename_labels_gen n A f))"
      "invar1 n \<Longrightarrow> invar3 A \<Longrightarrow> \<alpha>3 A = f ` (\<Sigma> (\<alpha>1 n)) \<Longrightarrow> 
         NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow>
         NFA_isomorphic_wf (\<alpha>2 (rename_labels_gen n A f)) (SemiAutomaton_rename_labels \<A> f)"
    using rename_labels_gen_correct[of n A f] n2.nfa_is_wellformed
          NFA_isomorphic_wf___NFA_rename_labels_cong [of "\<alpha>1 n" \<A> f]
    by simp_all 
  end

  lemma nfa_rename_labels_gen_impl :
    assumes "nfa_rename_labels_gen \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>3 invar3 rl"
        and "\<And>n f. invar1 n \<Longrightarrow> invar3 (im n f) \<and> \<alpha>3 (im n f) = f ` (\<Sigma> (\<alpha>1 n))"
    shows "nfa_rename_labels \<alpha>1 invar1 \<alpha>2 invar2 (\<lambda>AA f. rl AA (im AA f) f)"
    using assms
    unfolding nfa_rename_labels_def nfa_rename_labels_gen_def nfa_rename_labels_axioms_def
              nfa_rename_labels_gen_axioms_def
    by simp

  locale nfa_reverse = nfa \<alpha>1 invar1 + nfa \<alpha>2 invar2   
    for \<alpha>1 :: "('q,'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes reverse :: "'nfa1 \<Rightarrow> 'nfa2"
    assumes reverse_correct:
      "invar1 n \<Longrightarrow> invar2 (reverse n)"
      "invar1 n \<Longrightarrow> (\<alpha>2 (reverse n) = NFA_reverse (\<alpha>1 n))"
  begin
    lemma reverse_correct___isomorphic :
      "invar1 n \<Longrightarrow> invar2 (reverse n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) (\<A> :: ('q2, 'a) NFA_rec) \<Longrightarrow>
                    NFA_isomorphic_wf (\<alpha>2 (reverse n)) (NFA_reverse \<A>)"
      apply (simp add: reverse_correct)
      apply (insert reverse_correct(2)[of n] 
                  NFA_isomorphic_wf___NFA_reverse_cong [of "\<alpha>1 n" \<A>])
      apply (simp)
    done
  end

  locale nfa_complement = nfa \<alpha> invar   
    for \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" and invar +
    fixes complement :: "'nfa \<Rightarrow> 'nfa"
    assumes complement_correct:
      "invar n \<Longrightarrow> invar (complement n)"
      "invar n \<Longrightarrow> (\<alpha> (complement n) = DFA_complement (\<alpha> n))"
  begin
    lemma complement_correct___isomorphic :
      "invar n \<Longrightarrow> invar (complement n)"
      "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> n) (\<A> :: ('q2, 'a) NFA_rec) \<Longrightarrow>
                    NFA_isomorphic_wf (\<alpha> (complement n)) (DFA_complement \<A>)"
      apply (simp add: complement_correct)
      apply (insert complement_correct(2)[of n] 
                  NFA_isomorphic_wf___DFA_complement_cong [of "\<alpha> n" \<A>])
      apply (simp)
    done
  end

  type_synonym ('q2,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct = 
    "('q2 \<Rightarrow> 'i) \<Rightarrow> 'q2 list \<Rightarrow> 'a_set \<Rightarrow> ('q2 \<Rightarrow> bool) \<Rightarrow> 
     ('q2 \<Rightarrow> ('a\<times>'q2,'\<sigma>) set_iterator) \<Rightarrow> 'nfa"
  locale nfa_dfa_construct_no_enc = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes construct :: "bool \<Rightarrow> ('q2,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct"
    assumes nfa_dfa_construct_no_enc_correct:
       "\<lbrakk>NFA (\<A>::('q2, 'a) NFA_rec); det \<Longrightarrow> DFA \<A>; inj_on f (\<Q> \<A>); distinct I; set I = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. q \<in> \<Q> \<A> \<Longrightarrow> FP q \<longleftrightarrow> q \<in> \<F> \<A>;
         \<And>q. q \<in> \<Q> \<A> \<Longrightarrow> set_iterator (D_it q) {(a, q'). (q, a, q') \<in> \<Delta> \<A>}\<rbrakk> \<Longrightarrow> 
         (invar (construct det f I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct det f I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  locale nfa_construct_no_enc = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes construct :: "('q2,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct"
    assumes nfa_construct_no_enc_correct:
       "\<lbrakk>NFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>); distinct I; set I = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. q \<in> \<Q> \<A> \<Longrightarrow> FP q \<longleftrightarrow> q \<in> \<F> \<A>;
         \<And>q. q \<in> \<Q> \<A> \<Longrightarrow> set_iterator (D_it q) {(a, q'). (q, a, q') \<in> \<Delta> \<A>}\<rbrakk> \<Longrightarrow> 
         (invar (construct f I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct f I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  locale dfa_construct_no_enc = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes construct :: "('q2,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct"
    assumes dfa_construct_no_enc_correct:
       "\<lbrakk>DFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>); distinct I; set I = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. q \<in> \<Q> \<A> \<Longrightarrow> FP q \<longleftrightarrow> q \<in> \<F> \<A>;
         \<And>q. q \<in> \<Q> \<A> \<Longrightarrow> set_iterator (D_it q) {(a, q'). (q, a, q') \<in> \<Delta> \<A>}\<rbrakk> \<Longrightarrow> 
         (invar (construct f I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct f I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  type_synonym ('q2,'i,'a,'a_set,'nfa) nfa_construct_fun = 
    "('q2 \<Rightarrow> 'i) \<Rightarrow> 'q2 \<Rightarrow> 'a_set \<Rightarrow> ('q2 \<Rightarrow> bool) \<Rightarrow> 
     ('q2 \<Rightarrow> 'a \<Rightarrow> 'q2) \<Rightarrow> 'nfa"
  locale dfa_construct_no_enc_fun = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes construct :: "('q2,'i,'a,'a_set,'nfa) nfa_construct_fun"
    assumes dfa_construct_no_enc_fun_correct:
       "\<lbrakk>DFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>); I \<in> \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. q \<in> \<Q> \<A> \<Longrightarrow> FP q \<longleftrightarrow> q \<in> \<F> \<A>;
         \<And>q a. q \<in> \<Q> \<A> \<Longrightarrow> a \<in> \<Sigma> \<A> \<Longrightarrow> (q, a, D_fun q a) \<in> \<Delta> \<A>\<rbrakk> \<Longrightarrow> 
         (invar (construct f I A FP D_fun) \<and>
          NFA_isomorphic_wf (\<alpha> (construct f I A FP D_fun)) (NFA_remove_unreachable_states \<A>))"


  lemma nfa_construct_no_enc_sublocale :
  assumes pre: "nfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s construct"
  shows "dfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s construct"
    apply (intro dfa_construct_no_enc.intro dfa_construct_no_enc_axioms.intro)
      apply (insert pre) []
      apply (simp add: nfa_construct_no_enc_def)
    
      apply (rule_tac nfa_construct_no_enc.nfa_construct_no_enc_correct [OF pre])
      apply (simp_all add: DFA_alt_def)
  done

  lemma nfa_dfa_construct_no_enc_sublocale_nfa :
  assumes pre: "nfa_dfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s construct"
  shows "nfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s (construct False)"
    apply (intro nfa_construct_no_enc.intro nfa_construct_no_enc_axioms.intro)
      apply (insert pre) []
      apply (simp add: nfa_dfa_construct_no_enc_def)
    
      apply (rule_tac nfa_dfa_construct_no_enc.nfa_dfa_construct_no_enc_correct [OF pre])
      apply (simp_all)
  done

  lemma nfa_dfa_construct_no_enc_sublocale_dfa :
  assumes pre: "nfa_dfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s construct"
  shows "dfa_construct_no_enc \<alpha> invar \<alpha>_s invar_s (construct det)"
    apply (intro dfa_construct_no_enc.intro dfa_construct_no_enc_axioms.intro)
      apply (insert pre) []
      apply (simp add: nfa_dfa_construct_no_enc_def)
    
      apply (rule_tac nfa_dfa_construct_no_enc.nfa_dfa_construct_no_enc_correct [OF pre])
      apply (simp_all)
  done

  text {* Sometimes, one cannot work on abstract states directly, but needs an encoding of
          states. An example is the powerset construction for determinising automata. In this
          example states are sets, which one probably wants to encode using the Collection
          framework. *}
  locale nfa_dfa_construct = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and construct :: "bool \<Rightarrow> ('q2_rep,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct"
    assumes nfa_dfa_construct_correct:
       "\<lbrakk>NFA (\<A>::('q2, 'a) NFA_rec); det \<Longrightarrow> DFA \<A>; inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         distinct (map q2_\<alpha> I); \<And>q. q \<in> set I \<Longrightarrow> q2_invar q; q2_\<alpha> ` (set I) = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs
               (\<lambda>(a, q'). (a, q2_\<alpha> q')) (\<lambda>(a, q'). q2_invar q') (D_it q) 
               {(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}\<rbrakk> \<Longrightarrow> 
         (invar (construct det ff I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct det ff I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  locale nfa_construct = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and construct :: "('q2_rep,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct"
    assumes nfa_construct_correct:
       "\<lbrakk>NFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         distinct (map q2_\<alpha> I); \<And>q. q \<in> set I \<Longrightarrow> q2_invar q; q2_\<alpha> ` (set I) = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs
               (\<lambda>(a, q'). (a, q2_\<alpha> q')) (\<lambda>(a, q'). q2_invar q') (D_it q) 
               {(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}\<rbrakk> \<Longrightarrow> 
         (invar (construct ff I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct ff I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  locale dfa_construct = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and construct :: "('q2_rep,'i,'a,'a_set,'\<sigma>,'nfa) nfa_construct"
    assumes dfa_construct_correct:
       "\<lbrakk>DFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         distinct (map q2_\<alpha> I); \<And>q. q \<in> set I \<Longrightarrow> q2_invar q; q2_\<alpha> ` (set I) = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs
               (\<lambda>(a, q'). (a, q2_\<alpha> q')) (\<lambda>(a, q'). q2_invar q') (D_it q) 
               {(a, q'). (q2_\<alpha> q, a, q') \<in> \<Delta> \<A>}
            \<rbrakk> \<Longrightarrow> 
         (invar (construct ff I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct ff I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  lemma nfa_construct_sublocale :
  assumes pre: "nfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar construct"
  shows "dfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar construct"
    apply (intro dfa_construct.intro dfa_construct_axioms.intro)
    apply (insert pre) []
    apply (simp add: nfa_construct_def)
    
    apply (rule_tac nfa_construct.nfa_construct_correct [OF pre])
    apply (simp_all add: DFA_alt_def)
  done

  lemma nfa_dfa_construct_sublocale_dfa :
  assumes pre: "nfa_dfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar construct"
  shows "dfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar (construct det)"
    apply (intro dfa_construct.intro dfa_construct_axioms.intro)
    apply (insert pre) []
    apply (simp add: nfa_dfa_construct_def)
    
    apply (rule_tac nfa_dfa_construct.nfa_dfa_construct_correct [OF pre])
    apply (simp_all)
  done

  lemma nfa_dfa_construct_sublocale_nfa :
  assumes pre: "nfa_dfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar construct"
  shows "nfa_construct \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar (construct False)"
    apply (intro nfa_construct.intro nfa_construct_axioms.intro)
    apply (insert pre) []
    apply (simp add: nfa_dfa_construct_def)
    
    apply (rule_tac nfa_dfa_construct.nfa_dfa_construct_correct [OF pre])
    apply (simp_all)
  done

  locale dfa_construct_fun = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and construct :: "('q2_rep,'i,'a,'a_set,'nfa) nfa_construct_fun"
    assumes dfa_construct_fun_correct:
       "\<lbrakk>DFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         q2_invar I; q2_\<alpha> I \<in> \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; 
         \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q a. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> a \<in> \<Sigma> \<A> \<Longrightarrow> 
              (q2_\<alpha> q, a, q2_\<alpha> (D_fun q a)) \<in> \<Delta> \<A> \<and> q2_invar (D_fun q a) 
            \<rbrakk> \<Longrightarrow> 
         (invar (construct ff I A FP D_fun) \<and>
          NFA_isomorphic_wf (\<alpha> (construct ff I A FP D_fun)) (NFA_remove_unreachable_states \<A>))"

  locale nfa_dfa_construct_label_sets = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and a_\<alpha> :: "'as \<Rightarrow> 'a set"
      and a_invar :: "'as \<Rightarrow> bool"
      and construct 
    assumes nfa_dfa_construct_label_sets_correct:
       "\<lbrakk>NFA (\<A>::('q2, 'a) NFA_rec); det \<Longrightarrow> DFA \<A>; inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         distinct (map q2_\<alpha> I); \<And>q. q \<in> set I \<Longrightarrow> q2_invar q; q2_\<alpha> ` (set I) = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs 
             (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (\<lambda>(as, q). a_invar as \<and> q2_invar q) (D_it q) 
             (DS_q (q2_\<alpha> q));
         \<And>q a q'. q \<in> \<Q> \<A> \<Longrightarrow> ((q, a, q') \<in> \<Delta> \<A>) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS_q q);
         \<And>q as q'. q \<in> \<Q> \<A> \<Longrightarrow> (as, q') \<in> DS_q q \<Longrightarrow> as \<noteq> {}
            \<rbrakk> \<Longrightarrow> 
         (invar (construct det ff I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct det ff I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  locale nfa_construct_label_sets = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and a_\<alpha> :: "'as \<Rightarrow> 'a set"
      and a_invar :: "'as \<Rightarrow> bool"
      and construct 
    assumes nfa_construct_label_sets_correct:
       "\<lbrakk>NFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         distinct (map q2_\<alpha> I); \<And>q. q \<in> set I \<Longrightarrow> q2_invar q; q2_\<alpha> ` (set I) = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs 
             (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (\<lambda>(as, q). a_invar as \<and> q2_invar q) (D_it q) 
             (DS_q (q2_\<alpha> q));
         \<And>q a q'. q \<in> \<Q> \<A> \<Longrightarrow> ((q, a, q') \<in> \<Delta> \<A>) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS_q q);
         \<And>q as q'. q \<in> \<Q> \<A> \<Longrightarrow> (as, q') \<in> DS_q q \<Longrightarrow> as \<noteq> {}
            \<rbrakk> \<Longrightarrow> 
         (invar (construct ff I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct ff I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  locale dfa_construct_label_sets = nfa \<alpha> invar + set s_\<alpha> s_invar 
    for \<alpha> invar s_\<alpha> s_invar + 
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>" 
    fixes q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2" 
      and q2_invar :: "'q2_rep \<Rightarrow> bool" 
      and a_\<alpha> :: "'as \<Rightarrow> 'a set"
      and a_invar :: "'as \<Rightarrow> bool"
      and construct 
    assumes dfa_construct_label_sets_correct:
       "\<lbrakk>DFA (\<A>::('q2, 'a) NFA_rec); inj_on f (\<Q> \<A>);
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> ff q = (f (q2_\<alpha> q));
         distinct (map q2_\<alpha> I); \<And>q. q \<in> set I \<Longrightarrow> q2_invar q; q2_\<alpha> ` (set I) = \<I> \<A>;
         s_invar A; s_\<alpha> A = \<Sigma> \<A>; \<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> \<Q> \<A>\<rbrakk> \<Longrightarrow> FP q \<longleftrightarrow> q2_\<alpha> q \<in> \<F> \<A>;
         \<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs 
             (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (\<lambda>(as, q). a_invar as \<and> q2_invar q) (D_it q) 
             (DS_q (q2_\<alpha> q));
         \<And>q a q'. q \<in> \<Q> \<A> \<Longrightarrow> ((q, a, q') \<in> \<Delta> \<A>) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS_q q);
         \<And>q as q'. q \<in> \<Q> \<A> \<Longrightarrow> (as, q') \<in> DS_q q \<Longrightarrow> as \<noteq> {}
            \<rbrakk> \<Longrightarrow> 
         (invar (construct ff I A FP D_it) \<and>
          NFA_isomorphic_wf (\<alpha> (construct ff I A FP D_it)) (NFA_remove_unreachable_states \<A>))"

  lemma nfa_construct_label_sets_sublocale :
  assumes pre: "nfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar a_\<alpha> a_invar construct"
  shows "dfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar a_\<alpha> a_invar construct"
    apply (intro dfa_construct_label_sets.intro dfa_construct_label_sets_axioms.intro)
    apply (insert pre) []
    apply (simp add: nfa_construct_label_sets_def)
    
    apply (rule_tac nfa_construct_label_sets.nfa_construct_label_sets_correct [OF pre])
    apply (simp_all add: DFA_alt_def)
    apply metis
  done

  lemma nfa_dfa_construct_label_sets_sublocale_dfa :
  assumes pre: "nfa_dfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar a_\<alpha> a_invar construct"
  shows "dfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar a_\<alpha> a_invar (construct det)"
    apply (intro dfa_construct_label_sets.intro dfa_construct_label_sets_axioms.intro)
    apply (insert pre) []
    apply (simp add: nfa_dfa_construct_label_sets_def)
    
    apply (rule_tac nfa_dfa_construct_label_sets.nfa_dfa_construct_label_sets_correct [OF pre])
    apply (simp_all)
    apply metis
  done

  lemma nfa_dfa_construct_label_sets_sublocale_nfa :
  assumes pre: "nfa_dfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar a_\<alpha> a_invar construct"
  shows "nfa_construct_label_sets \<alpha> invar \<alpha>_s invar_s q2_\<alpha> q2_invar a_\<alpha> a_invar (construct False)"
    apply (intro nfa_construct_label_sets.intro nfa_construct_label_sets_axioms.intro)
    apply (insert pre) []
    apply (simp add: nfa_dfa_construct_label_sets_def)
    
    apply (rule_tac nfa_dfa_construct_label_sets.nfa_dfa_construct_label_sets_correct [OF pre])
    apply (simp_all)
    apply metis
  done

  locale nfa_normalise = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes normalise :: "'nfa \<Rightarrow> 'nfa" 
    assumes normalise_correct:
       "invar n \<Longrightarrow> invar (normalise n)"
       "invar n \<Longrightarrow> NFA_isomorphic_wf (\<alpha> (normalise n)) (NFA_remove_unreachable_states (\<alpha> n))"
  begin
    lemma normalise_correct___isomorphic:
       "invar n \<Longrightarrow> invar (normalise n)"
       "\<lbrakk>invar n; NFA_isomorphic_wf (\<alpha> n) (\<A> :: ('q2, 'a) NFA_rec)\<rbrakk> \<Longrightarrow> 
         NFA_isomorphic_wf (\<alpha> (normalise n)) (NFA_remove_unreachable_states \<A>)"
    proof -
      fix n
      assume invar_n: "invar n"
      with normalise_correct show invar_norm: "invar (normalise n)" by simp

      from normalise_correct[OF invar_n] 
      have iso_wf: "NFA_isomorphic_wf (\<alpha> (normalise n)) (NFA_remove_unreachable_states (\<alpha> n))"
        by simp

      assume "NFA_isomorphic_wf (\<alpha> n) (\<A> :: ('q2, 'a) NFA_rec)"
      note NFA_isomorphic_wf___NFA_remove_unreachable_states[OF this]
      from NFA_isomorphic_wf_trans[OF iso_wf this] 
      show "NFA_isomorphic_wf (\<alpha> (normalise n)) (NFA_remove_unreachable_states \<A>)" .
    qed
  end

  locale nfa_bool_comb_gen = nfa \<alpha>1 invar1 + nfa \<alpha>2 invar2 + nfa \<alpha>3 invar3 + set \<alpha>4 invar4
    for \<alpha>1 :: "('q1,'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 and
        \<alpha>3 :: "('q3,'a,'nfa3) nfa_\<alpha>" and invar3 and
        \<alpha>4 :: "'a_set \<Rightarrow> 'a set" and invar4 +
    fixes bool_comb :: "'a_set \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'nfa1 \<Rightarrow> 'nfa2 \<Rightarrow> 'nfa3"
    assumes bool_comb_correct_aux:
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> invar4 as \<Longrightarrow> 
         \<alpha>4 as = \<Sigma> (\<alpha>1 n1) \<inter> \<Sigma> (\<alpha>2 n2) \<Longrightarrow> 
       invar3 (bool_comb as bc n1 n2) \<and>
       NFA_isomorphic_wf (\<alpha>3 (bool_comb as bc n1 n2)) (NFA.efficient_bool_comb_NFA bc (\<alpha>1 n1) (\<alpha>2 n2))"
  begin
    lemma bool_comb_correct:
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> invar4 as \<Longrightarrow> 
         \<alpha>4 as = \<Sigma> (\<alpha>1 n1) \<inter> \<Sigma> (\<alpha>2 n2) \<Longrightarrow> invar3 (bool_comb as bc n1 n2)"
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> invar4 as \<Longrightarrow> 
         \<alpha>4 as = \<Sigma> (\<alpha>1 n1) \<inter> \<Sigma> (\<alpha>2 n2) \<Longrightarrow>
         NFA_isomorphic_wf (\<alpha>3 (bool_comb as bc n1 n2)) (NFA.efficient_bool_comb_NFA bc (\<alpha>1 n1) (\<alpha>2 n2))"
      using bool_comb_correct_aux by simp_all

    lemma bool_comb_correct___isomorphic:
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> invar4 as \<Longrightarrow> 
         \<alpha>4 as = \<Sigma> (\<alpha>1 n1) \<inter> \<Sigma> (\<alpha>2 n2) \<Longrightarrow> invar3 (bool_comb as bc n1 n2)"
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> invar4 as \<Longrightarrow> 
         \<alpha>4 as = \<Sigma> (\<alpha>1 n1) \<inter> \<Sigma> (\<alpha>2 n2) \<Longrightarrow>
       NFA_isomorphic_wf (\<alpha>1 n1) \<A>1 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 n2) \<A>2 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>3 (bool_comb as bc n1 n2)) (NFA.efficient_bool_comb_NFA bc \<A>1 \<A>2)"
      apply (simp add: bool_comb_correct)
      apply (insert bool_comb_correct(2)[of n1 n2 as bc]
                    NFA_isomorphic_efficient_bool_comb_NFA [of "\<alpha>1 n1" \<A>1 "\<alpha>2 n2" \<A>2 bc])
      apply (metis NFA_isomorphic_wf_trans)
    done
  end

  locale nfa_bool_comb = nfa \<alpha>1 invar1 + nfa \<alpha>2 invar2 + nfa \<alpha>3 invar3   
    for \<alpha>1 :: "('q1,'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 and
        \<alpha>3 :: "('q3,'a,'nfa3) nfa_\<alpha>" and invar3 +
    fixes bool_comb :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'nfa1 \<Rightarrow> 'nfa2 \<Rightarrow> 'nfa3"
    assumes bool_comb_correct_aux:
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> \<Sigma> (\<alpha>1 n1) = \<Sigma> (\<alpha>2 n2) \<Longrightarrow> 
       invar3 (bool_comb bc n1 n2) \<and>
       NFA_isomorphic_wf (\<alpha>3 (bool_comb bc n1 n2)) 
         (NFA.efficient_bool_comb_NFA bc (\<alpha>1 n1) (\<alpha>2 n2))"
  begin
    lemma bool_comb_correct:
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> \<Sigma> (\<alpha>1 n1) = \<Sigma> (\<alpha>2 n2) \<Longrightarrow> invar3 (bool_comb bc n1 n2)"
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> \<Sigma> (\<alpha>1 n1) = \<Sigma> (\<alpha>2 n2) \<Longrightarrow> NFA_isomorphic_wf (\<alpha>3 (bool_comb bc n1 n2)) 
                                     (NFA.efficient_bool_comb_NFA bc (\<alpha>1 n1) (\<alpha>2 n2))"
      using bool_comb_correct_aux by (simp_all)

    lemma bool_comb_correct___isomorphic:
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> \<Sigma> (\<alpha>1 n1) = \<Sigma> (\<alpha>2 n2) \<Longrightarrow> invar3 (bool_comb bc n1 n2)"
      "invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> 
       \<Sigma> (\<alpha>1 n1) = \<Sigma> (\<alpha>2 n2) \<Longrightarrow>
       NFA_isomorphic_wf (\<alpha>1 n1) \<A>1 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 n2) \<A>2 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>3 (bool_comb bc n1 n2)) (NFA.efficient_bool_comb_NFA bc \<A>1 \<A>2)"
      apply (simp add: bool_comb_correct)
      apply (insert bool_comb_correct(2)[of n1 n2 bc]
                    NFA_isomorphic_efficient_bool_comb_NFA [of "\<alpha>1 n1" \<A>1 "\<alpha>2 n2" \<A>2 bc])
      apply (metis NFA_isomorphic_wf_trans)
    done
  end

  locale nfa_bool_comb_gen_same = nfa_bool_comb_gen \<alpha> invar \<alpha> invar \<alpha> invar \<alpha>_s invar_s bool_comb
    for \<alpha> :: "('q::{automaton_states},'a,'nfa1) nfa_\<alpha>" and invar and
        \<alpha>_s :: "'a_set \<Rightarrow> 'a set" and invar_s bool_comb
  begin
    lemma bool_comb_correct___same:
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> invar_s as \<Longrightarrow> 
         \<alpha>_s as = \<Sigma> (\<alpha> n1) \<inter> \<Sigma> (\<alpha> n2) \<Longrightarrow> invar (bool_comb as bc n1 n2)"
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> invar_s as \<Longrightarrow> 
         \<alpha>_s as = \<Sigma> (\<alpha> n1) \<inter> \<Sigma> (\<alpha> n2) \<Longrightarrow>
         NFA_isomorphic_wf (\<alpha> (bool_comb as bc n1 n2))
              (NFA_bool_comb bc (\<alpha> n1) (\<alpha> n2))"
       using bool_comb_correct [of n1 n2 as bc] nfa_axioms[unfolded nfa_def]
             NFA_bool_comb___isomorphic_wf [of "\<alpha> n1" "\<alpha> n2" bc]
       by (simp_all, metis NFA_isomorphic_wf_trans)

    lemma bool_comb_correct___same_isomorphic:
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> invar_s as \<Longrightarrow> 
         \<alpha>_s as = \<Sigma> (\<alpha> n1) \<inter> \<Sigma> (\<alpha> n2) \<Longrightarrow> invar (bool_comb as bc n1 n2)"
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> invar_s as \<Longrightarrow> 
         \<alpha>_s as = \<Sigma> (\<alpha> n1) \<inter> \<Sigma> (\<alpha> n2) \<Longrightarrow>
       NFA_isomorphic_wf (\<alpha> n1) \<A>1 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha> n2) \<A>2 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha> (bool_comb as bc n1 n2)) (NFA_bool_comb bc \<A>1 \<A>2)"
      apply (simp add: bool_comb_correct)
      apply (insert bool_comb_correct___isomorphic(2)[of n1 n2 as \<A>1 \<A>2 bc] 
             nfa_axioms[unfolded nfa_def]
             NFA_bool_comb___isomorphic_wf [of \<A>1 \<A>2 bc])
      apply (simp add: NFA_isomorphic_wf_refl)
      apply (metis NFA_isomorphic_wf_trans NFA_isomorphic_wf_alt_def)
    done
  end


  locale nfa_bool_comb_same = nfa_bool_comb \<alpha> invar \<alpha> invar \<alpha> invar bool_comb
    for \<alpha> :: "('q::{automaton_states},'a,'nfa1) nfa_\<alpha>" and invar bool_comb
  begin
    lemma bool_comb_correct___same:
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> 
         \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2) \<Longrightarrow> invar (bool_comb bc n1 n2)"
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> 
         \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2) \<Longrightarrow>
         NFA_isomorphic_wf (\<alpha> (bool_comb bc n1 n2))
              (NFA_bool_comb bc (\<alpha> n1) (\<alpha> n2))"
       using bool_comb_correct [of n1 n2 bc] nfa_axioms[unfolded nfa_def]
             NFA_bool_comb___isomorphic_wf [of "\<alpha> n1" "\<alpha> n2" bc]
       by (simp_all, metis NFA_isomorphic_wf_trans)

    lemma bool_comb_correct___same_isomorphic:
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> 
         \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2) \<Longrightarrow> invar (bool_comb bc n1 n2)"
      "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2) \<Longrightarrow>
       NFA_isomorphic_wf (\<alpha> n1) \<A>1 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha> n2) \<A>2 \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha> (bool_comb bc n1 n2)) (NFA_bool_comb bc \<A>1 \<A>2)"
      apply (simp add: bool_comb_correct)
      apply (insert bool_comb_correct___isomorphic(2)[of n1 n2 \<A>1 \<A>2 bc] 
             nfa_axioms[unfolded nfa_def]
             NFA_bool_comb___isomorphic_wf [of \<A>1 \<A>2 bc])
      apply (simp add: NFA_isomorphic_wf_refl)
      apply (metis NFA_isomorphic_wf_trans NFA_isomorphic_wf_alt_def)
    done
  end

  locale nfa_determinise = n1: nfa \<alpha>1 invar1 + n2: nfa \<alpha>2 invar2    
    for \<alpha>1 :: "('q1::{automaton_states},'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes determinise :: "'nfa1 \<Rightarrow> 'nfa2"
    assumes determinise_correct_aux:
      "invar1 n \<Longrightarrow> invar2 (determinise n) \<and> 
       NFA_isomorphic_wf (\<alpha>2 (determinise n)) (efficient_determinise_NFA (\<alpha>1 n))"
  begin
    lemma determinise_correct:
      "invar1 n \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>2 (determinise n)) (efficient_determinise_NFA (\<alpha>1 n))"
      using determinise_correct_aux by (simp_all)

    lemma determinise_correct___isomorphic:
      "invar1 n \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 (determinise n)) (efficient_determinise_NFA \<A>)"
      apply (simp add: determinise_correct)
      apply (insert determinise_correct(2)[of n]
                    NFA_isomorphic_efficient_determinise [of "\<alpha>1 n" \<A>])
      apply (metis NFA_isomorphic_wf_trans)
    done

    lemma determinise_correct___same:
      "invar1 n \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>2 (determinise n)) (NFA_determinise (\<alpha>1 n))"
       using determinise_correct [of n] n1.nfa_axioms[unfolded nfa_def]
             NFA_determinise_isomorphic_wf [of "\<alpha>1 n"]
       by (simp_all, metis NFA_isomorphic_wf_trans)

    lemma determinise_correct___same_isomorphic:
      "invar1 n \<Longrightarrow> invar2 (determinise n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 (determinise n)) (NFA_determinise \<A>)"
      apply (simp add: determinise_correct)
      apply (insert determinise_correct___isomorphic(2)[of n \<A>]
                    NFA_determinise_isomorphic_wf [of \<A>])
      apply (simp)
      apply (metis NFA_isomorphic_wf_trans NFA_isomorphic_wf_alt_def)
    done
  end

  locale nfa_minimise = n1: nfa \<alpha>1 invar1 + n2: nfa \<alpha>2 invar2    
    for \<alpha>1 :: "('q1::{automaton_states},'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes minimise :: "'nfa1 \<Rightarrow> 'nfa2"
    assumes nfa_minimise_correct_aux:
      "invar1 n \<Longrightarrow> invar2 (minimise n) \<and> 
       NFA_isomorphic_wf (\<alpha>2 (minimise n)) (NFA_minimise (\<alpha>1 n))"
  begin
    lemma nfa_minimise_correct:
      "invar1 n \<Longrightarrow> invar2 (minimise n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>2 (minimise n)) (NFA_minimise (\<alpha>1 n))"
      using nfa_minimise_correct_aux by (simp_all)

    lemma nfa_minimise_correct___isomorphic:
      "invar1 n \<Longrightarrow> invar2 (minimise n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 (minimise n)) (NFA_minimise \<A>)"
      apply (simp add: nfa_minimise_correct)
      apply (insert nfa_minimise_correct(2)[of n]
                    NFA_isomorphic_wf___minimise_cong [of "\<alpha>1 n" \<A>])
      apply (metis NFA_isomorphic_wf_trans)
    done

   lemma nfa_minimise_correct___isomorphic_Brzozowski :
      "invar1 n \<Longrightarrow> invar2 (minimise n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) (\<A>::('q3::{automaton_states}, 'a) NFA_rec) \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 (minimise n)) (Brzozowski \<A>)"
      apply (simp add: nfa_minimise_correct)
      apply (insert nfa_minimise_correct___isomorphic(2)[of n \<A>]
                    Brzozowski___minimise [of \<A>])
      apply (metis NFA_isomorphic_wf_alt_def NFA_isomorphic_wf_sym NFA_isomorphic_wf_trans)
    done
  end


  locale dfa_minimise = n1: nfa \<alpha>1 invar1 + n2: nfa \<alpha>2 invar2    
    for \<alpha>1 :: "('q1::{automaton_states},'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes minimise :: "'nfa1 \<Rightarrow> 'nfa2"
    assumes dfa_minimise_correct_aux:
      "invar1 n \<Longrightarrow> DFA (\<alpha>1 n) \<Longrightarrow> SemiAutomaton_is_initially_connected (\<alpha>1 n) \<Longrightarrow> invar2 (minimise n) \<and> 
       NFA_isomorphic_wf (\<alpha>2 (minimise n)) (NFA_minimise (\<alpha>1 n))"
  begin
    lemma dfa_minimise_correct:
      "invar1 n \<Longrightarrow> DFA (\<alpha>1 n) \<Longrightarrow> SemiAutomaton_is_initially_connected (\<alpha>1 n) \<Longrightarrow> invar2 (minimise n)"
      "invar1 n \<Longrightarrow> DFA (\<alpha>1 n) \<Longrightarrow> SemiAutomaton_is_initially_connected (\<alpha>1 n) \<Longrightarrow> 
           NFA_isomorphic_wf (\<alpha>2 (minimise n)) (NFA_minimise (\<alpha>1 n))"
      using dfa_minimise_correct_aux by (simp_all)

    lemma dfa_minimise_correct___isomorphic:
      "invar1 n \<Longrightarrow> DFA \<A> \<Longrightarrow> SemiAutomaton_is_initially_connected \<A> \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> invar2 (minimise n)"
      "invar1 n \<Longrightarrow> DFA \<A> \<Longrightarrow> SemiAutomaton_is_initially_connected \<A> \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> 
       NFA_isomorphic_wf (\<alpha>2 (minimise n)) (NFA_minimise \<A>)"
      apply (insert dfa_minimise_correct[of n]
                    NFA_isomorphic_wf___minimise_cong [of "\<alpha>1 n" \<A>]
                    NFA_isomorphic_wf___DFA [of "\<alpha>1 n" \<A>]
                    SemiAutomaton_is_initially_connected___NFA_isomorphic_wf [of "\<alpha>1 n" \<A>])
      apply simp_all
      apply (metis NFA_isomorphic_wf_trans)
    done
  end

  lemma nfa_minimise_sublocale :
  assumes pre: "nfa_minimise \<alpha>1 invar1 \<alpha>2 invar2 minimise"
  shows "dfa_minimise \<alpha>1 invar1 \<alpha>2 invar2 minimise"
  using assms
  unfolding dfa_minimise_def dfa_minimise_axioms_def nfa_minimise_def nfa_minimise_axioms_def
  by simp

  locale nfa_right_quotient_lists = n1: nfa \<alpha>1 invar1 + n2: nfa \<alpha>2 invar2    
    for \<alpha>1 :: "('q1,'a,'nfa1) nfa_\<alpha>" and invar1 and
        \<alpha>2 :: "('q2,'a,'nfa2) nfa_\<alpha>" and invar2 +
    fixes right_quotient_lists :: "('a \<Rightarrow> bool) \<Rightarrow> 'nfa1 \<Rightarrow> 'nfa2"
    assumes right_quotient_lists_correct_aux:
      "invar1 n \<Longrightarrow> invar2 (right_quotient_lists AP n) \<and> 
       NFA_isomorphic_wf (\<alpha>2 (right_quotient_lists AP n)) (NFA_right_quotient_lists (\<alpha>1 n) {a. AP a})"
  begin
    lemma right_quotient_lists_correct:
      "invar1 n \<Longrightarrow> invar2 (right_quotient_lists AP n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>2 (right_quotient_lists AP n)) (NFA_right_quotient_lists (\<alpha>1 n) {a. AP a})"
      using right_quotient_lists_correct_aux by (simp_all)

    lemma right_quotient_lists_correct___isomorphic:
      "invar1 n \<Longrightarrow> invar2 (right_quotient_lists AP n)"
      "invar1 n \<Longrightarrow> NFA_isomorphic_wf (\<alpha>1 n) \<A> \<Longrightarrow> (AS \<inter> \<Sigma> \<A> = {a. AP a} \<inter>  \<Sigma> \<A>) \<Longrightarrow>
       NFA_isomorphic_wf (\<alpha>2 (right_quotient_lists AP n)) (NFA_right_quotient_lists \<A> AS)"
    proof -
      assume invar: "invar1 n"
      from right_quotient_lists_correct(1)[OF invar] 
      show "invar2 (right_quotient_lists AP n)" by simp

      assume iso: "NFA_isomorphic_wf (\<alpha>1 n) \<A>"
      assume AS_eq: "(AS \<inter> \<Sigma> \<A> = {a. AP a} \<inter>  \<Sigma> \<A>)"

      from iso have wf_A: "NFA \<A>" unfolding NFA_isomorphic_wf_alt_def by simp

      from right_quotient_lists_correct(2)[OF invar, of AP]
           NFA_isomorphic_right_quotient [OF iso, of "lists {a. AP a}"]
      have "NFA_isomorphic_wf (\<alpha>2 (right_quotient_lists AP n)) 
                              (NFA_right_quotient_lists \<A> {a. AP a})" 
        by (rule NFA_isomorphic_wf_trans)
 
      with NFA.NFA_right_quotient_lists_inter [of \<A> "{a. AP a}"]
           NFA.NFA_right_quotient_lists_inter [of \<A> AS] AS_eq wf_A
      show "NFA_isomorphic_wf (\<alpha>2 (right_quotient_lists AP n)) (NFA_right_quotient_lists \<A> AS)"
        by simp
    qed
  end

  locale nfa_language_is_empty = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes is_empty :: "'nfa \<Rightarrow> bool" 
    assumes language_is_empty_correct:
       "invar n \<Longrightarrow> is_empty n \<longleftrightarrow> \<L> (\<alpha> n) = {}"
  begin
    lemma language_is_empty_correct___isomorphic:
       "\<lbrakk>invar n; NFA_isomorphic_wf (\<alpha> n) (\<A> :: ('q2, 'a) NFA_rec)\<rbrakk> \<Longrightarrow> 
         is_empty n \<longleftrightarrow> \<L> \<A> = {}"
      using language_is_empty_correct[of n] 
    by (metis NFA_isomorphic_wf_\<L>)
  end

  locale nfa_language_is_univ = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes is_univ :: "'nfa \<Rightarrow> bool" 
    assumes language_is_univ_correct:
       "invar n \<Longrightarrow> is_univ n \<longleftrightarrow> \<L> (\<alpha> n) = lists (\<Sigma> (\<alpha> n))"
  begin
    lemma language_is_univ_correct___isomorphic:
       "\<lbrakk>invar n; NFA_isomorphic_wf (\<alpha> n) (\<A> :: ('q2, 'a) NFA_rec)\<rbrakk> \<Longrightarrow> 
         is_univ n \<longleftrightarrow> \<L> \<A> = lists (\<Sigma> \<A>)"
      using language_is_univ_correct[of n]
    by (metis NFA_isomorphic_wf_\<L> NFA_isomorphic_wf_\<Sigma>)
  end

  locale nfa_language_is_subset = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes is_subset :: "'nfa \<Rightarrow> 'nfa \<Rightarrow> bool" 
    assumes language_is_subset_correct:
       "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2) \<Longrightarrow> is_subset n1 n2 \<longleftrightarrow> \<L> (\<alpha> n1) \<subseteq> \<L> (\<alpha> n2)"
  begin
    lemma language_is_subset_correct___isomorphic:
       "\<lbrakk>invar n1; invar n2; \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2);
         NFA_isomorphic_wf (\<alpha> n1) (\<A>1 :: ('q2, 'a) NFA_rec);
         NFA_isomorphic_wf (\<alpha> n2) (\<A>2 :: ('q3, 'a) NFA_rec)\<rbrakk> \<Longrightarrow> 
         is_subset n1 n2 \<longleftrightarrow> \<L> \<A>1 \<subseteq> \<L> \<A>2"
      using language_is_subset_correct[of n1 n2]
    by (metis NFA_isomorphic_wf_\<L>)
  end

  locale nfa_language_is_eq = nfa +
    constrains \<alpha> :: "('q,'a,'nfa) nfa_\<alpha>"
    fixes is_eq :: "'nfa \<Rightarrow> 'nfa \<Rightarrow> bool" 
    assumes language_is_eq_correct:
       "invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2) \<Longrightarrow> is_eq n1 n2 \<longleftrightarrow> \<L> (\<alpha> n1) = \<L> (\<alpha> n2)"
  begin
    lemma language_is_eq_correct___isomorphic:
       "\<lbrakk>invar n1; invar n2; \<Sigma> (\<alpha> n1) = \<Sigma> (\<alpha> n2); NFA_isomorphic_wf (\<alpha> n1) (\<A>1 :: ('q2, 'a) NFA_rec);
         NFA_isomorphic_wf (\<alpha> n2) (\<A>2 :: ('q3, 'a) NFA_rec)\<rbrakk> \<Longrightarrow> 
         is_eq n1 n2 \<longleftrightarrow> \<L> \<A>1 = \<L> \<A>2"
      using language_is_eq_correct[of n1 n2]
    by (metis NFA_isomorphic_wf_\<L>)
  end

  subsection {* Record Based Interface *}

  record ('q,'a,'nfa) nfa_ops =
    nfa_op_\<alpha> :: "('q::{automaton_states},'a,'nfa) nfa_\<alpha>"
    nfa_op_invar :: "'nfa \<Rightarrow> bool"
    nfa_op_nfa_from_list :: "('q,'a,'nfa) nfa_from_list"
    nfa_op_dfa_from_list :: "('q,'a,'nfa) nfa_from_list"
    nfa_op_to_list :: "('q,'a,'nfa) nfa_to_list"
    nfa_op_to_list_simple :: "('q,'a,'nfa) nfa_to_list_simple"
    nfa_op_states_no :: "'nfa \<Rightarrow> nat"
    nfa_op_labels_no :: "'nfa \<Rightarrow> nat"
    nfa_op_trans_no :: "'nfa \<Rightarrow> nat"
    nfa_op_initial_no :: "'nfa \<Rightarrow> nat"
    nfa_op_final_no :: "'nfa \<Rightarrow> nat"
    nfa_op_accept :: "('q,'a,'nfa) nfa_accept"
    nfa_op_rename_labels :: "('a,'a,'nfa,'nfa) nfa_rename_labels"
    nfa_op_normalise :: "'nfa \<Rightarrow> 'nfa"
    nfa_op_reverse :: "'nfa \<Rightarrow> 'nfa"
    nfa_op_complement :: "'nfa \<Rightarrow> 'nfa"
    nfa_op_bool_comb :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'nfa \<Rightarrow> 'nfa \<Rightarrow> 'nfa"
    nfa_op_determinise :: "'nfa \<Rightarrow> 'nfa"
    nfa_op_minimise_Brzozowski :: "'nfa \<Rightarrow> 'nfa" 
    nfa_op_minimise_Hopcroft :: "'nfa \<Rightarrow> 'nfa" 
    nfa_op_minimise_Hopcroft_NFA :: "'nfa \<Rightarrow> 'nfa" 
    nfa_op_right_quotient_lists :: "('a \<Rightarrow> bool) \<Rightarrow> 'nfa \<Rightarrow> 'nfa"
    nfa_op_language_is_empty :: "'nfa \<Rightarrow> bool"
    nfa_op_language_is_univ :: "'nfa \<Rightarrow> bool"
    nfa_op_language_is_subset :: "'nfa \<Rightarrow> 'nfa \<Rightarrow> bool"
    nfa_op_language_is_eq :: "'nfa \<Rightarrow> 'nfa \<Rightarrow> bool"

  locale StdNFADefs =
    fixes ops :: "('q::{automaton_states},'a,'nfa) nfa_ops"
  begin
    abbreviation \<alpha> where "\<alpha> \<equiv> nfa_op_\<alpha> ops"
    abbreviation invar where "invar \<equiv> nfa_op_invar ops"
    abbreviation nfa_from_list where "nfa_from_list \<equiv> nfa_op_nfa_from_list ops"
    abbreviation dfa_from_list where "dfa_from_list \<equiv> nfa_op_dfa_from_list ops"
    abbreviation to_list where "to_list \<equiv> nfa_op_to_list ops"
    abbreviation accept where "accept \<equiv> nfa_op_accept ops"
    abbreviation rename_labels where "rename_labels \<equiv> nfa_op_rename_labels ops"
    abbreviation normalise where "normalise \<equiv> nfa_op_normalise ops"
    abbreviation reverse where "reverse \<equiv> nfa_op_reverse ops"
    abbreviation complement where "complement \<equiv> nfa_op_complement ops"
    abbreviation bool_comb where "bool_comb \<equiv> nfa_op_bool_comb ops"
    abbreviation product where "product \<equiv> bool_comb op\<and>"
    abbreviation determinise where "determinise \<equiv> nfa_op_determinise ops"
    abbreviation minimise_Brzozowski where "minimise_Brzozowski \<equiv> nfa_op_minimise_Brzozowski ops"
    abbreviation minimise_Hopcroft where "minimise_Hopcroft \<equiv> nfa_op_minimise_Hopcroft ops"
    abbreviation minimise_Hopcroft_NFA where "minimise_Hopcroft_NFA \<equiv> nfa_op_minimise_Hopcroft_NFA ops"
    abbreviation right_quotient_lists where "right_quotient_lists \<equiv> nfa_op_right_quotient_lists ops"
    abbreviation to_list_simple where "to_list_simple \<equiv> nfa_op_to_list_simple ops"
    abbreviation states_no where "states_no \<equiv> nfa_op_states_no ops"
    abbreviation labels_no where "labels_no \<equiv> nfa_op_labels_no ops"
    abbreviation trans_no where "trans_no \<equiv> nfa_op_trans_no ops"
    abbreviation initial_no where "initial_no \<equiv> nfa_op_initial_no ops"
    abbreviation final_no where "final_no \<equiv> nfa_op_final_no ops"
    abbreviation language_is_empty where "language_is_empty \<equiv> nfa_op_language_is_empty ops"
    abbreviation language_is_univ where "language_is_univ \<equiv> nfa_op_language_is_univ ops"
    abbreviation language_is_subset where "language_is_subset \<equiv> nfa_op_language_is_subset ops"
    abbreviation language_is_eq where "language_is_eq \<equiv> nfa_op_language_is_eq ops"
  end

  locale StdNFA = StdNFADefs +
    nfa \<alpha> invar +
    nfa_from_list \<alpha> invar nfa_from_list +
    dfa_from_list \<alpha> invar dfa_from_list +
    nfa_to_list \<alpha> invar to_list +
    nfa_to_list_simple \<alpha> invar to_list_simple +
    nfa_stats \<alpha> invar states_no labels_no trans_no initial_no final_no +
    nfa_accept \<alpha> invar accept +
    nfa_rename_labels \<alpha> invar \<alpha> invar rename_labels +
    nfa_normalise \<alpha> invar normalise +
    nfa_reverse \<alpha> invar \<alpha> invar reverse +
    nfa_complement \<alpha> invar complement +
    nfa_bool_comb_same \<alpha> invar bool_comb +
    nfa_determinise \<alpha> invar \<alpha> invar determinise +
    min_brz: nfa_minimise \<alpha> invar \<alpha> invar minimise_Brzozowski + 
    min_Hop: nfa_minimise \<alpha> invar \<alpha> invar minimise_Hopcroft_NFA + 
    min_Hop_dfa: dfa_minimise \<alpha> invar \<alpha> invar minimise_Hopcroft +
    nfa_right_quotient_lists \<alpha> invar \<alpha> invar right_quotient_lists +
    nfa_language_is_empty \<alpha> invar language_is_empty +
    nfa_language_is_univ \<alpha> invar language_is_univ +
    nfa_language_is_subset \<alpha> invar language_is_subset +
    nfa_language_is_eq \<alpha> invar language_is_eq
  begin
    lemmas nfa_minimise_Brzozowski_correct = min_brz.nfa_minimise_correct
    lemmas nfa_minimise_Hopcroft_correct = min_Hop.nfa_minimise_correct
    lemmas dfa_minimise_Hopcroft_correct = min_Hop_dfa.dfa_minimise_correct
    lemmas nfa_minimise_Brzozowski_correct___isomorphic = min_brz.nfa_minimise_correct___isomorphic
    lemmas nfa_minimise_Brzozowski_correct___isomorphic_Brzozowski= min_brz.nfa_minimise_correct___isomorphic_Brzozowski
    lemmas nfa_minimise_Hopcroft_correct___isomorphic = min_Hop.nfa_minimise_correct___isomorphic
    lemmas dfa_minimise_Hopcroft_correct___isomorphic = min_Hop_dfa.dfa_minimise_correct___isomorphic

    lemmas correct = nfa_from_list_correct dfa_from_list_correct to_list_correct
                     to_list_simple_correct stats_correct
                     accept_correct rename_labels_correct
                     normalise_correct reverse_correct complement_correct 
                     bool_comb_correct 
                     determinise_correct 
                     nfa_minimise_Brzozowski_correct 
                     nfa_minimise_Hopcroft_correct
                     dfa_minimise_Hopcroft_correct
                     right_quotient_lists_correct
                     bool_comb_correct bool_comb_correct___same(2)
                     determinise_correct determinise_correct___same(2)
                     language_is_empty_correct
                     language_is_univ_correct
                     language_is_subset_correct
                     language_is_eq_correct

    lemmas correct_isomorphic = 
       nfa_from_list_correct___isomorphic 
       dfa_from_list_correct___isomorphic
       to_list_correct___isomorphic
       to_list_simple_correct___isomorphic
       stats_correct___isomorphic
       accept_correct___isomorphic
       rename_labels_correct___isomorphic
       normalise_correct___isomorphic 
       reverse_correct___isomorphic
       complement_correct___isomorphic
       bool_comb_correct___isomorphic
       bool_comb_correct___same_isomorphic(2)
       determinise_correct___isomorphic
       determinise_correct___same_isomorphic(2)
       language_is_empty_correct___isomorphic
       language_is_univ_correct___isomorphic
       language_is_subset_correct___isomorphic
       language_is_eq_correct___isomorphic
       nfa_minimise_Brzozowski_correct___isomorphic 
       nfa_minimise_Brzozowski_correct___isomorphic_Brzozowski(2) 
       nfa_minimise_Hopcroft_correct___isomorphic
       dfa_minimise_Hopcroft_correct___isomorphic
       right_quotient_lists_correct___isomorphic
       nfa_is_wellformed NFA_isomorphic_wf_refl
       NFA_isomorphic_wf___NFA_normalise_states_cong
  end
end
