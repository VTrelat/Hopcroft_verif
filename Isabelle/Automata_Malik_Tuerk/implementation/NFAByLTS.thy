(* TODO: Port to new Collection Framework *)
section "Implementing Finite Automata using Labelled Transition Systems"
theory NFAByLTS
imports "../../Collections/ICF/Collections"
        "../../Accessible_Impl"
        "../Hopcroft_Minimisation"
        "../NFAConstruct"
  LTSSpec LTSGA NFASpec LTS_Impl TripleSetByMap LTSByTripleSetAQQ NFAGA
begin

subsection \<open> Locales for NFAs, DFAs \<close>

record nfa_props =
  nfa_prop_is_complete_deterministic :: bool
  nfa_prop_is_initially_connected :: bool

lemmas nfa_props_fields_def[code, simp] = nfa_props.defs(2)
abbreviation "nfa_props_trivial == nfa_props.fields False False"
abbreviation "nfa_props_connected det == nfa_props.fields det True"
abbreviation "nfa_props_dfa == nfa_props.fields True True"

type_synonym ('q_set, 'a_set, 'd) NFA_impl = 
   "'q_set \<times> 'a_set \<times> 'd \<times> 'q_set \<times> 'q_set \<times> nfa_props"

locale nfa_by_lts_defs = 
  s: StdSet s_ops (* Set operations on states *) +
  l: StdSet l_ops (* Set operations on labels *) +
  d: StdLTS d_ops (* An LTS *) 
  for s_ops::"('q::{automaton_states},'q_set,_) set_ops_scheme"
  and l_ops::"('a,'a_set,_) set_ops_scheme"
  and d_ops::"('q,'a,'d,_) lts_ops_scheme"

context nfa_by_lts_defs
begin

definition nfa_states :: "'q_set \<times> 'a_set \<times> 'd \<times> 'q_set \<times> 'q_set \<times> nfa_props \<Rightarrow> 'q_set" where
  "nfa_states A = fst A"
lemma nfa_states_simp [simp]: "nfa_states (Q, A, D, I, F, flags) = Q" by (simp add: nfa_states_def)

definition nfa_labels :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> 'a_set" where
  "nfa_labels A = fst (snd A)"
lemma nfa_labels_simp [simp]: "nfa_labels (Q, A, D, I, F, flags) = A" by (simp add: nfa_labels_def)

definition nfa_trans :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> 'd" where
  "nfa_trans A = fst (snd (snd A))"
lemma nfa_trans_simp [simp]: "nfa_trans (Q, A, D, I, F, flags) = D" by (simp add: nfa_trans_def)

definition nfa_initial :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> 'q_set" where
  "nfa_initial A = fst (snd (snd (snd A)))"
lemma nfa_initial_simp [simp]: "nfa_initial (Q, A, D, I, F, flags) = I" by (simp add: nfa_initial_def)

definition nfa_accepting :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> 'q_set" where
  "nfa_accepting A = fst (snd (snd (snd (snd A))))"
lemma nfa_accepting_simp [simp]: "nfa_accepting (Q, A, D, I, F, flags) = F" by (simp add: nfa_accepting_def)

definition nfa_props :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> nfa_props" where
  "nfa_props A = (snd (snd (snd (snd (snd A)))))"
lemma nfa_props_simp [simp]: "nfa_props (Q, A, D, I, F, flags) = flags" by (simp add: nfa_props_def)

fun nfa_set_props :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> nfa_props \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl" where
  "nfa_set_props (Q, A, D, I, F, p) p' = (Q, A, D, I, F, p')"

lemmas nfa_selectors_def = nfa_accepting_def nfa_states_def nfa_labels_def nfa_trans_def nfa_initial_def
  nfa_props_def

definition nfa_\<alpha> :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q, 'a) NFA_rec" where
  "nfa_\<alpha> A =
   \<lparr> \<Q> = s.\<alpha> (nfa_states A), 
     \<Sigma> = l.\<alpha> (nfa_labels A), 
     \<Delta> = d.\<alpha> (nfa_trans A),
     \<I> = s.\<alpha> (nfa_initial A), 
     \<F> = s.\<alpha> (nfa_accepting A) \<rparr>"

lemma nfa_\<alpha>_simp [simp] :
  "\<Q> (nfa_\<alpha> A) = s.\<alpha> (nfa_states A) \<and>
   \<Sigma> (nfa_\<alpha> A) = l.\<alpha> (nfa_labels A) \<and>
   \<Delta> (nfa_\<alpha> A) = d.\<alpha> (nfa_trans A) \<and>
   \<I> (nfa_\<alpha> A) = s.\<alpha> (nfa_initial A) \<and>
   \<F> (nfa_\<alpha> A) = s.\<alpha> (nfa_accepting A)"
by (simp add: nfa_\<alpha>_def)

definition nfa_invar_no_props :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> bool" where
  "nfa_invar_no_props A =
   (s.invar (nfa_states A) \<and>
    l.invar (nfa_labels A) \<and>
    d.invar (nfa_trans A) \<and>
    s.invar (nfa_initial A) \<and> 
    s.invar (nfa_accepting A))"

definition nfa_invar_weak :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> bool" where
  "nfa_invar_weak A \<equiv> (nfa_invar_no_props A \<and> NFA (nfa_\<alpha> A))"

definition nfa_invar_props :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> bool" where
  "nfa_invar_props A \<longleftrightarrow>
   (nfa_prop_is_complete_deterministic (nfa_props A) \<longrightarrow> SemiAutomaton_is_complete_deterministic (nfa_\<alpha> A)) \<and>
   (nfa_prop_is_initially_connected (nfa_props A) \<longrightarrow> SemiAutomaton_is_initially_connected (nfa_\<alpha> A))"

definition nfa_invar_weak2 :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> bool" where
  "nfa_invar_weak2 A \<equiv> (nfa_invar_no_props A \<and> nfa_invar_props A)"

lemma nfa_props_trivial_OK: 
  "nfa_props A = nfa_props_trivial \<Longrightarrow> nfa_invar_props A"
unfolding nfa_invar_props_def by simp

lemma nfa_props_trivial_OK_simp[simp]: 
  "nfa_invar_props (Q, A, D, I, F, nfa_props_trivial)"
unfolding nfa_invar_props_def by simp

definition nfa_invar :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> bool" where
  "nfa_invar A \<equiv> (nfa_invar_weak A \<and> nfa_invar_props A)"

lemma nfa_invar_alt_def :
  "nfa_invar A = (nfa_invar_no_props A \<and> NFA (nfa_\<alpha> A) \<and> nfa_invar_props A)"
unfolding nfa_invar_def nfa_invar_weak_def by simp

lemma nfa_invar_full_def :
  "nfa_invar A = 
    (set_op_invar s_ops (nfa_states A) \<and>
     set_op_invar l_ops (nfa_labels A) \<and>
     lts_op_invar d_ops (nfa_trans A) \<and>
     set_op_invar s_ops (nfa_initial A) \<and>
     set_op_invar s_ops (nfa_accepting A) \<and>
     NFA (nfa_\<alpha> A) \<and>
     (nfa_prop_is_complete_deterministic (nfa_props A) \<longrightarrow>
      SemiAutomaton_is_complete_deterministic (nfa_\<alpha> A)) \<and>
     (nfa_prop_is_initially_connected (nfa_props A) \<longrightarrow>
      SemiAutomaton_is_initially_connected (nfa_\<alpha> A)))"
unfolding nfa_invar_alt_def nfa_invar_no_props_def nfa_invar_props_def
by simp

lemma nfa_invar_implies_DFA :
  "nfa_invar A \<Longrightarrow> nfa_prop_is_complete_deterministic (nfa_props A) \<Longrightarrow> DFA (nfa_\<alpha> A)"
unfolding nfa_invar_alt_def DFA_alt_def nfa_invar_props_def by simp

lemma nfa_by_lts_correct [simp]: 
    "nfa nfa_\<alpha> nfa_invar"    
    unfolding nfa_def nfa_invar_alt_def
    by simp

subsection \<open> Constructing Automata \<close>
definition nfa_construct_aux ::
  "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> 'q \<times> 'a list \<times> 'q \<Rightarrow> 
   ('q_set, 'a_set, 'd) NFA_impl" where 
   "nfa_construct_aux = (\<lambda>(Q, A, D, I, F, props) (q1, l, q2).
    (s.ins q1 (s.ins q2 Q), 
     foldl (\<lambda>s x. l.ins x s) A l,
     foldl (\<lambda>d a. d.add q1 a q2 d) D l,
     I, F, props))"

lemma nfa_construct_aux_correct :
fixes q1 q2
assumes invar: "nfa_invar_no_props A"
shows "nfa_invar_no_props (nfa_construct_aux A (q1, l, q2))"
      "nfa_props (nfa_construct_aux A (q1, l, q2)) = nfa_props A"
      "nfa_\<alpha> (nfa_construct_aux A (q1, l, q2)) =
              construct_NFA_aux (nfa_\<alpha> A) (q1, l, q2)"
proof -
  obtain QL AL DL IL FL p where A_eq[simp]: "A = (QL, AL, DL, IL, FL, p)" by (cases A, blast)
  
  have AL_OK: "l.invar AL \<Longrightarrow> 
               l.invar (foldl (\<lambda>s x. l.ins x s) AL l) \<and>
               l.\<alpha> (foldl (\<lambda>s x. l.ins x s) AL l) = l.\<alpha> AL \<union> set l"
    by (induct l arbitrary: AL, simp_all add: l.correct)

  have DL_OK : "d.invar DL \<Longrightarrow>
                (d.invar (foldl (\<lambda>d a. d.add q1 a q2 d) DL l)) \<and>
                d.\<alpha> (foldl (\<lambda>d a. d.add q1 a q2 d) DL l) =
                d.\<alpha> DL \<union> {(q1, a, q2) |a. a \<in> set l}"
  proof (induct l arbitrary: DL)
    case Nil thus ?case by simp
  next
    case (Cons a l DL)
    note ind_hyp = Cons(1)
    note invar = Cons(2)

    let ?DL' = "d.add q1 a q2 DL"
    have DL'_props: "d.invar ?DL'" "d.\<alpha> ?DL' = insert (q1, a, q2) (d.\<alpha> DL)"
      using d.lts_add_correct[OF invar, of q1 a q2] by simp_all
        
    with ind_hyp[OF DL'_props(1)] show ?case by (auto simp add: DL'_props(2))
  qed

  from AL_OK DL_OK invar 
  show "nfa_\<alpha> (nfa_construct_aux A (q1, l, q2)) = construct_NFA_aux (nfa_\<alpha> A) (q1, l, q2)"
       "nfa_invar_no_props (nfa_construct_aux A (q1, l, q2))"
      "nfa_props (nfa_construct_aux A (q1, l, q2)) = nfa_props A"
    by (simp_all add: nfa_construct_aux_def nfa_\<alpha>_def s.correct nfa_invar_no_props_def nfa_invar_def)
qed

fun nfa_construct_gen where
   "nfa_construct_gen p (QL, AL, DL, IL, FL) =
    foldl nfa_construct_aux 
     (s.from_list (QL @ IL @ FL),
      l.from_list AL,
      d.empty (),
      s.from_list IL,
      s.from_list FL, p) DL"
declare nfa_construct_gen.simps [simp del]

lemma nfa_construct_correct_gen :
fixes ll :: "'q list \<times> 'a list \<times> ('q \<times> 'a list \<times> 'q) list \<times> 'q list \<times> 'q list"
shows "nfa_invar_no_props (nfa_construct_gen p ll)"
      "nfa_props (nfa_construct_gen p ll) = p"
      "nfa_\<alpha> (nfa_construct_gen p ll) = NFA_construct ll" 
proof -
  obtain QL AL DL IL FL where l_eq[simp]: "ll = (QL, AL, DL, IL, FL)" by (cases ll, blast)
  let ?A = "(s.from_list (QL @ IL @ FL), l.from_list AL,  d.empty (), s.from_list IL, s.from_list FL, p)"

  have A_invar: "nfa_invar_no_props ?A" unfolding nfa_invar_full_def 
    by (simp add: s.correct l.correct d.correct_common nfa_invar_no_props_def)
  have A_\<alpha>: "nfa_\<alpha> ?A = \<lparr>\<Q> = set (QL @ IL @ FL), \<Sigma> = set AL, \<Delta> = {}, \<I> = set IL, \<F> = set FL\<rparr>"
    by (simp add: nfa_\<alpha>_def s.correct d.correct_common l.correct)

  { fix A DL'
    have " nfa_invar_no_props A \<Longrightarrow> 
        nfa_invar_no_props (foldl nfa_construct_aux A DL') \<and>
        nfa_props (foldl nfa_construct_aux A DL') = nfa_props A \<and>
        nfa_\<alpha> (foldl nfa_construct_aux A DL') =
        foldl construct_NFA_aux (nfa_\<alpha> A) DL'"
    proof (induct DL' arbitrary: A)
      case Nil thus ?case by simp
    next
      case (Cons qlq DL')
      note ind_hyp = Cons(1)
      note invar_A = Cons(2)

      let ?A' = "nfa_construct_aux A qlq"
      obtain q1 l q2 where qlq_eq[simp]: "qlq = (q1, l, q2)" by (metis prod.exhaust)

      note aux_correct = nfa_construct_aux_correct [of A q1 l q2, OF invar_A]

      from ind_hyp[of ?A'] aux_correct
      show ?case by simp
    qed
  } note step = this [of ?A DL]

  with A_\<alpha> A_invar show "nfa_\<alpha> (nfa_construct_gen p ll) = NFA_construct ll" 
                     and "nfa_invar_no_props (nfa_construct_gen p ll)" 
                     and "nfa_props (nfa_construct_gen p ll) = p" 
    by (simp_all add: nfa_construct_gen.simps NFA_construct_fold_def d.correct_common
                      nfa_invar_alt_def nfa_props_trivial_OK)
qed

definition nfa_construct where
   "nfa_construct = nfa_construct_gen nfa_props_trivial"

lemma nfa_construct_correct :
  "nfa_from_list nfa_\<alpha> nfa_invar nfa_construct"
proof -
   from nfa_construct_correct_gen [of nfa_props_trivial]
   show ?thesis
     unfolding nfa_construct_def
     apply (intro nfa_from_list.intro nfa_by_lts_correct nfa_from_list_axioms.intro)
     apply (simp_all add: nfa_invar_alt_def nfa_invar_props_def NFA_construct___is_well_formed)
   done
qed

definition dfa_construct where
   "dfa_construct = nfa_construct_gen (nfa_props.fields True False)"

lemma dfa_construct_correct :
  "dfa_from_list nfa_\<alpha> nfa_invar dfa_construct"
proof -
   from nfa_construct_correct_gen [of "(nfa_props.fields True False)"]
   show ?thesis
     unfolding dfa_construct_def
     apply (intro dfa_from_list.intro nfa_by_lts_correct dfa_from_list_axioms.intro)
     apply (simp_all add: nfa_invar_alt_def nfa_invar_props_def DFA_alt_def)
   done
qed


subsection \<open> Destructing Automata \<close>

fun nfa_destruct :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _" where
   "nfa_destruct (Q, A, D, I, F, p) =
    (s.to_list Q,
     l.to_list A,
     d.to_collect_list D,
     s.to_list I,
     s.to_list F)"

lemma nfa_destruct_correct :
  "nfa_to_list nfa_\<alpha> nfa_invar nfa_destruct"
proof (intro nfa_to_list.intro nfa_by_lts_correct nfa_to_list_axioms.intro)
  fix n
  assume invar: "nfa_invar n"
  obtain QL AL DL IL FL p where l_eq[simp]: "n = (QL, AL, DL, IL, FL, p)" by (cases n, blast)

  from invar have invar_weak: "nfa_invar_no_props n" and wf: "NFA (nfa_\<alpha> n)"
    unfolding nfa_invar_alt_def by simp_all
  interpret NFA "nfa_\<alpha> n" by fact

  have aux: "\<And>l::'a list. l \<noteq> [] \<Longrightarrow> (\<exists>a. a \<in> set l)" by auto
  from invar_weak \<F>_consistent \<I>_consistent \<Delta>_consistent d.lts_to_collect_list_correct(1)[of DL]
       d.lts_to_collect_list_correct(3)[of DL]
  show "NFA_construct (nfa_destruct n) = nfa_\<alpha> n"
    apply (simp add: nfa_\<alpha>_def NFA_construct_alt_def nfa_invar_no_props_def s.correct l.correct d.correct_common)
    apply (auto simp add: set_eq_iff)
    apply (metis aux)
    apply (metis aux)
    apply (metis)
  done
qed

fun nfa_destruct_simple :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _" where
   "nfa_destruct_simple (Q, A, D, I, F, p) =
    (s.to_list Q,
     l.to_list A,
     d.to_list D,
     s.to_list I,
     s.to_list F)"

lemma nfa_destruct_simple_correct :
  "nfa_to_list_simple nfa_\<alpha> nfa_invar nfa_destruct_simple"
proof (intro nfa_to_list_simple.intro nfa_by_lts_correct nfa_to_list_simple_axioms.intro)
  fix n
  assume invar: "nfa_invar n"
  obtain QL AL DL IL FL p where l_eq[simp]: "n = (QL, AL, DL, IL, FL, p)" by (cases n, blast)

  from invar have invar_weak: "nfa_invar_no_props n" and wf: "NFA (nfa_\<alpha> n)"
    unfolding nfa_invar_alt_def by simp_all
  interpret NFA "nfa_\<alpha> n" by fact

  have aux: "\<And>l::'a list. l \<noteq> [] \<Longrightarrow> (\<exists>a. a \<in> set l)" by auto
  from invar_weak \<F>_consistent \<I>_consistent \<Delta>_consistent 
  show "NFA_construct_simple (nfa_destruct_simple n) = nfa_\<alpha> n"
    apply (simp add: nfa_\<alpha>_def NFA_construct_alt_def 
                     nfa_invar_no_props_def s.correct l.correct d.correct_common)
    apply (auto simp add: set_eq_iff image_iff Bex_def)
  done
qed

subsection \<open> Computing Statistics \<close>

  fun nfa_states_no :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _" where
     "nfa_states_no (Q, A, D, I, F, p) = s.size Q"

  fun nfa_labels_no :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _" where
     "nfa_labels_no (Q, A, D, I, F, p) = l.size A"

  fun nfa_trans_no :: "_ \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _" where
     "nfa_trans_no it (Q, A, D, I, F, p) = iterate_size (it D)"

  fun nfa_initial_no :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _" where
     "nfa_initial_no (Q, A, D, I, F, p) = s.size I"

  fun nfa_final_no :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _" where
     "nfa_final_no (Q, A, D, I, F, p) = s.size F"

  lemma nfa_stats_correct :
  assumes it_OK: "lts_iterator d.\<alpha> d.invar it"
  shows
    "nfa_stats nfa_\<alpha> nfa_invar 
        nfa_states_no nfa_labels_no (nfa_trans_no it) nfa_initial_no nfa_final_no"
  proof -
    note it_OK' = iterate_size_correct[OF lts_iterator.lts_it_correct [OF it_OK]]

    from it_OK' show ?thesis
      by (simp add: nfa_stats_def nfa_stats_axioms_def s.correct l.correct
                    nfa_invar_full_def)
  qed

subsection \<open> Acceptance \<close>

definition accept_nfa_impl :: "_ \<Rightarrow> _ \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> 'a list \<Rightarrow> _" where
   "accept_nfa_impl s_it succ_it A w = 
    (\<not>(s.disjoint (is_reachable_breath_impl s.empty s.ins s_it succ_it
      (nfa_trans A) w (nfa_initial A)) (nfa_accepting A)))"

lemma accept_nfa_impl_code :
  "accept_nfa_impl s_it succ_it = (\<lambda>(Q, A, D, I, F, p) w.
   (\<not> set_op_disjoint s_ops (foldl
          (\<lambda>Q a. s_it Q (\<lambda>_. True)
                  (\<lambda>q. succ_it D q a (\<lambda>_. True)
                        (set_op_ins s_ops))
                  (set_op_empty s_ops ())) I w) F))"
unfolding accept_nfa_impl_def[abs_def] nfa_selectors_def snd_conv fst_conv 
          is_reachable_breath_impl_alt_def
by (simp add: fun_eq_iff split_def)

lemma accept_nfa_impl_correct :
assumes s_it: "set_iteratei s.\<alpha> s.invar s_it"
    and succ_it: "lts_succ_it d.\<alpha> d.invar succ_it"
shows "nfa_accept nfa_\<alpha> nfa_invar (accept_nfa_impl s_it succ_it)"
proof (intro nfa_accept.intro nfa_by_lts_correct nfa_accept_axioms.intro)
  fix n w
  assume invar_n: "nfa_invar n"

  from invar_n have 
    "s.invar (nfa_initial n)" "s.invar (nfa_accepting n)" "d.invar (nfa_trans n)"
    "NFA (nfa_\<alpha> n)"
    unfolding nfa_invar_full_def by simp_all

  from is_reachable_breath_impl_correct [OF s.set_empty_axioms s.set_ins_axioms s_it succ_it,
    OF `d.invar (nfa_trans n)` `s.invar (nfa_initial n)`, of w] `s.invar (nfa_accepting n)`
  show "accept_nfa_impl s_it succ_it n w = NFA_accept (nfa_\<alpha> n) w"
    unfolding accept_nfa_impl_def
    by (simp add: s.correct NFA.NFA_accept_det_def[OF `NFA (nfa_\<alpha> n)`])
qed


definition accept_dfa_impl where
   "accept_dfa_impl A w = 
    s.bex (nfa_initial A) (\<lambda>q. case (d.DLTS_reach_impl (nfa_trans A) q w) of None \<Rightarrow> False
      | Some q' \<Rightarrow> s.memb q' (nfa_accepting A))"

lemma accept_dfa_impl_code :
  "accept_dfa_impl = (\<lambda>(Q, A, D, I, F, p) w. 
   set_op_bex s_ops I
     (\<lambda>q. case foldli w (\<lambda>q_opt. q_opt \<noteq> None)
                (\<lambda>\<sigma> q_opt. lts_op_succ d_ops D (the q_opt) \<sigma>)
                (Some q) of
          None \<Rightarrow> False | Some q' \<Rightarrow> set_op_memb s_ops q' F))"
unfolding accept_dfa_impl_def[abs_def] nfa_selectors_def fst_conv snd_conv
          d.DLTS_reach_impl_alt_def
  by (simp add: fun_eq_iff split_def)
  

lemma accept_dfa_impl_correct :
shows "dfa_accept nfa_\<alpha> nfa_invar accept_dfa_impl"
proof (intro dfa_accept.intro nfa_by_lts_correct dfa_accept_axioms.intro)
  fix n w
  assume dfa_n: "DFA (nfa_\<alpha> n)" and invar_n: "nfa_invar n"

  from invar_n have invar_IF: "s.invar (nfa_accepting n)" "s.invar (nfa_initial n)"
                and invar_l: "d.invar (nfa_trans n)"
    unfolding nfa_invar_full_def by simp_all

  from dfa_n have \<i>_intro: "s.\<alpha> (nfa_initial n) = {\<i> (nfa_\<alpha> n)}"
    using DetSemiAutomaton.\<I>_is_set_\<i> [of "nfa_\<alpha> n"]
    by (simp add: DFA_alt_def3)

  have \<delta>_intro: "(LTS_to_DLTS (d.\<alpha> (nfa_trans n))) = \<delta> (nfa_\<alpha> n)"
    unfolding \<delta>_def by simp
   
  from dfa_n have det_l: "LTS_is_deterministic (d.\<alpha> (nfa_trans n))"
    unfolding DFA_alt_def SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def
    by simp

  show "accept_dfa_impl n w = NFA_accept (nfa_\<alpha> n) w" 
    unfolding accept_dfa_impl_def DFA.DFA_accept_alt_def [OF dfa_n] 
    by (simp add: s.correct invar_IF \<i>_intro d.DLTS_reach_impl_correct [OF invar_l det_l]
                     \<delta>_intro
                split: option.split)
qed

definition accept_impl where
  "accept_impl s_it succ_it A w =
   (if (nfa_prop_is_complete_deterministic (nfa_props A)) then 
      (accept_dfa_impl A w) else (accept_nfa_impl s_it succ_it A w))"

lemma accept_impl_correct :
  assumes s_it: "set_iteratei s.\<alpha> s.invar s_it"
      and succ_it: "lts_succ_it d.\<alpha> d.invar succ_it"
  shows "nfa_accept nfa_\<alpha> nfa_invar (accept_impl s_it succ_it)"
proof (intro nfa_accept.intro nfa_by_lts_correct nfa_accept_axioms.intro)
  fix A w
  assume invar_A: "nfa_invar A"
  show "accept_impl s_it succ_it A w = NFA_accept (nfa_\<alpha> A) w" 
  proof (cases "nfa_prop_is_complete_deterministic (nfa_props A)")
    case True note is_det = this
    with nfa_invar_implies_DFA[OF invar_A] 
    have dfa_A: "DFA (nfa_\<alpha> A)" by simp

    from dfa_accept.accept_correct[OF accept_dfa_impl_correct, OF invar_A dfa_A, of w] is_det
    show ?thesis by (simp add: accept_impl_def)
  next
    case False note not_det = this
    from nfa_accept.accept_correct[OF accept_nfa_impl_correct, OF s_it succ_it invar_A, of w] not_det
    show ?thesis by (simp add: accept_impl_def)
  qed
qed



subsection \<open> Remove states \<close>

fun remove_states_impl :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> 'q_set \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl" where
  "remove_states_impl (Q, A, D, I, F, p) S =
   (s.diff Q S, A, 
    d.filter (\<lambda>q. \<not>(s.memb q S)) (\<lambda>_. True) (\<lambda>q. \<not>(s.memb q S)) (\<lambda>_. True) D,
    s.diff I S, s.diff F S, nfa_props_trivial)"

lemma remove_states_impl_correct :
  "nfa_remove_states nfa_\<alpha> nfa_invar s.\<alpha> s.invar remove_states_impl"
proof (intro nfa_remove_states.intro nfa_remove_states_axioms.intro nfa_by_lts_correct)
  fix n S
  assume invar_S: "s.invar S"
  assume invar: "nfa_invar n"
  obtain QL AL DL IL FL p where l_eq[simp]: "n = (QL, AL, DL, IL, FL, p)" by (cases n, blast)

  from invar have invar_no_props: "nfa_invar_no_props n" and wf: "NFA (nfa_\<alpha> n)" 
              and invar_props: "nfa_invar_props n"
    unfolding nfa_invar_alt_def by simp_all
  

  from invar_no_props invar_S invar_props
  have "nfa_invar_no_props (remove_states_impl n S) \<and>
        nfa_invar_props (remove_states_impl n S) \<and> 
        nfa_\<alpha> (remove_states_impl n S) = NFA_remove_states (nfa_\<alpha> n) (s.\<alpha> S)"
    by (simp add: nfa_invar_props_def nfa_invar_no_props_def nfa_\<alpha>_def s.correct NFA_remove_states_full_def d.correct_common)

  thus "nfa_\<alpha> (remove_states_impl n S) = NFA_remove_states (nfa_\<alpha> n) (s.\<alpha> S)" 
       "nfa_invar (remove_states_impl n S)"
    unfolding nfa_invar_alt_def 
    using NFA_remove_states___is_well_formed[OF wf, of "s.\<alpha> S"]
      by (simp_all add: NFA_remove_states___is_well_formed)
qed


subsection \<open> Rename states \<close>

fun rename_states_fixed_impl :: "_ \<Rightarrow> _ \<Rightarrow> bool \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q_set2, 'a_set, 'd2) NFA_impl" where
  "rename_states_fixed_impl im im2 det (Q, A, D, I, F, p) = 
   (im Q, A, im2 D, im I, im F, nfa_props.fields det (nfa_prop_is_initially_connected p))"
declare rename_states_fixed_impl.simps[simp del]

definition rename_states_impl :: "_ \<Rightarrow> _ \<Rightarrow> bool \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q \<Rightarrow> 'q) \<Rightarrow> ('q_set2, 'a_set, 'd2) NFA_impl" where
  "rename_states_impl im im2 det A f =
   rename_states_fixed_impl (im f) (im2 (\<lambda>qaq::('q \<times> 'a \<times> 'q). (f (fst qaq), fst (snd qaq), f (snd (snd qaq))))) 
       det A"

lemma rename_states_impl_code :
  "rename_states_impl im im2 det (Q, A, D, I, F, p) f = 
   (im f Q, A,
     im2 (\<lambda>(q, a, q'). (f q, a, f q'))
     D,
     im f I, im f F,
     nfa_props.fields det
      (nfa_prop_is_initially_connected p))"
unfolding rename_states_impl_def rename_states_fixed_impl.simps split_def by simp

lemma rename_states_fixed_impl_correct :
assumes wf_target: "nfa_by_lts_defs s_ops' l_ops d_ops'" 
    and im_OK: "set_image s.\<alpha> s.invar (set_op_\<alpha> s_ops') (set_op_invar s_ops') im"
    and im2_OK: "if det then dlts_rename_states_fixed d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') im2 f
                        else lts_rename_states_fixed d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') im2 f"
    and invar: "nfa_invar n"
    and det_OK: "det \<Longrightarrow> DFA (NFA_rename_states (nfa_\<alpha> n) f)"
shows "nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops' (rename_states_fixed_impl (im f) im2 det n)" (is ?T1)
      "nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops' (rename_states_fixed_impl (im f) im2 det n) =
          NFA_rename_states (nfa_\<alpha> n) f" (is ?T2)
proof -
  obtain QL AL DL IL FL p where n_eq[simp]: "n = (QL, AL, DL, IL, FL, p)" by (cases n, blast)

  interpret s': StdSet s_ops' using wf_target unfolding nfa_by_lts_defs_def by simp
  interpret d': StdLTS d_ops' using wf_target unfolding nfa_by_lts_defs_def by simp
  interpret im: set_image s.\<alpha> s.invar s'.\<alpha> s'.invar im by fact

  from invar have invar_no_props: "nfa_invar_no_props n" and wf: "NFA (nfa_\<alpha> n)" and
                  invar_props: "nfa_invar_props n" 
    unfolding nfa_invar_alt_def by simp_all

  interpret nfa_org: NFA "nfa_\<alpha> n" by fact

  let ?nfa_\<alpha>' = "nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops'"
  let ?nfa_invar_no_props' = "nfa_by_lts_defs.nfa_invar_no_props s_ops' l_ops d_ops'"
  let ?nfa_invar' = "nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops'"


  have image_trans_eq: "((\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq)))) ` lts_op_\<alpha> d_ops DL) =
                  {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> lts_op_\<alpha> d_ops DL}"
    by (auto simp add: image_iff Bex_def) metis+

  have im2_OK': "lts_op_invar d_ops' (im2 DL) \<and>
                 lts_op_\<alpha> d_ops' (im2 DL) =
                   {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> lts_op_\<alpha> d_ops DL}" 
  proof (cases det) 
    case False
    with im2_OK have im2_not_det: "lts_rename_states_fixed (lts_op_\<alpha> d_ops)
     (lts_op_invar d_ops) (lts_op_\<alpha> d_ops')
     (lts_op_invar d_ops') im2 f" by simp

    from lts_image_fixed.lts_image_fixed_correct [OF 
      im2_not_det[unfolded lts_rename_states_fixed_def], of DL] invar_no_props
    show ?thesis 
      unfolding nfa_invar_no_props_def image_trans_eq by simp
  next
    case True note det_eq_True = this

    with im2_OK have im2_det: "dlts_rename_states_fixed (lts_op_\<alpha> d_ops)
     (lts_op_invar d_ops) (lts_op_\<alpha> d_ops')
     (lts_op_invar d_ops') im2 f" by simp

    from det_OK[OF det_eq_True] have det_trans: "LTS_is_deterministic
          {(f s1, a, f s2) |s1 a s2. (s1, a, s2) \<in> lts_op_\<alpha> d_ops DL}"
      unfolding DFA_alt_def SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def
                NFA_rename_states_full_def
      by simp

    from dlts_image_fixed.dlts_image_fixed_correct [OF 
      im2_det[unfolded dlts_rename_states_fixed_def], of DL]  invar_no_props det_trans
    show ?thesis 
      unfolding nfa_invar_no_props_def image_trans_eq by simp
  qed

  from invar_no_props im2_OK'
  have "?nfa_invar_no_props' (rename_states_fixed_impl (im f) im2 det n) \<and> 
        ?nfa_\<alpha>' (rename_states_fixed_impl (im f) im2 det n) = NFA_rename_states (nfa_\<alpha> n) f"
    by (simp add: nfa_by_lts_defs.nfa_\<alpha>_def[OF wf_target]
                  nfa_by_lts_defs.nfa_invar_no_props_def [OF wf_target]
                  nfa_by_lts_defs.nfa_selectors_def [OF wf_target]
                  nfa_invar_no_props_def rename_states_fixed_impl.simps
                  s.correct NFA_rename_states_full_def d.correct_common
                  im.image_correct)

  thus "?nfa_\<alpha>' (rename_states_fixed_impl (im f) im2 det n) = NFA_rename_states (nfa_\<alpha> n) f" 
       "?nfa_invar' (rename_states_fixed_impl (im f) im2 det n)"
    unfolding nfa_by_lts_defs.nfa_invar_alt_def [OF wf_target] 
    using NFA_rename_states___is_well_formed[OF wf, of f]
          SemiAutomaton_is_initially_connected___NFA_rename_states [of "nfa_\<alpha> n" f]
          invar_props det_OK
      apply (simp_all add: NFA_remove_states___is_well_formed)
      apply (simp add: nfa_by_lts_defs.nfa_invar_props_def[OF wf_target])
      apply (simp add: rename_states_fixed_impl.simps nfa_invar_props_def
                       nfa_by_lts_defs.nfa_invar_props_def[OF wf_target]
                       nfa_by_lts_defs.nfa_selectors_def[OF wf_target] DFA_alt_def)
  done
qed
 
lemma rename_states_impl_correct :
assumes wf_target: "nfa_by_lts_defs s_ops' l_ops d_ops'" 
assumes im_OK: "set_image s.\<alpha> s.invar (set_op_\<alpha> s_ops') (set_op_invar s_ops') im"
assumes im2_OK: "lts_image d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') im2"
shows "nfa_rename_states nfa_\<alpha> nfa_invar 
           (nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops') 
           (nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops') 
           (rename_states_impl im im2 False)"
proof (intro nfa_rename_states.intro nfa_rename_states_axioms.intro 
             nfa_by_lts_defs.nfa_by_lts_correct)
  show "nfa_by_lts_defs s_ops l_ops d_ops" by (fact nfa_by_lts_defs_axioms)
  show "nfa_by_lts_defs s_ops' l_ops d_ops'" by (fact wf_target)

  fix n f
  assume invar: "nfa_invar n"
  let ?res = "rename_states_impl im im2 False n f"
  let ?nfa_\<alpha>' = "nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops'"
  let ?nfa_invar' = "nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops'"
  let ?f' = "(\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq))))"

  from rename_states_fixed_impl_correct[OF wf_target im_OK _ invar, of False "im2 ?f'" f]
       im2_OK
  show "?nfa_\<alpha>' ?res = NFA_rename_states (nfa_\<alpha> n) f" 
       "?nfa_invar' ?res" 
    by (simp_all add: lts_rename_states_fixed_def lts_image_alt_def rename_states_impl_def)
qed

lemma rename_states_impl_correct_dfa :
assumes wf_target: "nfa_by_lts_defs s_ops' l_ops d_ops'" 
assumes im_OK: "set_image s.\<alpha> s.invar (set_op_\<alpha> s_ops') (set_op_invar s_ops') im"
assumes im2_OK: "dlts_image d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') im2"
shows "dfa_rename_states nfa_\<alpha> nfa_invar 
           (nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops') 
           (nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops') 
           (rename_states_impl im im2 True)"
proof (intro dfa_rename_states.intro dfa_rename_states_axioms.intro 
             nfa_by_lts_defs.nfa_by_lts_correct)
  show "nfa_by_lts_defs s_ops l_ops d_ops" by (fact nfa_by_lts_defs_axioms)
  show "nfa_by_lts_defs s_ops' l_ops d_ops'" by (fact wf_target)

  fix n f
  assume invar: "nfa_invar n"
  let ?res = "rename_states_impl im im2 True n f"
  assume wf_res: "DFA (NFA_rename_states (nfa_\<alpha> n) f)"
  let ?nfa_\<alpha>' = "nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops'"
  let ?nfa_invar' = "nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops'"
  let ?f' = "(\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq))))"

  from rename_states_fixed_impl_correct[OF wf_target im_OK _ invar, of True "im2 ?f'" f] 
       wf_res im2_OK
  show "?nfa_\<alpha>' ?res = NFA_rename_states (nfa_\<alpha> n) f" 
       "?nfa_invar' ?res" 
    by (simp_all add: rename_states_impl_def dlts_image_alt_def
                      dlts_rename_states_fixed_def) 
qed

lemma rename_states_impl_correct___self :
assumes im_OK: "set_image s.\<alpha> s.invar s.\<alpha> s.invar im"
shows "nfa_rename_states nfa_\<alpha> nfa_invar
           nfa_\<alpha> nfa_invar
           (rename_states_impl im d.image False)"
apply (rule rename_states_impl_correct)
apply (simp_all add: nfa_by_lts_defs_axioms im_OK d.lts_image_axioms)
done

lemma rename_states_impl_correct_dfa___self :
assumes im_OK: "set_image s.\<alpha> s.invar s.\<alpha> s.invar im"
shows "dfa_rename_states nfa_\<alpha> nfa_invar
           nfa_\<alpha> nfa_invar
           (rename_states_impl im d.image True)"
apply (rule rename_states_impl_correct_dfa)
apply (simp_all add: nfa_by_lts_defs_axioms im_OK d.lts_image_axioms dlts_image_sublocale)
done

subsection \<open> Rename labels \<close>

fun rename_labels_fixed_impl :: "_ \<Rightarrow> bool \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> _ \<Rightarrow> ('q_set, 'a2_set, 'd) NFA_impl" where
  "rename_labels_fixed_impl im det (Q, A, D, I, F, p) A' = 
   (Q, A', im D, I, F, nfa_props.fields det (nfa_prop_is_initially_connected p))"
declare rename_labels_fixed_impl.simps[simp del]

definition rename_labels_impl_gen where
  "rename_labels_impl_gen im det A A' (f::'a \<Rightarrow> 'a2) =
   rename_labels_fixed_impl (im (\<lambda>qaq::('q \<times> 'a \<times> 'q). (fst qaq, f (fst (snd qaq)), snd (snd qaq)))) 
       det A A'"

lemma rename_labels_impl_gen_code :
  "rename_labels_impl_gen im det (Q, A, D, I, F, p) A' f = 
   (Q, A',
    im (\<lambda>(q, a, q'). (q, f a, q'))
    D, I, F,
    nfa_props.fields det (nfa_prop_is_initially_connected p))"
unfolding rename_labels_fixed_impl.simps rename_labels_impl_gen_def split_def by simp

definition rename_labels_impl where
  "rename_labels_impl im im2 det = (\<lambda>(Q, A, D, I, F) f.
   rename_labels_impl_gen im det (Q, A, D, I, F) (im2 f A) f)"

lemma rename_labels_fixed_impl_correct :
fixes l_ops' :: "('a2, 'a2_set, _) set_ops_scheme"
assumes wf_target: "nfa_by_lts_defs s_ops l_ops' d_ops'" 
assumes im_OK: "lts_rename_labels_fixed d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') im f"
    and invar: "nfa_invar n"
    and A_OK : "set_op_invar l_ops' A" "set_op_\<alpha> l_ops' A = f ` \<Sigma> (nfa_\<alpha> n)" 
    and det_OK: "det \<Longrightarrow> DFA (SemiAutomaton_rename_labels (nfa_\<alpha> n) f)"
shows "nfa_by_lts_defs.nfa_invar s_ops l_ops' d_ops' (rename_labels_fixed_impl im det n A)" (is ?T1)
      "nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops' d_ops'(rename_labels_fixed_impl im det n A) =
       SemiAutomaton_rename_labels (nfa_\<alpha> n) f" (is ?T2)
proof - 
  obtain QL AL DL IL FL p where n_eq[simp]: "n = (QL, AL, DL, IL, FL, p)" by (cases n, blast)

  interpret d': StdLTS d_ops' using wf_target unfolding nfa_by_lts_defs_def by simp

  from invar have invar_no_props: "nfa_invar_no_props n" and wf: "NFA (nfa_\<alpha> n)" and
                  invar_props: "nfa_invar_props n" 
    unfolding nfa_invar_alt_def by simp_all

  interpret nfa_org: NFA "nfa_\<alpha> n" by fact

  let ?nfa_\<alpha>' = "nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops' d_ops'"
  let ?nfa_invar_no_props' = "nfa_by_lts_defs.nfa_invar_no_props s_ops l_ops' d_ops'"
  let ?nfa_invar' = "nfa_by_lts_defs.nfa_invar s_ops l_ops' d_ops'"

  from invar_no_props A_OK
       lts_image_fixed.lts_image_fixed_correct [OF im_OK[unfolded lts_rename_labels_fixed_def]]
  have "?nfa_invar_no_props' (rename_labels_fixed_impl im det n A) \<and> 
        ?nfa_\<alpha>' (rename_labels_fixed_impl im det n A) = SemiAutomaton_rename_labels (nfa_\<alpha> n) f"
    apply (simp add: nfa_by_lts_defs.nfa_\<alpha>_def[OF wf_target]
                     nfa_\<alpha>_def
                     nfa_by_lts_defs.nfa_invar_no_props_def [OF wf_target]
                     nfa_by_lts_defs.nfa_selectors_def [OF wf_target]
                     nfa_invar_no_props_def rename_labels_fixed_impl.simps 
                     s.correct SemiAutomaton_rename_labels_def d.correct_common)
    apply (auto simp add: image_iff Bex_def)
  done
  thus "?nfa_\<alpha>' (rename_labels_fixed_impl im det n A) = SemiAutomaton_rename_labels (nfa_\<alpha> n) f" 
       "?nfa_invar' (rename_labels_fixed_impl im det n A)"
    unfolding nfa_by_lts_defs.nfa_invar_alt_def [OF wf_target] 
    using NFA.NFA_rename_labels___is_well_formed[OF wf, of f]
          SemiAutomaton_is_initially_connected___SemiAutomaton_rename_labels [of "nfa_\<alpha> n" f]
          invar_props det_OK
      apply (simp_all)
      apply (simp add: nfa_by_lts_defs.nfa_invar_props_def[OF wf_target])
      apply (simp add: rename_labels_fixed_impl.simps nfa_invar_props_def
                       nfa_by_lts_defs.nfa_invar_props_def[OF wf_target]
                       nfa_by_lts_defs.nfa_selectors_def[OF wf_target] DFA_alt_def)
  done
qed

lemma rename_labels_impl_gen_correct :
fixes l_ops' :: "('a2, 'a2_set, _) set_ops_scheme"
assumes wf_target: "nfa_by_lts_defs s_ops l_ops' d_ops'" 
assumes im_OK: "lts_image d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') im"
shows "nfa_rename_labels_gen nfa_\<alpha> nfa_invar 
           (nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops' d_ops') 
           (nfa_by_lts_defs.nfa_invar s_ops l_ops' d_ops')
           (set_op_\<alpha> l_ops') (set_op_invar l_ops') 
           (rename_labels_impl_gen im False)"
proof (intro nfa_rename_labels_gen.intro nfa_rename_labels_gen_axioms.intro 
             nfa_by_lts_defs.nfa_by_lts_correct)
  show "nfa_by_lts_defs s_ops l_ops d_ops" by (fact nfa_by_lts_defs_axioms)
  show "nfa_by_lts_defs s_ops l_ops' d_ops'" by (fact wf_target)

  interpret l': StdSet l_ops' using wf_target unfolding nfa_by_lts_defs_def by simp
  interpret d': StdLTS d_ops' using wf_target unfolding nfa_by_lts_defs_def by simp

  fix n A f
  assume invar: "nfa_invar n"
  assume A_OK: "l'.invar A" "l'.\<alpha> A = f ` \<Sigma> (nfa_\<alpha> n)"

  let ?res = "rename_labels_impl_gen im False n A f"
  let ?nfa_\<alpha>' = "nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops' d_ops'"
  let ?nfa_invar' = "nfa_by_lts_defs.nfa_invar s_ops l_ops' d_ops'"
  let ?f' = "(\<lambda>qaq. (fst qaq, f (fst (snd qaq)), snd (snd qaq)))"

  from rename_labels_fixed_impl_correct[OF wf_target _ invar A_OK, of "im ?f'" False] im_OK
  show "?nfa_\<alpha>' ?res = SemiAutomaton_rename_labels (nfa_\<alpha> n) f" 
       "?nfa_invar' ?res" 
    by (simp_all add: rename_labels_impl_gen_def lts_image_alt_def
                      lts_rename_labels_fixed_def) 
qed

lemma rename_labels_impl_correct :
fixes l_ops' :: "('a2, 'a2_set, _) set_ops_scheme"
assumes wf_target: "nfa_by_lts_defs s_ops l_ops' d_ops'" 
assumes im_OK: "lts_image d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') im"
assumes im2_OK: "set_image l.\<alpha> l.invar (set_op_\<alpha> l_ops') (set_op_invar l_ops') im2"
shows "nfa_rename_labels nfa_\<alpha> nfa_invar 
           (nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops' d_ops') 
           (nfa_by_lts_defs.nfa_invar s_ops l_ops' d_ops')
           (rename_labels_impl im im2 False)"
proof -
  note labels_gen_OK = rename_labels_impl_gen_correct [OF wf_target im_OK]

  let ?im2' = "\<lambda>(QL, AL, DL, IL, FL) f. im2 f AL"

  have pre_OK: "\<And>n f. nfa_invar n \<Longrightarrow>
       set_op_invar l_ops' (?im2' n f) \<and>
       set_op_\<alpha> l_ops' (?im2' n f) = f ` \<Sigma> (nfa_\<alpha> n)" 
    using im2_OK
    unfolding nfa_invar_full_def set_image_def nfa_invar_def
    by auto

  have post_OK: "(\<lambda>AA f. rename_labels_impl_gen im False AA ((\<lambda>(QL, AL, DL, IL, FL) f. im2 f AL) AA f) f) = 
        rename_labels_impl im im2 False" 
    unfolding rename_labels_impl_def by auto

  from nfa_rename_labels_gen_impl[OF labels_gen_OK, of ?im2', OF pre_OK] 
  show ?thesis unfolding post_OK by simp
qed

lemma rename_labels_impl_correct___self :
assumes im_OK: "set_image l.\<alpha> l.invar l.\<alpha> l.invar im"
shows "nfa_rename_labels 
           nfa_\<alpha> nfa_invar
           nfa_\<alpha> nfa_invar 
           (rename_labels_impl d.image im False)"
by (fact rename_labels_impl_correct [OF nfa_by_lts_defs_axioms d.lts_image_axioms im_OK])

end 

subsection \<open> construct reachable NFA \<close>

locale NFA_construct_reachable_locale = 
  nfa_by_lts_defs s_ops l_ops d_ops +
  qm: StdMap qm_ops (* The index max *) 
  for s_ops::"('q::{automaton_states},'q_set,_) set_ops_scheme"
  and l_ops::"('a,'a_set,_) set_ops_scheme"
  and d_ops::"('q,'a,'d,_) lts_ops_scheme"
  and qm_ops :: "('i, 'q::{automaton_states}, 'm, _) map_ops_scheme" +
  fixes a_\<alpha> :: "'as \<Rightarrow> 'a set" and a_invar :: "'as \<Rightarrow> bool" 
  and add_labels :: "bool \<Rightarrow> 'q \<Rightarrow> 'as \<Rightarrow> 'q \<Rightarrow> 'd \<Rightarrow> 'd"
  and f :: "'q2 \<Rightarrow> 'i"
  and ff :: "'q2_rep \<Rightarrow> 'i"
  and q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2"
  and q2_invar :: "'q2_rep \<Rightarrow> bool" 
begin

definition state_map_\<alpha> where "state_map_\<alpha> \<equiv> (\<lambda>(qm, n::nat). qm.\<alpha> qm \<circ> f)"
definition state_map_invar where "state_map_invar \<equiv> (\<lambda>(qm, n). qm.invar qm \<and> 
         (\<forall>i q. qm.\<alpha> qm i = Some q \<longrightarrow> (\<exists>n' < n. q = states_enumerate n')))"

lemma state_map_extend_thm :
fixes n qm q
defines "qm'' \<equiv> qm.update_dj (f q) (states_enumerate n) qm"
assumes f_inj_on: "inj_on f S"
    and invar_qm_n: "state_map_invar (qm, n)"
    and q_in_S: "q \<in> S"
    and q_nin_dom: "q \<notin> dom (state_map_\<alpha> (qm, n))"
    and map_OK : "NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm, n))"
shows "state_map_invar (qm'', Suc n)"
      "qm.\<alpha> qm'' = qm.\<alpha> qm(f q \<mapsto> states_enumerate n)"
      "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q} (state_map_\<alpha> (qm'', Suc n))"
      "S \<inter> dom (state_map_\<alpha> (qm'', Suc n)) = insert q ((dom (state_map_\<alpha> (qm, n))) \<inter> S)"
proof -
  from invar_qm_n have invar_qm: "qm.invar qm" unfolding state_map_invar_def by simp

  from q_nin_dom have fq_nin_dom_rm: "f q \<notin> dom (qm.\<alpha> qm)"
    unfolding state_map_\<alpha>_def by (simp add: dom_def)

  have qm''_props: "qm.invar qm''" "qm.\<alpha> qm'' = qm.\<alpha> qm(f q \<mapsto> states_enumerate n)"
    using qm.update_dj_correct [OF invar_qm fq_nin_dom_rm]
    by (simp_all add: qm''_def)  
  show "qm.\<alpha> qm'' = qm.\<alpha> qm(f q \<mapsto> states_enumerate n)" by (fact qm''_props(2))

  show invar_qm''_n: "state_map_invar (qm'', Suc n)"
    using invar_qm_n
    by (simp add: state_map_invar_def qm''_props) (metis less_Suc_eq)

  have rm''_q: "state_map_\<alpha> (qm'', Suc n) q = Some (states_enumerate n)"
    unfolding state_map_\<alpha>_def by (simp add: qm''_props)

  have dom_sub: "insert q (dom (state_map_\<alpha> (qm, n))) \<subseteq> dom (state_map_\<alpha> (qm'', Suc n))"
    unfolding state_map_\<alpha>_def 
    by (simp add: subset_iff dom_def qm''_props o_def)

  show dom_eq: "S \<inter> dom (state_map_\<alpha> (qm'', Suc n)) = insert q ((dom (state_map_\<alpha> (qm, n))) \<inter> S)"
      (is "?ls = ?rs")
  proof (intro set_eqI iffI)
    fix q'
    assume "q' \<in> ?rs" 
    with q_in_S dom_sub show "q' \<in> ?ls" by auto
  next
    fix q'
    assume "q' \<in> ?ls"
    hence q'_in_S: "q' \<in> S" and q'_in_dom: "q' \<in> dom (state_map_\<alpha> (qm'', Suc n))" by simp_all

    from f_inj_on q_in_S q'_in_S have fqq'[simp]: "f q' = f q \<longleftrightarrow> q' = q"
      unfolding inj_on_def by auto

    from q'_in_dom have "q' = q \<or> q' \<in> (dom (state_map_\<alpha> (qm, n)))" unfolding state_map_\<alpha>_def
      by (auto simp add: qm''_props o_def dom_def)
    with q'_in_S show "q' \<in> ?rs" by auto
  qed

  have qm''_inj_on: "inj_on (state_map_\<alpha> (qm'', Suc n)) (S \<inter> dom (state_map_\<alpha> (qm'', Suc n)))"
  proof (rule inj_onI)
    fix q' q''
    assume q'_in: "q' \<in> S \<inter> dom (state_map_\<alpha> (qm'', Suc n))"
    assume q''_in: "q'' \<in> S \<inter> dom (state_map_\<alpha> (qm'', Suc n))"
    assume state_map_\<alpha>_eq: "state_map_\<alpha> (qm'', Suc n) q' = state_map_\<alpha> (qm'', Suc n) q''"
 
    { fix q'''
      assume in_dom: "q''' \<in> S \<inter> dom (state_map_\<alpha> (qm, n))"

      from in_dom q_nin_dom have "q''' \<noteq> q" by auto
      with f_inj_on q_in_S in_dom have f_q'''_neq: "f q''' \<noteq> f q"
        unfolding inj_on_def by auto
            
      have prop1: "state_map_\<alpha> (qm'', Suc n) q''' = state_map_\<alpha> (qm, n) q'''" 
        unfolding state_map_\<alpha>_def
        by (simp add: o_def qm''_props f_q'''_neq)

      from invar_qm_n in_dom obtain n' where "n' < n" and 
           "state_map_\<alpha> (qm, n) q''' = Some (states_enumerate n')" 
        unfolding state_map_invar_def dom_def state_map_\<alpha>_def by auto

      with prop1 have prop2: "state_map_\<alpha> (qm'', Suc n) q''' \<noteq> state_map_\<alpha> (qm'', Suc n) q"
        by (simp add: rm''_q states_enumerate_eq)

      note prop1 prop2
    } note qm''_\<alpha>_props = this

    show "q' = q''"
    proof (cases "q' = q")
      case True note q'_eq[simp] = this
      show ?thesis
      proof (cases "q'' = q")
        case True thus ?thesis by simp
      next
        case False with q''_in dom_eq 
        have "q'' \<in> S \<inter> (dom (state_map_\<alpha> (qm, n)))" by simp
        with qm''_\<alpha>_props(2) [of q''] state_map_\<alpha>_eq have "False" by simp
        thus ?thesis ..
      qed
    next
      case False with q'_in dom_eq 
      have q'_in_dom_qm: "q' \<in> (S \<inter> dom (state_map_\<alpha> (qm, n)))" by simp
      show ?thesis
      proof (cases "q'' = q")
        case True 
        with qm''_\<alpha>_props(2) [of q'] state_map_\<alpha>_eq q'_in_dom_qm have "False" by simp
        thus ?thesis ..
      next
        case False with q''_in dom_eq 
        have q''_in_dom_qm: "q'' \<in> (S \<inter> dom (state_map_\<alpha> (qm, n)))" by simp

        from map_OK have "inj_on (state_map_\<alpha> (qm, n)) (S \<inter> dom (state_map_\<alpha> (qm, n)))"
          unfolding NFA_construct_reachable_map_OK_def by simp
        with q''_in_dom_qm q'_in_dom_qm state_map_\<alpha>_eq qm''_\<alpha>_props(1) show ?thesis
          unfolding inj_on_def by auto
      qed
    qed
  qed          

  show map_OK': "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q} (state_map_\<alpha> (qm'', Suc n))"
  proof
    show "{q} \<subseteq> dom (state_map_\<alpha> (qm'', Suc n))"
      by (simp add: rm''_q dom_def)
  next
    fix q' r'
    assume "state_map_\<alpha> (qm, n) q' = Some r'"
    with fq_nin_dom_rm show "state_map_\<alpha> (qm'', Suc n) q' = Some r'"
      unfolding state_map_\<alpha>_def by (auto simp add: qm''_props dom_def)
  next
    show "inj_on (state_map_\<alpha> (qm'', Suc n)) (S \<inter> dom (state_map_\<alpha> (qm'', Suc n)))"
      by (fact qm''_inj_on)
  qed
qed


definition NFA_construct_reachable_init_impl where
  "NFA_construct_reachable_init_impl I =
   foldl (\<lambda>((qm, n), Is) q. ((qm.update_dj (ff q) (states_enumerate n) qm, Suc n),
                             s.ins_dj (states_enumerate n) Is))
         ((qm.empty (), 0), s.empty ()) I"

lemma NFA_construct_reachable_init_impl_correct :
fixes II D
defines "I \<equiv> map q2_\<alpha> II"
defines "S \<equiv> accessible (LTS_forget_labels D) (set I)"
assumes f_inj_on: "inj_on f S"
    and dist_I: "distinct I"
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
shows
   "RETURN (NFA_construct_reachable_init_impl II) \<le> \<Down> 
       ((build_rel state_map_\<alpha> state_map_invar) \<times>\<^sub>r 
              (build_rel s.\<alpha> s.invar)) 
     (SPEC (\<lambda>(rm, I'). 
        NFA_construct_reachable_map_OK (accessible (LTS_forget_labels D) (set I)) Map.empty (set I) rm \<and>
        I' = (the \<circ> rm) ` (set I)))"
proof -
  let ?step = "(\<lambda>((qm, n), Is) q. ((qm.update_dj (ff q) (states_enumerate n) qm, Suc n),
                             s.ins_dj (states_enumerate n) Is))"

  { fix II
    have invar_OK : "\<And>qm n Is qm' n' Is'.
              set (map q2_\<alpha> II) \<subseteq> S \<Longrightarrow>
              distinct (map q2_\<alpha> II) \<Longrightarrow>
              \<forall>q\<in>set II. q2_invar q \<Longrightarrow>      
              dom (state_map_\<alpha> (qm, n)) \<inter> (set (map q2_\<alpha> II)) = {} \<Longrightarrow>
              state_map_invar (qm, n) \<Longrightarrow>
              s.invar Is \<Longrightarrow> 
              (\<And>q. q \<in> s.\<alpha> Is \<Longrightarrow> (\<exists>n' < n. q = states_enumerate n')) \<Longrightarrow>
              NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm, n)) \<Longrightarrow>
              ((qm', n'), Is') = foldl ?step ((qm, n),Is) II \<Longrightarrow>

              s.invar Is' \<and>
              s.\<alpha> Is' = ((the \<circ> (state_map_\<alpha> (qm', n'))) ` (set (map q2_\<alpha> II))) \<union> s.\<alpha> Is \<and>
              state_map_invar (qm', n') \<and>
              NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) (set (map q2_\<alpha> II)) (state_map_\<alpha> (qm', n'))" 
    proof (induct II)
      case Nil thus ?case by (simp add: NFA_construct_reachable_map_OK_def)
    next
      case (Cons q II' qm n Is qm' n' Is')
      from Cons(2) have q_in_S: "q2_\<alpha> q \<in> S" and II'_subset: "set (map q2_\<alpha> II') \<subseteq> S" by simp_all
      from Cons(3) have q_nin_I': "q2_\<alpha> q \<notin> set (map q2_\<alpha> II')" and "distinct (map q2_\<alpha> II')" by simp_all
      from Cons(4) have invar_q: "q2_invar q" and invar_II': "\<forall>q\<in>set II'. q2_invar q" by simp_all
      note dom_qII'_dist = Cons(5)
      note invar_qm_n = Cons(6) 
      note invar_Is = Cons(7) 
      note memb_Is = Cons(8) 
      note map_OK = Cons(9)
      note fold_eq = Cons(10)

      let ?I' = "map q2_\<alpha> II'"
      define qm'' where "qm'' \<equiv> qm.update_dj (ff q) (states_enumerate n) qm"
      define Is'' where "Is'' \<equiv> s.ins_dj (states_enumerate n) Is"

      note ind_hyp = Cons(1) [OF II'_subset `distinct ?I'` invar_II', 
                              of qm'' "Suc n" Is'' qm' n' Is']

      from dom_qII'_dist have q_nin_dom: "q2_\<alpha> q \<notin> dom (state_map_\<alpha> (qm, n))" by auto

      from state_map_extend_thm [OF f_inj_on invar_qm_n q_in_S q_nin_dom map_OK]
      have invar_qm''_n: "state_map_invar (qm'', Suc n)" and
           qm''_alpha: "map_op_\<alpha> qm_ops qm'' = map_op_\<alpha> qm_ops qm(ff q \<mapsto> states_enumerate n)" and
           map_OK': "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q} (state_map_\<alpha> (qm'', Suc n))" and
           dom_eq: "S \<inter> dom (state_map_\<alpha> (qm'', Suc n)) = insert (q2_\<alpha> q) ((dom (state_map_\<alpha> (qm, n))) \<inter> S)"
        using qm''_def[symmetric] ff_OK [OF invar_q q_in_S, symmetric]
        by simp_all

      have dom_II'_dist: "dom (state_map_\<alpha> (qm'', Suc n)) \<inter> set ?I' = {}" 
      proof -
        from II'_subset have "dom (state_map_\<alpha> (qm'', Suc n)) \<inter> set (map q2_\<alpha> II') =
             (S \<inter> dom (state_map_\<alpha> (qm'', Suc n))) \<inter> set (map q2_\<alpha> II')" by auto
        hence step: "dom (state_map_\<alpha> (qm'', Suc n)) \<inter> set (map q2_\<alpha> II') = 
                    insert (q2_\<alpha> q) ((dom (state_map_\<alpha> (qm, n))) \<inter> S) \<inter> set (map q2_\<alpha> II')"
          unfolding dom_eq by simp

        from dom_qII'_dist q_nin_I' show ?thesis unfolding step
           by (auto simp add: set_eq_iff) 
      qed

      have state_n_nin_Is: "states_enumerate n \<notin> s.\<alpha> Is"
      proof (rule notI)
        assume "states_enumerate n \<in> s.\<alpha> Is"
        from memb_Is[OF this] show False
          by (simp add: states_enumerate_eq)
      qed

      from state_n_nin_Is invar_Is 
      have Is''_props: "s.invar Is''" "s.\<alpha> Is'' = insert (states_enumerate n) (s.\<alpha> Is)"
        by (simp_all add: Is''_def s.correct)

      have state_n_nin_Is: "states_enumerate n \<notin> s.\<alpha> Is"
      proof (rule notI)
        assume "states_enumerate n \<in> s.\<alpha> Is"
        from memb_Is[OF this] show False
          by (simp add: states_enumerate_eq)
      qed

      from state_n_nin_Is invar_Is 
      have Is''_props: "s.invar Is''" "s.\<alpha> Is'' = insert (states_enumerate n) (s.\<alpha> Is)"
        by (simp_all add: Is''_def s.correct)

      have ind_hyp': "
        s.invar Is' \<and>
        s.\<alpha> Is' = (the \<circ> state_map_\<alpha> (qm', n')) ` set ?I' \<union> s.\<alpha> Is'' \<and>
        state_map_invar (qm', n') \<and>
        NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm'', Suc n)) (set ?I') (state_map_\<alpha> (qm', n'))"
      proof (rule ind_hyp [OF dom_II'_dist invar_qm''_n Is''_props(1)])
        fix q
        assume "q \<in> s.\<alpha> Is''"
        with Is''_props(2) memb_Is show "\<exists>n'<Suc n. q = states_enumerate n'"
          by auto (metis less_Suc_eq)
      next
        from map_OK' 
        show "NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm'', Suc n))"
          unfolding NFA_construct_reachable_map_OK_def by simp
      next
        from fold_eq show "((qm', n'), Is') = foldl ?step ((qm'', Suc n), Is'') II'" 
          by (simp add: qm''_def Is''_def)
      qed

      show ?case proof (intro conjI)
        show "s.invar Is'" "state_map_invar (qm', n')" by (simp_all add: ind_hyp')
      next
        from ind_hyp' qm''_alpha have "state_map_\<alpha> (qm', n') (q2_\<alpha> q) = Some (states_enumerate n)" 
          unfolding NFA_construct_reachable_map_OK_def state_map_\<alpha>_def 
          by (simp add: ff_OK[OF invar_q q_in_S])
        thus "s.\<alpha> Is' = (the \<circ> state_map_\<alpha> (qm', n')) ` set (map q2_\<alpha> (q # II')) \<union> s.\<alpha> Is"
          by (simp add: ind_hyp' Is''_props)
      next
        show "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) (set (map q2_\<alpha> (q # II')))
              (state_map_\<alpha> (qm', n'))"
        proof (rule NFA_construct_reachable_map_OK_trans [of _ _ "{q2_\<alpha> q}"
               "state_map_\<alpha> (qm'', Suc n)" "set ?I'"]) 
          show "set (map q2_\<alpha> (q # II')) \<subseteq> {q2_\<alpha> q} \<union> set ?I'" by auto
        next
          show "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm'', Suc n)) (set ?I') 
                  (state_map_\<alpha> (qm', n'))"
            using ind_hyp' by simp
        next
          show "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q} (state_map_\<alpha> (qm'', Suc n))" 
            by (simp add: map_OK')
        qed
      qed
    qed
  } note ind_proof = this

  have pre1 : "set (map q2_\<alpha> II) \<subseteq> S" unfolding S_def I_def by (rule accessible_subset_ws)
  have pre2 : "distinct (map q2_\<alpha> II)" using dist_I[unfolded I_def] by simp
  have pre3 : "\<forall>q\<in>set II. q2_invar q" using invar_I by simp

  have pre4 : "dom (state_map_\<alpha> (qm.empty (), 0)) \<inter> set (map q2_\<alpha> II) = {}"
    unfolding state_map_\<alpha>_def by (simp add: qm.correct o_def)

  have pre5 : "state_map_invar (qm.empty (), 0)"
    unfolding state_map_invar_def by (simp add: qm.correct)

  have pre6 : "NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm.empty (), 0))"
    unfolding NFA_construct_reachable_map_OK_def state_map_\<alpha>_def by (simp add: qm.correct o_def)

  note ind_proof' = ind_proof [OF ]
  obtain qm' n' Is' where res_eq: "NFA_construct_reachable_init_impl II = ((qm', n'), Is')" by (metis prod.exhaust)
  note ind_proof' = ind_proof [OF pre1 pre2 pre3 pre4 pre5 _ _ pre6, of "s.empty ()" qm' n' Is',
    folded NFA_construct_reachable_init_impl_def]
 
  from ind_proof' show ?thesis 
    apply (rule_tac SPEC_refine_sv prod_rel_sv br_sv)+
    apply (simp add: refine_hsimp
      s.correct I_def res_eq S_def NFA_construct_reachable_map_OK_def in_br_conv)
  done
qed

definition NFA_construct_reachable_impl_step_rel where
  "NFA_construct_reachable_impl_step_rel =
    build_rel (\<lambda>DS. {(a_\<alpha> as, q2_\<alpha> q') | as q'. (as, q') \<in> DS})
              (\<lambda>DS. (\<forall>as q'. (as, q') \<in> DS \<longrightarrow> a_invar as \<and> q2_invar q') \<and>
                    (\<forall>as1 q1' as2 q2'. (as1, q1') \<in> DS \<and> (as2, q2') \<in> DS \<and>
                        (a_\<alpha> as1 = a_\<alpha> as2) \<and> (q2_\<alpha> q1' = q2_\<alpha> q2') \<longrightarrow> as1 = as2 \<and> q1' = q2'))"

definition NFA_construct_reachable_impl_step where
"NFA_construct_reachable_impl_step det DS qm0 n D0 q =
FOREACH (DS q) (\<lambda>(as, q') ((qm, n), DD', N). do {
  let ((qm', n'), r') =
    (let r'_opt = qm.lookup (ff q') qm in
      if (r'_opt = None) then
         ((qm.update_dj (ff q') (states_enumerate n) qm, Suc n), states_enumerate n)
      else
         ((qm, n), the r'_opt)
    );
  RETURN ((qm', n'), add_labels det (the (qm.lookup (ff q) qm0)) as r' DD', q' # N)
}) ((qm0, n), D0, [])"

lemma NFA_construct_reachable_impl_step_correct :
fixes D II
fixes q :: "'q2_rep"
defines "I \<equiv> map q2_\<alpha> II"
defines "S \<equiv> accessible (LTS_forget_labels D) (set I)"
assumes f_inj_on: "inj_on f S"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and d_add_OK: "dlts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels True)"
                  "lts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels False)"
    and det_OK: "det \<Longrightarrow> LTS_is_deterministic D"
    and DS'_OK: "\<And>q a q'. q \<in> S \<Longrightarrow> ((q, a, q') \<in> D) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS' q)"
    and rm_eq: "rm = state_map_\<alpha> (qm0, n)"
    and invar_qm0_n: "state_map_invar (qm0, n)"
    and D0'_eq: "D0' = d.\<alpha> D0" "D0' = \<Delta> \<A>"
    and invar_D0: "d.invar D0"
    and rm_q:  "rm (q2_\<alpha> q) = Some r"
    and r_nin: "r \<notin> \<Q> \<A>"
    and invar_q: "q2_invar q"
    and q_in_S: "q2_\<alpha> q \<in> S"
    and DS_OK: "(DS q, DS' (q2_\<alpha> q)) \<in> NFA_construct_reachable_impl_step_rel"
    and weak_invar: "NFA_construct_reachable_abstract_impl_weak_invar I (l.\<alpha> A) FP D (rm, \<A>)"
notes refine_rel_defs[simp]
shows "NFA_construct_reachable_impl_step det DS qm0 n D0 q \<le> 
  \<Down> ((build_rel state_map_\<alpha> state_map_invar) \<times>\<^sub>r ((build_rel d.\<alpha> d.invar) \<times>\<^sub>r 
           (\<langle>build_rel q2_\<alpha> q2_invar\<rangle>list_rel)))
   (NFA_construct_reachable_abstract_impl_step S DS' rm D0' (q2_\<alpha> q))"
unfolding NFA_construct_reachable_impl_step_def
          NFA_construct_reachable_abstract_impl_step_def
using [[goals_limit = 1]]
apply (refine_rcg)
\<comment>\<open>preprocess goals\<close>
  apply (subgoal_tac "inj_on (\<lambda>(as, q'). (a_\<alpha> as, q2_\<alpha> q')) (DS q)")
  apply assumption
  apply (insert DS_OK)[]
  apply (simp add: inj_on_def Ball_def NFA_construct_reachable_impl_step_rel_def)
  apply blast
\<comment>\<open>goal solved\<close>
  apply (insert DS_OK)[]
  apply (simp add: NFA_construct_reachable_impl_step_rel_def)
  apply auto[]
\<comment>\<open>goal solved\<close>
  apply (simp add: rm_eq D0'_eq invar_qm0_n invar_D0 refine_hsimp)
\<comment>\<open>goal solved\<close>
  apply (clarify, simp add: refine_hsimp)+
  apply (rename_tac it N as'' q'' qm n D' NN as' q')
  apply (subgoal_tac "
    RETURN
        (let r'_opt = map_op_lookup qm_ops (ff q'') qm
         in if r'_opt = None
            then ((map_op_update_dj qm_ops (ff q'') (states_enumerate n) qm, Suc n), states_enumerate n)
            else ((qm, n), the r'_opt))
       \<le> \<Down> ((build_rel state_map_\<alpha> state_map_invar) \<times>\<^sub>r Id)
          (SPEC (\<lambda>(rm', r').
                    NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} rm' \<and>
                    rm' (q2_\<alpha> q') = Some r'))")
   apply assumption
   apply (simp del: br_def prod_rel_def add: Let_def ff_OK pw_le_iff refine_pw_simps prod_rel_sv)
   apply (simp)
   apply (rule conjI)
   apply (rule impI)
defer
   apply (rule impI)
   apply (erule exE)
   apply (rename_tac r)
   apply (simp)
defer
   apply (clarify, simp)+
   apply (rename_tac it N as'' q'' qm n D' NN r qm' n' as' q')
defer
using [[goals_limit = 10]]
proof -
  fix it N as'' q' as' q'' qm n D'

  assume aq'_in_it: "(as', q') \<in> it"
     and aq''_in_it: "(as'', q'') \<in> it"
     and it_subset: "it \<subseteq> DS q"
     and a''_a'_eq: "a_\<alpha> as'' = a_\<alpha> as'"
     and q''_q'_eq: "q2_\<alpha> q'' = q2_\<alpha> q'"
     and q'_in_S: "q2_\<alpha> q' \<in> S"
  let ?it' = "(\<lambda>(a, q'). (a_\<alpha> a, q2_\<alpha> q')) ` it"
  assume invar_foreach: "NFA_construct_reachable_abstract_impl_foreach_invar S DS' rm D0' (q2_\<alpha> q) ?it'
               (state_map_\<alpha> (qm, n), lts_op_\<alpha> d_ops D', N)"
     and invar_qm_n: "state_map_invar (qm, n)"
     and invar_D': "d.invar D'"
     
  from aq'_in_it aq''_in_it it_subset DS_OK 
  have invar_q': "q2_invar q'" and invar_q'': "q2_invar q''" 
   and invar_as': "a_invar as'" and invar_as'': "a_invar as''"
    by (auto simp add: NFA_construct_reachable_impl_step_rel_def)
  
  from q'_in_S q''_q'_eq have q''_in_S: "q2_\<alpha> q'' \<in> S" by simp
  from ff_OK[OF invar_q'' q''_in_S] q''_q'_eq have ff_q''_eq[simp]: "ff q'' = f (q2_\<alpha> q')" by simp

  define D'' where "D'' \<equiv> DS' (q2_\<alpha> q) - ?it'"
  from invar_foreach have 
     qm_OK: "NFA_construct_reachable_map_OK S rm (snd ` D'') (state_map_\<alpha> (qm, n))" and
     set_N_eq: "set N = snd ` D''" and
     D'_eq: "d.\<alpha> D' = D0' \<union>
       {(the (state_map_\<alpha> (qm, n) (q2_\<alpha> q)), a, the (state_map_\<alpha> (qm, n) q')) | a as q'. 
         (as, q') \<in> D'' \<and> a \<in> as}"
    unfolding NFA_construct_reachable_abstract_impl_foreach_invar.simps D''_def[symmetric]
      by (simp_all add: Let_def) 

  { \<comment>\<open>Consider the case that the map does not need to be extended\<close>
    fix r
    assume "qm.lookup (ff q'') qm = Some r"
    with invar_qm_n qm_OK
    show "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} (state_map_\<alpha> (qm, n)) \<and> 
          state_map_\<alpha> (qm, n) (q2_\<alpha> q') = Some r"
      by (simp add: state_map_\<alpha>_def qm.correct state_map_invar_def
                    NFA_construct_reachable_map_OK_def rm_eq dom_def)
  }

  { \<comment>\<open>... and the case that the map needs to be extended.\<close>
    assume "qm.lookup (ff q'') qm = None"
    with invar_qm_n have q'_nin_dom: "q2_\<alpha> q' \<notin> dom (state_map_\<alpha> (qm, n))"
      unfolding state_map_invar_def state_map_\<alpha>_def by (simp add: qm.correct dom_def)

    from qm_OK have qm_OK': 
      "NFA_construct_reachable_map_OK S Map.empty {} (state_map_\<alpha> (qm, n))"
      unfolding NFA_construct_reachable_map_OK_def by simp

    define qm' where "qm' \<equiv> qm.update_dj (f (q2_\<alpha> q')) (states_enumerate n) qm"
    from state_map_extend_thm [OF f_inj_on invar_qm_n q'_in_S q'_nin_dom qm_OK', folded qm'_def]
    have invar_qm'_n: "state_map_invar (qm', Suc n)" and
         qm'_alpha: "qm.\<alpha> qm' = qm.\<alpha> qm(f (q2_\<alpha> q') \<mapsto> states_enumerate n)" and
         qm'_OK: "NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'} (state_map_\<alpha> (qm', Suc n))"
      by simp_all

    from qm'_alpha have rm'_q': "state_map_\<alpha> (qm', Suc n) (q2_\<alpha> q') = Some (states_enumerate n)"
      unfolding state_map_\<alpha>_def by simp

    from invar_qm'_n qm'_OK rm'_q'
    show "state_map_invar (map_op_update_dj qm_ops (ff q'') (states_enumerate n) qm, Suc n) \<and>
          NFA_construct_reachable_map_OK S (state_map_\<alpha> (qm, n)) {q2_\<alpha> q'}
          (state_map_\<alpha> (map_op_update_dj qm_ops (ff q'') (states_enumerate n) qm, Suc n)) \<and>
         state_map_\<alpha> (map_op_update_dj qm_ops (ff q'') (states_enumerate n) qm, Suc n) (q2_\<alpha> q') =
         Some (states_enumerate n)"
      unfolding qm'_def[symmetric] ff_q''_eq by simp 
  }

  { \<comment>\<open>It remains to show that adding to the transition systems works. Here, a case distinction
        depending on whether the input is weak deterministic, is needed.\<close>
    fix r' qm' n'
    
    assume r'_props: "(let r'_opt = map_op_lookup qm_ops (ff q'') qm
                       in if r'_opt = None
                       then ((map_op_update_dj qm_ops (ff q'')
                             (states_enumerate n) qm,
                             Suc n),
                           states_enumerate n)
                      else ((qm, n), the r'_opt)) =
               ((qm', n'), r')"

    from qm_OK rm_q have r_intro1: "state_map_\<alpha> (qm, n) (q2_\<alpha> q) = Some r"
      unfolding NFA_construct_reachable_map_OK_def by simp

    from rm_q rm_eq have r_intro2: "qm.lookup (ff q) qm0 = Some r" using invar_qm0_n
      unfolding state_map_\<alpha>_def state_map_invar_def 
      using ff_OK [OF invar_q q_in_S] by (simp add: qm.correct)

    have "{(r, a, r') | a. a \<in> a_\<alpha> as'} \<union> d.\<alpha> D' = d.\<alpha> (add_labels det r as'' r' D') \<and>
          d.invar (add_labels det r as'' r' D')"
    proof (cases det)
      case False 
      with  lts_add_label_set.lts_add_label_set_correct[OF d_add_OK(2), OF invar_D' invar_as'', of r r']
      show ?thesis by (auto simp add: a''_a'_eq)
    next
      case True note det_True[simp] = this
      with det_OK have det_D: "LTS_is_deterministic D" by simp

      { fix a q'''
        assume "a \<in> a_\<alpha> as''" "q''' \<noteq> r'" 

        from weak_invar obtain s where
          rm_OK: "NFA_construct_reachable_map_OK S Map.empty (s \<union> set I \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D}) rm" and 
          s_subset: "s \<subseteq> S" and
          \<A>_eq: "\<A> = NFA_rename_states
           \<lparr>\<Q> = s, \<Sigma> = set_op_\<alpha> l_ops A, \<Delta> = {qsq \<in> D. fst qsq \<in> s}, \<I> = set I,
            \<F> = {q \<in> s. FP q}\<rparr>
           (the \<circ> rm)"
        unfolding NFA_construct_reachable_abstract_impl_weak_invar_def S_def[symmetric]
          by blast

        from r_nin 
        have r_nin_D0': "(r, a, q''') \<notin> D0'"
          unfolding \<A>_eq D0'_eq(2) by (simp add: image_iff Ball_def) metis

        { fix as q''''
          assume as_q''''_in_D'': "(as, q'''') \<in> D''"
             and q'''_eq: "q''' = the (state_map_\<alpha> (qm, n) q'''')"

          from as_q''''_in_D'' have "q'''' \<in> snd ` D''" by (simp add: image_iff Bex_def) blast
          with qm_OK have "q'''' \<in> dom (state_map_\<alpha> (qm, n))" 
             unfolding NFA_construct_reachable_map_OK_def by (simp add: subset_iff)
          with q'''_eq have qm_q''''_eq: "state_map_\<alpha> (qm, n) q'''' = Some q'''" by auto

          from as_q''''_in_D'' have "(as, q'''') \<in> DS' (q2_\<alpha> q)"
            unfolding D''_def by simp_all
          with DS'_OK(1)[OF q_in_S, of a q'''']  
          have in_D1: "a \<in> as \<Longrightarrow> ((q2_\<alpha> q, a, q'''') \<in> D)" by metis
           
          from aq'_in_it it_subset have "(as', q') \<in> DS q" by blast
          with DS_OK have "(a_\<alpha> as', q2_\<alpha> q') \<in> DS' (q2_\<alpha> q)" 
            unfolding NFA_construct_reachable_impl_step_rel_def by auto
          with DS'_OK(1)[OF q_in_S, of a "q2_\<alpha> q'"] `a \<in> a_\<alpha> as''` `a_\<alpha> as'' = a_\<alpha> as'`
          have in_D2: "((q2_\<alpha> q, a, q2_\<alpha> q') \<in> D)" by metis

          from `q''' \<noteq> r'` qm_q''''_eq r'_props invar_qm_n have q''''_neq: "q'''' \<noteq> q2_\<alpha> q'" 
            unfolding state_map_\<alpha>_def state_map_invar_def
            by (auto simp add: qm.correct)

          from in_D1 in_D2 q''''_neq det_D
          have "a \<notin> as" unfolding LTS_is_deterministic_def by metis
        } 
        hence "(r, a, q''') \<notin> d.\<alpha> D'" 
          by (simp add: D'_eq r_intro1 r_nin_D0')
      } note d_add = this

      from dlts_add_label_set.dlts_add_label_set_correct[OF d_add_OK(1), OF invar_D' invar_as'' d_add, of r']
      show ?thesis by (auto simp add: a''_a'_eq)
    qed

    thus "{(the (state_map_\<alpha> (qm, n) (q2_\<alpha> q)), a, r') |a. a \<in> a_\<alpha> as'} \<union> d.\<alpha> D' =
          d.\<alpha> (add_labels det (the (map_op_lookup qm_ops (ff q) qm0)) as'' r' D') \<and>
          d.invar (add_labels det (the (map_op_lookup qm_ops (ff q) qm0)) as'' r' D') \<and>
          q2_invar q'' " 
      unfolding r_intro1 r_intro2 option.sel ff_OK[OF invar_q] 
      by (simp add: invar_q'')
  }
qed


definition NFA_construct_reachable_impl where
  "NFA_construct_reachable_impl det S I A FP DS =
   do {
     let ((qm, n), Is) = NFA_construct_reachable_init_impl I;
     (((qm, n), \<A>::('q_set, 'a_set, 'd) NFA_impl), _) \<leftarrow> WORKLISTT (\<lambda>_. True)
      (\<lambda>((qm, n), AA) q. 
         if (s.memb (the (qm.lookup (ff q) qm)) (nfa_states AA)) then
           (RETURN (((qm, n), AA), []))
         else                    
           do {
             ASSERT (q2_invar q \<and> q2_\<alpha> q \<in> S);
             ((qm', n'), DD', N) \<leftarrow> NFA_construct_reachable_impl_step det DS qm n (nfa_trans AA) q;
             RETURN (((qm', n'),
                 (s.ins_dj (the (qm.lookup (ff q) qm)) (nfa_states AA), 
                  nfa_labels AA, DD', nfa_initial AA, 
                  (if (FP q) then (s.ins_dj (the (qm.lookup (ff q) qm))) 
                    (nfa_accepting AA) else (nfa_accepting AA)), nfa_props AA)), N)
           }
        ) (((qm, n), (s.empty (), A, d.empty (), Is, s.empty (), nfa_props_connected det)), I);
     RETURN \<A>
   }"



lemma NFA_construct_reachable_impl_correct :
fixes D II det
defines "I \<equiv> map q2_\<alpha> II"
defines "invar' \<equiv> (\<lambda>A. nfa_invar_no_props A \<and> nfa_props A = nfa_props_connected det)"
defines "R \<equiv> build_rel nfa_\<alpha> invar'"
defines "R' \<equiv> build_rel state_map_\<alpha> state_map_invar"
defines "R'' \<equiv> R' \<times>\<^sub>r ((build_rel d.\<alpha> d.invar) \<times>\<^sub>r (\<langle>build_rel q2_\<alpha> q2_invar\<rangle>list_rel))"
defines "S \<equiv> accessible (LTS_forget_labels D) (set I)"
assumes f_inj_on: "inj_on f S"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and d_add_OK: "dlts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels True)"
                  "lts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels False)"
    and det_OK: "det \<Longrightarrow> LTS_is_deterministic D"
    and DS'_OK: "\<And>q a q'. q \<in> S \<Longrightarrow> ((q, a, q') \<in> D) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS' q)"
    and dist_I: "distinct I"
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q" 
    and invar_A: "l.invar A"
    and DS_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> (DS q, DS' (q2_\<alpha> q)) \<in> NFA_construct_reachable_impl_step_rel"
    and FFP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> FFP q \<longleftrightarrow> FP (q2_\<alpha> q)"
notes refine_rel_defs[simp]
shows "NFA_construct_reachable_impl det S II A FFP DS \<le>
   \<Down>R (NFA_construct_reachable_abstract2_impl I (l.\<alpha> A) FP D DS')"
proof-
  {
    fix q rm \<A> qm n Qs As DD Is Fs p r
    assume rm_q: "rm (q2_\<alpha> q) = Some r" and
         in_R': "((qm, n), rm) \<in> R'" and
         in_R: "((Qs, As, DD, Is, Fs, p), \<A>) \<in> R" and
         invar_q: "q2_invar q" and
         q_in: "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"
    have "s.memb (the (qm.lookup (ff q) qm)) Qs = (r \<in> \<Q> \<A>)"
    proof -
      from q_in have q_in_S: "q2_\<alpha> q \<in> S" unfolding S_def I_def by simp
    
      from in_R' rm_q ff_OK[OF invar_q q_in_S] have "qm.lookup (ff q) qm = Some r"
        unfolding R'_def by (simp add: state_map_invar_def state_map_\<alpha>_def qm.correct)
    
      with in_R show "s.memb (the (qm.lookup (ff q) qm)) Qs = (r \<in> \<Q> \<A>)"
        unfolding R_def by (simp add: invar'_def nfa_invar_no_props_def
            nfa_selectors_def s.correct)
    qed
  } note aux=this
  
  show ?thesis
  unfolding NFA_construct_reachable_impl_def NFA_construct_reachable_abstract2_impl_def WORKLISTT_def
using [[goals_limit = 17]]
  supply [refine_dref_RELATES] = RELATESI[of R] RELATESI[of R'] RELATESI[of R''] RELATESI[of "build_rel q2_\<alpha> q2_invar"]
  supply [refine] = NFA_construct_reachable_impl_step_correct
  apply (refine_rcg)
             apply refine_dref_type

\<comment>\<open>preprocess goals\<close>
  \<comment>\<open>initialisation is OK\<close>
  subgoal
  apply (unfold I_def R'_def)
  apply (rule NFA_construct_reachable_init_impl_correct)
  apply (insert f_inj_on ff_OK dist_I invar_I)[4]
  apply (simp_all add: S_def I_def)[4]
done

  subgoal
    apply (simp add: prod_rel_sv R'_def R_def del: prod_rel_def br_def)
    done
  subgoal
    apply (simp add: R'_def R_def nfa_invar_weak2_def invar'_def
                   nfa_invar_no_props_def nfa_invar_props_def
                   s.correct d.correct_common invar_A)
    done
  subgoal
    using invar_I map_in_list_rel_conv unfolding I_def apply blast
    done
  subgoal by simp
  subgoal by simp
        apply clarsimp
  subgoal for am an bf y q rm \<A> qm n Qs As DD Is Fs p r
    apply (rule aux[of rm q r qm n Qs As DD Is Fs p \<A>])
        apply auto
    using I_def by auto
  
  subgoal by (simp add: prod_rel_sv R'_def R_def del: prod_rel_def br_def)
  subgoal by (simp del: br_def add: in_br_conv)
  subgoal by (simp add: in_br_conv I_def S_def)
  subgoal for v1 v2 v3 v4 v5 v6 v7 v8 q v10 q' rm As v14 qm n \<A>
    unfolding R''_def R'_def I_def
    apply (simp only: in_br_conv)
    apply (rule NFA_construct_reachable_impl_step_correct)
    prefer 13 \<comment>\<open>some variables were not instantiated so we solve this first\<close>
    apply blast
    apply (clarsimp_all)
    prefer 10 \<comment>\<open>some variables were not instantiated so we solve this first\<close>
    apply blast
    subgoal
      using I_def S_def f_inj_on by auto
    subgoal 
      by (simp add: I_def S_def ff_OK)
    subgoal 
      using d_add_OK(1) by blast
    subgoal 
      using d_add_OK(2) by blast
    subgoal 
      using det_OK by presburger
    subgoal
      by (simp add: DS'_OK I_def S_def)
    subgoal unfolding R_def by (simp add: in_br_conv)
    subgoal
      apply (unfold R_def)
      apply (simp add: in_br_conv invar'_def)
      using nfa_invar_no_props_def by blast
    subgoal using DS_OK by blast
    done
   apply (clarify)
   apply (simp add: R_def R'_def R''_def)
  subgoal for x1b x2a x2b q q2 qm n Qs As D0 Is Fs ps v1 v2 v3 v4 v5 r
   apply (intro conjI impI)
          apply (clarify)
          apply (simp add: invar'_def nfa_invar_no_props_def nfa_selectors_def s.correct state_map_invar_def state_map_\<alpha>_def qm.correct)
          defer
          apply (simp add: invar'_def nfa_invar_no_props_def)
          apply (intro conjI)
  using s.ins_dj_correct(2) s.memb_correct apply blast
          apply (rule_tac s.ins_dj_correct(2))
           apply blast
           defer
  using FFP_OK apply blast
         apply (simp add: invar'_def nfa_invar_no_props_def)
         apply (intro conjI)
  using FFP_OK apply blast
  using FFP_OK apply blast
  using FFP_OK apply blast
  using FFP_OK apply blast
      apply (simp add:  ff_OK state_map_\<alpha>_def invar'_def nfa_invar_no_props_def state_map_invar_def qm.lookup_correct s.ins_dj_correct(1))
     apply (simp add: invar'_def nfa_by_lts_defs.nfa_invar_no_props_def s.ins_dj_correct(2) R_def R'_def state_map_invar_def state_map_\<alpha>_def I_def S_def ff_OK nfa_invar_no_props_def nfa_by_lts_defs_axioms qm.lookup_correct s.memb_correct)
   defer
   apply (clarsimp simp add: state_map_invar_def I_def S_def ff_OK nfa_invar_no_props_def qm.lookup_correct s.memb_correct)
proof-
  assume asm:
    "NFA_construct_reachable_init_impl II = ((x1b, x2a), x2b)" "the (qm.\<alpha> qm (f (q2_\<alpha> q))) \<notin> s.\<alpha> Qs" "r \<notin> s.\<alpha> Qs" "state_map_\<alpha> (qm, n) (q2_\<alpha> q) = Some r" "q2_invar q"
    "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"
    "NFA_construct_reachable_abstract_impl_weak_invar (map q2_\<alpha> II) (l.\<alpha> A) FP D
         (state_map_\<alpha> (qm, n), nfa_\<alpha> (Qs, As, D0, Is, Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>))"
    "FFP q" "FP (q2_\<alpha> q)" "qm.invar x1b" "qm.invar qm" "qm.invar v2" "\<forall>i q. qm.\<alpha> x1b i = Some q \<longrightarrow> (\<exists>n'<x2a. q = states_enumerate n')" "s.invar x2b"
    "\<forall>i q. qm.\<alpha> qm i = Some q \<longrightarrow> (\<exists>n'<n. q = states_enumerate n')" "\<forall>i q. qm.\<alpha> v2 i = Some q \<longrightarrow> (\<exists>n'<v3. q = states_enumerate n')" "s.invar Qs" "d.invar v4"
    "list_all2 (\<lambda>x x'. x' = q2_\<alpha> x \<and> q2_invar x) v5 v1" "l.invar As" "d.invar D0" "s.invar Is" "s.invar Fs" "the (qm.\<alpha> qm (f (q2_\<alpha> q))) \<in> s.\<alpha> Fs"

  let ?A = "nfa_\<alpha> (Qs, As, D0, Is, Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>)"\<comment>\<open>basically, we have to show that ?A is an NFA\<close>

  from asm(7)[simplified NFA_construct_reachable_abstract_impl_weak_invar_def I_def[symmetric]] obtain s where
  "NFA_construct_reachable_map_OK (accessible (LTS_forget_labels D) (set I)) Map.empty (s \<union> set I \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D}) (state_map_\<alpha> (qm, n)) \<and>
        s \<subseteq> accessible (LTS_forget_labels D) (set I) \<and>
        ?A = NFA_rename_states \<lparr>\<Q> = s, \<Sigma> = l.\<alpha> A, \<Delta> = {qsq \<in> D. fst qsq \<in> s}, \<I> = set I, \<F> = {q \<in> s. FP q}\<rparr> (the \<circ> (state_map_\<alpha> (qm, n)))"
    by blast

  hence "s.\<alpha> Qs = the ` ((NFA_construct_reachable_locale.state_map_\<alpha> qm_ops f (qm, n)) ` s)"
        "s.\<alpha> Fs = the ` ((NFA_construct_reachable_locale.state_map_\<alpha> qm_ops f (qm, n)) ` {q \<in> s. FP q})"
    unfolding nfa_\<alpha>_def
    using NFA_rename_states_def[of "\<lparr>\<Q> = s, \<Sigma> = l.\<alpha> A, \<Delta> = {qsq \<in> D. fst qsq \<in> s}, \<I> = set I, \<F> = {q \<in> s. FP q}\<rparr>" "(the \<circ> (state_map_\<alpha> (qm, n)))", simplified SemiAutomaton_rename_states_ext_def]
    by auto
    

  show False
    sorry
next
  assume asm:
    "NFA_construct_reachable_init_impl II = ((x1b, x2a), x2b)" "r \<notin> s.\<alpha> Qs" "qm.\<alpha> qm (f (q2_\<alpha> q)) = Some r" "q2_invar q" "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"
    "NFA_construct_reachable_abstract_impl_weak_invar (map q2_\<alpha> II) (l.\<alpha> A) FP D
         (qm.\<alpha> qm \<circ> f, nfa_\<alpha> (Qs, As, D0, Is, Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>))"
    "FFP q" "FP (q2_\<alpha> q)" "qm.invar x1b \<and> (\<forall>i q. qm.\<alpha> x1b i = Some q \<longrightarrow> (\<exists>n'<x2a. q = states_enumerate n'))" "s.invar x2b"
    "qm.invar qm \<and> (\<forall>i q. qm.\<alpha> qm i = Some q \<longrightarrow> (\<exists>n'<n. q = states_enumerate n'))" "s.invar Qs \<and> l.invar As \<and> d.invar D0 \<and> s.invar Is \<and> s.invar Fs"
    "qm.invar v2 \<and> (\<forall>i q. qm.\<alpha> v2 i = Some q \<longrightarrow> (\<exists>n'<v3. q = states_enumerate n'))" "d.invar v4" "list_all2 (\<lambda>x x'. x' = q2_\<alpha> x \<and> q2_invar x) v5 v1"

  from \<open>r \<notin> s.\<alpha> Qs\<close> have r_not_in_Fs:"r \<notin> s.\<alpha> Fs"
    sorry
  
  show "\<lparr>\<Q> = insert r (s.\<alpha> Qs), \<Sigma> = l.\<alpha> As, \<Delta> = d.\<alpha> v4, \<I> = s.\<alpha> Is, \<F> = insert r (s.\<alpha> Fs)\<rparr> =
            nfa_\<alpha> (s.ins_dj r Qs, As, v4, Is, s.ins_dj r Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>)"
    apply (unfold nfa_\<alpha>_def)
    apply (simp add: s.ins_dj_correct)
    using asm(12) asm(2) r_not_in_Fs s.ins_dj_correct(1) by blast
qed



  (* apply clarify *)
     (* apply (simp del: br_def add: in_br_conv S_def I_def R_def R'_def) *)
  apply (subgoal_tac "\<And>x' x1 x2 x1a x1b x2a x2b s e s' e' x1c x2c x1d x1e x2d x2e.
       \<lbrakk>(NFA_construct_reachable_init_impl II, x') \<in> br state_map_\<alpha> state_map_invar \<times>\<^sub>r br s.\<alpha> s.invar; x' = (x1, x2); x1a = (x1b, x2a); NFA_construct_reachable_init_impl II = (x1a, x2b); (s, s') \<in> R' \<times>\<^sub>r R;
        (e, e') \<in> br q2_\<alpha> q2_invar; True; True; s' = (x1c, x2c); x1d = (x1e, x2d); s = (x1d, x2e);
        e' \<in> dom x1c \<and> e' \<in> accessible (LTS_forget_labels D) (set (map q2_\<alpha> II)) \<and> NFA_construct_reachable_abstract_impl_weak_invar (map q2_\<alpha> II) (l.\<alpha> A) FP D (x1c, x2c); \<not> s.memb (the (qm.lookup (ff e) x1e)) (nfa_states x2e);
        the (x1c e') \<notin> \<Q> x2c; q2_invar e \<and> q2_\<alpha> e \<in> S\<rbrakk>
       \<Longrightarrow> NFA_construct_reachable_impl_step det DS x1e x2d (nfa_trans x2e) e
            \<le> \<Down> (br state_map_\<alpha> state_map_invar \<times>\<^sub>r br d.\<alpha> d.invar \<times>\<^sub>r \<langle>br q2_\<alpha> q2_invar\<rangle>list_rel) (NFA_construct_reachable_abstract_impl_step (accessible (LTS_forget_labels D) (set (map q2_\<alpha> II))) DS' x1c (\<Delta> x2c) e')")
      apply blast
     apply (clarify, simp)
     apply (rule_tac \<A> = "nfa_\<alpha> (ay, az, bm, bn, bo, bp)" in NFA_construct_reachable_impl_step_correct[simplified])
                     apply (metis I_def S_def f_inj_on image_set)
                    apply (metis ff_OK I_def S_def image_set)
  using d_add_OK(1) apply blast
  using d_add_OK(2) apply blast
  using det_OK apply blast
  apply (simp add: DS'_OK I_def S_def)
               apply (simp add: in_br_conv R'_def)
              apply (simp add: in_br_conv R'_def)
             apply (simp add: R_def)
            apply (simp add: in_br_conv R_def)
  apply (simp add: R_def invar'_def nfa_by_lts_defs.nfa_invar_no_props_def nfa_by_lts_defs_axioms)
  apply (subgoal_tac "\<And>x1b x2a x2b e e' x1c x2c x1e x2d aj ak al am an bf x1f x1ba ea e'a x1ca x2ca x1ea x2da ay az bm bn bo bp y ya.
       \<lbrakk>state_map_invar (x1b, x2a) \<and> s.invar x2b; x1ba = x1b; ((x1e, x2d), x1c) \<in> R' \<and> ((aj, ak, al, am, an, bf), x2c) \<in> R; e' = q2_\<alpha> e; \<not> s.memb (the (qm.lookup (ff e) x1e)) aj; y \<notin> \<Q> x2c; x1f = state_map_\<alpha> (x1b, x2a);
        NFA_construct_reachable_init_impl II = ((x1b, x2a), x2b); ((x1ea, x2da), x1ca) \<in> R' \<and> ((ay, az, bm, bn, bo, bp), x2ca) \<in> R; e'a = q2_\<alpha> ea; \<not> s.memb (the (qm.lookup (ff ea) x1ea)) ay; ya \<notin> \<Q> x2ca; x1c (q2_\<alpha> e) = Some y;
        q2_invar e; q2_\<alpha> e \<in> S; x1ca (q2_\<alpha> ea) = Some ya; q2_invar ea; q2_\<alpha> ea \<in> S; q2_\<alpha> e \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II);
        NFA_construct_reachable_abstract_impl_weak_invar (map q2_\<alpha> II) (l.\<alpha> A) FP D (x1c, x2c); q2_\<alpha> ea \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II);
        NFA_construct_reachable_abstract_impl_weak_invar (map q2_\<alpha> II) (l.\<alpha> A) FP D (x1ca, x2ca)\<rbrakk>
       \<Longrightarrow> x1ca (q2_\<alpha> ea) = Some ya") (* Maybe not \<open>Some ya\<close> but something like \<open>(qm.lookup (ff ea) x1ea)\<close> *)
          apply blast
          apply (clarify, simp add: R'_def R_def ff_OK state_map_\<alpha>_def)
        apply blast
       apply blast
      apply (simp add: DS_OK)
     apply (clarify, simp add: R_def)
    apply (clarify)
    apply (simp add: R_def R'_def)
    apply (rename_tac x1b x2a x2b q q2 qm n Qs As D0 Is Fs ps v1 v2 v3 v4 v5 r)
    apply (intro conjI impI)
           apply (clarify)
           apply (simp add: invar'_def nfa_invar_no_props_def nfa_selectors_def s.correct state_map_invar_def state_map_\<alpha>_def qm.correct)
           defer
           apply (simp add: invar'_def nfa_invar_no_props_def)
           apply (intro conjI)
  using s.ins_dj_correct(2) s.memb_correct apply blast
           apply (rule_tac s.ins_dj_correct(2))
            apply blast
           defer
  using FFP_OK apply blast
          apply (simp add: invar'_def nfa_invar_no_props_def)
          apply (intro conjI)
  using FFP_OK apply blast
  using FFP_OK apply blast
  using FFP_OK apply blast
  using FFP_OK apply blast
       apply (simp add:  ff_OK state_map_\<alpha>_def invar'_def nfa_invar_no_props_def state_map_invar_def qm.lookup_correct s.ins_dj_correct(1))
      apply (simp add: invar'_def nfa_by_lts_defs.nfa_invar_no_props_def nfa_by_lts_defs_axioms s.ins_dj_correct(2) s.memb_correct)
     apply (simp add: in_br_conv R_def)
    apply (simp add: R_def R'_def invar'_def state_map_invar_def state_map_\<alpha>_def I_def S_def ff_OK nfa_invar_no_props_def nfa_by_lts_defs_axioms qm.lookup_correct s.memb_correct)
   apply (clarify, simp add: R_def R'_def invar'_def state_map_invar_def state_map_\<alpha>_def I_def S_def ff_OK nfa_invar_no_props_def nfa_by_lts_defs_axioms qm.lookup_correct s.memb_correct)
   defer
    apply (clarify, simp add: R_def R'_def invar'_def state_map_invar_def state_map_\<alpha>_def I_def[symmetric] S_def ff_OK nfa_invar_no_props_def nfa_by_lts_defs_axioms qm.lookup_correct s.memb_correct)
proof-
  fix x1b x2a x2b q qm n Qs As D0 Is Fs v1 v2 v3 v4 v5 r
  assume asm:
    "NFA_construct_reachable_init_impl II = ((x1b, x2a), x2b)"
    "r \<notin> s.\<alpha> Qs"
    "qm.\<alpha> qm (f (q2_\<alpha> q)) = Some r"
    "q2_invar q" "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"
    "NFA_construct_reachable_abstract_impl_weak_invar I (l.\<alpha> A) FP D (qm.\<alpha> qm \<circ> f, nfa_\<alpha> (Qs, As, D0, Is, Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>))"
    "FFP q"
    "FP (q2_\<alpha> q)"
    "qm.invar x1b \<and> (\<forall>i q. qm.\<alpha> x1b i = Some q \<longrightarrow> (\<exists>n'<x2a. q = states_enumerate n'))"
    "s.invar x2b"
    "qm.invar qm \<and> (\<forall>i q. qm.\<alpha> qm i = Some q \<longrightarrow> (\<exists>n'<n. q = states_enumerate n'))"
    "qm.invar v2 \<and> (\<forall>i q. qm.\<alpha> v2 i = Some q \<longrightarrow> (\<exists>n'<v3. q = states_enumerate n'))"
    "s.invar Qs" "d.invar v4" "list_all2 (\<lambda>x x'. x' = q2_\<alpha> x \<and> q2_invar x) v5 v1" "l.invar As" "d.invar D0" "s.invar Is" "s.invar Fs" "r \<in> s.\<alpha> Fs"
  let ?A = "nfa_\<alpha> (Qs, As, D0, Is, Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>)"
  have "NFA ?A"
    unfolding nfa_\<alpha>_def NFA_def using asm
    apply auto
    unfolding FinSemiAutomaton_def
     apply (intro conjI)
      defer
    unfolding FinSemiAutomaton_axioms_def
    apply simp
    unfolding NFA_axioms_def
     apply (intro conjI[rotated])
      apply simp
    apply simp
     defer
    unfolding SemiAutomaton_def
     apply (intro conjI allI impI)
        apply auto
    sorry
  
  find_consts name: RELATES
  find_theorems RELATES


  moreover have "\<Q> ?A = s.\<alpha> Qs" "\<F> ?A = s.\<alpha> Fs"
    by simp+

  ultimately show False
    using asm(2, 20) NFA.\<F>_consistent[of ?A] by blast
next
  fix x1b x2a x2b q qm n Qs As D0 Is Fs v1 v2 v3 v4 v5 r
  assume asm:
    "NFA_construct_reachable_init_impl II = ((x1b, x2a), x2b)" "r \<notin> s.\<alpha> Qs" "qm.\<alpha> qm (f (q2_\<alpha> q)) = Some r" "q2_invar q" "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"
    "NFA_construct_reachable_abstract_impl_weak_invar (map q2_\<alpha> II) (l.\<alpha> A) FP D (qm.\<alpha> qm \<circ> f, nfa_\<alpha> (Qs, As, D0, Is, Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>))"
    "FFP q" "FP (q2_\<alpha> q)" "s.invar x2b" "d.invar v4" "list_all2 (\<lambda>x x'. x' = q2_\<alpha> x \<and> q2_invar x) v5 v1" "qm.invar x1b" "\<forall>i q. qm.\<alpha> x1b i = Some q \<longrightarrow> (\<exists>n'<x2a. q = states_enumerate n')" "qm.invar qm"
    "\<forall>i q. qm.\<alpha> qm i = Some q \<longrightarrow> (\<exists>n'<n. q = states_enumerate n')" "s.invar Qs" "qm.invar v2" "\<forall>i q. qm.\<alpha> v2 i = Some q \<longrightarrow> (\<exists>n'<v3. q = states_enumerate n')" "l.invar As" "d.invar D0" "s.invar Is" "s.invar Fs"

  from \<open>r \<notin> s.\<alpha> Qs\<close> have r_not_in_Fs:"r \<notin> s.\<alpha> Fs"
    sorry
  
  show "\<lparr>\<Q> = insert r (s.\<alpha> Qs), \<Sigma> = l.\<alpha> As, \<Delta> = d.\<alpha> v4, \<I> = s.\<alpha> Is, \<F> = insert r (s.\<alpha> Fs)\<rparr> =
            nfa_\<alpha> (s.ins_dj r Qs, As, v4, Is, s.ins_dj r Fs, \<lparr>nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True\<rparr>)"
    apply (unfold nfa_\<alpha>_def)
    apply (simp add: s.ins_dj_correct)
    using s.ins_dj_correct(1)[OF \<open>s.invar Fs\<close> r_not_in_Fs] apply auto
      by (simp add: \<open>s.invar Qs\<close> \<open>r \<notin> s.\<alpha> Qs\<close> s.ins_dj_correct(1))+
qed


(*
\<comment>\<open>goal solved\<close>
     apply clarify
     apply (simp add: in_br_conv split: if_split)
     apply auto[]
\<comment>\<open>goal solved\<close>
  apply (simp add: in_br_conv)
\<comment>\<open>goal solved\<close>
  defer
  apply clarify
  apply (simp)
  apply (rename_tac q qm n Qs As D0 Is Fs ps r)
*)

(*
  \<comment>\<open>step OK\<close>
  apply (unfold I_def[symmetric])
  apply (simp add: R'_def R_def)
  apply (clarify, simp)+
  apply (unfold I_def)
  apply (rule_tac \<A> = "nfa_\<alpha> (ak, al, am, an, ao, bg)" in NFA_construct_reachable_impl_step_correct)
  apply (unfold I_def[symmetric])
  apply (simp_all add: invar'_def nfa_invar_no_props_def f_inj_on[unfolded S_def] ff_OK[unfolded S_def] 
                       DS_OK[unfolded S_def] DS'_OK[unfolded S_def] d_add_OK det_OK) [17] 

\<comment>\<open>goal solved\<close>
  apply (simp add: prod_rel_sv R'_def R_def del: prod_rel_def br_def)
\<comment>\<open>goal solved\<close>
  apply (simp del: br_def)
\<comment>\<open>goal solved\<close>
  apply (clarify, simp split del: if_splits add: R'_def)+
  apply (unfold S_def[symmetric] nfa_accepting_def snd_conv)
  apply (rename_tac qm'' n'' bba q' \<A> qm n Qs As DD Is Fs p bga qm' n' D' bja r)
  apply (unfold fst_conv)
defer
  apply (simp del: br_def add: R_def)
\<comment>\<open>goal solved\<close>
  apply simp
\<comment>\<open>goal solved\<close>
*)
(* using [[goals_limit = 6]] *)
(*
proof -
  fix q rm \<A> qm n Qs As DD Is Fs p r
  assume rm_q: "rm (q2_\<alpha> q) = Some r" and
         in_R': "((qm, n), rm) \<in> R'" and
         in_R: "((Qs, As, DD, Is, Fs, p), \<A>) \<in> R" and
         invar_q: "q2_invar q" and
         q_in: "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"

  from q_in have q_in_S: "q2_\<alpha> q \<in> S" unfolding S_def I_def by simp

  from in_R' rm_q ff_OK[OF invar_q q_in_S] have "qm.lookup (ff q) qm = Some r"
    unfolding R'_def by (simp add: state_map_invar_def state_map_\<alpha>_def qm.correct)

  with in_R show "s.memb (the (qm.lookup (ff q) qm)) Qs = (r \<in> \<Q> \<A>)"
    unfolding R_def by (simp add: invar'_def nfa_invar_no_props_def
        nfa_selectors_def s.correct)
next
  fix q qm n Qs As D0 Is Fs ps r
  assume asm:
    "\<not> s.memb (the (qm.lookup (ff q) qm)) Qs"
    "r \<notin> s.\<alpha> Qs"
    "state_map_\<alpha> (qm, n) (q2_\<alpha> q) = Some r"
    "q2_invar q"
    "q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)"
    "NFA_construct_reachable_abstract_impl_weak_invar (map q2_\<alpha> II) (l.\<alpha> A) FP D (state_map_\<alpha> (qm, n), nfa_\<alpha> (Qs, As, D0, Is, Fs, ps))"
    "state_map_invar (qm, n)"
    "invar' (Qs, As, D0, Is, Fs, ps)"
  
  have map_I:"q2_\<alpha> ` set II = set I" using I_def by simp
  have inj_on_f:"inj_on f (accessible (LTS_forget_labels D) (set I))"
    using S_def f_inj_on by blast
  have q2_1:"\<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (set I)\<rbrakk> \<Longrightarrow> ff q = f (q2_\<alpha> q)"
    by (simp add: S_def ff_OK)
  have q2_2:"\<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (set I)\<rbrakk> \<Longrightarrow> q2_invar q"
    by simp
  have q2_3:"\<And>q. \<lbrakk>q2_invar q; q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (set I)\<rbrakk> \<Longrightarrow> q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (set I)"
    by simp
  have add_lb:"dlts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels True)"
              "lts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels False)"
    using d_add_OK by blast+
  have det:"det \<Longrightarrow> LTS_is_deterministic D"
    using det_OK by blast
  have acc:"\<And>q a q'. q \<in> accessible (LTS_forget_labels D) (set I) \<Longrightarrow> ((q, a, q') \<in> D) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS' q)"
           "\<And>q a q'. q \<in> accessible (LTS_forget_labels D) (set I) \<Longrightarrow> q \<in> accessible (LTS_forget_labels D) (set I)"
    by (simp add: DS'_OK S_def)
  have invar_qm_n:"state_map_invar (qm, n)"
    using asm(7) by blast
  have D0_nfa: "d.\<alpha> D0 = \<Delta> (nfa_\<alpha> (Qs, As, D0, Is, Fs, ps))"
    by simp
  have invar_D0: "d.invar D0"
    using asm(8) invar'_def nfa_invar_no_props_def by simp
  note some_r=asm(3)
  have r_not_in_Q:"r \<notin> \<Q> (nfa_\<alpha> (Qs, As, D0, Is, Fs, ps))"
    by (simp add: asm(2))
  have q2_acc:"q2_\<alpha> q \<in> accessible (LTS_forget_labels D) (set I)"
    using asm(5,6) map_I by simp
  have nfa_construct_mem:"(DS q, DS' (q2_\<alpha> q)) \<in> NFA_construct_reachable_impl_step_rel"
    by (simp add: DS_OK S_def q2_acc asm(4))
  have nfa_construct_invar:"NFA_construct_reachable_abstract_impl_weak_invar I (l.\<alpha> A) FP D (state_map_\<alpha> (qm, n), nfa_\<alpha> (Qs, As, D0, Is, Fs, ps))"
    by (simp add: I_def asm(6))

  from NFA_construct_reachable_impl_step_correct[of D II det DS' "state_map_\<alpha> (qm, n)" qm n "d.\<alpha> D0" D0 "nfa_\<alpha> (Qs, As, D0, Is, Fs, ps)" q r DS A FP]
  have aux:"NFA_construct_reachable_impl_step det DS qm n D0 q
       \<le> \<Down> (br state_map_\<alpha> state_map_invar \<times>\<^sub>r br d.\<alpha> d.invar \<times>\<^sub>r \<langle>br q2_\<alpha> q2_invar\<rangle>list_rel)
           (NFA_construct_reachable_abstract_impl_step (accessible (LTS_forget_labels D) (set I)) DS' (state_map_\<alpha> (qm, n)) (d.\<alpha> D0) (q2_\<alpha> q))"
    using D0_nfa DS'_OK I_def S_def asm(4) asm(6) d_add_OK(1) d_add_OK(2) det_OK f_inj_on ff_OK invar_D0 invar_qm_n nfa_construct_mem q2_acc r_not_in_Q some_r by blast

(*
  have empty:"(br state_map_\<alpha> state_map_invar \<times>\<^sub>r br d.\<alpha> d.invar \<times>\<^sub>r \<langle>br q2_\<alpha> q2_invar\<rangle>list_rel) = {}"
  apply simp
  apply (intro impI allI)
  apply (unfold state_map_invar_def)
    apply (auto)
    apply (rename_tac q1 q2 qm D n)
    sorry
*)
  note DS_OK_of_q=DS_OK[of q, simplified NFA_construct_reachable_impl_step_rel_def in_br_conv, OF asm(4) q2_acc[simplified S_def[symmetric]]]
  show "NFA_construct_reachable_impl_step det DS qm n D0 q
            \<le> \<Down> {} (NFA_construct_reachable_abstract_impl_step (accessible (LTS_forget_labels D) (q2_\<alpha> ` set II)) DS' (state_map_\<alpha> (qm, n)) (d.\<alpha> D0) (q2_\<alpha> q))"
    apply (simp_all add: map_I)
    apply (simp add: NFA_construct_reachable_abstract_impl_step_def)
    apply (unfold NFA_construct_reachable_impl_step_def)
    apply (refine_rcg)
          defer
          apply (subgoal_tac " DS' (q2_\<alpha> q) = (\<lambda>(as, q'). (a_\<alpha> as, q2_\<alpha> q')) ` DS q")
    using DS_OK_of_q apply auto
     defer
     apply (auto simp add: inj_on_def)
  proof-
    assume
      DS'_DS:"DS' (q2_\<alpha> q) = {(a_\<alpha> as, q2_\<alpha> q') |as q'. (as, q') \<in> DS q}" and
      DS_invar:"\<forall>as q'. (as, q') \<in> DS q \<longrightarrow> a_invar as \<and> q2_invar q'" and
      DS_inj_on_abs:"\<forall>as1 q1' as2 q2'. (as1, q1') \<in> DS q \<and> (as2, q2') \<in> DS q \<and> a_\<alpha> as1 = a_\<alpha> as2 \<and> q2_\<alpha> q1' = q2_\<alpha> q2' \<longrightarrow> as1 = as2 \<and> q1' = q2'"

    let ?f = "\<lambda>(as, q'). (a_\<alpha> as, q2_\<alpha> q')"
    from DS_inj_on_abs have "inj_on ?f (DS q)"
      by (auto simp add: inj_on_def)

    show False
      sorry
  qed
qed

*)

lemma NFA_construct_reachable_impl_alt_def :
  "NFA_construct_reachable_impl det S I A FP DS =
   do {
     let ((qm, n), Is) = NFA_construct_reachable_init_impl I;
     ((_, \<A>), _) \<leftarrow> WORKLISTT (\<lambda>_. True)
      (\<lambda>((qm, n), (Qs, As, DD, Is, Fs, p)) q. do { 
         let r = the (qm.lookup (ff q) qm);
         if (s.memb r Qs) then
           (RETURN (((qm, n), (Qs, As, DD, Is, Fs, p)), []))
         else                    
           do {
             ASSERT (q2_invar q \<and> q2_\<alpha> q \<in> S);
             ((qm', n'), DD', N) \<leftarrow> NFA_construct_reachable_impl_step det DS qm n DD q;
             RETURN (((qm', n'), 
                 (s.ins_dj r Qs, 
                  As, DD', Is, 
                  (if (FP q) then (s.ins_dj r Fs) else Fs), p)), N)
           }
         }
        ) (((qm, n), (s.empty (), A, d.empty (), Is, s.empty (), nfa_props_connected det)), I);
     RETURN \<A>
   }"
unfolding NFA_construct_reachable_impl_def
apply (simp add: Let_def split_def)
apply (unfold nfa_selectors_def fst_conv snd_conv prod.collapse)
apply simp
done

schematic_goal NFA_construct_reachable_impl_code_aux: 
fixes D_it :: "'q2_rep \<Rightarrow> (('as \<times> 'q2_rep),('m \<times> nat) \<times> 'd \<times> 'q2_rep list) set_iterator"
assumes D_it_OK[rule_format, refine_transfer]: "\<forall>q. q2_invar q \<longrightarrow> q2_\<alpha> q \<in> S \<longrightarrow> set_iterator (D_it q) (DS q)"
shows "RETURN ?f \<le> NFA_construct_reachable_impl det S I A FP DS"
    unfolding NFA_construct_reachable_impl_alt_def WORKLISTT_def NFA_construct_reachable_impl_step_def
    apply (unfold split_def snd_conv fst_conv prod.collapse)
    apply (rule refine_transfer | assumption | erule conjE)+
done

definition (in nfa_by_lts_defs) NFA_construct_reachable_impl_code where
"NFA_construct_reachable_impl_code add_labels qm_ops det (ff::'q2_rep \<Rightarrow> 'i) I A FP D_it =
(let ((qm, n), Is) = foldl (\<lambda>((qm, n), Is) q. ((map_op_update_dj qm_ops (ff q) (states_enumerate n) qm, Suc n),
                             s.ins_dj (states_enumerate n) Is))
                           ((map_op_empty qm_ops (), 0), s.empty ()) I;
     ((_, AA::('q_set, 'a_set, 'd) NFA_impl), _) = worklist (\<lambda>_. True)
        (\<lambda>((qm, n), Qs, As, DD, Is, Fs, p) (q::'q2_rep).
            let r = the (map_op_lookup qm_ops (ff q) qm)
            in if set_op_memb s_ops r Qs then (((qm, n), Qs, As, DD, Is, Fs, p), [])
               else let ((qm', n'), DD', N) = D_it q (\<lambda>_::(('m \<times> nat) \<times> 'd \<times> 'q2_rep list). True)
                           (\<lambda>(a, q') ((qm::'m, n::nat), DD'::'d, N::'q2_rep list).
                               let r'_opt = map_op_lookup qm_ops (ff q') qm; 
                                   ((qm', n'), r') = if r'_opt = None then 
                                       let r'' = states_enumerate n in 
                                          ((map_op_update_dj qm_ops (ff q') r'' qm, Suc n), r'') 
                                      else ((qm, n), the r'_opt)
                               in ((qm', n'), add_labels det r a r' DD', q' # N))
                           ((qm, n), DD, [])
                    in (((qm', n'), set_op_ins_dj s_ops r Qs, As, DD', Is, if FP q then set_op_ins_dj s_ops r Fs else Fs, 
                         p), N))
        (((qm, n), set_op_empty s_ops (), A, lts_op_empty d_ops (), Is, set_op_empty s_ops (), nfa_props_connected det), I)
 in AA)"

lemma NFA_construct_reachable_impl_code_correct: 
fixes D_it :: "'q2_rep \<Rightarrow> (('as \<times> 'q2_rep),('m \<times> nat) \<times> 'd \<times> 'q2_rep list) set_iterator"
assumes D_it_OK: "\<forall>q. q2_invar q \<longrightarrow> q2_\<alpha> q \<in> S \<longrightarrow> set_iterator (D_it q) (DS q)"
shows "RETURN (NFA_construct_reachable_impl_code add_labels qm_ops det ff I A FP D_it) \<le> 
               NFA_construct_reachable_impl det S I A FP DS"
proof -
  have rule: "\<And>f1 f2. \<lbrakk>RETURN f1 \<le> NFA_construct_reachable_impl det S I A FP DS; f1 = f2\<rbrakk> \<Longrightarrow>
                       RETURN f2 \<le> NFA_construct_reachable_impl det S I A FP DS" by simp

  note aux_thm = NFA_construct_reachable_impl_code_aux[OF D_it_OK, of I det FP A]

  note rule' = rule[OF aux_thm]
  show ?thesis 
    apply (rule rule')
    apply (simp add: NFA_construct_reachable_impl_code_def split_def Let_def NFA_construct_reachable_init_impl_def
                cong: if_cong)
  done
qed


lemma NFA_construct_reachable_impl_code_correct_full: 
fixes D_it :: "'q2_rep \<Rightarrow> (('as \<times> 'q2_rep),('m \<times> nat) \<times> 'd \<times> 'q2_rep list) set_iterator"
fixes II D
defines "S \<equiv> accessible (LTS_forget_labels D) (set (map q2_\<alpha> II))"
assumes f_inj_on: "inj_on f S"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and d_add_OK: "dlts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels True)"
                  "lts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels False)"
    and det_OK: "det \<Longrightarrow> LTS_is_deterministic D"
    and DS_q_OK: "\<And>q a q'. q \<in> S \<Longrightarrow> ((q, a, q') \<in> D) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS_q q)"
               "\<And>q as q'. q \<in> S \<Longrightarrow> (as, q') \<in> DS_q q \<Longrightarrow> as \<noteq> {}"
    and dist_I: "distinct (map q2_\<alpha> II)"
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q" 
    and invar_A: "l.invar A"
    and fin_S: "finite S"
    and fin_D: "\<And>q. finite {(a, q'). (q, a, q') \<in> D}"
    and D_it_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> set_iterator_abs 
                      (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (\<lambda>(as, q). a_invar as \<and> q2_invar q) (D_it q) (DS_q (q2_\<alpha> q))"
    and FFP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> FFP q \<longleftrightarrow> FP (q2_\<alpha> q)"
shows "NFA_isomorphic (NFA_construct_reachable (set (map q2_\<alpha> II)) (l.\<alpha> A) FP D)
         (nfa_\<alpha> (NFA_construct_reachable_impl_code add_labels qm_ops det ff II A FFP D_it)) \<and>
       nfa_invar_no_props (NFA_construct_reachable_impl_code add_labels qm_ops det ff II A FFP D_it) \<and>
       nfa_props (NFA_construct_reachable_impl_code add_labels qm_ops det ff II A FFP D_it) =
       nfa_props_connected det"
proof - 

  { fix q
    assume "q2_invar q" "q2_\<alpha> q \<in> S"
    with D_it_OK[of q] 
    have it_abs: "set_iterator_abs (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (\<lambda>(as, q). a_invar as \<and> q2_invar q) 
          (D_it q) (DS_q (q2_\<alpha> q))"
      by simp

    note set_iterator_abs_genord.remove_abs2 [OF it_abs[unfolded set_iterator_abs_def], 
       folded set_iterator_def]    
  }
  then obtain DS where
        DS_props: "\<forall>q. q2_invar q \<longrightarrow> q2_\<alpha> q \<in> S \<longrightarrow> 
             set_iterator (D_it q) (DS q) \<and> inj_on (\<lambda>(as, q'). (a_\<alpha> as, q2_\<alpha> q')) (DS q) \<and>
             (\<lambda>(as, q'). (a_\<alpha> as, q2_\<alpha> q')) ` (DS q) = (DS_q (q2_\<alpha> q)) \<and>
             (\<forall>(as, q') \<in> DS q. a_invar as \<and> q2_invar q')"
    by metis

  from DS_props have
        D_it_OK': "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> set_iterator (D_it q) (DS q)" and
        inj_on_DS: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> inj_on (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (DS q)" and
        DS_q_alt_eq: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) ` (DS q) = (DS_q (q2_\<alpha> q))" and
        invar_DS_q: "\<And>q as q'. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> S \<Longrightarrow> (as, q') \<in> DS q \<Longrightarrow> a_invar as \<and> q2_invar q'"
    by auto

  from NFA_construct_reachable_impl_code_correct [of S D_it DS det II A FFP] D_it_OK'
  have step1: "RETURN (NFA_construct_reachable_impl_code add_labels qm_ops det ff  II A FFP D_it)
     \<le> NFA_construct_reachable_impl det S II A FFP DS" by simp

  { fix q
    assume q_props: "q2_invar q" "q2_\<alpha> q \<in> S"
    from inj_on_DS[OF q_props] invar_DS_q[OF q_props]
    have "(DS q, DS_q (q2_\<alpha> q)) \<in> NFA_construct_reachable_impl_step_rel"
      unfolding NFA_construct_reachable_impl_step_rel_def
      by (auto simp add: DS_q_alt_eq[OF q_props, symmetric] inj_on_def in_br_conv)
  } note DS_in_step_rel = this

  from NFA_construct_reachable_impl_correct [OF f_inj_on[unfolded S_def] ff_OK[unfolded S_def]
    d_add_OK det_OK _ dist_I invar_I invar_A, of det DS_q DS FFP FP, folded S_def] FFP_OK DS_in_step_rel DS_q_OK
  have step2: "NFA_construct_reachable_impl det S II A FFP DS \<le> \<Down> 
       (br nfa_\<alpha> (\<lambda>A. nfa_invar_no_props A \<and> nfa_props A = nfa_props_connected det))
     (NFA_construct_reachable_abstract2_impl (map q2_\<alpha> II) (l.\<alpha> A) FP D DS_q)" 
    by simp

  { fix q
    assume q_in_S: "q \<in> S" 
    
    from DS_q_OK(1)[OF q_in_S]
    have "{(a, q'). (q, a, q') \<in> D} = \<Union> ((\<lambda>(as, q'). {(a, q') |a. a \<in> as}) ` (DS_q q))"
      by (auto simp add: set_eq_iff Bex_def)
    with fin_D[of q] have "finite (\<Union> ((\<lambda>(as, q'). {(a, q') |a. a \<in> as}) ` (DS_q q)))"
      by simp
    hence "finite ((\<lambda>(as, q'). {(a, q') |a. a \<in> as}) ` (DS_q q))" 
      by (rule finite_UnionD)
    hence "finite (DS_q q)"
    proof (rule finite_imageD)
      show "inj_on (\<lambda>(as, q'). {(a, q') |a. a \<in> as}) (DS_q q)"
        unfolding inj_on_def 
      proof (clarify)
        fix as1 q1 as2 q2
        assume in_DS_q1: "(as1, q1) \<in> DS_q q" and in_DS_q2: "(as2, q2) \<in> DS_q q" and
               set_eq: "{(a, q1) |a. a \<in> as1} = {(a, q2) |a. a \<in> as2}"

        from DS_q_OK(2) [OF q_in_S in_DS_q1] have "as1 \<noteq> {}" .
        from DS_q_OK(2) [OF q_in_S in_DS_q2] have "as2 \<noteq> {}" .

        from `as1 \<noteq> {}` `as2 \<noteq> {}` set_eq have q2_eq[simp]: "q2 = q1" by auto
        from set_eq have "as1 = as2" by auto
        thus "as1 = as2 \<and> q1 = q2" by simp
      qed
    qed
  }             
  with NFA_construct_reachable_abstract2_impl_correct_full[of D "map q2_\<alpha> II" DS_q "l.\<alpha> A"
     FP, folded S_def, OF fin_S] DS_q_OK
  have step3: "NFA_construct_reachable_abstract2_impl (map q2_\<alpha> II) (set_op_\<alpha> l_ops A) FP D DS_q \<le> SPEC
      (NFA_isomorphic (NFA_construct_reachable (set (map q2_\<alpha> II)) (set_op_\<alpha> l_ops A) FP D))"
    by auto
  
  note step1 also note step2 also note step3
  finally have "RETURN (NFA_construct_reachable_impl_code add_labels qm_ops det ff II A FFP D_it) \<le> \<Down> 
         (br nfa_\<alpha> (\<lambda>A. nfa_invar_no_props A \<and> nfa_props A = nfa_props_connected det))
     (SPEC (NFA_isomorphic (NFA_construct_reachable (set (map q2_\<alpha> II)) (l.\<alpha> A) FP D)))"
    by simp
  thus ?thesis 
    by (erule_tac RETURN_ref_SPECD) (simp_all add: in_br_conv)
qed

lemma NFA_construct_reachable_impl_code_correct___remove_unreachable: 
fixes D_it :: "'q2_rep \<Rightarrow> (('as \<times> 'q2_rep),('m \<times> nat) \<times> 'd \<times> 'q2_rep list) set_iterator"
fixes II D
assumes f_inj_on: "inj_on f (\<Q> \<A>)"
    and ff_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> (\<Q> \<A>) \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
    and d_add_OK: "dlts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels True)"
                  "lts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels False)"
    and DS_q_OK: "\<And>q a q'. q \<in> \<Q> \<A> \<Longrightarrow> ((q, a, q') \<in> \<Delta> \<A>) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS_q q)"
               "\<And>q as q'. q \<in> \<Q> \<A> \<Longrightarrow> (as, q') \<in> DS_q q \<Longrightarrow> as \<noteq> {}"
    and dist_I: "distinct (map q2_\<alpha> II)"
    and invar_I: "\<And>q. q \<in> set II \<Longrightarrow> q2_invar q" 
    and invar_A: "l.invar A"
    and I_OK: "set (map q2_\<alpha> II) = \<I> \<A>"
    and A_OK: "l.\<alpha> A = \<Sigma> \<A>"
    and D_it_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs 
                      (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (\<lambda>(as, q). a_invar as \<and> q2_invar q) (D_it q) (DS_q (q2_\<alpha> q))"
    and FP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> FP q \<longleftrightarrow> (q2_\<alpha> q) \<in> \<F> \<A>"
    and wf_\<A>: "NFA \<A>"
    and det_OK: "det \<Longrightarrow> DFA \<A>"
shows "nfa_invar (NFA_construct_reachable_impl_code add_labels qm_ops det ff II A FP D_it) \<and>
       NFA_isomorphic_wf (nfa_\<alpha> (NFA_construct_reachable_impl_code add_labels qm_ops det ff II A FP D_it))
                         (NFA_remove_unreachable_states \<A>)"
proof -
  interpret NFA \<A> by fact
  define S where "S \<equiv> accessible (LTS_forget_labels (\<Delta> \<A>)) (set (map q2_\<alpha> II))"
  from LTS_is_reachable_from_initial_finite I_OK have fin_S: "finite S" unfolding S_def by simp
  from LTS_is_reachable_from_initial_subset I_OK have S_subset: "S \<subseteq> \<Q> \<A>" unfolding S_def by simp
  from f_inj_on S_subset have f_inj_on': "inj_on f S" unfolding S_def by (rule subset_inj_on)

  { fix q
    have "{(a, q'). (q, a, q') \<in> \<Delta> \<A>} = (\<lambda>(q,a,q'). (a,q')) ` {(q, a, q') | a q'. (q, a, q') \<in> \<Delta> \<A>}"
      by (auto simp add: image_iff)
    hence "finite {(a, q'). (q, a, q') \<in> \<Delta> \<A>}"
      apply simp
      apply (rule finite_imageI)
      apply (rule finite_subset [OF _ finite_\<Delta>])
      apply auto
    done
  } note fin_D = this

  from det_OK have det_OK': "det \<Longrightarrow> LTS_is_deterministic (\<Delta> \<A>)" 
    unfolding DFA_alt_def SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def
    by simp

  let ?FP = "\<lambda>q. q \<in> \<F> \<A>"
  let ?I = "map q2_\<alpha> II"
  define code where "code \<equiv> NFA_construct_reachable_impl_code add_labels qm_ops det ff II A FP D_it"
  from NFA_construct_reachable_impl_code_correct_full [of "\<Delta> \<A>" II, folded S_def,
    OF f_inj_on' ff_OK d_add_OK _ _ _ dist_I invar_I invar_A fin_S fin_D, of det DS_q D_it FP, 
    where ?FP = ?FP,
    OF _ _ det_OK' DS_q_OK(1)] 
    S_subset DS_q_OK(2) FP_OK D_it_OK
  have step1:
    "NFA_isomorphic (NFA_construct_reachable (set ?I) (l.\<alpha> A) ?FP (\<Delta> \<A>)) (nfa_\<alpha> code)"
    "nfa_invar_no_props code" 
    "nfa_props code = nfa_props_connected det" 
      apply (simp_all add: subset_iff code_def[symmetric])
      apply metis+
  done

  from NFA.NFA_remove_unreachable_states_implementation [OF wf_\<A> I_OK A_OK, of "?FP" "\<Delta> \<A>"]
  have step2: "NFA_construct_reachable (set ?I) (l.\<alpha> A) ?FP (\<Delta> \<A>) = 
               NFA_remove_unreachable_states \<A>" by simp
 
  from step1(1) step2 NFA_remove_unreachable_states___is_well_formed [OF wf_\<A>] have 
    step3: "NFA_isomorphic_wf (NFA_remove_unreachable_states \<A>) (nfa_\<alpha> code)"
    by (simp add: NFA_isomorphic_wf_def)

  from step3 have step4: "NFA (nfa_\<alpha> code)"
    unfolding NFA_isomorphic_wf_alt_def by simp

  have step5: "SemiAutomaton_is_initially_connected (nfa_\<alpha> code)"
  proof -
    have "SemiAutomaton_is_initially_connected (NFA_remove_unreachable_states \<A>)"
      by (fact NFA.SemiAutomaton_is_initially_connected___NFA_remove_unreachable_states)
    with SemiAutomaton_is_initially_connected___NFA_isomorphic_wf[OF step3]
    show ?thesis by simp
  qed

  have step6: "det \<Longrightarrow> SemiAutomaton_is_complete_deterministic (nfa_\<alpha> code)"
  proof -
    assume det
    with det_OK have "DFA \<A>" by simp
    hence "DFA (NFA_remove_unreachable_states \<A>)" by (metis DFA___NFA_remove_unreachable_states)
    with NFA_isomorphic_wf___DFA[OF step3] have "DFA (nfa_\<alpha> code)" by simp
    thus "SemiAutomaton_is_complete_deterministic (nfa_\<alpha> code)"
      unfolding DFA_alt_def by simp
  qed

  from step3 step1(2) step4 step6 show ?thesis
    unfolding nfa_invar_alt_def code_def[symmetric]
    apply (simp add: nfa_invar_props_def step1(3) step5)
    apply (metis NFA_isomorphic_wf_sym)
  done
qed
end

context nfa_by_lts_defs
begin

lemma NFA_construct_reachable_impl_code_correct_label_sets :
  fixes qm_ops :: "('i, 'q::{automaton_states}, 'm, _) map_ops_scheme" 
    and q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2"
    and q2_invar :: "'q2_rep \<Rightarrow> bool" 
    and a_\<alpha> :: "'as \<Rightarrow> 'a set"                                               
    and a_invar :: "'as \<Rightarrow> bool" 
  assumes "StdMap qm_ops"
      and add_labels_OK: "lts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels False)"
                         "dlts_add_label_set d.\<alpha> d.invar a_\<alpha> a_invar (add_labels True)"
  shows "nfa_dfa_construct_label_sets nfa_\<alpha> nfa_invar l.\<alpha> l.invar q2_\<alpha> q2_invar a_\<alpha> a_invar 
                 (NFA_construct_reachable_impl_code add_labels qm_ops)"
proof (intro nfa_dfa_construct_label_sets.intro nfa_by_lts_correct nfa_dfa_construct_label_sets_axioms.intro)
  fix \<A>:: "('q2, 'a) NFA_rec" and f :: "'q2 \<Rightarrow> 'i" and ff I A FP DS_q det
  fix D_it :: "'q2_rep \<Rightarrow> (('as \<times> 'q2_rep),('m \<times> nat) \<times> 'd \<times> 'q2_rep list) set_iterator"
  assume wf_\<A>: "NFA \<A>" 
     and det_OK: "det \<Longrightarrow> DFA \<A>"
     and f_inj_on: "inj_on f (\<Q> \<A>)"
     and f_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> (\<Q> \<A>) \<Longrightarrow> ff q = f (q2_\<alpha> q)" 
     and dist_I: "distinct (map q2_\<alpha> I)"
     and invar_I: "\<And>q. q \<in> set I \<Longrightarrow> q2_invar q"
     and I_OK: "q2_\<alpha> ` set I = \<I> \<A>"
     and invar_A: "set_op_invar l_ops A"
     and A_OK: "set_op_\<alpha> l_ops A = \<Sigma> \<A>"
     and FP_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> FP q = (q2_\<alpha> q \<in> \<F> \<A>)"
     and D_it_OK: "\<And>q. q2_invar q \<Longrightarrow> q2_\<alpha> q \<in> \<Q> \<A> \<Longrightarrow> set_iterator_abs 
             (\<lambda>(as, q). (a_\<alpha> as, q2_\<alpha> q)) (\<lambda>(as, q). a_invar as \<and> q2_invar q) (D_it q) 
             (DS_q (q2_\<alpha> q))"
     and DS_OK: "\<And>q a q'. q \<in> \<Q> \<A> \<Longrightarrow> ((q, a, q') \<in> \<Delta> \<A>) = (\<exists>as. a \<in> as \<and> (as, q') \<in> DS_q q)"
         "\<And>q as q'. q \<in> \<Q> \<A> \<Longrightarrow> (as, q') \<in> DS_q q \<Longrightarrow> as \<noteq> {}"

  interpret reach: NFA_construct_reachable_locale s_ops l_ops d_ops qm_ops a_\<alpha> a_invar add_labels f ff q2_\<alpha> q2_invar 
    using nfa_by_lts_defs_axioms add_labels_OK `StdMap qm_ops` 
    unfolding NFA_construct_reachable_locale_def nfa_by_lts_defs_def by simp

  note correct = reach.NFA_construct_reachable_impl_code_correct___remove_unreachable
    [OF f_inj_on f_OK, of DS_q, OF _ _ _ _ _ _ dist_I invar_I invar_A _ A_OK _ _ wf_\<A>, of D_it FP det]

  show "nfa_invar (NFA_construct_reachable_impl_code add_labels qm_ops det ff I A FP D_it) \<and>
       NFA_isomorphic_wf (nfa_\<alpha> (NFA_construct_reachable_impl_code add_labels qm_ops det ff I A FP D_it))
        (NFA_remove_unreachable_states \<A>)"
     apply (rule_tac correct)
     apply (simp_all add: I_OK FP_OK reach.NFA_construct_reachable_impl_step_rel_def DS_OK D_it_OK
              add_labels_OK lts_add_label_set_sublocale det_OK)
  done
qed

lemma NFA_construct_reachable_impl_code_correct :
  fixes qm_ops :: "('i, 'q::{automaton_states}, 'm, _) map_ops_scheme" 
    and q2_\<alpha> :: "'q2_rep \<Rightarrow> 'q2"
    and q2_invar :: "'q2_rep \<Rightarrow> bool" 
  assumes qm_OK: "StdMap qm_ops" and
          d_add_OK: "lts_dlts_add d.\<alpha> d.invar d_add"
  shows "NFASpec.nfa_dfa_construct nfa_\<alpha> nfa_invar l.\<alpha> l.invar q2_\<alpha> q2_invar 
                 (NFA_construct_reachable_impl_code d_add qm_ops)"
apply (intro nfa_dfa_construct_default NFA_construct_reachable_impl_code_correct_label_sets assms)
apply (insert d_add_OK)
apply (simp_all add: lts_add_label_set_def dlts_add_label_set_def lts_dlts_add_def lts_add_def dlts_add_def)
done

lemma NFA_construct_reachable_impl_code_correct_no_enc:
  assumes qm_OK: "StdMap qm_ops"
      and d_add_OK: "lts_dlts_add d.\<alpha> d.invar d_add"
  shows "NFASpec.nfa_dfa_construct_no_enc nfa_\<alpha> nfa_invar l.\<alpha> l.invar 
       (NFA_construct_reachable_impl_code d_add qm_ops)"
by (intro NFAGA.nfa_dfa_construct_no_enc_default NFA_construct_reachable_impl_code_correct d_add_OK qm_OK)


subsection \<open> normalise \<close>

definition nfa_normalise_impl where
  "nfa_normalise_impl d_add qm_ops sl_it = (\<lambda>(Q::'q_set, A::'a_set, D::'d, I::'q_set, F::'q_set, p).
   (if (nfa_prop_is_initially_connected p) then (Q, A, D, I, F, p) else
    NFA_construct_reachable_impl_code d_add qm_ops (nfa_prop_is_complete_deterministic p)
      id (s.to_list I) A (\<lambda>q. s.memb q F) (sl_it D)))"

lemma nfa_normalise_correct :
  assumes qm_OK: "StdMap qm_ops"
      and d_add_OK: "lts_dlts_add d.\<alpha> d.invar d_add"
      and ls_it_OK: "lts_succ_label_it d.\<alpha> d.invar sl_it"
  shows "nfa_normalise nfa_\<alpha> nfa_invar (nfa_normalise_impl d_add qm_ops sl_it)"
proof (intro nfa_normalise.intro nfa_normalise_axioms.intro nfa_by_lts_correct)
  fix n
  assume invar: "nfa_invar n"
  obtain Q A D I F p where n_eq[simp]: "n = (Q, A, D, I, F, p)" by (metis prod.exhaust)

  from invar have nfa_n: "NFA (nfa_\<alpha> n)"  unfolding nfa_invar_full_def by simp

  have dfa_n: "nfa_prop_is_complete_deterministic p \<Longrightarrow> DFA (nfa_\<alpha> n)" 
    using nfa_invar_implies_DFA[OF invar] by simp

  have connected_n: "nfa_prop_is_initially_connected p \<Longrightarrow> SemiAutomaton_is_initially_connected (nfa_\<alpha> n)" 
    using invar unfolding nfa_invar_full_def by simp

  have "nfa_invar (nfa_normalise_impl d_add qm_ops sl_it n) \<and>
        NFA_isomorphic_wf
         (nfa_\<alpha> (nfa_normalise_impl d_add qm_ops sl_it n))
         (NFA_remove_unreachable_states (nfa_\<alpha> n))" 
  proof (cases "nfa_prop_is_initially_connected p")
    case True note conn = this

    from connected_n[OF conn] have idem: "NFA_remove_unreachable_states (nfa_\<alpha> n) =  (nfa_\<alpha> n)"
      using NFA_remove_unreachable_states_no_change[OF nfa_n] by simp
    with invar show ?thesis 
      apply (simp add: nfa_normalise_impl_def conn)
      apply (simp add: NFA_isomorphic_wf_refl nfa_invar_alt_def)
    done
  next
    case False note not_conn = this

    note ls_it' = lts_succ_label_it.lts_succ_label_it_correct [OF ls_it_OK, of D]
    from invar have invars: "s.invar Q \<and> l.invar A \<and> d.invar D \<and> s.invar I \<and> s.invar F" 
      unfolding nfa_invar_full_def by simp
 
    note const_OK = NFA_construct_reachable_impl_code_correct_no_enc [OF qm_OK d_add_OK]
    note correct = nfa_dfa_construct_no_enc.nfa_dfa_construct_no_enc_correct 
        [OF const_OK, of "nfa_\<alpha> n" "nfa_prop_is_complete_deterministic p" id 
                         "s.to_list I" A "\<lambda>q. s.memb q F" "sl_it D"]
    with nfa_n dfa_n ls_it' show ?thesis 
      by (simp_all add: s.correct set_iterator_def nfa_normalise_impl_def not_conn invars) 
  qed
  thus "nfa_invar (nfa_normalise_impl d_add qm_ops sl_it n)"
       "NFA_isomorphic_wf
         (nfa_\<alpha> (nfa_normalise_impl d_add qm_ops sl_it n))
         (NFA_remove_unreachable_states (nfa_\<alpha> n))" by simp_all
qed 
 

subsection \<open> Reverse \<close>

definition nfa_reverse_impl :: "_ \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl" where
  "nfa_reverse_impl rf = (\<lambda>(Q, A, D, I, F, p). (Q, A, rf D, F, I, nfa_props_trivial))"

lemma nfa_reverse_impl_correct :
fixes l_ops' :: "('a2, 'a2_set, _) set_ops_scheme"
assumes wf_target: "nfa_by_lts_defs s_ops l_ops d_ops'" 
assumes rf_OK: "lts_reverse d.\<alpha> d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') rf"
shows "nfa_reverse nfa_\<alpha> nfa_invar
           (nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops d_ops') 
           (nfa_by_lts_defs.nfa_invar s_ops l_ops d_ops')
           (nfa_reverse_impl rf)"
proof (intro nfa_reverse.intro nfa_reverse_axioms.intro 
             nfa_by_lts_defs.nfa_by_lts_correct)
  show "nfa_by_lts_defs s_ops l_ops d_ops" by (fact nfa_by_lts_defs_axioms)
  show "nfa_by_lts_defs s_ops l_ops d_ops'" by (intro nfa_by_lts_defs_axioms wf_target)

  fix n
  assume invar: "nfa_invar n"
  obtain QL AL DL IL FL p where n_eq[simp]: "n = (QL, AL, DL, IL, FL, p)" by (cases n, blast)

  from invar have invar_no_props: "nfa_invar_no_props n" and wf: "NFA (nfa_\<alpha> n)" and
                  invar_props: "nfa_invar_no_props n"
    unfolding nfa_invar_alt_def by simp_all

  let ?nfa_\<alpha>' = "nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops d_ops'"
  let ?nfa_invar_no_props' = "nfa_by_lts_defs.nfa_invar_no_props s_ops l_ops d_ops'"
  let ?nfa_invar' = "nfa_by_lts_defs.nfa_invar s_ops l_ops d_ops'"

  from invar_no_props rf_OK
  have "?nfa_invar_no_props' (nfa_reverse_impl rf n) \<and> 
        ?nfa_\<alpha>' (nfa_reverse_impl rf n) = NFA_reverse (nfa_\<alpha> n)"
    apply (simp add: nfa_by_lts_defs.nfa_invar_no_props_def[OF wf_target]  
                     nfa_by_lts_defs.nfa_\<alpha>_def [OF wf_target]
                     nfa_by_lts_defs.nfa_selectors_def[OF wf_target]
                     nfa_invar_no_props_def
                     nfa_reverse_impl_def NFA_reverse_def
                     s.correct NFA_rename_states_def d.correct_common lts_reverse_def)
    apply auto
  done

  with wf 
  show "?nfa_\<alpha>' (nfa_reverse_impl rf n) = NFA_reverse (nfa_\<alpha> n)" 
       "?nfa_invar' (nfa_reverse_impl rf n)"
    unfolding nfa_by_lts_defs.nfa_invar_alt_def[OF wf_target] 
    apply (simp_all add: NFA_reverse___is_well_formed)
    apply (simp add: nfa_reverse_impl_def
                     nfa_by_lts_defs.nfa_invar_props_def[OF wf_target]
                     nfa_by_lts_defs.nfa_selectors_def[OF wf_target])
  done
qed


subsection \<open> Complement \<close>

definition nfa_complement_impl :: "('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl"  where
  "nfa_complement_impl = (\<lambda>(Q, A, D, I, F, p). (Q, A, D, I, s.diff Q F, p))"

lemma nfa_complement_impl_correct :
shows "nfa_complement nfa_\<alpha> nfa_invar nfa_complement_impl"
proof (intro nfa_complement.intro nfa_complement_axioms.intro)
  show "nfa nfa_\<alpha> nfa_invar" by simp

  fix n
  assume invar: "nfa_invar n"
  obtain QL AL DL IL FL p where n_eq: "n = (QL, AL, DL, IL, FL, p)" by (cases n, blast)

  from invar have invar_no_props: "nfa_invar_no_props n" and wf: "NFA (nfa_\<alpha> n)" and
                  invar_props: "nfa_invar_props n"
    unfolding nfa_invar_alt_def by simp_all

  from invar_no_props
  have invar_no_props': "nfa_invar_no_props (nfa_complement_impl n)" and 
       \<alpha>_eq: "nfa_\<alpha> (nfa_complement_impl n) = DFA_complement (nfa_\<alpha> n)"
    by (simp_all add: nfa_invar_no_props_def nfa_\<alpha>_def n_eq
                      DFA_complement_def nfa_complement_impl_def
                      s.correct NFA_rename_states_def d.correct_common lts_reverse_def)

  show "nfa_\<alpha> (nfa_complement_impl n) = DFA_complement (nfa_\<alpha> n)" by (fact \<alpha>_eq)

  from invar_props have invar_props': "nfa_invar_props (nfa_complement_impl n)"
    apply (simp add: nfa_invar_props_def \<alpha>_eq DFA_complement_alt_def)
    apply (simp add: nfa_complement_impl_def n_eq)
  done

  from wf
  show "nfa_invar (nfa_complement_impl n)"
    unfolding nfa_invar_alt_def \<alpha>_eq
    by (simp_all add: DFA_complement___is_well_formed invar_no_props' invar_props')
qed


subsection \<open> Boolean combinations \<close>

definition product_iterator where
  "product_iterator (it_1::'q1 \<Rightarrow> ('a \<times> 'q1, '\<sigma>) set_iterator)
     (it_2::'q2 \<Rightarrow> 'a \<Rightarrow> ('q2, '\<sigma>) set_iterator) = (\<lambda>(q1, q2).
   set_iterator_image (\<lambda>((a, q1'), q2'). (a, (q1', q2'))) (set_iterator_product (it_1 q1) 
     (\<lambda>aq. it_2 q2 (fst aq))))"

lemma product_iterator_alt_def :
"product_iterator it_1 it_2 = 
 (\<lambda>(q1, q2) c f. it_1 q1 c (\<lambda>(a,q1'). it_2 q2 a c (\<lambda>q2'. f (a, q1', q2'))))"
unfolding product_iterator_def set_iterator_image_alt_def set_iterator_product_def
by (auto simp add: split_def)

lemma product_iterator_correct :
fixes D1 :: "('q1 \<times> 'a \<times> 'q1) set"
fixes D2 :: "('q2 \<times> 'a \<times> 'q2) set"
assumes it_1_OK: "set_iterator (it_1 q1) {(a, q1'). (q1, a, q1') \<in> D1}"
    and it_2_OK: "\<And>a. set_iterator (it_2 q2 a) {q2'. (q2, a, q2') \<in> D2}"
shows "set_iterator (product_iterator it_1 it_2 (q1, q2)) 
          {(a, (q1', q2')). ((q1, q2), a, (q1', q2')) \<in> LTS_product D1 D2}"
proof -
  from it_2_OK have it_2_OK': 
    "\<And>aq. set_iterator (((it_2 q2) \<circ> fst) aq) {q2'. (q2, (fst aq), q2') \<in> D2}" by simp

  note thm_1 = set_iterator_product_correct [where ?it_a = "it_1 q1" and 
    ?it_b = "(it_2 q2) \<circ> fst", OF it_1_OK it_2_OK']

  let ?f = "\<lambda>((a, q1'), q2'). (a, (q1', q2'))"
  have inj_on_f: "\<And>S. inj_on ?f S"
    unfolding inj_on_def by auto

  note thm_2 = set_iterator_image_correct [OF thm_1 inj_on_f]

  let ?Sigma = "(SIGMA a:{(a, q1'). (q1, a, q1') \<in> D1}. {q2'. (q2, fst a, q2') \<in> D2})"
  have "?f ` ?Sigma = {(a, (q1', q2')). ((q1, q2), a, (q1', q2')) \<in> LTS_product D1 D2}"
    by (auto simp add: image_iff)
  with thm_2 show ?thesis by (simp add: product_iterator_def o_def)
qed

definition bool_comb_impl_aux where
"bool_comb_impl_aux const det f it_1 it_2 I I' FP FP' =
 (\<lambda>A' bc AA1 AA2. const (det AA1 AA2) f (List.product (I AA1) (I' AA2)) A'
  (\<lambda>(q1', q2'). bc (FP AA1 q1') (FP' AA2 q2')) (product_iterator (it_1 AA1) (it_2 AA2)))"
 
lemma bool_comb_impl_aux_correct :
assumes const_OK: "nfa_dfa_construct_no_enc \<alpha>3 invar3 \<alpha>_s invar_s const"
    and nfa_1_OK: "nfa \<alpha>1 invar1"
    and nfa_2_OK: "nfa \<alpha>2 invar2"
    and f_inj_on: "\<And>n1 n2. inj_on f (\<Q> (\<alpha>1 n1) \<times> \<Q> (\<alpha>2 n2))"
    and I1_OK: "\<And>n1. invar1 n1 \<Longrightarrow> distinct (I1 n1) \<and> set (I1 n1) = \<I> (\<alpha>1 n1)" 
    and I2_OK: "\<And>n2. invar2 n2 \<Longrightarrow> distinct (I2 n2) \<and> set (I2 n2) = \<I> (\<alpha>2 n2)"
    and FP1_OK: "\<And>n1 q. invar1 n1 \<Longrightarrow> q \<in> \<Q> (\<alpha>1 n1) \<Longrightarrow> FP1 n1 q \<longleftrightarrow> (q \<in> \<F> (\<alpha>1 n1))"
    and FP2_OK: "\<And>n2 q. invar2 n2 \<Longrightarrow> q \<in> \<Q> (\<alpha>2 n2) \<Longrightarrow> FP2 n2 q \<longleftrightarrow> (q \<in> \<F> (\<alpha>2 n2))"
    and det_OK: "\<And>n1 n2. invar1 n1 \<Longrightarrow> invar2 n2 \<Longrightarrow> det n1 n2 \<Longrightarrow> DFA (\<alpha>1 n1) \<and> DFA (\<alpha>2 n2)"
    and it_1_OK: "\<And>n1 q. invar1 n1 \<Longrightarrow> set_iterator (it_1 n1 q) {(a, q'). (q, a, q') \<in> \<Delta> (\<alpha>1 n1)}"
    and it_2_OK: "\<And>n2 q a. invar2 n2 \<Longrightarrow> set_iterator (it_2 n2 q a) 
                             {q'. (q, a, q') \<in> \<Delta> (\<alpha>2 n2)}"
shows "nfa_bool_comb_gen \<alpha>1 invar1 \<alpha>2 invar2 \<alpha>3 invar3 \<alpha>_s invar_s
       (bool_comb_impl_aux const det f it_1 it_2 I1 I2 FP1 FP2)"
proof (intro nfa_bool_comb_gen.intro nfa_1_OK nfa_2_OK nfa_bool_comb_gen_axioms.intro)
  from const_OK show "nfa \<alpha>3 invar3" unfolding nfa_dfa_construct_no_enc_def by simp

  fix n1 n2 as bc
  assume invar_1: "invar1 n1"
     and invar_2: "invar2 n2"
     and invar_s: "invar_s as"
     and as_OK: "\<alpha>_s as = \<Sigma> (\<alpha>1 n1) \<inter> \<Sigma> (\<alpha>2 n2)"
  let ?AA' = "bool_comb_NFA bc (\<alpha>1 n1) (\<alpha>2 n2)"
  have f_inj_on': "inj_on f (\<Q> ?AA')" using f_inj_on by (simp add: bool_comb_NFA_def)

  from invar_1 invar_2 nfa_1_OK nfa_2_OK have AA'_wf: "NFA ?AA'"
    apply (rule_tac NFA.bool_comb_NFA___is_well_formed)
    apply (simp_all add: nfa_def)
  done

  from det_OK[OF invar_1 invar_2] have AA'_wf': "det n1 n2 \<Longrightarrow> DFA ?AA'"
    apply (rule_tac DFA.bool_comb_DFA___is_well_formed)
    apply (simp_all)
  done

  let ?II = "List.product (I1 n1) (I2 n2)"
  have dist_II: "distinct ?II" and set_II: "set ?II = \<I> ?AA'"
    apply (intro List.distinct_product)
    apply (insert I1_OK[OF invar_1] I2_OK[OF invar_2])
    apply (simp_all)
  done

  from as_OK have as_OK': "\<alpha>_s as = \<Sigma> ?AA'" by simp

  let ?FP = "(\<lambda>(q1', q2'). bc (FP1 n1 q1') (FP2 n2 q2'))"  
  from FP1_OK[OF invar_1] FP2_OK[OF invar_2]
  have FP_OK: "\<And>q. q \<in> \<Q> ?AA' \<Longrightarrow> ?FP q = (q \<in> \<F> ?AA')" by auto

  let ?D_it = "product_iterator (it_1 n1) (it_2 n2)"

  from product_iterator_correct [where ?it_1.0 = "it_1 n1" and ?it_2.0 = "it_2 n2", 
           OF it_1_OK[OF invar_1] it_2_OK[OF invar_2]]
  have D_it_OK: "\<And>q. set_iterator (product_iterator (it_1 n1) (it_2 n2) q)
     {(a, q'). (q, a, q') \<in> \<Delta> ?AA'}" 
    by (case_tac q) (simp add: split_def)

  note construct_correct = nfa_dfa_construct_no_enc.nfa_dfa_construct_no_enc_correct [where det = "det n1 n2", OF const_OK
    AA'_wf AA'_wf' f_inj_on' dist_II set_II, OF _ invar_s as_OK' FP_OK D_it_OK]
  thus "invar3 (bool_comb_impl_aux const det f it_1 it_2 I1 I2 FP1 FP2 as bc n1 n2) \<and> 
        NFA_isomorphic_wf (\<alpha>3 (bool_comb_impl_aux const det f it_1 it_2 I1 I2 FP1 FP2 as bc n1 n2))
        (efficient_bool_comb_NFA bc (\<alpha>1 n1) (\<alpha>2 n2))" 
    by (simp_all add: bool_comb_impl_aux_def efficient_bool_comb_NFA_def)
qed

lemma bool_comb_impl_aux_correct_same :
assumes const_OK: "nfa_dfa_construct_no_enc \<alpha>2 invar2 \<alpha>_s invar_s const"
    and nfa_OK: "nfa \<alpha> invar"
    and f_inj_on: "\<And>n1 n2. inj_on f (\<Q> (\<alpha> n1) \<times> \<Q> (\<alpha> n2))"
    and I_OK: "\<And>n. invar n \<Longrightarrow> distinct (I n) \<and> set (I n) = \<I> (\<alpha> n)" 
    and FP_OK: "\<And>n q. invar n \<Longrightarrow> q \<in> \<Q> (\<alpha> n) \<Longrightarrow> FP n q \<longleftrightarrow> (q \<in> \<F> (\<alpha> n))"
    and det_OK: "\<And>n1 n2. invar n1 \<Longrightarrow> invar n2 \<Longrightarrow> det n1 n2 \<Longrightarrow> DFA (\<alpha> n1) \<and> DFA (\<alpha> n2)"
    and it_1_OK: "\<And>n1 q. invar n1 \<Longrightarrow> set_iterator (it_1 n1 q) {(a, q'). (q, a, q') \<in> \<Delta> (\<alpha> n1)}"
    and it_2_OK: "\<And>n2 q a. invar n2 \<Longrightarrow> set_iterator (it_2 n2 q a) {q'. (q, a, q') \<in> \<Delta> (\<alpha> n2)}"
shows "nfa_bool_comb_gen \<alpha> invar \<alpha> invar \<alpha>2 invar2 \<alpha>_s invar_s
       (bool_comb_impl_aux const det f it_1 it_2 I I FP FP)"
apply (rule bool_comb_impl_aux_correct)
apply (rule const_OK)
apply (rule nfa_OK)
apply (rule nfa_OK)
apply (rule f_inj_on)
apply (rule I_OK, simp)
apply (rule I_OK, simp)
apply (rule FP_OK, simp_all)
apply (rule FP_OK, simp_all)
apply (rule det_OK, simp_all)
apply (rule it_1_OK, simp)
apply (rule it_2_OK, simp)
done

definition bool_comb_gen_impl :: "
   _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl" where
  "bool_comb_gen_impl d_add qm_ops it_1 it_2 A' bc A1 A2 =
   bool_comb_impl_aux (NFA_construct_reachable_impl_code d_add qm_ops) 
     (\<lambda>A1 A2. nfa_prop_is_complete_deterministic (nfa_props A1) \<and> 
              nfa_prop_is_complete_deterministic (nfa_props A2)) 
     id 
     (\<lambda>A. it_1 (nfa_trans A)) (\<lambda>A. it_2 (nfa_trans A))
     (\<lambda>A. (s.to_list (nfa_initial A))) (\<lambda>A. (s.to_list (nfa_initial A))) 
     (\<lambda>A q. s.memb q (nfa_accepting A)) 
     (\<lambda>A q. s.memb q (nfa_accepting A)) A' bc A1 A2"

schematic_goal bool_comb_gen_impl_code :
  "bool_comb_gen_impl d_add qm_ops it_1 it_2 A' bc (Q1, A1, D1, I1, F1, p1) (Q2, A2, D2, I2, F2, p2) = ?XXX"
 unfolding bool_comb_gen_impl_def bool_comb_impl_aux_def product_iterator_alt_def
           nfa_selectors_def snd_conv fst_conv
 by (rule refl)+

lemma bool_comb_gen_impl_correct :
assumes qm_ops_OK: "StdMap qm_ops"
    and d_add_OK: "lts_dlts_add d.\<alpha> d.invar d_add"
    and it_1_OK: "lts_succ_label_it d.\<alpha> d.invar it_1"
    and it_2_OK: "lts_succ_it d.\<alpha> d.invar it_2"
shows "nfa_bool_comb_gen_same nfa_\<alpha> nfa_invar l.\<alpha> l.invar
       (bool_comb_gen_impl d_add qm_ops it_1 it_2)"
proof (intro nfa_bool_comb_gen_same.intro nfa_bool_comb_gen.intro nfa_by_lts_correct
             nfa_bool_comb_gen_axioms.intro)
  fix a1 a2 as bc
  assume invar_1: "nfa_invar a1"
     and invar_2: "nfa_invar a2"
     and invar_s: "l.invar as"
     and as_OK: "l.\<alpha> as = \<Sigma> (nfa_\<alpha> a1) \<inter> \<Sigma> (nfa_\<alpha> a2)"

  note it_1_OK' = lts_succ_label_it.lts_succ_label_it_correct [OF it_1_OK]
  note it_2_OK' = lts_succ_it.lts_succ_it_correct [OF it_2_OK]

  note const_OK = NFA_construct_reachable_impl_code_correct_no_enc [OF qm_ops_OK d_add_OK]

  note correct = nfa_bool_comb_gen.bool_comb_correct_aux [OF bool_comb_impl_aux_correct_same, 
      where as = as and bc=bc, OF const_OK nfa_by_lts_correct]

  show "nfa_invar (bool_comb_gen_impl d_add qm_ops it_1 it_2 as bc a1 a2) \<and>
        NFA_isomorphic_wf
          (nfa_\<alpha> (bool_comb_gen_impl d_add qm_ops it_1 it_2 as bc a1 a2))
          (efficient_bool_comb_NFA bc (nfa_\<alpha> a1) (nfa_\<alpha> a2))"
    unfolding bool_comb_gen_impl_def
  proof (rule correct)
    show "nfa_invar a1" by fact
  next
    show "nfa_invar a2" by fact
  next
    show "l.invar as" by fact
  next
    show "l.\<alpha> as = \<Sigma> (nfa_\<alpha> a1) \<inter> \<Sigma> (nfa_\<alpha> a2)" by fact 
  next
    fix n1 n2 
    show "inj_on id (\<Q> (nfa_\<alpha> n1) \<times> \<Q> (nfa_\<alpha> n2))" by simp
  next
    fix n1
    assume invar_n1: "nfa_invar n1"
    hence invar': "nfa_invar_no_props n1" by (simp add: nfa_invar_alt_def)

    from invar'
    show "distinct (set_op_to_list s_ops (nfa_initial n1)) \<and>
          set (set_op_to_list s_ops (nfa_initial n1)) = \<I> (nfa_\<alpha> n1)"
      unfolding nfa_invar_no_props_def by (simp add: s.correct)

    { fix q 
      from it_1_OK' [of "nfa_trans n1" q] invar'
      show "set_iterator (it_1 (nfa_trans n1) q)
             {(a, q'). (q, a, q') \<in> \<Delta> (nfa_\<alpha> n1)}"
        unfolding nfa_invar_no_props_def by simp
    }

    { fix q a
      from it_2_OK' [of "nfa_trans n1" q] invar'
      show "set_iterator (it_2 (nfa_trans n1) q a) {q'. (q, a, q') \<in> \<Delta> (nfa_\<alpha> n1)}"
        unfolding nfa_invar_no_props_def by simp
    }

    { fix q
      assume "q \<in> \<Q> (nfa_\<alpha> n1)"
      with invar' show "s.memb q (nfa_accepting n1) = (q \<in> \<F> (nfa_\<alpha> n1))"
         unfolding nfa_invar_no_props_def by (simp add: s.correct)
    }
  next
    fix n1 n2
    assume "nfa_invar n1" "nfa_invar n2"
           "nfa_prop_is_complete_deterministic (nfa_props n1) \<and>
            nfa_prop_is_complete_deterministic (nfa_props n2)"
    thus "DFA (nfa_\<alpha> n1) \<and> DFA (nfa_\<alpha> n2)" by (simp add: nfa_invar_implies_DFA)
  qed
qed


definition bool_comb_impl where
     "bool_comb_impl     d_add qm_ops it_1 it_2 bc A1 A2 =
      bool_comb_gen_impl d_add qm_ops it_1 it_2 (nfa_labels A1) bc A1 A2"

schematic_goal bool_comb_impl_code :
  "bool_comb_impl d_add qm_ops it_1 it_2 bc (Q1, A1, D1, I1, F1, p1) (Q2, A2, D2, I2, F2, p2) = ?XXX"
 unfolding bool_comb_impl_def nfa_selectors_def snd_conv fst_conv
 by (rule refl)

lemma bool_comb_impl_correct :
assumes qm_ops_OK: "StdMap qm_ops"
    and d_add_OK: "lts_dlts_add d.\<alpha> d.invar d_add"
    and it_1_OK: "lts_succ_label_it d.\<alpha> d.invar it_1"
    and it_2_OK: "lts_succ_it d.\<alpha> d.invar it_2"
shows "nfa_bool_comb_same nfa_\<alpha> nfa_invar (bool_comb_impl d_add qm_ops it_1 it_2)"
proof (intro nfa_bool_comb_same.intro nfa_bool_comb.intro nfa_by_lts_correct
             nfa_bool_comb_axioms.intro)
  fix n1 n2 bc
  assume invar_n1: "nfa_invar n1"
     and invar_n2: "nfa_invar n2"
     and labels_eq: "\<Sigma> (nfa_\<alpha> n1) = \<Sigma> (nfa_\<alpha> n2)"

  from invar_n1 have invar_labels: "l.invar (nfa_labels n1)" 
    unfolding nfa_invar_alt_def nfa_invar_no_props_def by simp

  have labels_eq: "l.\<alpha> (nfa_labels n1) = \<Sigma> (nfa_\<alpha> n1) \<inter> \<Sigma> (nfa_\<alpha> n2)"
    using labels_eq unfolding nfa_\<alpha>_def by simp

  note bool_comb_gen_OK = bool_comb_gen_impl_correct [OF qm_ops_OK d_add_OK it_1_OK it_2_OK]
  note rule = nfa_bool_comb_gen.bool_comb_correct [OF bool_comb_gen_OK[unfolded nfa_bool_comb_gen_same_def]]
    
  from rule[OF invar_n1 invar_n2 invar_labels labels_eq, of bc]
  show "nfa_invar (bool_comb_impl d_add qm_ops it_1 it_2 bc n1 n2) \<and>
        NFA_isomorphic_wf
          (nfa_\<alpha> (bool_comb_impl d_add qm_ops it_1 it_2 bc n1 n2))
          (efficient_bool_comb_NFA bc (nfa_\<alpha> n1) (nfa_\<alpha> n2))" 
    unfolding bool_comb_impl_def by simp
qed


subsection \<open> right quotient \<close>

definition right_quotient_map_lookup where
  "right_quotient_map_lookup m_ops m q =
   (case (map_op_lookup m_ops q m) of
      None \<Rightarrow> s.empty ()
    | Some S \<Rightarrow> S)"

definition right_quotient_map_build ::
  "('q, 'q_set, 'm, _) map_ops_scheme \<Rightarrow>
   ('q \<times> 'a \<times> 'q, 'm) set_iterator \<Rightarrow> 'm"where
  "right_quotient_map_build m_ops it = 
   it (\<lambda>_. True) (\<lambda>(q, a, q') m. 
     let S = right_quotient_map_lookup m_ops m q' in
     let S' = s.ins q S in
     (map_op_update m_ops q' S' m))
   (map_op_empty m_ops ())"

lemma right_quotient_map_build_correct :
fixes m_ops it
defines "m \<equiv> right_quotient_map_build m_ops it"
assumes m_ops_OK: "StdMap m_ops"
    and it_OK: "set_iterator it D"
shows "map_op_invar m_ops m \<and>
       s.invar (right_quotient_map_lookup m_ops m q) \<and>
       s.\<alpha> (right_quotient_map_lookup m_ops m q) =
       {q'. \<exists>a. (q', a, q) \<in> D}"
proof -
  interpret m: StdMap m_ops by fact
  
  let ?I = "\<lambda>D m. \<forall>q. 
       m.invar m \<and>
       s.invar (right_quotient_map_lookup m_ops m q) \<and>
       s.\<alpha> (right_quotient_map_lookup m_ops m q) =
       {q'. \<exists>a. (q', a, q) \<in> D}"

  note it_rule = set_iterator_no_cond_rule_insert_P [OF it_OK, where ?I = ?I]

  have "?I D m" 
    unfolding m_def right_quotient_map_build_def
  proof (rule it_rule)
    show "\<forall>q. m.invar (m.empty ()) \<and> s.invar (right_quotient_map_lookup m_ops (m.empty ()) q) \<and> s.\<alpha> (right_quotient_map_lookup m_ops (m.empty ()) q) = {q'. \<exists>a. (q', a, q) \<in> {}}"
      by (simp add: right_quotient_map_lookup_def s.correct m.correct)
    next
      show "\<And>\<sigma>. \<forall>q. m.invar \<sigma> \<and> s.invar (right_quotient_map_lookup m_ops \<sigma> q) \<and> s.\<alpha> (right_quotient_map_lookup m_ops \<sigma> q) = {q'. \<exists>a. (q', a, q) \<in> D} \<Longrightarrow>
         \<forall>q. m.invar \<sigma> \<and> s.invar (right_quotient_map_lookup m_ops \<sigma> q) \<and> s.\<alpha> (right_quotient_map_lookup m_ops \<sigma> q) = {q'. \<exists>a. (q', a, q) \<in> D}"
        by simp
    next
      fix D' m qaq
      assume asm: "qaq \<in> D - D'" "\<forall>q. m.invar m \<and> s.invar (right_quotient_map_lookup m_ops m q) \<and> s.\<alpha> (right_quotient_map_lookup m_ops m q) = {q'. \<exists>a. (q', a, q) \<in> D'}" "D' \<subseteq> D"
      obtain q a q' where qaq_eq[simp]: "qaq = (q, a, q')" by (metis prod.exhaust)

      from asm(1) have qaq_in_D: "(q,a,q') \<in> D" and qaq_nin_D': "(q,a,q') \<notin> D'" by simp_all
      from asm(2) have 
         invar_m: "m.invar m" and
         ind_hyp_invar[simp]: "\<And>q. s.invar (right_quotient_map_lookup m_ops m q)" and
         ind_hyp_\<alpha>[simp]: "\<And>q. s.\<alpha> (right_quotient_map_lookup m_ops m q) = {q'. \<exists>a. (q', a, q) \<in> D'}"
        by simp_all
      note D'_subset = asm(3) 

      define m' where "m' \<equiv> map_op_update m_ops q' (s.ins q (right_quotient_map_lookup m_ops m q')) m"
      have invar_m': "m.invar m'" by (simp add: m.correct invar_m m'_def)
      have lookup_m': "\<And>q''. map_op_lookup m_ops q'' m' =
        (if (q'' = q') then  Some (s.ins q (right_quotient_map_lookup m_ops m q')) else
            map_op_lookup m_ops q'' m)"
        unfolding m'_def by (simp add: invar_m m.correct)

      have map_lookup_m': "\<And>q''. right_quotient_map_lookup m_ops m' q'' =
        (if (q'' = q') then  (s.ins q (right_quotient_map_lookup m_ops m q')) else
            right_quotient_map_lookup m_ops m q'')"
        by (simp add: lookup_m' right_quotient_map_lookup_def)

      show "\<forall>q. m.invar ((case qaq of (q, a) \<Rightarrow> case a of (a, q') \<Rightarrow> \<lambda>m. let S = right_quotient_map_lookup m_ops m q'; S' = s.ins q S in m.update q' S' m) m) \<and>
                s.invar (right_quotient_map_lookup m_ops ((case qaq of (q, a) \<Rightarrow> case a of (a, q') \<Rightarrow> \<lambda>m. let S = right_quotient_map_lookup m_ops m q'; S' = s.ins q S in m.update q' S' m) m) q) \<and>
                s.\<alpha> (right_quotient_map_lookup m_ops ((case qaq of (q, a) \<Rightarrow> case a of (a, q') \<Rightarrow> \<lambda>m. let S = right_quotient_map_lookup m_ops m q'; S' = s.ins q S in m.update q' S' m) m) q) =
                {q'. \<exists>a. (q', a, q) \<in> insert qaq D'}"
        apply (rule allI, rename_tac q'')
        apply (case_tac "q'' = q'")
        apply (simp_all add: m'_def[symmetric])
        apply (simp_all add: map_lookup_m' s.correct invar_m'
                        split: option.split )
        apply (auto)
      done
    qed
  thus ?thesis by simp
qed

definition right_quotient_lists_impl ::
  "('q, 'q_set, 'm, _) map_ops_scheme \<Rightarrow>
   ('q, 'a, 'm, 'd) lts_filter_it \<Rightarrow> 
   ('a \<Rightarrow> bool) \<Rightarrow> 
   ('q_set \<times> 'a_set \<times> 'd \<times> 'q_set \<times> 'q_set \<times> nfa_props) \<Rightarrow> 
   ('q_set \<times> 'a_set \<times> 'd \<times> 'q_set \<times> 'q_set \<times> nfa_props)"
where
  "right_quotient_lists_impl m_ops it AP AA =
   (let m = right_quotient_map_build m_ops 
              (it (\<lambda>_. True) AP  (\<lambda>_. True)  (\<lambda>_. True) (nfa_trans AA)) in
    let F = s.accessible_restrict_code
              (\<lambda>q. s.to_list (right_quotient_map_lookup m_ops m q)) (s.empty ()) (s.to_list (nfa_accepting AA)) in
   (nfa_states AA, nfa_labels AA, nfa_trans AA,
    nfa_initial AA, F, nfa_props AA))"

lemma right_quotient_lists_impl_code :
  "right_quotient_lists_impl m_ops it AP (Q, A, D, I, F, p) = 
   (let m = it (\<lambda>_. True) AP (\<lambda>_. True) (\<lambda>_. True) D (\<lambda>_. True)
              (\<lambda>(q, a, q') m.
                  let S = case map_op_lookup m_ops q' m of None \<Rightarrow> set_op_empty s_ops () | Some S \<Rightarrow> S
                  in map_op_update m_ops q' (set_op_ins s_ops q S) m)
              (map_op_empty m_ops ());
         F = fst (worklist (\<lambda>s. True)
                    (\<lambda>s e. if set_op_memb s_ops e s then (s, [])
                           else (set_op_ins s_ops e s,
                                 case_option [] (set_op_to_list s_ops) (map_op_lookup m_ops e m)))
                    (set_op_empty s_ops (), set_op_to_list s_ops F))        
     in (Q, A, D, I, F, p))"
proof -
  have "s.to_list (s.empty ()) = []"
    using s.to_list_correct [of "s.empty ()"]
    by (simp add: s.empty_correct)
  hence "\<And>q m. s.to_list (right_quotient_map_lookup m_ops m q) = 
              (case map_op_lookup m_ops q m of None \<Rightarrow> [] | Some S \<Rightarrow> set_op_to_list s_ops S)"
    unfolding right_quotient_map_lookup_def
    by (simp split: option.split)

  thus ?thesis
    unfolding right_quotient_lists_impl_def right_quotient_map_build_def
              nfa_selectors_def snd_conv fst_conv right_quotient_map_lookup_def
    by (simp add: s.accessible_restrict_code_def[abs_def] split_def
                cong: if_cong)
qed

lemma right_quotient_lists_impl_correct :
assumes m_ops_OK: "StdMap m_ops"
    and it_OK: "lts_filter_it d.\<alpha> d.invar it"
shows "nfa_right_quotient_lists nfa_\<alpha> nfa_invar nfa_\<alpha> nfa_invar (right_quotient_lists_impl m_ops it)"
proof (intro nfa_right_quotient_lists.intro nfa_by_lts_correct
             nfa_right_quotient_lists_axioms.intro)
  fix n AP
  assume invar_n: "nfa_invar n"

  from invar_n have invars: 
    "s.invar (nfa_states n)"
    "l.invar (nfa_labels n)"
    "d.invar (nfa_trans n)"
    "s.invar (nfa_initial n)" 
    "s.invar (nfa_accepting n)"
    unfolding nfa_invar_full_def by simp_all

  define it' where "it' \<equiv> it (\<lambda>_. True) AP (\<lambda>_. True) (\<lambda>_. True) (nfa_trans n)"
  define m where "m \<equiv> right_quotient_map_build m_ops it'"
  define R where "R \<equiv> {(q, q'). \<exists>a. (q', a, q) \<in> lts_op_\<alpha> d_ops (nfa_trans n) \<and> AP a}"
  define F where "F \<equiv> s.accessible_restrict_code 
               (\<lambda>q. s.to_list (right_quotient_map_lookup m_ops m q)) (s.empty ())
               (s.to_list (nfa_accepting n))"

  from invars lts_filter_it.lts_filter_it_correct [OF it_OK, of "nfa_trans n"
       "\<lambda>_. True" AP "\<lambda>_. True" "\<lambda>_. True"]
  have it'_OK: "set_iterator it' {(q, a, q'). (q, a, q') \<in> d.\<alpha> (nfa_trans n) \<and> AP a}"
    unfolding it'_def by simp

  note m_OK = right_quotient_map_build_correct [OF m_ops_OK it'_OK, folded m_def]

  have fin_R: "finite R"
  proof -
    have R_eq: "R = (\<lambda>(q,a,q'). (q', q)) ` {(q,a,q'). (q,a,q') \<in> d.\<alpha> (nfa_trans n) \<and> AP a}"
      unfolding R_def by (auto simp add: image_iff)

    show "finite R"
      apply (unfold R_eq)
      apply (rule finite_imageI)
      apply (rule finite_subset [of _ "d.\<alpha> (nfa_trans n)"])
      apply (auto simp add: invars)
    done
  qed

  have fin_S: "finite (accessible R (s.\<alpha> (nfa_accepting n)))" 
    apply (rule accessible_finite___args_finite)
    apply (simp_all add: invars fin_R)
  done

  from s.accessible_restrict_code_correct [
     where succ_list = "(\<lambda>q. s.to_list (right_quotient_map_lookup m_ops m q))" and
           rs = "s.empty ()" and wl = "s.to_list (nfa_accepting n)"
           and R=R, folded F_def] m_OK invar_n fin_S
  have F_OK: "s.invar F \<and> s.\<alpha> F = accessible R (s.\<alpha> (nfa_accepting n))" 
    by (simp add: s.correct LTS_forget_labels_pred_def R_def accessible_restrict_empty
                     nfa_invar_full_def)

  from invar_n F_OK
  have "nfa_invar_no_props (right_quotient_lists_impl m_ops it AP n) \<and>
        ((nfa_\<alpha> (right_quotient_lists_impl m_ops it AP n)) =
         (NFA_right_quotient_lists (nfa_\<alpha> n) {a. AP a}))" 
    unfolding right_quotient_lists_impl_def
    apply (simp add: m_def[symmetric] F_def[symmetric] R_def[symmetric] it'_def[symmetric])
    apply (simp add: nfa_invar_no_props_def nfa_invar_full_def NFA.NFA_right_quotient_lists_alt_def
                     nfa_\<alpha>_def R_def[symmetric])
  done

  with invar_n
  show "nfa_invar (right_quotient_lists_impl m_ops it AP n) \<and>
        NFA_isomorphic_wf (nfa_\<alpha> (right_quotient_lists_impl m_ops it AP n))
            (NFA_right_quotient_lists (nfa_\<alpha> n) {a. AP a})"
    apply (simp add: m_def[symmetric] F_def[symmetric]
                  nfa_invar_alt_def NFA_right_quotient___is_well_formed
                  NFA_isomorphic_wf_refl)
    apply (simp add: nfa_invar_props_def right_quotient_lists_impl_def
                     NFA_right_quotient_alt_def)
  done    
qed 

end

subsection \<open> determinise \<close>

definition determinise_next_state :: 
  "('q, 'q_set, _) set_ops_scheme \<Rightarrow> ('q,'q_set) set_iterator \<Rightarrow> 
   ('q \<Rightarrow> ('q,'q_set) set_iterator) \<Rightarrow> 'q_set" where
  "determinise_next_state s_ops it_S it_D =
   (set_iterator_product it_S it_D) (\<lambda>_. True) (\<lambda>(_,q') S. set_op_ins s_ops q' S) (set_op_empty s_ops ())"

schematic_goal determinise_next_state_code :
   "determinise_next_state s_ops it_S it_D = ?XXXX"
unfolding determinise_next_state_def set_iterator_product_def
by (rule refl)

lemma determinise_next_state_correct :
assumes s_ops_OK: "StdSet s_ops" 
    and it_S_OK: "set_iterator it_S S"
    and it_D_OK: "\<And>q. set_iterator (it_D q) {q'. (q, a, q') \<in> D}"
shows "set_op_invar s_ops (determinise_next_state s_ops it_S it_D) \<and>
       set_op_\<alpha> s_ops (determinise_next_state s_ops it_S it_D) = {q' . \<exists>q. q \<in> S \<and> (q, a, q') \<in> D}"
proof -
  interpret s: StdSet s_ops by fact
  have "(SIGMA aa:S. {q'. (aa, a, q') \<in> D}) = {(q, q') . q \<in> S \<and> (q, a, q') \<in> D}" by auto
  with set_iterator_product_correct [where it_a = it_S and it_b = it_D,
    OF it_S_OK it_D_OK]
  have comb_OK: "set_iterator (set_iterator_product it_S it_D)
     {(q, q') . q \<in> S \<and> (q, a, q') \<in> D}" by simp

  have res_eq: "{q' . \<exists>q. q \<in> S \<and> (q, a, q') \<in> D} = snd ` {(q, q') . q \<in> S \<and> (q, a, q') \<in> D}"
    by (auto simp add: image_iff)

  show ?thesis
    unfolding determinise_next_state_def res_eq
    apply (rule set_iterator_no_cond_rule_insert_P [OF comb_OK,
                where I = "\<lambda>S \<sigma>. s.invar \<sigma> \<and> s.\<alpha> \<sigma> = snd ` S"])
    apply (auto simp add: s.correct image_iff Ball_def)
  done
qed

definition determinise_iterator where
"determinise_iterator s_ops it_A it_S it_D =
 set_iterator_image (\<lambda>a. (a, determinise_next_state s_ops it_S (\<lambda>q. it_D q a))) it_A"

lemma determinise_iterator_code :
   "determinise_iterator s_ops it_A it_S it_D = 
    (\<lambda>c f. it_A c (\<lambda>x. f (x, it_S (\<lambda>_. True) (\<lambda>a. it_D a x (\<lambda>_. True)
       (set_op_ins s_ops)) (set_op_empty s_ops ()))))"
unfolding determinise_iterator_def determinise_next_state_code set_iterator_image_alt_def
by simp


lemma determinise_iterator_correct :
fixes D :: "('q \<times> 'a \<times> 'q) set"
assumes it_A_OK: "set_iterator it_A A"
shows "set_iterator (determinise_iterator s_ops it_A it_S it_D) 
         ((\<lambda>a. (a, determinise_next_state s_ops it_S (\<lambda>q. it_D q a))) ` A)"
unfolding determinise_iterator_def
apply (rule set_iterator_image_correct [OF it_A_OK])
apply (simp_all add: inj_on_def)
done

definition determinise_impl_aux where
"determinise_impl_aux const s_ops ff it_A it_D it_S I A FP =
 (\<lambda>AA. const (ff AA) [I AA] (A AA)
          (FP AA) (\<lambda>S. determinise_iterator s_ops (it_A AA) (it_S S) (it_D AA)))"
 
lemma (in nfa_by_lts_defs) determinise_impl_aux_correct :
fixes ss_ops :: "('q2::{automaton_states}, 'q2_set, _) set_ops_scheme" 
  and \<alpha> :: "'org_nfa \<Rightarrow> ('q2, 'a) NFA_rec"
assumes const_OK: "NFASpec.dfa_construct nfa_\<alpha> nfa_invar l.\<alpha> l.invar (set_op_\<alpha> ss_ops) (set_op_invar ss_ops) const"
    and nfa_OK: "nfa \<alpha> invar"
    and ss_ops_OK: "StdSet ss_ops"
    and FP_OK: "\<And>n q. invar n \<Longrightarrow> set_op_invar ss_ops q \<Longrightarrow>
                set_op_\<alpha> ss_ops q \<subseteq> \<Q> (\<alpha> n) \<Longrightarrow> FP n q = (set_op_\<alpha> ss_ops q \<inter> \<F> (\<alpha> n) \<noteq> {})"
    and I_OK: "\<And>n. invar n \<Longrightarrow> set_op_invar ss_ops (I n) \<and> set_op_\<alpha> ss_ops (I n) = \<I> (\<alpha> n)"
    and A_OK: "\<And>n. invar n \<Longrightarrow> set_op_invar l_ops (A n) \<and> set_op_\<alpha> l_ops (A n) = \<Sigma> (\<alpha> n)"
    and it_A_OK: "\<And>n. invar n \<Longrightarrow> set_iterator (it_A n) (\<Sigma> (\<alpha> n))"
    and it_S_OK: "\<And>S. set_op_invar ss_ops S \<Longrightarrow> set_iterator (it_S S) (set_op_\<alpha> ss_ops S)"
    and it_D_OK: "\<And>n q a. invar n \<Longrightarrow> a \<in> \<Sigma> (\<alpha> n) \<Longrightarrow>
                      set_iterator (it_D n q a) {q'. (q, a, q') \<in> \<Delta> (\<alpha> n)}"
    and ff_OK: "\<And>n. invar n \<Longrightarrow> 
        (\<exists>f. inj_on f {q. q \<subseteq> \<Q> (\<alpha> n)} \<and>
            (\<forall>q. set_op_invar ss_ops q \<and> set_op_\<alpha> ss_ops q \<subseteq> \<Q> (\<alpha> n) \<longrightarrow> ff n q = f (set_op_\<alpha> ss_ops q)))" 
shows "nfa_determinise \<alpha> invar nfa_\<alpha> nfa_invar 
     (determinise_impl_aux const ss_ops ff it_A it_D it_S I A FP)"
proof (intro nfa_determinise.intro nfa_OK nfa_by_lts_correct nfa_determinise_axioms.intro)
  fix n
  assume invar_n: "invar n"

  let ?AA' = "determinise_NFA (\<alpha> n)"
  let ?D_it = "\<lambda>S. determinise_iterator ss_ops (it_A n) (it_S S) (it_D n)"

  from invar_n nfa_OK have AA'_wf: "DFA ?AA'"
    apply (rule_tac determinise_NFA___DFA)
    apply (simp add: nfa_def)
  done

  { fix q
    assume invar_q: "set_op_invar ss_ops q"
       and q_subset: "set_op_\<alpha> ss_ops q \<in> \<Q> (determinise_NFA (\<alpha> n))"

    let ?DS = "(\<lambda>a. (a, determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))) ` \<Sigma> (\<alpha> n)"

    from determinise_iterator_correct [OF it_A_OK, OF invar_n, of ss_ops "it_S q" "it_D n"]
    have D_it_OK: "set_iterator (?D_it q) ?DS" by simp
    
    note it_S_OK' = it_S_OK [OF invar_q]
 
    { fix a
      assume a_in: "a \<in> \<Sigma> (\<alpha> n)"
      from determinise_next_state_correct [OF ss_ops_OK it_S_OK', of "\<lambda>q. it_D n q a" a, OF it_D_OK,
          OF invar_n a_in]
      have "set_op_invar ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a))"
           "set_op_\<alpha> ss_ops (determinise_next_state ss_ops (it_S q) (\<lambda>q. it_D n q a)) =
            {q'. \<exists>qa. qa \<in> set_op_\<alpha> ss_ops q \<and> (qa, a, q') \<in> \<Delta> (\<alpha> n)}" by simp_all
    } note det_next_state_eval = this

    have "set_iterator_abs (\<lambda>(a, q'). (a, set_op_\<alpha> ss_ops q'))
                           (\<lambda>(a, q'). set_op_invar ss_ops q')
            (determinise_iterator ss_ops (it_A n) (it_S q) (it_D n))
        {(a, q'). (set_op_\<alpha> ss_ops q, a, q') \<in> \<Delta> (determinise_NFA (\<alpha> n))}" 
      apply (rule set_iterator_abs_I2)
      apply (rule D_it_OK)
      apply (insert q_subset)
      apply (auto simp add: image_iff det_next_state_eval Bex_def)
    done
  } note D_it_OK' = this

  from ff_OK[OF invar_n] obtain f where f_props:
    "inj_on f {q. q \<subseteq> \<Q> (\<alpha> n)}"
    "\<And>q. set_op_invar ss_ops q \<Longrightarrow> set_op_\<alpha> ss_ops q \<subseteq> \<Q> (\<alpha> n) \<Longrightarrow> ff n q = f (set_op_\<alpha> ss_ops q)"
    by blast
    
  note construct_correct = dfa_construct.dfa_construct_correct [OF const_OK AA'_wf,
    where ?I= "[I n]" and ?A="A n" and ?FP="FP n" and ?ff="ff n" and ?f=f and ?D_it = ?D_it, 
    OF _ _ _ _ _ _ _ _ D_it_OK']

  show "nfa_invar (determinise_impl_aux const ss_ops ff it_A it_D it_S I A FP n) \<and>
        NFA_isomorphic_wf (nfa_\<alpha> (determinise_impl_aux const ss_ops ff it_A it_D it_S I A FP n))
         (efficient_determinise_NFA (\<alpha> n))"
    unfolding determinise_impl_aux_def efficient_determinise_NFA_def
    apply (rule_tac construct_correct) 
    apply (simp_all add: I_OK[OF invar_n] A_OK[OF invar_n] FP_OK[OF invar_n]
                         f_props  determinise_NFA_full_def ff_OK[OF invar_n])
  done
qed


definition set_encode_rename :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> nat" where
  "set_encode_rename f S = set_encode (f ` S)"

lemma set_encode_rename_eq:
assumes fin: "finite S" 
    and f_inj_on: "inj_on f S"
    and sub: "A \<subseteq> S" "B \<subseteq> S"
shows "set_encode_rename f A = set_encode_rename f B \<longleftrightarrow> A = B"
proof -
  from sub f_inj_on have f_inj_on': "inj_on f (A \<union> B)"
    by (simp add: inj_on_def Ball_def subset_iff)

  from fin sub have fin': "finite A" "finite B" by (metis finite_subset)+

  from inj_on_Un_image_eq_iff[OF f_inj_on']
       fin' set_encode_eq [of "f ` A" "f ` B"] show ?thesis
    by (simp add: set_encode_rename_def)
qed


definition set_encode_rename_map :: 
  "('q, nat, 'm, _) map_ops_scheme \<Rightarrow> ('q, 'm \<times> nat) set_iterator \<Rightarrow> 'm" where
  "set_encode_rename_map m_ops it =
   fst (it (\<lambda>_. True) (\<lambda>q (m, n). (map_op_update_dj m_ops q n m, 2*n)) (map_op_empty m_ops (), 1))"

lemma set_encode_rename_map_correct :
fixes m_ops ::  "('q, nat, 'm, _) map_ops_scheme" 
  and it :: "('q, 'm \<times> nat) set_iterator" 
defines "m \<equiv> set_encode_rename_map m_ops it"
assumes it_OK: "set_iterator it S"
    and m_ops_OK: "StdMap m_ops"
shows "\<exists>f. inj_on f S \<and> map_op_invar m_ops m \<and> 
           (dom (map_op_\<alpha> m_ops m) = S) \<and>
           (\<forall>q\<in>S. (map_op_\<alpha> m_ops m) q = Some (2 ^ (f q)))"
proof -
  interpret m: StdMap m_ops by fact

  let ?I = "\<lambda>S (m, n).
        \<exists>f n'. inj_on f S \<and> map_op_invar m_ops m \<and> 
           (dom (map_op_\<alpha> m_ops m) = S) \<and>
           (\<forall>q\<in>S. (map_op_\<alpha> m_ops m) q = Some (2 ^ (f q))) \<and>
           (\<forall>q\<in>S. f q < n') \<and> (n = 2 ^ n')"

  obtain m' n where m_eq': 
    "it (\<lambda>_. True) (\<lambda>q (m, n). (map_op_update_dj m_ops q n m, 2*n)) (map_op_empty m_ops (), 1) = (m', n)"
    by (rule prod.exhaust)

  have "?I S ((it (\<lambda>_. True) (\<lambda>q (m, n). (map_op_update_dj m_ops q n m, 2*n)) (map_op_empty m_ops (), 1)))"
  proof (rule set_iterator_no_cond_rule_insert_P[OF it_OK, of ?I])
    show "case (m.empty (), 1) of (m, n) \<Rightarrow> \<exists>f n'. inj_on f {} \<and> m.invar m \<and> dom (m.\<alpha> m) = {} \<and> (\<forall>q\<in>{}. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>{}. f q < n') \<and> n = 2 ^ n'"
      apply (simp add: m.correct) 
      apply (rule exI [where x = 0]) 
      apply simp
    done
  next
    show "\<And>\<sigma>. case \<sigma> of (m, n) \<Rightarrow> \<exists>f n'. inj_on f S \<and> m.invar m \<and> dom (m.\<alpha> m) = S \<and> (\<forall>q\<in>S. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>S. f q < n') \<and> n = 2 ^ n' \<Longrightarrow>
         case \<sigma> of (m, n) \<Rightarrow> \<exists>f n'. inj_on f S \<and> m.invar m \<and> dom (m.\<alpha> m) = S \<and> (\<forall>q\<in>S. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>S. f q < n') \<and> n = 2 ^ n'"
      by simp
  next
    fix S' and mn::"'m \<times> nat" and q
    assume asm: "q \<in> S - S'" "case mn of (m, n) \<Rightarrow> \<exists>f n'. inj_on f S' \<and> m.invar m \<and> dom (m.\<alpha> m) = S' \<and> (\<forall>q\<in>S'. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q\<in>S'. f q < n') \<and> n = 2 ^ n'" "S' \<subseteq> S"
    note q_in = asm(1)
    note ind_hyp = asm(2)
    note S'_subset = asm(3)
    obtain m n where mn_eq[simp]: "mn = (m, n)" by (rule prod.exhaust)

    from ind_hyp obtain f n' where f_props: "
        inj_on f S' \<and>
        map_op_invar m_ops m \<and>
        dom (map_op_\<alpha> m_ops m) = S' \<and> (\<forall>q\<in>S'. map_op_\<alpha> m_ops m q = Some (2 ^ f q)) \<and> 
        (\<forall>q\<in>S'. f q < n') \<and> (n = 2 ^ n')" 
      by auto

    let ?f' = "\<lambda>q'. if q' = q then n' else f q'"

    from f_props q_in
    show "case case mn of (m, n) \<Rightarrow> (m.update_dj q n m, 2 * n) of
            (m, n) \<Rightarrow> \<exists>f n'. inj_on f (insert q S') \<and> m.invar m \<and> dom (m.\<alpha> m) = insert q S' \<and> (\<forall>q\<in>insert q S'. m.\<alpha> m q = Some (2 ^ f q)) \<and> (\<forall>q'\<in>insert q S'. f q' < n') \<and> n = 2 ^ n'"
      apply (simp add: m.correct)
      apply (rule exI[where x = ?f'])
      apply (simp add: image_iff Ball_def)
      apply (intro conjI)
        apply (simp add: inj_on_def)
        apply (metis order_less_irrefl)
         
        apply (rule exI [where x = "Suc n'"])
        apply (simp)
        apply (metis less_SucI)
    done
  qed
  with m_eq' show ?thesis
    apply (simp add: m_def set_encode_rename_map_def)
    apply metis
  done
qed

definition set_encode_rename_impl ::
  "('q, nat, 'm, _) map_ops_scheme \<Rightarrow> 'm \<Rightarrow> ('q, nat) set_iterator \<Rightarrow> nat" where
  "set_encode_rename_impl m_ops m it =
   (it (\<lambda>_. True) (\<lambda>q n. n + the (map_op_lookup m_ops q m)) 0)"
 
lemma set_encode_rename_impl_correct:
assumes invar_m: "map_op_invar m_ops m"
    and f_inj_on: "inj_on f S"
    and m_ops_OK: "StdMap m_ops"
    and m_prop: "\<And>q. q \<in> S \<Longrightarrow> (map_op_\<alpha> m_ops m) q = Some (2 ^ (f q))"
    and it_OK: "set_iterator it S"
shows "set_encode_rename_impl m_ops m it = set_encode_rename f S"
proof -
  interpret m: StdMap m_ops by fact
  let ?I = "\<lambda>S n. n = set_encode_rename f S"

  show ?thesis
  unfolding set_encode_rename_impl_def
  proof (rule set_iterator_no_cond_rule_insert_P[OF it_OK, of ?I])
    fix S' n q
    assume q_in: "q \<in> S - S'" and
           n_eq: "n = set_encode_rename f S'" and
           S'_subset: "S' \<subseteq> S" 

    from it_OK have "finite S" by (rule set_iterator_finite)
    with S'_subset have "finite S'" by (metis finite_subset)
    hence fin_f_S': "finite (f ` S')" by (rule finite_imageI)

    from q_in f_inj_on S'_subset
    have fq_nin: "f q \<notin> f ` S'" by (simp add: image_iff Ball_def subset_iff inj_on_def) metis

    from set_encode_insert [OF fin_f_S' fq_nin]
    have enc_insert: "set_encode (insert (f q) (f ` S')) = 2 ^ f q + set_encode (f ` S')" . 

    from q_in m_prop[of q] invar_m have m_q_eq: "map_op_lookup m_ops q m = Some (2 ^ (f q))"
      by (simp add: m.correct)
    show "n + the (map_op_lookup m_ops q m) = set_encode_rename f (insert q S')"
      by (simp add: set_encode_rename_def m_q_eq enc_insert n_eq)
  qed (simp_all add: set_encode_rename_def)
qed

context nfa_by_lts_defs
begin

definition determinise_impl where
   "determinise_impl d_add qm_ops m_ops it_S it_S2 it_q it_A it_D n =
    (if (nfa_prop_is_initially_connected (nfa_props n) \<and>
         nfa_prop_is_complete_deterministic (nfa_props n)) then n else  
       (determinise_impl_aux 
          (NFA_construct_reachable_impl_code d_add qm_ops True) 
          s_ops
          (\<lambda>n q. set_encode_rename_impl m_ops 
                   (set_encode_rename_map m_ops (it_S2 (nfa_states n))) 
               (it_q q))
          (\<lambda>n. it_A (nfa_labels n)) 
          (\<lambda>n. it_D (nfa_trans n))
          it_S
          nfa_initial
          nfa_labels
          (\<lambda>n q. \<not>(s.disjoint q (nfa_accepting n))) n))"

lemma determinise_impl_code: 
   "determinise_impl d_add qm_ops m_ops it_S it_S2 it_q it_A it_D (Q1, A1, D1, I1, F1, p1) =
    (if nfa_prop_is_initially_connected p1 \<and>
        nfa_prop_is_complete_deterministic p1
     then (Q1, A1, D1, I1, F1, p1)
     else let re_map = (fst (it_S2 Q1 (\<lambda>_. True)
       (\<lambda>q (m, n). (map_op_update_dj m_ops q n m, 2 * n))
       (map_op_empty m_ops (), 1))) in
          NFA_construct_reachable_impl_code
           d_add qm_ops True
           (\<lambda>q. it_q q (\<lambda>_. True)
                 (\<lambda>q n. n +
                        the (map_op_lookup m_ops q re_map))
                 0)
           [I1] A1 (\<lambda>q. \<not> set_op_disjoint s_ops q F1)
           (\<lambda>S c f.
               it_A A1 c
                (\<lambda>x. f (x, it_S S (\<lambda>_. True)
                            (\<lambda>a.
  it_D D1 a x (\<lambda>_. True) (set_op_ins s_ops))
                            (set_op_empty s_ops ())))))"
unfolding determinise_impl_def determinise_impl_aux_def 
          nfa_selectors_def
          determinise_iterator_code snd_conv fst_conv
          set_encode_rename_impl_def set_encode_rename_map_def
by simp_all


lemma determinise_impl_correct :
assumes it_S_OK: "set_iteratei  s.\<alpha> s.invar it_S"
    and it_S2_OK: "set_iteratei  s.\<alpha> s.invar it_S2"
    and it_q_OK: "set_iteratei  s.\<alpha> s.invar it_q"
    and it_A_OK: "set_iteratei l.\<alpha> l.invar it_A"
    and it_D_OK: "lts_succ_it d.\<alpha> d.invar it_D"
    and d_add_OK: "lts_dlts_add d.\<alpha> d.invar d_add"
    and qm_ops_OK: "StdMap qm_ops"
    and m_ops_OK: "StdMap m_ops"
shows "nfa_determinise nfa_\<alpha> nfa_invar nfa_\<alpha> nfa_invar 
     (determinise_impl d_add qm_ops m_ops it_S it_S2 it_q it_A it_D)"
   (is "nfa_determinise nfa_\<alpha> nfa_invar nfa_\<alpha> nfa_invar ?code")
proof (intro nfa_determinise.intro nfa_by_lts_correct
             nfa_determinise_axioms.intro)
  fix a
  assume invar_a: "nfa_invar a"

  show "nfa_invar (?code a) \<and>
        NFA_isomorphic_wf (nfa_\<alpha> (?code a))
          (efficient_determinise_NFA (nfa_\<alpha> a))"
  proof (cases "nfa_prop_is_initially_connected (nfa_props a) \<and>
                nfa_prop_is_complete_deterministic (nfa_props a)")
    case True note is_already_dfa = this

    from invar_a is_already_dfa have wf_a: 
       "DFA (nfa_\<alpha> a)" 
       "SemiAutomaton_is_initially_connected (nfa_\<alpha> a)"
      unfolding nfa_invar_alt_def nfa_invar_props_def by (simp_all add: DFA_alt_def)

    from efficient_determinise_NFA_already_det[OF wf_a]
    show ?thesis by (simp add: determinise_impl_def is_already_dfa invar_a)
  next
    case False note is_not_dfa = this
  
    note it_A_OK' = set_iteratei.iteratei_rule[OF it_A_OK]
    note it_S_OK' = set_iteratei.iteratei_rule[OF it_S_OK]
    note it_S2_OK' = set_iteratei.iteratei_rule[OF it_S2_OK]

    { fix Q
      assume invar_Q: "s.invar Q"
      define m where "m \<equiv> set_encode_rename_map m_ops (it_S2 Q)"

      from invar_Q have fin_Q: "finite (s.\<alpha> Q)" by simp

      from set_encode_rename_map_correct [OF it_S2_OK', OF invar_Q m_ops_OK,folded m_def] 
      obtain f where f_props: "inj_on f (s.\<alpha> Q)"
                              "map_op_invar m_ops m"
                              "dom (map_op_\<alpha> m_ops m) = s.\<alpha> Q"
                              "\<And>q. q\<in>s.\<alpha> Q \<Longrightarrow> map_op_\<alpha> m_ops m q = Some (2 ^ f q)"
        by auto
 
      { fix S
        assume "s.invar S" "s.\<alpha> S \<subseteq> s.\<alpha> Q"
        with f_props set_encode_rename_impl_correct [of m_ops m f "s.\<alpha> S" "it_q S"] 
        have " set_encode_rename_impl m_ops m (it_q S) = set_encode_rename f (set_op_\<alpha> s_ops S)" 
          by (simp add: m_ops_OK subset_iff set_iteratei.iteratei_rule[OF it_q_OK] inj_on_def)
      } note rename_impl_OK = this

      have "\<exists>f. inj_on f {q. q \<subseteq> s.\<alpha> Q} \<and>
            (\<forall>S. s.invar S \<and> s.\<alpha> S \<subseteq> s.\<alpha> Q \<longrightarrow>
                 set_encode_rename_impl m_ops m (it_q S) =
                 f (s.\<alpha> S))" 
        apply (rule exI [where x ="set_encode_rename f"])
        apply (simp add: rename_impl_OK inj_on_def set_encode_rename_eq
                         set_encode_rename_eq [OF fin_Q f_props(1)])
      done
    } note ff_OK = this

    note aux_rule = nfa_determinise.determinise_correct_aux [OF determinise_impl_aux_correct,
          OF _ nfa_by_lts_correct] 
    show ?thesis 
      apply (simp add: determinise_impl_def is_not_dfa)
      apply (rule aux_rule)
      apply (simp_all add: s.StdSet_axioms invar_a it_S_OK')
      apply (rule nfa_dfa_construct_sublocale_dfa)
      apply (rule NFA_construct_reachable_impl_code_correct [OF qm_ops_OK d_add_OK])

      apply (simp_all add: nfa_invar_full_def s.correct it_A_OK')
      apply (insert it_D_OK) []
      apply (simp add: lts_succ_it_def)

      apply (rule ff_OK) 
      apply (simp)
    done
  qed
qed

subsection \<open> Emptyness Check \<close>

definition language_is_empty_impl ::
   "(('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> ('q_set, 'a_set, 'd) NFA_impl) \<Rightarrow> 
    ('q_set, 'a_set, 'd) NFA_impl \<Rightarrow> bool" where
   "language_is_empty_impl norm n = (s.isEmpty (nfa_accepting (norm n)))"

lemma language_is_empty_impl_code :
   "language_is_empty_impl norm n =
    (let (Q, A, D, I, F, p) = norm n in s.isEmpty F)"
unfolding language_is_empty_impl_def
by (case_tac "norm n") simp

lemma language_is_empty_impl_correct :
 assumes norm_OK: "nfa_normalise nfa_\<alpha> nfa_invar norm"
 shows "nfa_language_is_empty nfa_\<alpha> nfa_invar (language_is_empty_impl norm)"
proof (intro nfa_language_is_empty.intro 
             nfa_language_is_empty_axioms.intro nfa_by_lts_correct)
  fix n
  assume invar_n: "nfa_invar n"

  from nfa_normalise.normalise_correct[OF norm_OK, OF invar_n]
  have invar_norm: "nfa_invar (norm n)" and
       iso: "NFA_isomorphic_wf (nfa_\<alpha> (norm n)) (NFA_remove_unreachable_states (nfa_\<alpha> n))"
    by simp_all

  from invar_norm have NFA_norm: "NFA (nfa_\<alpha> (norm n))" unfolding nfa_invar_alt_def by simp

  from iso have conn_norm: "SemiAutomaton_is_initially_connected (nfa_\<alpha> (norm n))"
    by (metis SemiAutomaton_is_initially_connected___NFA_isomorphic_wf 
              SemiAutomaton_is_initially_connected___NFA_remove_unreachable_states)

  from iso have L_eq: "\<L> (nfa_\<alpha> (norm n)) = \<L> (nfa_\<alpha> n)" 
    by (metis NFA_isomorphic_wf_\<L> NFA_remove_unreachable_states_\<L>)

  from NFA.NFA_is_empty_\<L>[OF NFA_norm conn_norm, unfolded L_eq] invar_norm
  show "language_is_empty_impl norm n = (\<L> (nfa_\<alpha> n) = {})" 
    unfolding language_is_empty_impl_def
    apply (cases "norm n") 
    apply (simp add: nfa_\<alpha>_def nfa_invar_alt_def nfa_invar_no_props_def s.correct)
  done
qed

subsection \<open> Hopcroft \<close>

definition (in -) Hopcroft_class_map_\<alpha>_impl where
  "Hopcroft_class_map_\<alpha>_impl pim l u =
   map (\<lambda>i. the (pim i)) [l..<Suc u]"

lemma (in -) Hopcroft_class_map_\<alpha>_impl_correct :
  "set (Hopcroft_class_map_\<alpha>_impl pim l u) =
   class_map_\<alpha> (pm, pim) (l, u)"
unfolding Hopcroft_class_map_\<alpha>_impl_def class_map_\<alpha>_def
by (auto simp add: image_iff Bex_def)

lemma (in -) upt_simps2 :
  "[i..<j] = (if (i < j) then i # [Suc i..<j] else [])" 
by (induct j) simp_all

lemma (in -) Hopcroft_class_map_\<alpha>_impl_code [code] :
  "Hopcroft_class_map_\<alpha>_impl pim l u =
   (if (l \<le> u) then
      (the (pim l) # (Hopcroft_class_map_\<alpha>_impl pim (Suc l) u))
    else [])"
unfolding Hopcroft_class_map_\<alpha>_impl_def
by (simp add: upt_simps2)
end
print_locale Hopcroft_impl_locale
locale nfa_by_lts_hop = nfa: nfa_by_lts_defs s_ops l_ops d_ops +
                        hop: Hopcroft_impl_locale s_ops s2_\<alpha> s2_invar sm_ops im_ops pm_ops pim_ops iM_ops sm_it cm_it pre_it pre_it2 iM_it
  for s_ops :: "('q::{automaton_states}, 'q_set, _) set_ops_scheme"
  and l_ops :: "('l, 'l_set, _) set_ops_scheme"
  and d_ops :: "('q, 'l, 'd, _) lts_ops_scheme"
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
  and iM_it :: "'iM \<Rightarrow> (nat \<times> nat, ('im \<times> 'sm \<times> nat) \<times> ('l \<times> nat) list) set_iterator"
begin

definition Hopcroft_minimise_impl where
"Hopcroft_minimise_impl rev_emp rev_add rev_get_succs rev_cleanup s_image_rename d_it d_image_rename AA =
(let AL = (nfa.l.to_list (nfa_by_lts_defs.nfa_labels AA)) in
 let rv_D = rev_cleanup (ltsga_reverse rev_emp rev_add d_it (nfa_by_lts_defs.nfa_trans AA)) in
 let pre_fun = (\<lambda>a pim (l, u). 
   rev_get_succs rv_D (Hopcroft_class_map_\<alpha>_impl (\<lambda>i. hop.pim.lookup i pim) l u) a) in
 let ((_, sm, _), _) = hop.Hopcroft_code (nfa_by_lts_defs.nfa_states AA) (nfa_by_lts_defs.nfa_accepting AA) AL pre_fun in
  nfa.rename_states_impl s_image_rename d_image_rename True AA (\<lambda>q. states_enumerate (the (hop.sm.lookup q sm))))"

schematic_goal Hopcroft_minimise_impl_code :
  "Hopcroft_minimise_impl rev_emp rev_add rev_get_succs rev_cleanup s_image_rename d_it d_image_rename 
    (Q, A, D, I, F, p) = ?XXX"
unfolding Hopcroft_minimise_impl_def nfa.nfa_selectors_def fst_conv snd_conv
by (rule refl)

lemma Hopcroft_minimise_impl_correct :
  fixes d_ops' :: "('q, 'l, 'd', _) lts_ops_scheme"
  and succ_it :: "('q,'l,'q_set,'d'') lts_succ_it"
  and rev_cleanup :: "'lts1 \<Rightarrow> 'lts2"
assumes wf_target: "nfa_by_lts_defs s_ops' l_ops d_ops'" 
    and s_image_rename_OK: "set_image nfa.s.\<alpha> nfa.s.invar (set_op_\<alpha> s_ops') (set_op_invar s_ops') s_image_rename"
    and d_image_rename_OK: "dlts_image nfa.d.\<alpha> nfa.d.invar (lts_op_\<alpha> d_ops') (lts_op_invar d_ops') d_image_rename"
    and d_it_OK: "lts_iterator nfa.d.\<alpha> nfa.d.invar d_it"
    and rev_emp_OK: "lts_empty rev_\<alpha> rev_invar rev_emp"
    and rev_add_OK: "lts_add rev_\<alpha> rev_invar rev_add"
    and rev_get_succs_OK: "lts_get_succ_set rev2_\<alpha> rev2_invar s2_\<alpha> s2_invar rev_get_succs"
    and rev_cleanup_OK: "lts_copy rev_\<alpha> rev_invar rev2_\<alpha> rev2_invar rev_cleanup"
  shows "dfa_minimise
           (nfa_by_lts_defs.nfa_\<alpha> s_ops l_ops d_ops)
           (nfa_by_lts_defs.nfa_invar s_ops l_ops d_ops)
           (nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops')
           (nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops') 
       (Hopcroft_minimise_impl rev_emp rev_add rev_get_succs rev_cleanup s_image_rename d_it d_image_rename)"
proof (intro dfa_minimise.intro nfa_by_lts_defs.nfa_by_lts_correct
             dfa_minimise_axioms.intro)
  from nfa.nfa_by_lts_defs_axioms show "nfa_by_lts_defs s_ops l_ops d_ops" .
  from wf_target show "nfa_by_lts_defs s_ops' l_ops d_ops'" .

  (* from wf_target show "nfa (nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops') *)
     (* (nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops')" *)
     (* by (rule_tac nfa_by_lts_defs.nfa_by_lts_correct) *)

  fix AA
  assume invar_AA: "nfa.nfa_invar AA"
     and DFA_AA: "DFA (nfa.nfa_\<alpha> AA)"
     and AA_initially_connected: "SemiAutomaton_is_initially_connected (nfa.nfa_\<alpha> AA)"

  from invar_AA have invar_no_props_AA: "nfa.nfa_invar_no_props AA" by (simp add: nfa.nfa_invar_alt_def)

  let ?AA' = "(Hopcroft_minimise_impl rev_emp rev_add rev_get_succs rev_cleanup s_image_rename d_it d_image_rename) AA"

  let ?AL = "nfa.l.to_list (nfa.nfa_labels AA)"
  have AL_OK: "distinct ?AL" "set ?AL = \<Sigma> (nfa.nfa_\<alpha> AA)"
    using invar_no_props_AA by (simp_all add: nfa.nfa_invar_no_props_def nfa.l.correct)
  
  define rv where "rv \<equiv> rev_cleanup (ltsga_reverse rev_emp rev_add d_it (nfa.nfa_trans AA))"
  from ltsga_reverse_correct [OF rev_emp_OK rev_add_OK d_it_OK] 
  have rv_OK: "lts_reverse nfa.d.\<alpha> nfa.d.invar rev_\<alpha> rev_invar (ltsga_reverse rev_emp rev_add d_it)" .
 
  from lts_reverse.lts_reverse_correct[OF rv_OK, of "nfa.nfa_trans AA"]
       lts_copy.copy_correct [OF rev_cleanup_OK]
  have rev_d_props: "rev2_invar rv"
      "rev2_\<alpha> rv = {(v', e, v) |v e v'. (v, e, v') \<in> nfa.d.\<alpha> (nfa.nfa_trans AA)}"
    using invar_no_props_AA
    by (simp_all add: nfa.nfa_invar_no_props_def rv_def)
 
  define pre_fun where "pre_fun \<equiv> (\<lambda>a pim (l, u). 
   rev_get_succs rv (Hopcroft_class_map_\<alpha>_impl (\<lambda>i. hop.pim.lookup i pim) l u) a)"

  { fix a pim u l

    note rev_get_succs_correct = lts_get_succ_set.lts_get_succ_set_correct [OF rev_get_succs_OK]
    from rev_d_props
    have "s2_invar (pre_fun a pim (l, u)) \<and>
      s2_\<alpha> (pre_fun a pim (l, u)) =
      {q. \<exists>q'. (q, a, q') \<in> \<Delta> (nfa.nfa_\<alpha> AA) \<and>
               q' \<in> {the (map_op_lookup pim_ops i pim) |i. l \<le> i \<and> i \<le> u}}"
     unfolding pre_fun_def
     apply (simp add: rev_get_succs_correct Hopcroft_class_map_\<alpha>_impl_correct[of _ _ _ pm]
                      class_map_\<alpha>_def)
     apply auto
     done
  } note pre_fun_OK = this

  define rename_map where "rename_map \<equiv> hop.Hopcroft_code_rename_map (nfa.nfa_states AA) (nfa.nfa_accepting AA) ?AL pre_fun"
  define rename_fun where "rename_fun \<equiv> (\<lambda>q. states_enumerate (the (hop.sm.lookup q rename_map)))::('q \<Rightarrow> 'q)"

  have Q_OK: "(nfa.nfa_states AA, \<Q> (nfa.nfa_\<alpha> AA)) \<in> hop.s_rel" and
       F_OK: "(nfa.nfa_accepting AA, \<F> (nfa.nfa_\<alpha> AA)) \<in> hop.s_rel"
    using invar_no_props_AA by (simp_all add: nfa.nfa_invar_no_props_def hop.s_rel_def in_br_conv)

  from hop.Hopcroft_code_correct_rename_fun [OF Q_OK F_OK DFA_AA AL_OK pre_fun_OK,
       folded rename_map_def]
  have "hop.sm.invar rename_map"
       "dom (hop.sm.\<alpha> rename_map) = \<Q> (nfa.nfa_\<alpha> AA)" and
       rename_fun_OK: "NFA_is_strong_equivalence_rename_fun (nfa.nfa_\<alpha> AA) rename_fun"
    unfolding rename_fun_def
    by auto

  from nfa.rename_states_impl_correct_dfa [OF wf_target s_image_rename_OK d_image_rename_OK]
  have rename_states_OK: "dfa_rename_states nfa.nfa_\<alpha> nfa.nfa_invar (nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops')
   (nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops')
   (nfa_by_lts_defs.rename_states_impl s_image_rename d_image_rename True)" by simp

  from merge_NFA_minimise [OF DFA_AA AA_initially_connected rename_fun_OK]
  have rename_is_minimal: "NFA_isomorphic_wf (NFA_rename_states (nfa.nfa_\<alpha> AA) rename_fun) (NFA_minimise (nfa.nfa_\<alpha> AA))"
    by simp

  have AA'_alt_def: "?AA' = nfa.rename_states_impl s_image_rename d_image_rename True AA rename_fun"
    unfolding Hopcroft_minimise_impl_def rename_fun_def rename_map_def pre_fun_def rv_def
              hop.Hopcroft_code_rename_map_def 
    by (simp add: Let_def split_def)

  from DFA_AA rename_is_minimal invar_AA
       dfa_rename_states.dfa_rename_states_correct [OF rename_states_OK, of AA rename_fun]
  have "nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops' ?AA'"
       "nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops' ?AA' = NFA_rename_states (nfa.nfa_\<alpha> AA) rename_fun"
    by (simp_all add: NFA_isomorphic_wf___minimise DFA_alt_def DFA_is_minimal_def 
             nfa.nfa_invar_def AA'_alt_def)
 
  with rename_is_minimal show
       "nfa_by_lts_defs.nfa_invar s_ops' l_ops d_ops' ?AA' \<and>
        NFA_isomorphic_wf (nfa_by_lts_defs.nfa_\<alpha> s_ops' l_ops d_ops' ?AA') (NFA_minimise (nfa.nfa_\<alpha> AA))"
    by simp
qed

end

text \<open> It remains to implement the operations for the reversed transition system \<close>
locale Hopcroft_lts =
  m: StdMap m_ops + 
  m2: StdMap m2_ops + 
  s: StdSet s_ops +
  s2: StdSet s2_ops +
  mm: StdMap mm_ops + 
  un: set_union_list "set_op_\<alpha> s2_ops" "set_op_invar s2_ops" "set_op_\<alpha> s2_ops" "set_op_invar s2_ops" un_list +
  cp: set_copy "set_op_\<alpha> s_ops" "set_op_invar s_ops" "set_op_\<alpha> s2_ops" "set_op_invar s2_ops" copy +
  m_it: map_iteratei "map_op_\<alpha> m_ops" "map_op_invar m_ops" m_it +
  mm_it: map_iteratei "map_op_\<alpha> mm_ops" "map_op_invar mm_ops" mm_it
  for m_ops::"('q,'mm,'m1,_) map_ops_scheme"
  and m2_ops::"('q,'s2 option array,'m2,_) map_ops_scheme"
  and mm_ops::"(nat,'s, 'mm,_) map_ops_scheme"
  and s_ops::"(nat,'s,_) set_ops_scheme"
  and s2_ops::"(nat,'s2,_) set_ops_scheme"
  and copy :: "'s \<Rightarrow> 's2"
  and m_it :: "'m1 \<Rightarrow> ('q \<times> 'mm, 'm2) set_iterator"
  and mm_it :: "'mm \<Rightarrow> (nat \<times> 's, 's2 option array) set_iterator"
  and un_list 
begin
  lemma ts_impl : "tsbm_defs m_ops mm_ops s_ops"
    unfolding tsbm_defs_def
    by (simp add: m.StdMap_axioms s.StdSet_axioms mm.StdMap_axioms)

  definition "hopcroft_lts_\<alpha> \<equiv> ltsbm_AQQ_defs.ltsbm_\<alpha>(tsbm_defs.tsbm_\<alpha> m_ops mm_ops s_ops)"
  definition "hopcroft_lts_invar \<equiv> ltsbm_AQQ_defs.ltsbm_invar(tsbm_defs.tsbm_invar m_ops mm_ops s_ops)"

  lemma ts2_impl : "tsbm_defs m2_ops iam_ops s2_ops"
    unfolding tsbm_defs_def
    by (simp add: m2.StdMap_axioms s2.StdSet_axioms iam.StdMap_axioms)

  definition "hopcroft_lts_\<alpha>2 \<equiv> ltsbm_AQQ_defs.ltsbm_\<alpha>(tsbm_defs.tsbm_\<alpha> m2_ops iam_ops s2_ops)"
  definition "hopcroft_lts_invar2 \<equiv> ltsbm_AQQ_defs.ltsbm_invar(tsbm_defs.tsbm_invar m2_ops iam_ops s2_ops)"

  lemma hopcroft_lts_\<alpha>_alt_def :
    "hopcroft_lts_\<alpha> m1 = {(w, v, v').
     \<exists>m2 s3.
        map_op_\<alpha> m_ops m1 v = Some m2 \<and>
        map_op_\<alpha> mm_ops m2 w = Some s3 \<and>
        v' \<in> set_op_\<alpha> s_ops s3}"
    unfolding hopcroft_lts_\<alpha>_def ltsbm_AQQ_defs.ltsbm_\<alpha>_def[abs_def]
              tsbm_defs.tsbm_\<alpha>_def[OF ts_impl] 
    by (auto simp add: image_iff)

  lemma hopcroft_lts_\<alpha>2_alt_def :
    "hopcroft_lts_\<alpha>2 m1 = {(w, v, v').
     \<exists>m2 s3.
        map_op_\<alpha> m2_ops m1 v = Some m2 \<and>
        map_op_\<alpha> iam_ops m2 w = Some s3 \<and>
        v' \<in> set_op_\<alpha> s2_ops s3}"
    unfolding hopcroft_lts_\<alpha>2_def ltsbm_AQQ_defs.ltsbm_\<alpha>_def[abs_def]
              tsbm_defs.tsbm_\<alpha>_def[OF ts2_impl] 
    by (auto simp add: image_iff)

  definition hopcroft_lts_copy where
    "hopcroft_lts_copy m =
     m_it m (\<lambda>_. True) (\<lambda>(a, mm) m2.
       m2.update a (
         mm_it mm (\<lambda>_. True) (\<lambda>(q, s) mm2.
            iam.update q (copy s) mm2) (iam.empty ())) m2) (m2.empty ())"
       
  lemma hopcroft_lts_copy_correct :
    "lts_copy hopcroft_lts_\<alpha> hopcroft_lts_invar hopcroft_lts_\<alpha>2 hopcroft_lts_invar2
              hopcroft_lts_copy"
  proof
    fix l1
    assume invar_l1: "hopcroft_lts_invar l1"

    define inner_it where "inner_it \<equiv> \<lambda>mm. mm_it mm iam_invar
              (\<lambda>(q, s). map_op_update iam_ops q (copy s))
              (map_op_empty iam_ops ())"
    have inner_it_intro: "\<And>mm. mm_it mm iam_invar
              (\<lambda>(q, s). map_op_update iam_ops q (copy s))
              (map_op_empty iam_ops ()) = inner_it mm"
      unfolding inner_it_def by simp

    have "hopcroft_lts_\<alpha>2 (hopcroft_lts_copy l1) = hopcroft_lts_\<alpha> l1 \<and>
          hopcroft_lts_invar2 (hopcroft_lts_copy l1)"
      unfolding hopcroft_lts_copy_def inner_it_intro 
      proof (rule m_it.iterate_rule_insert_P [where I =
               "\<lambda>d m2. hopcroft_lts_\<alpha>2 m2 = {(q, a, q'). (q, a, q') \<in> hopcroft_lts_\<alpha> l1 \<and> a \<in> d} \<and>
          hopcroft_lts_invar2 m2 \<and> dom (m2.\<alpha> m2) = d"])  
        from invar_l1 show "m.invar l1"
          unfolding hopcroft_lts_invar_def ltsbm_AQQ_defs.ltsbm_invar_def tsbm_defs.tsbm_invar_alt_def[OF ts_impl]
          by simp
      next
        show "hopcroft_lts_\<alpha>2 (m2.empty ()) = {(q, a, q'). (q, a, q') \<in> hopcroft_lts_\<alpha> l1 \<and> a \<in> {}} \<and> hopcroft_lts_invar2 (m2.empty ()) \<and> dom (m2.\<alpha> (m2.empty ())) = {}"
          unfolding hopcroft_lts_invar2_def ltsbm_AQQ_defs.ltsbm_invar_def
                    tsbm_defs.tsbm_invar_alt_def[OF ts2_impl]
          by (simp add: hopcroft_lts_\<alpha>2_alt_def m2.correct)
      next
        fix k v it \<sigma>
        assume asm:"k \<in> dom (m.\<alpha> l1) - it" "m.\<alpha> l1 k = Some v" "it \<subseteq> dom (m.\<alpha> l1)" "hopcroft_lts_\<alpha>2 \<sigma> = {(q, a, q'). (q, a, q') \<in> hopcroft_lts_\<alpha> l1 \<and> a \<in> it} \<and> hopcroft_lts_invar2 \<sigma> \<and> dom (m2.\<alpha> \<sigma>) = it"
        from asm(1) have k_nin_it: "k \<notin> it" by simp
        note l1_k_eq = asm(2)
        note it_subset = asm(3)
        note ind_hyp = asm(4)

        from ind_hyp k_nin_it 
        have "k \<notin> dom (map_op_\<alpha> m2_ops \<sigma>)" by simp
        hence mm_k_eq: "m2.\<alpha> \<sigma> k = None" by auto

        from ind_hyp have invar2_hop_mm: "hopcroft_lts_invar2 \<sigma>" by simp
        hence invar_mm: "m2.invar \<sigma>"
          unfolding hopcroft_lts_invar2_def ltsbm_AQQ_defs.ltsbm_invar_def
                    tsbm_defs.tsbm_invar_alt_def[OF ts2_impl]
          by simp

        from invar_l1 l1_k_eq 
        have invar_v: "mm.invar v \<and>
                 (\<forall>w s3. mm.\<alpha> v w = Some s3 \<longrightarrow> s.invar s3)"
          unfolding hopcroft_lts_invar_def ltsbm_AQQ_defs.ltsbm_invar_def
                    tsbm_defs.tsbm_invar_alt_def[OF ts_impl]
          by simp

        define inner_it_val where "inner_it_val \<equiv> {(q, k, q') | q q'. 
                \<exists>s3. iam.\<alpha> (inner_it v) q = Some s3 \<and>
                     q' \<in> s2.\<alpha> s3}"
         
        have inner_it_OK: "iam.invar (inner_it v) \<and>
                           (\<forall>w s3.  iam.\<alpha> (inner_it v) w = Some s3 \<longrightarrow>
                                    s2.invar s3) \<and>
                           inner_it_val = {(q, a, q'). a = k \<and> (q, a, q') \<in> hopcroft_lts_\<alpha> l1}" 
          unfolding inner_it_def inner_it_val_def
        proof (rule mm_it.iterate_rule_insert_P [where I = "\<lambda>d a.
                   iam.invar a \<and>
                   (\<forall>w s3.  iam.\<alpha> a w = Some s3 \<longrightarrow> s2.invar s3) \<and>
                   (\<forall>q q'. (\<exists>s3. iam.\<alpha> a q = Some s3 \<and> q' \<in> s2.\<alpha> s3) = 
                           (q \<in> d \<and> (q, k, q') \<in> hopcroft_lts_\<alpha> l1))"])
          show "mm.invar v"
              using invar_v by simp
          next
            show "iam.invar (iam.empty ()) \<and> (\<forall>w s3. iam.\<alpha> (iam.empty ()) w = Some s3 \<longrightarrow> s2.invar s3) \<and> (\<forall>q q'. (\<exists>s3. iam.\<alpha> (iam.empty ()) q = Some s3 \<and> q' \<in> s2.\<alpha> s3) = (q \<in> {} \<and> (q, k, q') \<in> hopcroft_lts_\<alpha> l1))"
              by (simp add: iam.correct)
          next
            fix ka va it \<sigma>
            assume "ka \<in> dom (mm.\<alpha> v) - it" "mm.\<alpha> v ka = Some va" "it \<subseteq> dom (mm.\<alpha> v)"
                   "iam.invar \<sigma> \<and> (\<forall>w s3. iam.\<alpha> \<sigma> w = Some s3 \<longrightarrow> s2.invar s3) \<and> (\<forall>q q'. (\<exists>s3. iam.\<alpha> \<sigma> q = Some s3 \<and> q' \<in> s2.\<alpha> s3) = (q \<in> it \<and> (q, k, q') \<in> hopcroft_lts_\<alpha> l1))"
            then show "iam.invar ((case (ka, va) of (q, s) \<Rightarrow> iam.update q (copy s)) \<sigma>) \<and>
            (\<forall>w s3. iam.\<alpha> ((case (ka, va) of (q, s) \<Rightarrow> iam.update q (copy s)) \<sigma>) w = Some s3 \<longrightarrow> s2.invar s3) \<and>
            (\<forall>q q'. (\<exists>s3. iam.\<alpha> ((case (ka, va) of (q, s) \<Rightarrow> iam.update q (copy s)) \<sigma>) q = Some s3 \<and> q' \<in> s2.\<alpha> s3) = (q \<in> insert ka it \<and> (q, k, q') \<in> hopcroft_lts_\<alpha> l1))"
              apply (intro conjI allI)
              apply (auto simp add: hopcroft_lts_\<alpha>_alt_def l1_k_eq)
              using invar_v cp.copy_correct(2) apply (simp add: iam.correct split: if_splits)
              apply blast
              apply (simp add: s2.correct iam.correct)
              apply force
              apply (simp add: s2.correct iam.correct split: if_splits)
              using cp.copy_correct(1) invar_v apply blast
              apply blast
              apply (auto simp add: s2.correct iam.correct cp.copy_correct(1) invar_v)
              done
          next
            show "\<And>\<sigma>. iam.invar \<sigma> \<and> (\<forall>w s3. iam.\<alpha> \<sigma> w = Some s3 \<longrightarrow> s2.invar s3) \<and> (\<forall>q q'. (\<exists>s3. iam.\<alpha> \<sigma> q = Some s3 \<and> q' \<in> s2.\<alpha> s3) = (q \<in> dom (mm.\<alpha> v) \<and> (q, k, q') \<in> hopcroft_lts_\<alpha> l1)) \<Longrightarrow>
         iam.invar \<sigma> \<and> (\<forall>w s3. iam.\<alpha> \<sigma> w = Some s3 \<longrightarrow> s2.invar s3) \<and> {(q, k, q') |q q'. \<exists>s3. iam.\<alpha> \<sigma> q = Some s3 \<and> q' \<in> s2.\<alpha> s3} = {a. case a of (q, aa, q') \<Rightarrow> aa = k \<and> (q, aa, q') \<in> hopcroft_lts_\<alpha> l1}"
              apply (intro conjI allI impI)
              apply blast
              apply blast
              apply (auto simp add: hopcroft_lts_\<alpha>_alt_def l1_k_eq)
              done
        qed
        from invar2_hop_mm
        have \<alpha>_new: "hopcroft_lts_\<alpha>2 (map_op_update m2_ops k (inner_it v) \<sigma>) = 
              hopcroft_lts_\<alpha>2 \<sigma> \<union> inner_it_val"
          unfolding hopcroft_lts_\<alpha>2_alt_def inner_it_val_def
                    hopcroft_lts_invar2_def ltsbm_AQQ_defs.ltsbm_invar_def
                    tsbm_defs.tsbm_invar_alt_def[OF ts2_impl]
          by (simp add: m2.correct set_eq_iff all_conj_distrib mm_k_eq)

        from ind_hyp
        show "hopcroft_lts_\<alpha>2 ((case (k, v) of (a, mm) \<Rightarrow> m2.update a (inner_it mm)) \<sigma>) = {(q, a, q'). (q, a, q') \<in> hopcroft_lts_\<alpha> l1 \<and> a \<in> insert k it} \<and>
            hopcroft_lts_invar2 ((case (k, v) of (a, mm) \<Rightarrow> m2.update a (inner_it mm)) \<sigma>) \<and> dom (m2.\<alpha> ((case (k, v) of (a, mm) \<Rightarrow> m2.update a (inner_it mm)) \<sigma>)) = insert k it"
          unfolding hopcroft_lts_invar2_def ltsbm_AQQ_defs.ltsbm_invar_def
                    tsbm_defs.tsbm_invar_alt_def[OF ts2_impl]
          apply (simp add: m2.correct invar_mm \<alpha>_new inner_it_OK)
          apply auto
          done
      next
        fix \<sigma>
        assume "hopcroft_lts_\<alpha>2 \<sigma> = {(q, a, q'). (q, a, q') \<in> hopcroft_lts_\<alpha> l1 \<and> a \<in> dom (m.\<alpha> l1)} \<and> hopcroft_lts_invar2 \<sigma> \<and> dom (m2.\<alpha> \<sigma>) = dom (m.\<alpha> l1)"
        thus "hopcroft_lts_\<alpha>2 \<sigma> = hopcroft_lts_\<alpha> l1 \<and> hopcroft_lts_invar2 \<sigma>"
          by (auto simp add: hopcroft_lts_\<alpha>_alt_def)
      qed
    thus "hopcroft_lts_\<alpha>2 (hopcroft_lts_copy l1) = hopcroft_lts_\<alpha> l1"
         "hopcroft_lts_invar2 (hopcroft_lts_copy l1)" by simp_all
  qed

  definition "hopcroft_lts_empty \<equiv> m.empty"

  lemma hopcroft_lts_empty_correct :
    "lts_empty hopcroft_lts_\<alpha> hopcroft_lts_invar hopcroft_lts_empty"
    using ltsbm_AQQ_defs.ltsbm_empty_correct[OF 
        tsbm_defs.tsbm_empty_correct[OF ts_impl, 
        unfolded tsbm_defs.tsbm_empty_def[OF ts_impl],
        folded hopcroft_lts_\<alpha>_def hopcroft_lts_invar_def hopcroft_lts_empty_def]]
     unfolding hopcroft_lts_\<alpha>_def[symmetric] hopcroft_lts_invar_def[symmetric] .

  definition "hopcroft_lts_add \<equiv> ltsbm_AQQ_defs.ltsbm_add(
      tsbm_defs.tsbm_add m_ops mm_ops s_ops)"
  lemma hopcroft_lts_add_alt_def :
    "hopcroft_lts_add = (\<lambda>q a v' l.
        case map_op_lookup m_ops a l of
        None \<Rightarrow>
          map_op_update m_ops a (mm.sng q (set_op_sng s_ops v')) l
        | Some m2 \<Rightarrow>
            (case mm.lookup q m2 of
            None \<Rightarrow>
              map_op_update m_ops a
               (mm.update q (set_op_sng s_ops v') m2) l
            | Some s3 \<Rightarrow>
                map_op_update m_ops a
                 (mm.update q (set_op_ins s_ops v' s3) m2) l))"

    unfolding hopcroft_lts_add_def tsbm_defs.tsbm_add_def[OF ts_impl, abs_def]
              ltsbm_AQQ_defs.ltsbm_add_def[abs_def]
    by simp

  lemma hopcroft_lts_add_correct :
    "lts_add hopcroft_lts_\<alpha> hopcroft_lts_invar hopcroft_lts_add"
    using ltsbm_AQQ_defs.ltsbm_add_correct[OF 
        tsbm_defs.tsbm_add_correct[OF ts_impl, 
        unfolded tsbm_defs.tsbm_empty_def[OF ts_impl],
        folded hopcroft_lts_\<alpha>_def hopcroft_lts_invar_def]]
     unfolding hopcroft_lts_\<alpha>_def[symmetric] hopcroft_lts_add_def 
               hopcroft_lts_invar_def[symmetric] .

  definition "hopcroft_lts_get_succ_set l vs a = 
     (case m2.lookup a l of None \<Rightarrow> s2.empty ()
     | Some im \<Rightarrow> un_list (List.map_filter (\<lambda>q. iam.lookup q im) vs))"

  lemma hopcroft_lts_get_succ_set_correct :
    "lts_get_succ_set hopcroft_lts_\<alpha>2 hopcroft_lts_invar2 s2.\<alpha> s2.invar hopcroft_lts_get_succ_set"
  proof
    fix l vs a
    assume invar_l: "hopcroft_lts_invar2 l"

    have "s2.invar (hopcroft_lts_get_succ_set l vs a) \<and> 
          s2.\<alpha> (hopcroft_lts_get_succ_set l vs a) =
               {v'. \<exists>v. v \<in> set vs \<and> (v, a, v') \<in> hopcroft_lts_\<alpha>2 l}" (is "?P1 \<and> ?P2")
    proof (cases "m2.lookup a l")
      case None
      with invar_l
      show ?thesis
        by (simp add: hopcroft_lts_get_succ_set_def s2.correct hopcroft_lts_\<alpha>2_alt_def
                      hopcroft_lts_invar2_def ltsbm_AQQ_defs.ltsbm_invar_def
                      tsbm_defs.tsbm_invar_def[OF ts2_impl] m2.correct)
    next
      case (Some im) note l_a_eq = this

      define l' where "l' \<equiv> List.map_filter (\<lambda>q. iam.lookup q im) vs" 

      from invar_l l_a_eq
      have invar_im : "iam.invar im" 
       and l'_OK: "\<forall>s1\<in>set l'. s2.invar s1" 
       unfolding l'_def set_map_filter hopcroft_lts_invar2_def ltsbm_AQQ_defs.ltsbm_invar_def
                 tsbm_defs.tsbm_invar_alt_def[OF ts2_impl]
       apply (auto simp add: m2.correct iam.correct)
       apply (metis option.collapse)
       done

      from invar_l l_a_eq un.union_list_correct[OF l'_OK] invar_im
      show ?thesis
        apply (simp add: l'_def hopcroft_lts_get_succ_set_def s2.correct hopcroft_lts_\<alpha>2_alt_def
                      hopcroft_lts_invar2_def ltsbm_AQQ_defs.ltsbm_invar_def iam.correct
                      tsbm_defs.tsbm_invar_def[OF ts2_impl] m2.correct set_map_filter)
        apply fastforce
      done
    qed
    thus "?P1" "?P2" by simp_all
  qed
end
end
