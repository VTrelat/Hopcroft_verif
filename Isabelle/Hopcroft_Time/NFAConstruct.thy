(*  Title:       Constructing Nondeterministic Finite Automata
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

section \<open> Constructing Nondeterministic Finite Automata \<close>

theory NFAConstruct
imports Main LTS SemiAutomaton NFA 
begin

text \<open> In the following automata are constructed by 
sequentially adding states together to an initially empty automaton.
An \emph{empty} automaton contains an alphabet of labels and a set of initial states.
Adding states updates the set of states, the transition relation and the set of
accepting states.

This construction is used to add only the reachable states to an automaton.
\<close>

definition NFA_initial_automaton :: "'q set \<Rightarrow> 'a set \<Rightarrow> ('q, 'a) NFA_rec" where
  "NFA_initial_automaton I A \<equiv> \<lparr> \<Q>={}, \<Sigma>=A, \<Delta> = {}, \<I>=I, \<F> = {} \<rparr>"

definition NFA_insert_state :: "('q \<Rightarrow> bool) \<Rightarrow> ('q, 'a) LTS \<Rightarrow> 'q \<Rightarrow> ('q, 'a) NFA_rec \<Rightarrow> ('q, 'a) NFA_rec" where
"NFA_insert_state FP D q \<A> \<equiv>
\<lparr> \<Q>=insert q (\<Q> \<A>), \<Sigma>=\<Sigma> \<A>, \<Delta> = \<Delta> \<A> \<union> {qsq . qsq \<in> D \<and> fst qsq = q}, 
  \<I>=\<I> \<A>, \<F> = if (FP q) then insert q (\<F> \<A>) else (\<F> \<A>)\<rparr>"

definition NFA_construct_reachable where
"NFA_construct_reachable I A FP D =
 Finite_Set.fold (NFA_insert_state FP D) (NFA_initial_automaton I A) 
 (accessible (LTS_forget_labels D) I)"

lemma NFA_insert_state___comp_fun_commute :
  "comp_fun_commute_on UNIV (NFA_insert_state FP D)"
apply (simp add: NFA_insert_state_def comp_fun_commute_on_def o_def)
apply (subst fun_eq_iff)
apply simp
apply (metis Un_commute Un_left_commute insert_commute)
done

lemma fold_NFA_insert_state : 
"finite Q \<Longrightarrow> Finite_Set.fold (NFA_insert_state FP D) \<A> Q =
\<lparr> \<Q>=Q \<union> (\<Q> \<A>), \<Sigma>=\<Sigma> \<A>, \<Delta> = \<Delta> \<A> \<union> {qsq. qsq \<in> D \<and> fst qsq \<in> Q}, 
  \<I>=\<I> \<A>, \<F> = (\<F> \<A>) \<union> {q. q \<in> Q \<and> FP q} \<rparr>"
apply (induct rule: finite_induct)
apply (simp)
apply (simp add: comp_fun_commute_on.fold_insert [OF NFA_insert_state___comp_fun_commute])
apply (auto simp add: NFA_insert_state_def)
done

lemma NFA_construct_reachable_simp :
 "finite (accessible (LTS_forget_labels D) I) \<Longrightarrow>
  NFA_construct_reachable I A FP D = 
  \<lparr>\<Q> = accessible (LTS_forget_labels D) I, \<Sigma> = A, \<Delta> = {qsq. qsq \<in> D \<and> 
      fst qsq \<in> accessible (LTS_forget_labels D) I}, \<I> = I,
   \<F> = {q \<in> accessible (LTS_forget_labels D) I. FP q}\<rparr>"
by (simp add: NFA_construct_reachable_def
              fold_NFA_insert_state NFA_initial_automaton_def)

text \<open> Now show that this can be used to remove unreachable states \<close>
lemma (in NFA) NFA_remove_unreachable_states_implementation :
assumes I_OK: "I = \<I> \<A>"
    and A_OK: "A = \<Sigma> \<A>"
    and FP_OK: "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> FP q \<longleftrightarrow> q \<in> \<F> \<A>"
    and D_OK: "D = \<Delta> \<A>"
shows
  "(NFA_remove_unreachable_states \<A>) = (NFA_construct_reachable I A FP D)"
  (is "?ls = ?rs")
proof -
  let ?D = "LTS_forget_labels (\<Delta> \<A>)"
  note access_eq = LTS_is_reachable_from_initial_alt_def
  have access_eq' : "accessible ?D (\<I> \<A>) = \<Q> \<A> - SemiAutomaton_unreachable_states \<A>"
                    (is "?ls' = ?rs'")
  proof (intro set_eqI iffI)
    fix q
    assume "q \<in> ?rs'" 
    thus "q \<in> ?ls'"
      by (auto simp add: SemiAutomaton_unreachable_states_def access_eq LTS_is_unreachable_def)
  next
    fix q
    assume ls: "q \<in> ?ls'" 
    with LTS_is_reachable_from_initial_subset have q_in_Q: "q \<in> \<Q> \<A>" by auto
    from \<I>_consistent have I_subset_Q: "\<And>q. q \<in> \<I> \<A> \<Longrightarrow> q \<in> \<Q> \<A>" by auto

    from ls q_in_Q I_subset_Q show "q \<in> ?rs'"
      by (auto simp add: SemiAutomaton_unreachable_states_def access_eq LTS_is_unreachable_def Bex_def)
  qed

  have \<I>_diff_eq: "\<I> \<A> - SemiAutomaton_unreachable_states \<A> = \<I> \<A>"
    by (auto simp add: SemiAutomaton_unreachable_states_\<I>)

  from \<F>_consistent FP_OK have \<F>_eq: 
    "{q \<in> \<Q> \<A>. q \<notin> SemiAutomaton_unreachable_states \<A> \<and> FP q} =
     \<F> \<A> - SemiAutomaton_unreachable_states \<A>" by auto

  from LTS_is_reachable_from_initial_finite
  show "?ls = ?rs"
    apply (simp add: NFA_construct_reachable_simp A_OK I_OK D_OK)
    apply (simp add: NFA_remove_unreachable_states_def SemiAutomaton_to_NFA_def
                     NFA_remove_states_def access_eq' SemiAutomaton_remove_states_def)
    apply (auto simp add: \<I>_diff_eq \<F>_eq \<Delta>_consistent)
    apply (metis SemiAutomaton_unreachable_states_extend)
  done
qed

text \<open> Now let's implement efficiently constructing NFAs. During implementation, 
        the states are renamend as well. \<close>
definition NFA_construct_reachable_map_OK where
  "NFA_construct_reachable_map_OK S rm DD rm' \<longleftrightarrow>
   DD \<subseteq> dom rm' \<and>
   (\<forall>q r'. rm q = Some r' \<longrightarrow> rm' q = Some r') \<and>
   inj_on rm' (S \<inter> dom rm')"

lemma NFA_construct_reachable_map_OK_I [intro!] :
"\<lbrakk>DD \<subseteq> dom rm'; \<And>q r'. rm q = Some r' \<Longrightarrow> rm' q = Some r'; inj_on rm' (S \<inter> dom rm')\<rbrakk> \<Longrightarrow>
 NFA_construct_reachable_map_OK S rm DD rm'"
unfolding NFA_construct_reachable_map_OK_def by simp

lemma NFA_construct_reachable_map_OK_insert_DD :
  "NFA_construct_reachable_map_OK S rm (insert q DD) rm' \<longleftrightarrow>
   q \<in> dom rm' \<and> NFA_construct_reachable_map_OK S rm DD rm'"
unfolding NFA_construct_reachable_map_OK_def by simp

lemma NFA_construct_reachable_map_OK_trans :
  "\<lbrakk>NFA_construct_reachable_map_OK S rm DD rm'; 
    NFA_construct_reachable_map_OK S rm' DD' rm''; 
    DD'' \<subseteq> DD \<union> DD'\<rbrakk> \<Longrightarrow>
   NFA_construct_reachable_map_OK S rm DD'' rm''"
unfolding NFA_construct_reachable_map_OK_def 
by (simp add: subset_iff dom_def) metis

definition NFA_construct_reachable_abstract_impl_invar where
"NFA_construct_reachable_abstract_impl_invar I A FP D \<equiv> (\<lambda>((rm, \<A>), wl).
(\<exists>s. NFA_construct_reachable_map_OK (accessible (LTS_forget_labels D) (set I)) Map.empty 
       (s \<union> set I \<union> set wl \<union> {q'. \<exists>a q. q\<in>s \<and> (q,a,q')\<in> D}) rm \<and>
     (accessible (LTS_forget_labels D) (set I)  = 
      accessible_restrict (LTS_forget_labels D) s (set wl)) \<and>
     (\<A> = NFA_rename_states 
        \<lparr>\<Q> = s, \<Sigma> = A, \<Delta> = {qsq. qsq \<in> D \<and> fst qsq \<in> s}, \<I> = set I,
         \<F> = {q \<in> s. FP q}\<rparr> (the \<circ> rm))))"

definition NFA_construct_reachable_abstract_impl_weak_invar where
"NFA_construct_reachable_abstract_impl_weak_invar I A FP D \<equiv> (\<lambda>(rm, \<A>).
(\<exists>s. NFA_construct_reachable_map_OK (accessible (LTS_forget_labels D) (set I)) Map.empty 
       (s \<union> set I \<union> {q'. \<exists>a q. q\<in>s \<and> (q,a,q')\<in> D}) rm \<and>
     s \<subseteq> accessible (LTS_forget_labels D) (set I) \<and> 
     (\<A> = NFA_rename_states 
        \<lparr>\<Q> = s, \<Sigma> = A, \<Delta> = {qsq. qsq \<in> D \<and> fst qsq \<in> s}, \<I> = set I,
         \<F> = {q \<in> s. FP q}\<rparr> (the \<circ> rm))))"

lemma NFA_construct_reachable_abstract_impl_invar_weaken :
assumes invar: "NFA_construct_reachable_abstract_impl_invar I A FP D ((rm, \<A>), wl)"
shows "NFA_construct_reachable_abstract_impl_weak_invar I A FP D (rm, \<A>)"
using assms
unfolding NFA_construct_reachable_abstract_impl_weak_invar_def
          NFA_construct_reachable_abstract_impl_invar_def
          accessible_restrict_def NFA_construct_reachable_map_OK_def
apply clarify
apply (rule_tac x=s in exI)
apply auto
done

fun NFA_construct_reachable_abstract_impl_foreach_invar where
  "NFA_construct_reachable_abstract_impl_foreach_invar S DD rm D0 q it (rm', D', N) =
   (let D'' = (DD q) - it; qS = snd ` D'' in
    (NFA_construct_reachable_map_OK S rm qS rm' \<and>
     set N = qS \<and> q \<in> S \<and>
     D' = D0 \<union> {(the (rm' q), a, the (rm' q')) | a as q'. (as, q') \<in> D'' \<and> a \<in> as}))"
declare NFA_construct_reachable_abstract_impl_foreach_invar.simps [simp del]

definition NFA_construct_reachable_abstract_impl_step where
"NFA_construct_reachable_abstract_impl_step S DD rm D0 q =
  FOREACHi 
    (NFA_construct_reachable_abstract_impl_foreach_invar S DD rm D0 q)
    (DD q)
    (\<lambda>(as, q') (rm, D', N). do {
       ASSERT (q' \<in> S);
       (rm', r') \<leftarrow> SPEC (\<lambda>(rm', r'). NFA_construct_reachable_map_OK S rm {q'} rm' \<and> rm' q' = Some r');
       RETURN (rm', {(the (rm q), a, r') | a. a \<in> as} \<union> D', q' # N)
     }) (rm, D0, [])"

lemma NFA_construct_reachable_abstract_impl_step_correct :
assumes fin: "finite (DD q)"
    and DD_OK: "\<And>q as q'. q \<in> S \<Longrightarrow> (as, q') \<in> DD q \<Longrightarrow> q' \<in> S" 
    and inj_rm: "inj_on rm (S \<inter> dom rm)"
    and q_in_dom: "q \<in> S \<inter> dom rm"
shows "NFA_construct_reachable_abstract_impl_step S DD rm D0 q \<le>
      SPEC (NFA_construct_reachable_abstract_impl_foreach_invar S DD rm D0 q {})"
unfolding NFA_construct_reachable_abstract_impl_step_def
apply (intro refine_vcg)
apply (fact fin)
apply (insert q_in_dom)[]
apply (simp add: NFA_construct_reachable_abstract_impl_foreach_invar.simps
                 NFA_construct_reachable_map_OK_def inj_rm)
apply (insert q_in_dom)[] apply (simp, metis DD_OK subset_iff)
apply (clarify, simp)
apply (rename_tac it as q' rm' D' N rm'' r)
defer
apply simp
proof -
  fix it as q' rm' D' N rm'' r'
  assume in_it: "(as, q') \<in> it"
     and it_subset: "it \<subseteq> DD q"
     and invar: "NFA_construct_reachable_abstract_impl_foreach_invar S DD rm D0 q it (rm', D', N)"
     and map_OK: "NFA_construct_reachable_map_OK S rm' {q'} rm''"
     and rm''_q': "rm'' q' = Some r'"
  from q_in_dom obtain r where rm_q: "rm q = Some r" by auto

  define D'' where "D'' \<equiv> DD q - it"
  have D''_intro : "(DD q - (it - {(as, q')})) = insert (as, q') D''"
    using in_it it_subset D''_def by auto 

  from invar have
    rm'_OK: "NFA_construct_reachable_map_OK S rm (snd ` D'') rm'" and 
    set_N_eq: "set N = snd ` D''"  and 
    D'_eq: "D' = D0 \<union> {(the (rm' q), a, the (rm' q')) |a as q'. (as, q') \<in> D'' \<and> a \<in> as}"
    unfolding NFA_construct_reachable_abstract_impl_foreach_invar.simps
    by (simp_all add: Let_def D''_def)

  have prop1: "NFA_construct_reachable_map_OK S rm (insert q' (snd ` D'')) rm''" 
    using map_OK rm'_OK
    unfolding NFA_construct_reachable_map_OK_def
    by auto

  have prop2: "{(the (rm' q), a, r') |a. a \<in> as} \<union> D' =
    D0 \<union> {(the (rm'' q), aa, the (rm'' q'a)) |aa as' q'a. aa \<in> as' \<and> 
       (as' = as \<and> q'a = q' \<or> (as', q'a) \<in> D'')}"
    (is "?ls = D0 \<union> ?rs") 
  proof -
    from rm'_OK rm_q have rm'_q: "rm' q = Some r"
      unfolding NFA_construct_reachable_map_OK_def by simp
    with map_OK have rm''_q: "rm'' q = Some r"
      unfolding NFA_construct_reachable_map_OK_def by simp

    have step1: "?rs = {(the (rm'' q), a, the (rm'' q')) | a. a \<in> as} \<union> 
      {(the (rm'' q), a, the (rm'' q')) |a as q'. (as, q') \<in> D'' \<and> a \<in> as}"
      (is "_ = _ \<union> ?rs'")
      by auto

    from rm'_OK map_OK have rm''_eq: "\<And>a q'. (a, q') \<in> D'' \<Longrightarrow> rm'' q' = rm' q'"
      unfolding NFA_construct_reachable_map_OK_def dom_def subset_iff
      by auto 

    from rm''_eq have D'_eq': "D' = D0 \<union> ?rs'" unfolding D'_eq rm'_q rm''_q 
      by auto  metis+
    
    show ?thesis unfolding D'_eq' step1 by (auto simp add: rm'_q rm''_q rm''_q')
  qed

  show "NFA_construct_reachable_abstract_impl_foreach_invar
        S DD rm D0 q (it - {(as, q')})
        (rm'', {(the (rm' q), a, r') |a. a \<in> as} \<union> D', q' # N) " 
    unfolding NFA_construct_reachable_abstract_impl_foreach_invar.simps D''_intro using q_in_dom
    by (auto simp add: Let_def set_N_eq prop1 prop2)
qed

definition NFA_construct_reachable_abstract_impl where
  "NFA_construct_reachable_abstract_impl I A FP D DD =
   do {
     (rm, I') \<leftarrow> SPEC (\<lambda>(rm, I'). 
        NFA_construct_reachable_map_OK (accessible (LTS_forget_labels D) (set I)) Map.empty (set I) rm \<and>
        I' = (the \<circ> rm) ` (set I));
     ((rm, \<A>), _) \<leftarrow> WORKLISTIT (NFA_construct_reachable_abstract_impl_invar I A FP D) 
      (\<lambda>_. True)
      (\<lambda>(rm, \<A>) q. do {
         ASSERT (q \<in> dom rm \<and> q \<in> accessible (LTS_forget_labels D) (set I) \<and>
                 NFA_construct_reachable_abstract_impl_weak_invar I A FP D (rm, \<A>));
         if (the (rm q) \<in> \<Q> \<A>) then
           (RETURN ((rm, \<A>), []))
         else                    
           do {
             (rm', D', N) \<leftarrow> SPEC (NFA_construct_reachable_abstract_impl_foreach_invar 
                 (accessible (LTS_forget_labels D) (set I)) DD rm (\<Delta> \<A>) q {});
             RETURN ((rm', \<lparr> \<Q>=insert (the (rm q)) (\<Q> \<A>), \<Sigma>=\<Sigma> \<A>, \<Delta> = D', 
                           \<I>=\<I> \<A>, \<F> = if (FP q) then (insert (the (rm q)) (\<F> \<A>)) else (\<F> \<A>)\<rparr>), N)
           }
        }) ((rm, \<lparr> \<Q>={}, \<Sigma>=A, \<Delta> = {}, \<I>=I', \<F>={} \<rparr>), I);
     RETURN \<A>
   }"

lemma NFA_construct_reachable_abstract_impl_correct :
fixes D :: "('q \<times> 'a \<times> 'q) set" and I
  and DD :: "'q \<Rightarrow> ('a set \<times> 'q) set"
defines "S \<equiv> (accessible (LTS_forget_labels D) (set I))"
assumes fin_S: "finite S"
    and DD_OK: "\<And>q a q'. q \<in> S \<Longrightarrow> (q, a, q') \<in> D \<longleftrightarrow> (\<exists>as. a \<in> as \<and> (as, q') \<in> DD q)" 
               "\<And>q as q'. q \<in> S \<Longrightarrow> (as, q') \<in> DD q \<Longrightarrow> as \<noteq> {}" 
shows "NFA_construct_reachable_abstract_impl I A FP D DD \<le>
       SPEC (\<lambda>\<A>. NFA_isomorphic (NFA_construct_reachable (set I) A FP D) (\<A>::('q2, 'a) NFA_rec))"
unfolding NFA_construct_reachable_abstract_impl_def S_def[symmetric]
apply (intro refine_vcg WORKLISTIT_rule)
apply (simp_all split: prod.splits split del: if_splits)

  apply (clarify, simp)
  apply (rename_tac rm)
defer
  apply (clarify, simp)
  apply (rename_tac rm)
  apply (subgoal_tac "wf (inv_image (measure (\<lambda>\<A>. card S - card (\<Q> \<A>))) snd)")
  apply assumption
defer
   apply (clarify) 
   apply (intro refine_vcg)
   apply simp
   apply (rename_tac rm' wl q rm \<A>)
   apply (intro conjI)
defer
defer
defer
   apply (clarify, simp) 
   apply (rename_tac rm' wl q rm \<A> r)
defer
   apply clarify 
   apply (simp split del: if_splits)
   apply (rename_tac rm'' wl q rm \<A> rm' D' N r)
   apply (intro conjI)
defer
defer
   apply (clarify, simp)
   apply (rename_tac rm' rm \<A>)
defer
proof -
  fix rm :: "'q \<Rightarrow> 'q2 option"
  assume rm_OK: "NFA_construct_reachable_map_OK S Map.empty (set I) rm"

  thus "NFA_construct_reachable_abstract_impl_invar I A FP D
          ((rm, \<lparr>\<Q> = {}, \<Sigma> = A, \<Delta> = {}, \<I> = (\<lambda>x. the (rm x)) ` set I, \<F> = {}\<rparr>), I)"
    unfolding NFA_construct_reachable_abstract_impl_invar_def
    apply (simp)
    apply (rule exI [where x = "{}"])
    apply (simp add: accessible_restrict_def NFA_rename_states_full_def S_def)
  done
next
  show "wf (inv_image (measure (\<lambda>\<A>. card S - card (\<Q> \<A>))) snd)"
    by (intro wf_inv_image wf_measure)
next
  fix rm :: "'q \<Rightarrow> 'q2 option" and \<A>

  note reach_simp = NFA_construct_reachable_simp [OF fin_S[unfolded S_def]]
  assume "NFA_construct_reachable_abstract_impl_invar I A FP D ((rm, \<A>), [])"
  thus "NFA_isomorphic (NFA_construct_reachable (set I) A FP D) \<A>"
    unfolding NFA_construct_reachable_abstract_impl_invar_def
    apply (simp add: reach_simp S_def[symmetric])
    apply (rule NFA_isomorphic___NFA_rename_states)
    apply (simp add: inj_on_def NFA_construct_reachable_map_OK_def dom_def subset_iff Ball_def)
    apply (metis option.sel)
  done
next
  fix rm :: "'q \<Rightarrow> 'q2 option"
  fix \<A> q wl 
  assume invar: "NFA_construct_reachable_abstract_impl_invar I A FP D ((rm, \<A>), q # wl)"

  from invar obtain s where 
    S_eq: "S = accessible_restrict (LTS_forget_labels D) s (insert q (set wl))" and
    rm_OK: "NFA_construct_reachable_map_OK S Map.empty (insert q (s \<union> set I \<union> 
            set wl \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D})) rm" and
    \<A>_eq: "\<A> = NFA_rename_states
           \<lparr>\<Q> = s, \<Sigma> = A, \<Delta> = {qsq \<in> D. fst qsq \<in> s}, \<I> = set I, \<F> = {q \<in> s. FP q}\<rparr>
           (the \<circ> rm)"
    unfolding NFA_construct_reachable_abstract_impl_invar_def S_def[symmetric] 
  by auto
 
  from rm_OK show "q \<in> dom rm"
    unfolding NFA_construct_reachable_map_OK_def by simp 

  from S_eq show "q \<in> S"
    using accessible_restrict_subset_ws[of "insert q (set wl)" "LTS_forget_labels D" s]
    by simp

  from NFA_construct_reachable_abstract_impl_invar_weaken[OF invar]
  show "NFA_construct_reachable_abstract_impl_weak_invar I A FP D (rm, \<A>)" by simp
next
  fix rm :: "'q \<Rightarrow> 'q2 option" and \<A> q wl r

  assume invar: "NFA_construct_reachable_abstract_impl_invar I A FP D ((rm, \<A>), q # wl)" and
         rm_q_eq: "rm q = Some r" and
         rm_q: "r \<in> \<Q> \<A>" and
         q_in_S: "q \<in> S"
    
  show "NFA_construct_reachable_abstract_impl_invar I A FP D ((rm, \<A>), wl)"
  proof -
    from invar obtain s where 
      rm_OK: "NFA_construct_reachable_map_OK S Map.empty (insert q (s \<union> set I \<union> 
              set wl \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D})) rm" and
      S_eq: "S = accessible_restrict (LTS_forget_labels D) s (insert q (set wl))" and
      \<A>_eq: "\<A> = NFA_rename_states 
        \<lparr>\<Q> = s, \<Sigma> = A, \<Delta> = {qsq. qsq \<in> D \<and> fst qsq \<in> s}, \<I> = set I,
         \<F> = {q \<in> s. FP q}\<rparr> (the \<circ> rm)" 
      unfolding NFA_construct_reachable_abstract_impl_invar_def S_def[symmetric] by auto
    from S_eq have s_subset: "s \<subseteq> S" unfolding accessible_restrict_def by simp

    from rm_q \<A>_eq have "r \<in> (the \<circ> rm) ` s" by simp
    with rm_OK rm_q_eq q_in_S s_subset have "q \<in> s"
      unfolding NFA_construct_reachable_map_OK_def
      apply (simp add: image_iff Bex_def dom_def subset_iff inj_on_def Ball_def)
      apply (metis option.sel)
    done

    from `q \<in> s` have "insert q (s \<union> set I \<union> set wl \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D}) = 
                       s \<union>  set I \<union> set wl \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D}" by auto
    with `q \<in> s` rm_OK s_subset show ?thesis
      unfolding NFA_construct_reachable_abstract_impl_invar_def S_def[symmetric]
      apply simp
      apply (rule exI[where x = s])
      apply (simp add: \<A>_eq S_eq accessible_restrict_insert_in)
    done
  qed
next
  fix rm :: "'q \<Rightarrow> 'q2 option"
  fix \<A> q wl rm' D' N r
  assume invar: "NFA_construct_reachable_abstract_impl_invar I A FP D ((rm, \<A>), q # wl)"
     and rm_q_eq: "rm q = Some r" 
     and nin_Q: "r \<notin> \<Q> \<A>"
     and q_in_S: "q \<in> S"
  assume foreach_invar: "NFA_construct_reachable_abstract_impl_foreach_invar S DD rm (\<Delta> \<A>) q {} (rm', D', N)"
  from rm_q_eq have r_eq: "r = the (rm q)" by simp

  from invar obtain s where 
     S_eq: "S = accessible_restrict (LTS_forget_labels D) s (insert q (set wl))" and
     rm_OK: "NFA_construct_reachable_map_OK S Map.empty 
          (insert q (s \<union> set I \<union> set wl \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D})) rm" and
     \<A>_eq: "\<A> = NFA_rename_states 
        \<lparr>\<Q> = s, \<Sigma> = A, \<Delta> = {qsq. qsq \<in> D \<and> fst qsq \<in> s}, \<I> = set I,
         \<F> = {q \<in> s. FP q}\<rparr> (the \<circ> rm)" 
     unfolding NFA_construct_reachable_abstract_impl_invar_def S_def[symmetric] by auto

   define D'' where "D'' \<equiv> {(a, q'). (q, a, q') \<in> D}" 

  from DD_OK[OF q_in_S] 
  have snd_D''_eq: "snd ` D'' = snd ` (DD q)"
    unfolding D''_def by (auto simp add: image_iff Bex_def) (metis ex_in_conv)

  from foreach_invar have 
    rm'_OK: "NFA_construct_reachable_map_OK S rm (snd ` D'') rm'" and 
    set_N_eq: "set N = snd ` D''"  and 
    D'_eq: "D' = \<Delta> \<A> \<union> {(the (rm' q), a, the (rm' q')) |a q'. (a, q') \<in> D''}"
    unfolding NFA_construct_reachable_abstract_impl_foreach_invar.simps snd_D''_eq
    by (auto simp add: Let_def D''_def DD_OK)

  define DDD where "DDD \<equiv> insert q (s \<union> set I \<union> set wl \<union> {q'. \<exists>a q. q \<in> s \<and> (q, a, q') \<in> D})"
  have DDD_intro: "(insert q
       (s \<union> set I \<union> (set N \<union> set wl) \<union> {q'. \<exists>a qa. (qa = q \<or> qa \<in> s) \<and> (qa, a, q') \<in> D})) = DDD \<union> snd ` D''"  
    unfolding DDD_def by (auto simp add: image_iff set_N_eq D''_def)

  from nin_Q \<A>_eq have q_nin_s: "q \<notin> s" by (auto simp add: image_iff r_eq)

  have "(set wl \<union> {y. (q, y) \<in> LTS_forget_labels D}) = set N \<union> set wl"
    unfolding set_N_eq D''_def LTS_forget_labels_def by (auto simp add: image_iff)
  hence prop1: "S = accessible_restrict (LTS_forget_labels D) (insert q s) (set N \<union> set wl)"
     by (simp add: S_eq accessible_restrict_insert_nin q_nin_s)

  have prop2: "NFA_construct_reachable_map_OK S Map.empty
     (insert q  (s \<union> set I \<union> (set N \<union> set wl) \<union> {q'. \<exists>a qa. (qa = q \<or> qa \<in> s) \<and> (qa, a, q') \<in> D})) rm'" 
    unfolding DDD_intro NFA_construct_reachable_map_OK_def
  proof (intro conjI allI impI Un_least)
    from rm'_OK show "snd ` D'' \<subseteq> dom rm'" "inj_on rm' (S \<inter> dom rm')"
      unfolding NFA_construct_reachable_map_OK_def by simp_all
  next
    from rm_OK have "DDD \<subseteq> dom rm"
      unfolding NFA_construct_reachable_map_OK_def DDD_def[symmetric] by simp
    moreover from rm'_OK have "dom rm \<subseteq> dom rm'"
      unfolding NFA_construct_reachable_map_OK_def dom_def by auto
    finally show "DDD \<subseteq> dom rm'" .
  qed simp

  from rm'_OK have "\<And>q. q \<in> dom rm \<Longrightarrow> rm' q = rm q" 
    unfolding NFA_construct_reachable_map_OK_def
    by (simp add: dom_def) metis
  with rm_OK have rm'_eq: "\<And>q'. q' \<in> DDD \<Longrightarrow> rm' q' = rm q'" 
    unfolding NFA_construct_reachable_map_OK_def DDD_def[symmetric]
    by (simp add: subset_iff)

  have prop3: " 
    \<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>, \<Delta> = D', \<I> = \<I> \<A>,
       \<F> = if FP q then insert (the (rm q)) (\<F> \<A>) else \<F> \<A>\<rparr> =
    NFA_rename_states
     \<lparr>\<Q> = insert q s, \<Sigma> = A, \<Delta> = {qsq \<in> D. fst qsq = q \<or> fst qsq \<in> s}, \<I> = set I,
        \<F> = {qa. (qa = q \<or> qa \<in> s) \<and> FP qa}\<rparr>
     (the \<circ> rm')" 
  proof -
    from DDD_def have "set I \<subseteq> DDD" unfolding DDD_def by auto
    with rm'_eq have rm'_eq_I: "(the \<circ> rm) ` set I = (the \<circ> rm') ` set I" 
      apply (rule_tac set_eqI)
      apply (auto simp add: image_iff Bex_def subset_iff)
    done

    have "insert q s \<subseteq> DDD" unfolding DDD_def by auto
    with rm'_eq have rm'_eq_Q: "insert r ((the \<circ> rm) ` s) = insert (the (rm' q)) ((the \<circ> rm') ` s)"
      apply (rule_tac set_eqI)
      apply (auto simp add: image_iff Bex_def subset_iff r_eq)
    done

    have D'_eq' : "D' = {(the (rm' s1), a, the (rm' s2)) |s1 a s2. (s1, a, s2) \<in> D \<and> (s1 = q \<or> s1 \<in> s)}"    
       (is "_ = ?ls")
    proof -
      have "?ls = {(the (rm' s1), a, the (rm' s2)) |s1 a s2. (s1, a, s2) \<in> D \<and> s1 \<in> s} \<union>
                  {(the (rm' q), a, the (rm' q')) |a q'. (a, q') \<in> D''}"
           (is "_ = ?ls' \<union> _")
        unfolding D''_def by auto
      moreover
        from rm'_eq have "?ls' = \<Delta> \<A>" unfolding \<A>_eq DDD_def
          by (auto simp add: NFA_rename_states_def) metis+
      finally show ?thesis by (simp add: D'_eq)
    qed

    from rm'_eq have rm'_eq_F: 
      "(if FP q then insert (the (rm q)) (\<F> \<A>) else \<F> \<A>) =
        (the \<circ> rm') ` {qa. (qa = q \<or> qa \<in> s) \<and> FP qa}" 
      apply (rule_tac set_eqI)
      apply (simp add: image_iff \<A>_eq DDD_def)
      apply (metis) 
    done

  show ?thesis
    using rm'_eq_I rm'_eq_Q by (simp add: NFA_rename_states_full_def \<A>_eq rm'_eq_F D'_eq')
  qed

  from S_eq have s_subset: "s \<subseteq> S" unfolding accessible_restrict_def by simp
  show "NFA_construct_reachable_abstract_impl_invar I A FP D
        ((rm',\<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>, \<Delta> = D', \<I> = \<I> \<A>,
             \<F> = if FP q then insert (the (rm q)) (\<F> \<A>) else \<F> \<A>\<rparr>), N @ wl)"
    unfolding NFA_construct_reachable_abstract_impl_invar_def S_def[symmetric]
    apply (simp split del: if_splits)
    apply (rule exI [where x = "insert q s"])
    apply (simp split del: if_splits add: q_in_S s_subset)
    apply (simp add: prop3 prop2)
    apply (simp add: prop1)
  done

  from S_eq have s_subset: "s \<subseteq> S" unfolding accessible_restrict_def by simp
  with fin_S have fin_s: "finite s" by (metis finite_subset)

  from \<A>_eq fin_s nin_Q have fin_Q: "finite (\<Q> \<A>)" and card_Q_le': "card (\<Q> \<A>) \<le> card s"
    unfolding NFA_rename_states_def by (simp_all add: card_image_le image_iff r_eq) 

  from S_eq s_subset accessible_restrict_subset_ws[of "(insert q (set wl))" "LTS_forget_labels D" s] 
  have "insert q s \<subseteq> S" unfolding accessible_restrict_def by simp 
  hence "card (insert q s) \<le> card S" by (rule card_mono[OF fin_S])
  hence "card s < card S" by (simp add: q_nin_s fin_s)
  with card_Q_le' have card_Q_le: "card (\<Q> \<A>) < card S" by simp

  hence "card S - card (insert r (\<Q> \<A>)) < card S - card (\<Q> \<A>)"  by (simp add: nin_Q fin_Q)
  thus "card S - card (insert r (\<Q> \<A>)) < card S - card (\<Q> \<A>) \<or>
       rm' = rm \<and> \<lparr>\<Q> = insert r (\<Q> \<A>), \<Sigma> = \<Sigma> \<A>, \<Delta> = D', \<I> = \<I> \<A>,
          \<F> = if FP q then insert (the (rm q)) (\<F> \<A>) else \<F> \<A>\<rparr> = \<A> \<and> N = []" by simp
qed

definition NFA_construct_reachable_abstract2_impl where
  "NFA_construct_reachable_abstract2_impl I A FP D DD =
   do {
     (rm, I') \<leftarrow> SPEC (\<lambda>(rm, I'). 
        NFA_construct_reachable_map_OK (accessible (LTS_forget_labels D) (set I)) Map.empty (set I) rm \<and>
        I' = (the \<circ> rm) ` (set I));
     ((rm, \<A>), _) \<leftarrow> WORKLISTIT (NFA_construct_reachable_abstract_impl_invar I A FP D) 
      (\<lambda>_. True)
      (\<lambda>(rm, \<A>) q. do {
         ASSERT (q \<in> dom rm \<and> q \<in> accessible (LTS_forget_labels D) (set I) \<and>
                 NFA_construct_reachable_abstract_impl_weak_invar I A FP D (rm, \<A>));
         if (the (rm q) \<in> \<Q> \<A>) then
           (RETURN ((rm, \<A>), []))
         else                    
           do {
             ASSERT (the (rm q) \<notin> \<F> \<A>); \<^cancel>\<open>Peter: I inserted the assertion here, to justify refinement to insert-dj later\<close>
             (rm', D', N) \<leftarrow> NFA_construct_reachable_abstract_impl_step 
                 (accessible (LTS_forget_labels D) (set I)) DD rm (\<Delta> \<A>) q;
             RETURN ((rm', \<lparr> \<Q>=insert (the (rm q)) (\<Q> \<A>), \<Sigma>=\<Sigma> \<A>, \<Delta> = D', 
                           \<I>=\<I> \<A>, \<F> = if (FP q) then (insert (the (rm q)) (\<F> \<A>)) else (\<F> \<A>)\<rparr>), N)
           }
        }) ((rm, \<lparr> \<Q>={}, \<Sigma>=A, \<Delta> = {}, \<I>=I', \<F>={} \<rparr>), I);
     RETURN \<A>
   }"

lemma NFA_construct_reachable_abstract2_impl_correct :
fixes D :: "('q \<times> 'a \<times> 'q) set" and I
defines "S \<equiv> accessible (LTS_forget_labels D) (set I)"
assumes fin_S: "finite S"
    and fin_DD: "\<And>q. q \<in> S \<Longrightarrow> finite (DD q)"
    and DD_OK: "\<And>q as q'. q \<in> S \<Longrightarrow> (as, q') \<in> DD q \<Longrightarrow> q' \<in> S" 
shows "NFA_construct_reachable_abstract2_impl I A FP D DD \<le> \<Down>Id ((NFA_construct_reachable_abstract_impl I A FP D DD)::('q2, 'a) NFA_rec nres)"
unfolding NFA_construct_reachable_abstract2_impl_def NFA_construct_reachable_abstract_impl_def S_def[symmetric]
apply refine_rcg
apply (simp)
apply (rule single_valued_Id)
apply (rule single_valued_Id)
apply (simp)
apply (simp_all add: list_all2_eq[symmetric] refine_hsimp)

(** Peter: New assertion is easily proved here *)
subgoal by (auto simp: NFA_construct_reachable_abstract_impl_weak_invar_def)

apply (clarify, simp)
apply (rename_tac q rm \<A> r)
apply (rule NFA_construct_reachable_abstract_impl_step_correct)
proof -
  fix q
  assume "q \<in> S"
  thus "finite (DD q)" by (rule fin_DD)
next
  fix rm :: "'q \<Rightarrow> 'q2 option" and
      \<A> :: "('q2, 'a) NFA_rec" 

  assume "NFA_construct_reachable_abstract_impl_weak_invar I A FP D (rm, \<A>)"
  thus "inj_on rm (S \<inter> dom rm)" 
     unfolding NFA_construct_reachable_abstract_impl_weak_invar_def 
               NFA_construct_reachable_map_OK_def S_def[symmetric] by auto
next
  fix q as q'
  assume "q \<in> S" "(as, q') \<in> DD q"
  with DD_OK show "q' \<in> S" by blast
next
  fix rm :: "'q \<Rightarrow> 'q2 option" and q r
  assume "rm q = Some r" "q \<in> S" 
  thus "q \<in> S \<inter> dom rm" by blast
qed


lemma NFA_construct_reachable_abstract2_impl_correct_full :
fixes D :: "('q \<times> 'a \<times> 'q) set" and I
  and DD :: "'q \<Rightarrow> ('a set \<times> 'q) set"
defines "S \<equiv> (accessible (LTS_forget_labels D) (set I))"
assumes fin_S: "finite S"
    and DD_OK: "\<And>q a q'. q \<in> S \<Longrightarrow> (q, a, q') \<in> D \<longleftrightarrow> (\<exists>as. a \<in> as \<and> (as, q') \<in> DD q)" 
               "\<And>q as q'. q \<in> S \<Longrightarrow> (as, q') \<in> DD q \<Longrightarrow> as \<noteq> {}"
    and fin_DD: "\<And>q. q \<in> S \<Longrightarrow> finite (DD q)" 
shows "NFA_construct_reachable_abstract2_impl I A FP D DD \<le>
       SPEC (\<lambda>\<A>. NFA_isomorphic (NFA_construct_reachable (set I) A FP D) (\<A>::('q2, 'a) NFA_rec))"
proof -
  from assms
  have step1 : "NFA_construct_reachable_abstract_impl I A FP D DD \<le> SPEC
     (NFA_isomorphic (NFA_construct_reachable (set I) A FP D))"
    apply (rule_tac NFA_construct_reachable_abstract_impl_correct)
    apply (simp_all add: S_def)
  done

  have step2: "NFA_construct_reachable_abstract2_impl I A FP D DD \<le> \<Down> Id
     (NFA_construct_reachable_abstract_impl I A FP D DD)" 
  proof -
    { fix q as q'
      assume q_in_S: "q \<in> S" and in_DD_q: "(as, q') \<in> DD q" 

      from in_DD_q DD_OK[OF q_in_S] have qq'_in_D: "(q, q') \<in> (LTS_forget_labels D)"
        unfolding LTS_forget_labels_def
        by simp (metis all_not_in_conv)

      from q_in_S qq'_in_D
      have "q' \<in> S" unfolding S_def accessible_def 
      by (metis rtrancl_image_advance)
    } note pre = this

    from NFA_construct_reachable_abstract2_impl_correct[of D I DD, folded S_def, OF fin_S]
         fin_DD pre
    show ?thesis by auto
  qed

  from conc_trans_additional(5)[OF step2 step1] show ?thesis .
qed

end
