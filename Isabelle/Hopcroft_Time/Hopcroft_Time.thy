(* authors:
    Vincent Trélat <vincent.trelat@depinfonancy.net>
    Peter Lammich  <lammich@in.tum.de>
*)

section \<open>Running-time analysis of Hopcroft's algorithm\<close>

theory Hopcroft_Time
  imports
    "Isabelle_LLVM_Time.NREST_Main"
    Hopcroft_Thms
begin



(* TODO: Add type constraint to definition *)  
abbreviation monadic_WHILEIET :: 
  "('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> (char list, nat) acost) \<Rightarrow>
   ('b \<Rightarrow> (bool, (char list, enat) acost) nrest) \<Rightarrow>
   ('b \<Rightarrow> ('b, (char list, enat) acost) nrest) \<Rightarrow> 'b \<Rightarrow> ('b, (char list, enat) acost) nrest"
  where "monadic_WHILEIET I E b f s \<equiv> NREST.monadic_WHILEIET I E b f s"


text
\<open>
  Abstract level I
    def: Hopcroft_abstract
\<close>

definition "preds \<A> a C \<equiv> {q. \<exists>q'. (q,a,q')\<in>\<Delta> \<A> \<and> q'\<in>C }"

definition "pick_splitter_spec \<equiv> \<lambda>(P,L). do {
  ASSERT (L \<noteq> {});
  SPEC (\<lambda>(a,p). (a,p) \<in> L) (\<lambda>_. cost ''pick_splitter'' 1)
}"

definition "update_split_spec \<A> \<equiv> \<lambda>(P,L) a p. 
  SPEC (\<lambda>(P', L'). Hopcroft_update_splitters_pred \<A> p a P L L' 
                \<and> P' = Hopcroft_split \<A> p a {} P)
    (\<lambda>_. cost ''update_split'' (enat (card (\<Sigma> \<A>) * card (preds \<A> a p))))"


definition Hopcroft_abstract_f where
"Hopcroft_abstract_f \<A> = 
 (\<lambda>PL. do {
     ASSERT (Hopcroft_abstract_invar \<A> PL);                             
     (a,p) \<leftarrow> pick_splitter_spec PL;
     PL' \<leftarrow> update_split_spec \<A> PL a p;
     RETURNT PL'
   })"


definition "check_b_spec \<equiv> \<lambda>PL. consume (RETURNT (Hopcroft_abstract_b PL)) (cost ''check_l_empty'' 1)"   
   
definition "init_spec \<A> \<equiv> consume (RETURNT (Hopcroft_abstract_init \<A>)) (cost ''init_state'' 1)"

definition "check_states_empty_spec \<A> \<equiv> consume (RETURNT (\<Q> \<A> = {})) (cost ''check_states_empty'' 1)"

definition "check_final_states_empty_spec \<A> \<equiv> consume (RETURNT (\<F> \<A> = {})) (cost ''check_final_states_empty'' 1)"



definition mop_partition_empty :: "('a set set, _) nrest" where
  [simp]: "mop_partition_empty \<equiv> consume (RETURNT {}) (cost ''part_empty'' 1)"

definition mop_partition_singleton :: "'a set \<Rightarrow> ('a set set, _) nrest" where
  [simp]: "mop_partition_singleton s \<equiv> consume (RETURNT {s}) (cost ''part_singleton'' 1)"


text
\<open>
Formula in the paper proof:
For \<A>, (P, L),
\<Sum>{card (preds \<A> a C) * \<lfloor>log (real (card C))\<rfloor>. (a, C) \<in> L} + \<Sum>{card (preds \<A> a B) * \<lfloor>log (real (card B) / 2)\<rfloor>. (a, B) \<in> ((\<Sigma> \<A>)\<times>P) - L)}
\<close>

definition "estimate1 \<A> \<equiv> \<lambda>(P,L).
  \<Sum>{(card (preds \<A> (fst s) (snd s))) * (Discrete.log (card (snd s))) | s. s \<in> L} +
  \<Sum>{(card (preds \<A> (fst s) (snd s))) * (Discrete.log (card (snd s) div 2)) | s. s \<in> \<Sigma> \<A> \<times> P - L}"\<comment>\<open>@{term s} is a splitter (a, C).}\<close>
  
definition "cost_1_iteration \<equiv> 
  cost ''call'' 1 +
  cost ''check_l_empty'' 1 +
  cost ''if'' 1 +
  cost ''pick_splitter'' 1 +
  cost ''update_split'' 1"
  
definition estimate_iteration where
  "estimate_iteration \<A> PL \<equiv> estimate1 \<A> PL *m cost_1_iteration"

definition Hopcroft_abstractT where
  "Hopcroft_abstractT \<A> \<equiv>
   (if\<^sub>N (check_states_empty_spec \<A>) then mop_partition_empty else (
    if\<^sub>N (check_final_states_empty_spec \<A>) then mop_partition_singleton (\<Q> \<A>) else (
       do {
         PL \<leftarrow> init_spec \<A>;
         (P, _) \<leftarrow> monadic_WHILEIET (Hopcroft_abstract_invar \<A>) (\<lambda>s. estimate_iteration \<A> s)
                     check_b_spec
                     (Hopcroft_abstract_f \<A>) PL;
         RETURNT P
       })))"
       
       
lemma costmult_right_mono_nat:
  fixes a :: nat
  shows "a \<le> a' \<Longrightarrow> a *m c \<le> a' *m c"
  unfolding costmult_def less_eq_acost_def
  by (auto simp add: mult_right_mono)  


definition split_pred where
\<comment>\<open>@{term "(a, C)"} is a splitter of B and the result of the split is @{term "{B', B''}"}\<close>
  "split_pred \<A> P B a C B' B'' \<equiv>
    B \<in> P \<and>
    (\<exists> q1 q2. q1 \<in> B \<and> q2 \<in> B \<and>
      (\<exists> q1'. (q1, a, q1') \<in> \<Delta> \<A> \<and> q1' \<in> C) \<and>
      (\<exists> q2'. (q2, a, q2') \<in> \<Delta> \<A> \<and> q2' \<notin> C)) \<and>
    ((B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P \<or> (B, B'', B') \<in> Hopcroft_splitted \<A> C a {} P)"

lemma split_disj_union:
  assumes "P' = Hopcroft_split \<A> C a {} P" "is_partition (\<Q> \<A>) P" "split_pred \<A> P B a C B' B''"
  shows "B = B' \<union> B''" "B' \<inter> B'' = {}"
  using assms Hopcroft_splitted_aux[of B _ _ \<A> C a P]
  unfolding split_pred_def Hopcroft_splitted_def
  by blast+

lemma (in DFA) split_block_in_partition_prop1:
  assumes "P' = Hopcroft_split \<A> C a {} P" "is_partition (\<Q> \<A>) P"
  shows "(B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P \<or> (B, B'', B') \<in> Hopcroft_splitted \<A> C a {} P \<Longrightarrow> B' \<in> P' \<and> B'' \<in> P' \<and> B \<notin> P'"
  apply (simp add: assms(1))
  unfolding Hopcroft_splitted_def Hopcroft_split_def split_language_equiv_partition_set_def
  apply (simp, intro conjI)
    apply fastforce+
  unfolding split_language_equiv_partition_def split_set_def
  by blast

lemma (in DFA) split_block_in_partition_prop2:
  assumes "split_pred \<A> P B a C B' B''" "Hopcroft_abstract_invar \<A> (P, L)"
  defines "P' \<equiv> Hopcroft_split \<A> C a {} P"
  shows "B' \<in> P' \<and> B'' \<in> P' \<and> B \<notin> P'"
  apply (rule split_block_in_partition_prop1[of P' C a P B B' B''])
    apply (simp add: P'_def)
   apply (simp add: case_prodD[OF assms(2)[simplified Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def]])
  apply (simp add: assms(1)[simplified split_pred_def])
  done

lemma (in DFA) split_block_not_in_workset:
  assumes "(b, C) \<in> L" "(b, C) \<noteq> (a, B)" "split_pred \<A> P B b C B' B''" "(a, B) \<in> L" "a \<in> \<Sigma> \<A>"
          "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_update_splitters_pred \<A> C b P L L'"
        shows "(b, C) \<notin> L' \<and> (a, B) \<notin> L' \<and> (a, B') \<in> L' \<and> (a, B'') \<in> L'"
proof (rule conjI)
  show "(b, C) \<notin> L'"
  proof (rule ccontr)
    assume "\<not> (b, C) \<notin> L'" hence asm:"(b, C) \<in> L'" by simp
    from asm assms(7) assms(5) have "(b, C) \<in> L - {(b, C)} \<and> (\<forall>pa pb. (C, pa, pb) \<notin> Hopcroft_splitted \<A> C b {} P) \<or> (\<exists>p' pa pb. (p', pa, pb) \<in> Hopcroft_splitted \<A> C b {} P \<and> a \<in> \<Sigma> \<A> \<and> (C = pa \<or> C = pb))"
        unfolding Hopcroft_update_splitters_pred_def
                  Hopcroft_update_splitters_pred_aux_def
                  Hopcroft_update_splitters_pred_aux_upper_def
        by blast
      then obtain p' pa pb where
        part_def:"(p', pa, pb) \<in> Hopcroft_splitted \<A> C b {} P" "C = pa \<or> C = pb"
        by blast
      with Hopcroft_splitted_aux[OF part_def(1)] obtain C' where
        C_part:"p' = C \<union> C'" "C \<inter> C' = {}" "C' \<noteq> {}" "p' \<in> P"
        by blast
      moreover from assms(1) assms(6) have "C \<in> P" "p' \<inter> C \<noteq> {}"
        unfolding Hopcroft_abstract_invar_def
         using Hopcroft_splitted_aux[OF part_def(1)] part_def(2) by (fastforce, blast)
      moreover from assms(6) have "is_partition (\<Q> \<A>) P"
        unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def
        by simp
    ultimately show False
      unfolding is_partition_def by blast
  qed
next
  show "(a, B) \<notin> L' \<and> (a, B') \<in> L' \<and> (a, B'') \<in> L'"
  proof (rule conjI)
    show "(a, B) \<notin> L'"
    proof (rule ccontr)
      assume "\<not> (a, B) \<notin> L'" hence asm:"(a, B) \<in> L'" by simp
      from asm assms(7) assms(5) have "(a, B) \<in> L - {(b, C)} \<and> (\<forall>pa pb. (B, pa, pb) \<notin> Hopcroft_splitted \<A> C b {} P) \<or> (\<exists>p' pa pb. (p', pa, pb) \<in> Hopcroft_splitted \<A> C b {} P \<and> a \<in> \<Sigma> \<A> \<and> (B = pa \<or> B = pb))"
        unfolding Hopcroft_update_splitters_pred_def
                    Hopcroft_update_splitters_pred_aux_def
                    Hopcroft_update_splitters_pred_aux_upper_def
        by blast
      then obtain p' pa pb where
        part_def:"(p', pa, pb) \<in> Hopcroft_splitted \<A> C b {} P" "B = pa \<or> B = pb"
        using assms(3) unfolding split_pred_def
        by blast
        with Hopcroft_splitted_aux[OF part_def(1)] obtain BB where
          C_part:"p' = B \<union> BB" "B \<inter> BB = {}" "BB \<noteq> {}" "p' \<in> P"
          by blast
        moreover from assms(1) assms(3) assms(6) have "B \<in> P" "p' \<inter> B \<noteq> {}"
          unfolding split_pred_def apply blast
          unfolding Hopcroft_abstract_invar_def
          using Hopcroft_splitted_aux[OF part_def(1)] part_def(2) by blast
        moreover from assms(6) have "is_partition (\<Q> \<A>) P"
          unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def
          by simp
        ultimately show False
          unfolding is_partition_def by blast
    qed
  next
    show "(a, B') \<in> L' \<and> (a, B'') \<in> L'"
      using assms(3)[simplified split_pred_def]
      apply (cases "(B, B', B'') \<in> Hopcroft_splitted \<A> C b {} P")
      subgoal
      apply (rule Hopcroft_update_splitters_pred___in_splitted_in_L[of \<A> C b P L L' a B])
         apply (simp add: assms(7))
        apply (simp add: assms(5))
        apply (simp add: assms(3)[simplified split_pred_def])
        using assms(2) assms(4)
        apply blast
        done
      subgoal
        apply (rule conj_commute1)
        apply (rule Hopcroft_update_splitters_pred___in_splitted_in_L[of \<A> C b P L L' a B])
           apply (simp add: assms(7))
          apply (simp add: assms(5))
         apply (simp add: assms(3)[simplified split_pred_def])
        using assms(2) assms(4)
        apply blast
        done
      done
  qed
qed

definition aq_splitter where
  "aq_splitter a q L \<equiv> (if (\<exists> (a, B) \<in> L. q \<in> B) then 
                           let (a, B) = THE (a, B). (a, B) \<in> L \<and> q \<in> B in Some (a, B)
                          else None)"

lemma aq_splitter_unique:
  assumes "is_partition (\<Q> \<A>) P" "q \<in> \<Q> \<A>" "a \<in> \<Sigma> \<A>"
  shows "\<exists>! B. (a, B) \<in> (\<Sigma> \<A> \<times> P) \<and> q \<in> B"
  using is_partition_find[OF assms(1,2)]
    by (simp add: assms(3))

lemma aq_splitter_atmost1:
  assumes "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_abstract_b (P, L)" "q \<in> \<Q> \<A>" "a \<in> \<Sigma> \<A>"
  shows "(\<forall> B. (a, B) \<in> L \<longrightarrow> q \<notin> B) \<or> (\<exists>! B. (a, B) \<in> L \<and> q \<in> B)"
\<comment>\<open>Given a and q, there is at most one splitter containing q.\<close>
proof (rule SMT.verit_and_neg(3))
  assume "\<not> (\<forall>B. (a, B) \<in> L \<longrightarrow> q \<notin> B)"
  then obtain B where B_def:"(a, B) \<in> L \<and> q \<in> B" by blast
  show "\<exists>!B. (a, B) \<in> L \<and> q \<in> B"
  proof
    show "(a, B) \<in> L \<and> q \<in> B" using B_def .
    show "(a, B') \<in> L \<and> q \<in> B' \<Longrightarrow> B' = B" for B'
    proof-
      assume asm:"(a, B') \<in> L \<and> q \<in> B'"
      with assms(1) have "B' \<in> P"
        unfolding Hopcroft_abstract_invar_def
        by auto
      with assms(1) B_def asm show "B' = B"
        unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def is_partition_def
        by fastforce
    qed
  qed
qed

lemma (in DFA) preds_disj_eq:
  assumes "split_pred \<A> P B a C B' B''" "is_partition (\<Q> \<A>) P" "a \<in> \<Sigma> \<A>"
  shows
    "preds \<A> a B = preds \<A> a B' \<union> preds \<A> a B''"
    "preds \<A> a B' \<inter> preds \<A> a B'' = {}"
proof-
  have B_eq:"B = B' \<union> B''" "B' \<inter> B'' = {}"
    using assms split_disj_union by meson+

  have union:"preds \<A> a B' \<union> preds \<A> a B'' = {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> (q' \<in> B' \<or> q' \<in> B'')}"
    unfolding preds_def
    by blast

  have inter:"preds \<A> a B' \<inter> preds \<A> a B'' = {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> (q' \<in> B' \<inter>B'')}"
  proof-
    have "preds \<A> a B' \<inter> preds \<A> a B'' = {q. \<exists>q' q''. (q, a, q') \<in> \<Delta> \<A> \<and> (q, a, q'') \<in> \<Delta> \<A> \<and> (q' \<in> B' \<and> q'' \<in> B'')}"
      unfolding preds_def by blast
    moreover have "\<dots> = {q. \<exists>q' q''. (q, a, q') \<in> \<Delta> \<A> \<and> (q, a, q'') \<in> \<Delta> \<A> \<and> q' = q'' \<and>(q' \<in> B' \<and> q'' \<in> B'')}"
      using deterministic_LTS
      unfolding LTS_is_deterministic_def
      by blast
    ultimately show ?thesis
      by blast
  qed

  from B_eq(1) union show "preds \<A> a B = preds \<A> a B' \<union> preds \<A> a B''"
    unfolding preds_def
    by blast

  from B_eq(2) inter show "preds \<A> a B' \<inter> preds \<A> a B'' = {}"
    unfolding preds_def
    by blast
qed

lemma (in DFA) log_ineq:
  assumes "split_pred \<A> P B a C B' B''" "is_partition (\<Q> \<A>) P" "a \<in> \<Sigma> \<A>"
  shows "card (preds \<A> a B) * Discrete.log (card B) \<ge> card (preds \<A> a B') * Discrete.log (card B') + card (preds \<A> a B'') * Discrete.log (card B'')"
proof (intro discrete_log_ineqI)
  have fin:"finite (preds \<A> a B')" "finite (preds \<A> a B'')"
  proof-
    have "preds \<A> a E \<subseteq> \<Q> \<A>" for E
      unfolding preds_def
      using \<Delta>_consistent by blast
    from rev_finite_subset[OF finite_\<Q> this, of B'] rev_finite_subset[OF finite_\<Q> this, of B'']
    show "finite (preds \<A> a B')" "finite (preds \<A> a B'')" .
  qed

  from card_Un_Int[OF fin, simplified preds_disj_eq(1)[symmetric, OF assms] preds_disj_eq(2)[OF assms] Finite_Set.card.empty nat_arith.rule0[symmetric]]
  show "card (preds \<A> a B') + card (preds \<A> a B'') = card (preds \<A> a B)" .

  note incl =
    Un_upper1[of B' B'', simplified card_Un_Int split_disj_union(1)[OF _ assms(2,1), simplified, symmetric]]
    Un_upper2[of B'' B', simplified card_Un_Int split_disj_union(1)[OF _ assms(2,1), simplified, symmetric]]
  note fin =
    finite_subset[OF incl(1) is_partition_memb_finite[OF finite_\<Q> assms(2) conjunct1[OF assms(1)[simplified split_pred_def]]]]
    finite_subset[OF incl(2) is_partition_memb_finite[OF finite_\<Q> assms(2) conjunct1[OF assms(1)[simplified split_pred_def]]]]
  from
    card_Un_Int[OF fin,
      simplified split_disj_union(1)[OF _ assms(2,1), simplified, symmetric]
                 split_disj_union(2)[OF _ assms(2,1), simplified]
                 Finite_Set.card.empty
                 nat_arith.rule0[symmetric]]
  show "card B' + card B'' = card B" .
qed

lemma estimate1_decrease:
  fixes \<A> :: "('q,'a, 'DFA_more) NFA_rec_scheme"
    and P :: "'q set set"
    and L :: "('a \<times> 'q set) set"
    and a :: 'a
    and C :: "'q set"
  defines "P' \<equiv> Hopcroft_split \<A> C a {} P"
  assumes "DFA \<A>" "\<Q> \<A> \<noteq> {}" "\<F> \<A> \<noteq> {}" 
  "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_abstract_b (P, L)"
  "Hopcroft_update_splitters_pred \<A> C a P L L'" "(a, C) \<in> L"
  "a \<in> \<Sigma> \<A>"
  shows "estimate1 \<A> (P', L') \<le> estimate1 \<A> (P,L)"
proof-
  let ?Lc = "\<Sigma> \<A> \<times> P - L"
  let ?Lc' = "\<Sigma> \<A> \<times> P' - L'"

  {
    fix \<sigma>::'a and q::'q and B::"'q set" and B'::"'q set"
    assume "\<sigma> \<in> \<Sigma> \<A>" "q \<in> \<Q> \<A>"
    define aq where "aq = aq_splitter \<sigma> q L"
    define aq' where "aq' = aq_splitter \<sigma> q L'"
    assume asm:"aq = None" "aq' = None" "q\<in>B \<and> B \<in> P" "q\<in>B'\<and>B'\<in>P'"
    then have uniqueBB':"\<exists>! B. q \<in> B \<and> (\<sigma>, B) \<in> ?Lc" "\<exists>! B'. q \<in> B' \<and> (\<sigma>, B') \<in> ?Lc'"
    proof-
      have "(a, B) \<in> L \<Longrightarrow> q \<notin> B" for a B
      proof (rule ccontr)
        assume "(a, B)\<in>L" "\<not> q \<notin> B" hence asm:"\<exists>(a, B)\<in>L. q\<in>B" by blast
        then obtain s where "aq = Some s"
          by (simp add: aq_def aq_splitter_def)
        then show False
          by (simp add: \<open>aq = None\<close>)
      qed
      moreover from assms(5) \<open>q \<in> \<Q> \<A>\<close>
      have "\<exists>! B \<in> P. q \<in> B"
        unfolding Hopcroft_abstract_invar_def
          is_weak_language_equiv_partition_def
          is_partition_def
        by auto
      moreover have "B\<in>P \<Longrightarrow> (\<sigma>, B) \<in> L \<or> (\<sigma>, B) \<in> ?Lc" for B
        by (simp add: \<open>\<sigma> \<in> \<Sigma> \<A>\<close>)
      ultimately show "\<exists>! B. q \<in> B \<and> (\<sigma>, B) \<in> ?Lc"
        by blast
    next
      have nonsplitter:"(a, B') \<in> L' \<Longrightarrow> q \<notin> B'" for a B'
      proof (rule ccontr)
        assume "(a, B')\<in>L'" "\<not> q \<notin> B'" hence asm:"\<exists>(a, B')\<in>L'. q\<in>B'" by blast
        then obtain s where "aq' = Some s"
          by (simp add: aq'_def aq_splitter_def)
        then show False
          by (simp add: \<open>aq' = None\<close>)
      qed

      moreover have part_disj_workset:"B'\<in>P' \<Longrightarrow> (\<sigma>, B') \<in> L' \<or> (\<sigma>, B') \<in> ?Lc'" for B'
        by (simp add: \<open>\<sigma> \<in> \<Sigma> \<A>\<close>)

      show "\<exists>! B'. q \<in> B' \<and> (\<sigma>, B') \<in> ?Lc'"
      proof-
        from DFA.split_is_partition[OF assms(2) assms(5) assms(9) assms(8)] asm(4) \<open>q \<in> \<Q> \<A>\<close> have "\<exists>! B'. q\<in>B' \<and> B'\<in>P'"
          unfolding is_partition_def P'_def
          by blast
        then show ?thesis
          using nonsplitter part_disj_workset
          by auto
      qed
    qed
    
    from uniqueBB' have uniqueBB'_aux:
      "unique_pred B (\<lambda>p. q \<in> p \<and> (\<sigma>, p) \<in> ?Lc)" (* B = THE B. (\<sigma>, B) \<in> ?Lc \<and> q \<in> B *)
      "unique_pred B' (\<lambda>p. q \<in> p \<and> (\<sigma>, p) \<in> ?Lc')"
      unfolding unique_pred_def
      using asm(3,4) aq_splitter_unique[OF _ \<open>q \<in> \<Q> \<A>\<close> \<open>\<sigma> \<in> \<Sigma> \<A>\<close>] assms(5)
      unfolding Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def
       apply auto[1]
      using aq_splitter_unique[OF DFA.split_is_partition[OF assms(2) assms(5) assms(9) assms(8)] \<open>q \<in> \<Q> \<A>\<close> \<open>\<sigma> \<in> \<Sigma> \<A>\<close>] asm(4) uniqueBB'(2)
      unfolding P'_def by blast

    have "B = B' \<or> (\<exists> B'' aa CC. B = B' \<union> B'' \<and> B' \<inter> B'' = {} \<and> card B'' \<le> card B' \<and> (\<sigma>, B'') \<in> L' \<and> (\<sigma>, B') \<in> ?Lc' \<and> split_pred \<A> P B aa CC B' B'')"
    proof (cases "\<exists> B'' aa CC. split_pred \<A> P B aa CC B' B''") \<comment>\<open>The proof should examine wether B is split or not\<close>
      case True
      then obtain B'' aa CC where pred:"split_pred \<A> P B aa CC B' B''"
        by blast
      then have "B \<noteq> B''"
        using DFA.split_block_in_partition_prop2[OF assms(2) pred assms(5)]
        by blast
      then show ?thesis
      proof-
        have "B = B' \<union> B''" "B' \<inter> B'' = {}"
          using case_prodD[OF assms(5)[simplified Hopcroft_abstract_invar_def]]
          unfolding is_weak_language_equiv_partition_def
          using pred split_disj_union
          by meson+
        from uniqueBB'_aux(2) have "(\<sigma>, B') \<in> ?Lc'"
          unfolding unique_pred_def
          by blast
        show ?thesis
          sorry
      qed
    next
      case False
      then show ?thesis sorry
    qed
  }

  show ?thesis sorry
qed

lemma estimate1_progress:
  assumes (* "\<Q> \<A> \<noteq> {}" "\<F> \<A> \<noteq> {}" *) 
  "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_abstract_b (P, L)"
  "Hopcroft_update_splitters_pred \<A> p a P L L'"
  shows "estimate1 \<A> (Hopcroft_split \<A> p a {} P, L')
          + card (\<Sigma> \<A>) * card (preds \<A> a p) < estimate1 \<A> (P,L)" 
  unfolding estimate1_def preds_def
  apply simp
proof -
  show "\<Sum> {card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * Discrete.log (card b) |a b. (a, b) \<in> L'} +
    \<Sum> {card {q. \<exists>q'. (q, aa, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * (Discrete.log (card b) - Suc 0) |aa b. aa \<in> \<Sigma> \<A> \<and> b \<in> Hopcroft_split \<A> p a {} P \<and> (aa, b) \<notin> L'} +
    card (\<Sigma> \<A>) * card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> p}
    < \<Sum> {card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * Discrete.log (card b) |a b. (a, b) \<in> L} +
      \<Sum> {card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * (Discrete.log (card b) - Suc 0) |a b. a \<in> \<Sigma> \<A> \<and> b \<in> P \<and> (a, b) \<notin> L}"
    sorry
qed
  
lemma estimate1_progress_decrease:
  assumes "estimate1 \<A> (Hopcroft_split \<A> ba aa {} a, bb) + f aa ba < estimate1 \<A> (a, b)"
  shows
    "lift_acost c1 + cost ''update_split'' (enat (f aa ba)) +
      lift_acost (estimate1 \<A> (Hopcroft_split \<A> ba aa {} a, bb) *m (c1 + cost ''update_split'' 1)) 
    \<le> lift_acost (estimate1 \<A> (a, b) *m (c1 + cost ''update_split'' 1))"
proof -
  find_theorems lift_acost "(*m)"
  show ?thesis sorry
qed

lemma finite_sum_positive_cost:"finite {a. the_acost (cost n m) a > (0::nat)}"
  using finite_sum_nonzero_cost[of n m]
  by simp

lemma (in DFA) Hopcroft_abstract_correct :
  fixes t
  assumes [simp]: " cost ''part_empty'' 1 + (cost ''if'' 1 + cost ''check_states_empty'' 1) \<le> t"
  assumes [simp]: " cost ''part_singleton'' 1 +
        (cost ''if'' 1 +
         (cost ''check_final_states_empty'' 1 + (cost ''if'' 1 + cost ''check_states_empty'' 1)))
        \<le> t"
  
  shows "Hopcroft_abstractT \<A> \<le> SPEC (\<lambda>P. P = Myhill_Nerode_partition \<A>) (\<lambda>_. t)"
proof (cases "\<Q> \<A> = {} \<or> \<F> \<A> = {}")
  case True thus ?thesis    
    unfolding SPEC_def
    apply -
    apply(rule gwp_specifies_I)
    
    unfolding Hopcroft_abstractT_def check_states_empty_spec_def check_final_states_empty_spec_def
    apply simp
    supply [simp] = \<Q>_not_Emp Myhill_Nerode_partition___\<F>_emp
    apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET If_le_rule)
    done
next
  case False thus ?thesis
    unfolding SPEC_def
    apply -
    apply(rule gwp_specifies_I)

    unfolding Hopcroft_abstractT_def check_states_empty_spec_def check_final_states_empty_spec_def
      init_spec_def check_b_spec_def    
    
    apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET If_le_rule)
    subgoal
      apply (rule wfR2_If_if_wfR2)
      apply (simp add: wfR2_def estimate_iteration_def cost_1_iteration_def
          costmult_def the_acost_propagate Collect_conj_eq)
      apply (intro impI conjI)
      apply (rule finite_sum_positive_cost)+
      done

    subgoal
      unfolding Hopcroft_abstract_f_def pick_splitter_spec_def
        SPEC_REST_emb'_conv update_split_spec_def
      apply (refine_vcg \<open>simp\<close> rules: gwp_ASSERT_bind_I)
      apply (rule loop_body_conditionI)
      subgoal
        apply clarsimp
        apply (rule lift_acost_mono)
        unfolding estimate_iteration_def
        apply (rule costmult_right_mono_nat)
        sorry
      apply clarsimp
      unfolding estimate_iteration_def cost_1_iteration_def
      apply (drule (4) estimate1_progress_decrease)
      
      apply (rule lift_acost_mono)
      
      oops
      apply sc_solve
      apply auto []
      
      
      oops
(*       ci(state) \<ge> const1 + const2*cpreds(splitter) + ci(split(splitter,state)) *)
      
      
(*       estimate1(state) > estimate1(split(splitter,state)) + cpreds(splitter) *)
      
      
      
      unfolding cost_iteration_def cost_1_iteration_def
      
      apply sc_solve
      apply simp
        
      subgoal  
        
        
    apply clarsimp  
    subgoal for P L
        
      
      find_theorems "_ *m _" "(\<le>)"
      
      term lift_acost
      
      find_theorems "SPEC _ (\<lambda>_. ?a)"
      
      subgoal
        apply (simp add: SPEC_def loop_body_condition_def)
        
        
        sorry
      subgoal
        apply (simp add: Hopcroft_abstract_b_def)
        done
      done

  subgoal
    unfolding loop_exit_condition_def
    apply simp
    sorry

  subgoal by (simp add: Hopcroft_abstract_invar_init)

qed

text
\<open>
  Abstract level II
  Refinement of the specification for acquiring next state toward an inner loop.
    def: Hopcroft_set_f
\<close>
(* thm Hopcroft_set_f_def *)

text
\<open>
  Abstract level III
  Precomputation of the set of predecessors of the currently chosen set.
    def: Hopcroft_precompute_step
\<close>
(* thm Hopcroft_precompute_step_def *)

text
\<open>
  First data refinement
  Refinement towards efficient data structures. Partition of \<Q> \<rightarrow> maps
    def: Hopcroft_map
\<close>
(* thm Hopcroft_map_def *)

text
\<open>
  Second data refinement
  Classes as sets \<rightarrow> maps (bijection with natural numbers).
    def: Hopcroft_map2
\<close>
(* thm Hopcroft_map2_def *)

text
\<open>
  Implementation
  Instantiation of the locales
\<close>
(* thm hopcroft_impl_def *)
(* thm hop_impl.Hopcroft_code_def *)


end