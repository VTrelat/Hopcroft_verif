(* authors:
    Vincent Trélat <vincent.trelat@depinfonancy.net>
    Peter Lammich  <lammich@in.tum.de>
*)

section \<open>Running-time analysis of Hopcroft's algorithm\<close>

theory Hopcroft_Time
  imports
    "Isabelle_LLVM_Time.NREST_Main"
    Hopcroft_Thms
    "HOL-Combinatorics.Permutations"
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

lemma split_pred_sym:"split_pred \<A> P B a C B' B'' = split_pred \<A> P B a C B'' B'"
  unfolding split_pred_def by blast

lemma (in DFA) Hopcroft_splitted_split_pred:
  assumes "is_partition (\<Q> \<A>) P" "(B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P"
  shows "split_pred \<A> P B a C B' B''"
proof-
  have props:
    "B' = {s \<in> B. \<exists>q'\<in>C. (s, a, q') \<in> \<Delta> \<A>}"
    "B'' = {s \<in> B. \<forall>q'\<in>C. (s, a, q') \<notin> \<Delta> \<A>}"
    "B \<in> P"
    "(\<exists>x. x \<in> B \<and> (\<exists>q'\<in>C. (x, a, q') \<in> \<Delta> \<A>))"
    "(\<exists>x. x \<in> B \<and> (\<forall>q'\<in>C. (x, a, q') \<notin> \<Delta> \<A>))"
    using assms
    unfolding Hopcroft_splitted_def split_language_equiv_partition_def split_set_def split_pred_def
    by blast+

  show ?thesis unfolding split_pred_def
  proof (intro conjI)
    show "\<exists>q1 q2. q1 \<in> B \<and> q2 \<in> B \<and> (\<exists>q1'. (q1, a, q1') \<in> \<Delta> \<A> \<and> q1' \<in> C) \<and> (\<exists>q2'. (q2, a, q2') \<in> \<Delta> \<A> \<and> q2' \<notin> C)"
    proof-
      from props obtain q1 q2 where q1q2_def:"q1 \<in> B'" "q2 \<in> B''"
        by blast
      from q1q2_def have "q1 \<in> B" "q2 \<in> B"
        using props(1,2) by blast+

      from \<open>q2\<in>B\<close> \<open>B\<in>P\<close> \<open>is_partition (\<Q> \<A>) P\<close> have "q2 \<in> \<Q> \<A>"
        using is_partition_in_subset by blast

      from props(1) q1q2_def obtain q1' where "q1' \<in> C" "(q1, a, q1') \<in> \<Delta> \<A>"
        by blast
      from props(2) q1q2_def obtain q2' where "(q2, a, q2') \<in> \<Delta> \<A>"
        using complete_LTS
        unfolding LTS_is_complete_def
        using \<Delta>_consistent \<open>(q1, a, q1') \<in> \<Delta> \<A>\<close> \<open>q2 \<in> \<Q> \<A>\<close> by blast
      then have "q2' \<notin> C"
        using props(2) q1q2_def(2) by blast
      show ?thesis
        using \<open>(q2, a, q2') \<in> \<Delta> \<A>\<close> \<open>q2 \<in> B\<close> \<open>q2' \<notin> C\<close> props(4) by blast
    qed
  qed (simp add: \<open>B \<in> P\<close>, insert assms, blast)
qed

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

definition "estimate2 \<A> \<equiv> \<lambda>(P,L) xs.
  if (xs <~~~> (\<Sigma> \<A> \<times> P)) then 
    \<Sum>s\<leftarrow>xs. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s))
  else undefined"
(* xs should be defined as SOME xs. xs <~~~> \<Sigma> \<A> \<times> P *)

lemma (in DFA) estimate2_decrease:
  assumes "P' = Hopcroft_split \<A> C a {} P" "DFA \<A>" "\<Q> \<A> \<noteq> {}" "\<F> \<A> \<noteq> {}"
  "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_abstract_b (P, L)"
  "Hopcroft_update_splitters_pred \<A> C a P L L'" "(a, C) \<in> L"
  "a \<in> \<Sigma> \<A>"
  shows "estimate2 \<A> (P', L') \<le> estimate2 \<A> (P,L)"
proof-
  let ?S = "P \<inter> P'"\<comment>\<open>Set of blocks remained unchanged\<close>
  let ?P1 = "P - ?S"\<comment>\<open>Set of blocks that will be split\<close>
  let ?P1'= "P' - ?S"\<comment>\<open>Set of split blocks (unordered)\<close>
  note is_partition_P = conjunct1[OF conjunct1[OF case_prodD[OF assms(5)[simplified Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def]]]]
  note is_partition_P'= split_is_partition[OF assms(5, 9, 8), simplified assms(1)[symmetric]]
  note block_cases = DFA.Hopcroft_split_in2[OF assms(2) conjunct1[OF conjunct1[OF case_prodD[OF assms(5)[simplified Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def]]]] assms(9), of _ C, simplified assms(1)[symmetric]]

  have "B \<in> ?P1 \<Longrightarrow> (\<exists> B' B''. B' \<in> ?P1' \<and> B'' \<in> ?P1' \<and> (B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P)" for B
    \<comment>\<open>A block in the set of blocks that are going to be split is actually
       split in two blocks that are in the set of split blocks\<close>
  proof-
    assume "B \<in> ?P1"
    then have "B \<notin> P'" by blast

    have conj:"(B \<notin> P \<or> (\<exists>pa pb. (B, pa, pb) \<in> Hopcroft_splitted \<A> C a {} P)) \<and> ((\<forall>p1 p1a p1b. (p1, p1a, p1b) \<notin> Hopcroft_splitted \<A> C a {} P \<or> (B \<noteq> p1a \<and> B \<noteq> p1b)))"
    proof-
      from block_cases[of B] have "B \<notin> P' \<longleftrightarrow> ((B \<notin> P \<or> (\<exists>pa pb. (B, pa, pb) \<in> Hopcroft_splitted \<A> C a {} P)) \<and> ((\<forall>p1 p1a p1b. (p1, p1a, p1b) \<notin> Hopcroft_splitted \<A> C a {} P \<or> (B \<noteq> p1a \<and> B \<noteq> p1b))))"
        by presburger
      with \<open>B \<notin> P'\<close> show ?thesis
        by fast
    qed

    from conjunct1[OF conj] \<open>B \<in> ?P1\<close> obtain B' B'' where split:"(B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P"
      by blast

    with conjunct2[OF conj] have "B \<noteq> B' \<and> B \<noteq> B''"
      by blast

    have "B' \<in> P'" "B'' \<in> P'"
      using DFA.split_block_in_partition_prop1[OF assms(2) assms(1) is_partition_P disjI1[OF split]]
      by blast+

    moreover have "B' \<in> ?P1'"
    proof (rule ccontr)
      assume "B' \<notin> ?P1'"
      with \<open>B' \<in> P'\<close> have "B' \<in> P" by blast
      moreover have "B \<inter> B' \<noteq> {}"
        using Hopcroft_splitted_aux[OF split]
        by simp
      ultimately show False using is_partition_P unfolding is_partition_def
        using \<open>B \<in> ?P1\<close> \<open>B \<noteq> B' \<and> B \<noteq> B''\<close> by blast 
    qed

    moreover have "B'' \<in> ?P1'"
    proof (rule ccontr)
      assume "B'' \<notin> ?P1'"
      with \<open>B'' \<in> P'\<close> have "B'' \<in> P" by blast
      moreover have "B \<inter> B'' \<noteq> {}"
        using Hopcroft_splitted_aux[OF split]
        by simp
      ultimately show False using is_partition_P unfolding is_partition_def
        using \<open>B \<in> ?P1\<close> \<open>B \<noteq> B' \<and> B \<noteq> B''\<close> by blast 
    qed

    ultimately show "\<exists>B' B''. B' \<in> ?P1' \<and> B'' \<in> ?P1' \<and> (B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P"
      using split by blast
  qed

  note fin\<Sigma>P = finite_cartesian_product[OF finite_\<Sigma> is_partition_finite[OF finite_\<Q> is_partition_P]]
  note fin\<Sigma>P'= finite_cartesian_product[OF finite_\<Sigma> is_partition_finite[OF finite_\<Q> is_partition_P']]

  obtain xs ys zs where split_xs:
    "xs = ys @ zs"
    "\<forall> e \<in> set ys. snd e \<in> ?S" "\<forall> e \<in> set zs. snd e \<notin> ?S"
    "xs <~~~> \<Sigma> \<A> \<times> P"
    "estimate2 \<A> (P, L) xs = (\<Sum>s\<leftarrow>xs. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s)))"
    unfolding estimate2_def
    using ls_perm_split_prop[OF fin\<Sigma>P, of "\<lambda>s. snd s \<in> ?S"]
    by clarsimp

  obtain xs' ys' zs' where split_xs':
    "xs' = ys' @ zs'"
    "\<forall> e \<in> set ys'. snd e \<in> ?S" "\<forall> e \<in> set zs'. snd e \<notin> ?S"
    "xs' <~~~> \<Sigma> \<A> \<times> P'"
    "estimate2 \<A> (P', L') xs' = (\<Sum>s\<leftarrow>xs'. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s)))"
    unfolding estimate2_def
    using ls_perm_split_prop[OF fin\<Sigma>P', of "\<lambda>s. snd s \<in> ?S"]
    by clarsimp

  have "estimate2 \<A> (P, L) xs =
    (\<Sum>s\<leftarrow>ys. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s)))+
    (\<Sum>s\<leftarrow>zs. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s)))"
    unfolding estimate2_def
    using split_xs(4) sum_list_conc_distr[OF split_xs(1), of "\<lambda>s. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s))"]
    by simp

  have "estimate2 \<A> (P', L') xs' =
    (\<Sum>s\<leftarrow>ys'. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s)))+
    (\<Sum>s\<leftarrow>zs'. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s)))"
    unfolding estimate2_def
    using split_xs'(4) sum_list_conc_distr[OF split_xs'(1), of "\<lambda>s. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s))"]
    by simp

  have fst_ys:"e \<in> set ys \<Longrightarrow> fst e \<in> \<Sigma> \<A>" for e
    using set_append[of ys zs, simplified split_xs(1)[symmetric] ls_perm_set_eq[OF fin\<Sigma>P split_xs(4)]]
    by (metis SigmaD1 UnI1 prod.exhaust_sel)
  have fst_zs:"e \<in> set zs \<Longrightarrow> fst e \<in> \<Sigma> \<A>" for e
    using set_append[of ys zs, simplified split_xs(1)[symmetric] ls_perm_set_eq[OF fin\<Sigma>P split_xs(4)]]
    by (metis SigmaD1 UnI2 prod.exhaust_sel)

  have fst_ys':"e \<in> set ys' \<Longrightarrow> fst e \<in> \<Sigma> \<A>" for e
    using set_append[of ys' zs', simplified split_xs'(1)[symmetric] ls_perm_set_eq[OF fin\<Sigma>P' split_xs'(4)]]
    by (metis SigmaD1 UnI1 prod.exhaust_sel)
  have fst_zs':"e \<in> set zs' \<Longrightarrow> fst e \<in> \<Sigma> \<A>" for e
    using set_append[of ys' zs', simplified split_xs'(1)[symmetric] ls_perm_set_eq[OF fin\<Sigma>P' split_xs'(4)]]
    by (metis SigmaD1 UnI2 prod.exhaust_sel)

  have list_set_eq:
    "set ys = \<Sigma> \<A> \<times> ?S" "set zs = \<Sigma> \<A> \<times> ?P1"
    "set ys' = \<Sigma> \<A> \<times> ?S" "set zs' = \<Sigma> \<A> \<times> ?P1'"
  proof-
    show "set ys = \<Sigma> \<A> \<times> ?S"
    proof
      show "\<Sigma> \<A> \<times> ?S \<subseteq> set ys"
      proof
        fix s
        assume asm:"s \<in> \<Sigma> \<A> \<times> ?S" 
        then obtain \<sigma> E where s_split:"s = (\<sigma>, E)" by blast
        with asm have "\<sigma> \<in> \<Sigma> \<A>" "E \<in> ?S"
          by blast+
        from asm ls_perm_set_eq[OF fin\<Sigma>P split_xs(4)] have "s \<in> set xs"
          by blast
        with split_xs show "s \<in> set ys"
          using \<open>E \<in> ?S\<close> s_split by auto
      qed
    qed (insert fst_ys in_prod_fst_sndI split_xs(2), blast)

    show "set zs = \<Sigma> \<A> \<times> ?P1"
    proof
      show "set zs \<subseteq> \<Sigma> \<A> \<times> ?P1"
      proof
        fix s
        assume asm:"s \<in> set zs"
        with fst_zs split_xs obtain \<sigma> E where zs_split:"s = (\<sigma>, E)" "\<sigma> \<in> \<Sigma> \<A>" "E \<notin> ?S"
          using prod.exhaust_sel by blast
        have "E \<in> P"
        proof-
          from split_xs(1) asm have "s \<in> set xs" by simp
          with ls_perm_set_eq[OF fin\<Sigma>P split_xs(4)] zs_split
          show ?thesis by blast
        qed
        with zs_split show "s \<in> \<Sigma> \<A> \<times> ?P1"
          by blast
      qed

      show "\<Sigma> \<A> \<times> ?P1 \<subseteq> set zs"
      proof
        fix s
        assume asm:"s \<in> \<Sigma> \<A> \<times> ?P1"
        then obtain \<sigma> E where "s = (\<sigma>, E)" by blast
        then show "s \<in> set zs"
          using \<open>set ys = \<Sigma> \<A> \<times> ?S\<close> asm ls_perm_set_eq[OF fin\<Sigma>P split_xs(4)] set_append[of ys zs] split_xs(1)
          by blast
      qed
    qed

    show "set ys' = \<Sigma> \<A> \<times> ?S"
    proof
      show "\<Sigma> \<A> \<times> ?S \<subseteq> set ys'"
      proof
        fix s
        assume asm:"s \<in> \<Sigma> \<A> \<times> ?S" 
        then obtain \<sigma> E where s_split:"s = (\<sigma>, E)" by blast
        with asm have "\<sigma> \<in> \<Sigma> \<A>" "E \<in> ?S"
          by blast+
        from asm ls_perm_set_eq[OF fin\<Sigma>P' split_xs'(4)] have "s \<in> set xs'"
          by blast
        with split_xs' show "s \<in> set ys'"
          using \<open>E \<in> ?S\<close> s_split by auto
      qed
    qed (insert fst_ys' in_prod_fst_sndI split_xs'(2), blast)

    show "set zs' = \<Sigma> \<A> \<times> ?P1'"
    proof
      show "set zs' \<subseteq> \<Sigma> \<A> \<times> ?P1'"
      proof
        fix s
        assume asm:"s \<in> set zs'"
        with fst_zs' split_xs' obtain \<sigma> E where zs'_split:"s = (\<sigma>, E)" "\<sigma> \<in> \<Sigma> \<A>" "E \<notin> ?S"
          using prod.exhaust_sel by blast
        have "E \<in> P'"
        proof-
          from split_xs'(1) asm have "s \<in> set xs'" by simp
          with ls_perm_set_eq[OF fin\<Sigma>P' split_xs'(4)] zs'_split
          show ?thesis by blast
        qed
        with zs'_split show "s \<in> \<Sigma> \<A> \<times> ?P1'"
          by blast
      qed

      show "\<Sigma> \<A> \<times> ?P1' \<subseteq> set zs'"
      proof
        fix s
        assume asm:"s \<in> \<Sigma> \<A> \<times> ?P1'"
        then obtain \<sigma> E where "s = (\<sigma>, E)" by blast
        then show "s \<in> set zs'"
          using \<open>set ys' = \<Sigma> \<A> \<times> ?S\<close> asm ls_perm_set_eq[OF fin\<Sigma>P' split_xs'(4)] set_append[of ys' zs'] split_xs'(1)
          by blast
      qed
    qed
  qed
  note ys_ys'_set_eq = this(1)[simplified this(3)[symmetric]]

  have distinct:
    "distinct xs" "distinct ys" "distinct zs"
    "distinct xs'" "distinct ys'" "distinct zs'"
    using distinct_append[of ys zs] finite_distinct_list[OF fin\<Sigma>P] mset_set_set perm_distinct_iff split_xs(1) split_xs(4)
    using distinct_append[of ys' zs'] finite_distinct_list[OF fin\<Sigma>P'] split_xs'(1) split_xs'(4)
    by metis+

  have ys_ys'_mset_eq: "mset ys = mset ys'"
    using mset_set_set[OF distinct(2)] mset_set_set[OF distinct(5)] ys_ys'_set_eq
    by argo

  {
    fix B
    assume "B \<in> set zs"
    with list_set_eq(2) have "snd B \<in> ?P1" using mem_Times_iff[of B "\<Sigma> \<A>" ?P1] by presburger
    with block_cases[of "snd B"] obtain B' B'' where
      split: "fst B \<in> \<Sigma> \<A>" "fst B = fst B'" "fst B = fst B''"
        "(snd (B::'a \<times> 'q set), snd (B'::'a \<times> 'q set), snd (B''::'a \<times> 'q set)) \<in> Hopcroft_splitted \<A> C a {} P"
      using fst_zs[OF \<open>B \<in> set zs\<close>] by fastforce
    
    have "snd B' \<in> P'" "snd B'' \<in> P'"
      using split split_block_in_partition_prop1[OF assms(1) is_partition_P]
      by blast+
    
    then have "B' \<in> set zs'" "B'' \<in> set zs'"
    proof-
      show "B' \<in> set zs'"
      proof-
        have "B' \<in> set xs'"
          using \<open>snd B' \<in> P'\<close> split ls_perm_set_eq[OF fin\<Sigma>P' split_xs'(4)] in_prod_fst_sndI
          by metis
        have "B' \<notin> set ys'"
        proof (rule ccontr)
          assume "\<not> B' \<notin> set ys'" hence "B' \<in> set ys'" by blast
          with list_set_eq(3) have "snd B' \<in> ?S"
            by fastforce
          with \<open>snd B \<in> ?P1\<close> have "snd B \<in> P" "snd B' \<in> P"
            by blast+

          then show False
            using Hopcroft_splitted_aux[OF split(4)] is_partition_P
            unfolding is_partition_def
            using Int_commute Un_Int_eq(3) Un_Int_eq(4)
            by blast
        qed
        then show ?thesis
          using \<open>B' \<in> set xs'\<close> split_xs'(1) by simp
      qed

      show "B'' \<in> set zs'"
      proof-
        have "B'' \<in> set xs'"
          using \<open>snd B'' \<in> P'\<close> split ls_perm_set_eq[OF fin\<Sigma>P' split_xs'(4)] in_prod_fst_sndI
          by metis
        have "B'' \<notin> set ys'"
        proof (rule ccontr)
          assume "\<not> B'' \<notin> set ys'" hence "B'' \<in> set ys'" by blast
          with list_set_eq(3) have "snd B'' \<in> ?S"
            by fastforce
          with \<open>snd B \<in> ?P1\<close> have "snd B \<in> P" "snd B'' \<in> P"
            by blast+

          then show False
            using Hopcroft_splitted_aux[OF split(4)] is_partition_P
            unfolding is_partition_def
            using Int_commute Un_Int_eq(3) Un_Int_eq(4)
            by blast
        qed
        then show ?thesis
          using \<open>B'' \<in> set xs'\<close> split_xs'(1) by simp
      qed
    qed

    have "B \<notin> set zs'"
      using split_block_in_partition_prop1[OF assms(1) is_partition_P, of "snd B" "snd B'" "snd B''"] split list_set_eq(4)
      by fastforce

    have "\<exists>! B'. \<exists>! B''. B' \<in> set zs' \<and> B'' \<in> set zs' \<and> (snd B, snd B', snd B'') \<in> Hopcroft_splitted \<A> C a {} P \<and> fst B = fst B' \<and> fst B = fst B''"
    proof (intro ex1_ex1I)
      show "B' \<in> set zs' \<and> B'' \<in> set zs' \<and> (snd B, snd B', snd B'') \<in> Hopcroft_splitted \<A> C a {} P \<and> fst B = fst B' \<and> fst B = fst B''"
      proof (intro conjI)
        show "(snd B, snd B', snd B'') \<in> Hopcroft_splitted \<A> C a {} P" using split(4) .
        show "B' \<in> set zs'" using \<open>B' \<in> set zs'\<close> .
        show "B'' \<in> set zs'" using \<open>B'' \<in> set zs'\<close> .
        show "fst B = fst B'" using split(2) .
        show "fst B = fst B''" using split(3) .
      qed
      show "\<And>x y. x \<in> set zs' \<and> y \<in> set zs' \<and> (snd B, snd x, snd y) \<in> Hopcroft_splitted \<A> C a {} P \<and> fst B = fst x \<and> fst B = fst y \<Longrightarrow> B' = x \<and> B'' = y"
      proof-
        show "x \<in> set zs' \<and> y \<in> set zs' \<and> (snd B, snd x, snd y) \<in> Hopcroft_splitted \<A> C a {} P \<and> fst B = fst x \<and> fst B = fst y \<Longrightarrow> B' = x \<and> B'' = y" for x y
        proof-
          assume asm:"x \<in> set zs' \<and> y \<in> set zs' \<and> (snd B, snd x, snd y) \<in> Hopcroft_splitted \<A> C a {} P \<and> fst B = fst x \<and> fst B = fst y"
          with split(4) have "snd x = snd B'" "snd y = snd B''"
            unfolding Hopcroft_splitted_def
            by (simp, metis fst_conv snd_conv)+
          moreover have "fst x = fst B'" "fst y = fst B''"
            using asm split(2,3) by argo+
          ultimately show "B' = x \<and> B'' = y"
            using prod.expand by blast
        qed
      qed
    qed
  } note unique_split=this


  have "estimate2 \<A> (P, L) xs \<le> estimate2 \<A> (P', L') xs'"
  proof-
    have sum_ys_ys'_eq:"(\<Sum>s\<leftarrow>ys. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s))) = (\<Sum>s\<leftarrow>ys'. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s)))"
      using mset_eq_sum_list_eq[OF ys_ys'_mset_eq, of "\<lambda>s. card (preds \<A> (fst s) (snd s)) * Discrete.log (card (snd s))"] .
    show ?thesis
      unfolding estimate2_def
      apply (simp add: split_xs(4) split_xs'(4))
      apply (simp add: sum_list_conc_distr[OF split_xs(1)] sum_list_conc_distr[OF split_xs'(1)])
      apply (simp add: sum_ys_ys'_eq)
      using unique_split (* maybe show the result by induction after showing that unique_split exactly describes zs'. *)
      sorry
  qed

  show ?thesis
    sorry (* we need to define estimate2 differently so that xs is not a parameter but inherent to the definition *)
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
\<comment>\<open>WARNING: incorrect definition of estimate1 (via sets, should be done with lists and permutations) plus too hard to prove\<close>
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