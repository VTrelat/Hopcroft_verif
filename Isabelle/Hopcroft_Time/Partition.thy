(*  Title:       Partitions 
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

section \<open> Partition \<close>

theory Partition
imports Main 
begin

definition is_partition :: "'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where
  "is_partition Q P \<longleftrightarrow>
   (\<Union>P = Q) \<and> ({} \<notin> P) \<and> (\<forall>p1 p2. p1 \<in> P \<and> p2 \<in> P \<and> p1 \<noteq> p2 \<longrightarrow> p1 \<inter> p2 = {})"

lemma is_partitionI [intro!]:
  "\<lbrakk>\<And>q. q \<in> Q \<Longrightarrow> q \<in> \<Union>P;
    \<And>p. p \<in> P \<Longrightarrow> p \<subseteq> Q;
    \<And>p. p \<in> P \<Longrightarrow> p \<noteq> {};
    \<And>q p1 p2. \<lbrakk>p1 \<in> P; p2 \<in> P; q \<in> p1; q \<in> p2\<rbrakk> \<Longrightarrow> p1 = p2
   \<rbrakk> \<Longrightarrow> is_partition Q P"
unfolding is_partition_def
by auto metis+

lemma is_partition_Nil_Q :
  "is_partition {} P \<longleftrightarrow> P = {}"
unfolding is_partition_def
by auto

lemma is_partition_Nil [simp] :
  "is_partition Q {} \<longleftrightarrow> Q = {}"
unfolding is_partition_def
by auto

lemma is_partition_Insert :
assumes p_nin: "p \<notin> P"
shows "is_partition Q (insert p P) \<longleftrightarrow> 
       (p \<noteq> {}) \<and> (p \<subseteq> Q) \<and> is_partition (Q - p) P"
proof (cases "p \<noteq> {} \<and> ({} \<notin> P) \<and> p \<subseteq> Q")
  case False thus ?thesis
    unfolding is_partition_def
    by (rule_tac iffI, auto)
next
  case True 
  note p_not_Emp = conjunct1 [OF True]
  note P_not_Emp = conjunct1 [OF conjunct2 [OF True]]
  note p_subset = conjunct2 [OF conjunct2 [OF True]]

  have "(p \<union> \<Union>P = Q \<and>
        (\<forall>p1 p2. (p1 = p \<or> p1 \<in> P) \<and> (p2 = p \<or> p2 \<in> P) \<and> p1 \<noteq> p2 \<longrightarrow> p1 \<inter> p2 = {})) =
        (\<Union>P = Q - p \<and> (\<forall>p1 p2. p1 \<in> P \<and> p2 \<in> P \<and> p1 \<noteq> p2 \<longrightarrow> p1 \<inter> p2 = {}))"
     (is "?l1 \<and> ?l2 \<longleftrightarrow> ?r1 \<and> ?r2")
  proof (intro iffI conjI)
    assume r12: "?r1 \<and> ?r2"
    note r1 = conjunct1 [OF r12]
    note r2 = conjunct2 [OF r12]

    from r1 show "?l1" using p_subset by auto

    have p_disjoint : "\<And>p'. p' \<in> P \<Longrightarrow> p \<inter> p' = {}"
    proof -
      fix p'
      assume "p' \<in> P" 
      with r1 have "p' \<subseteq> Q - p"
        by auto
      thus "p \<inter> p' = {}" by auto
    qed

    with r2 show ?l2 by blast
  next
    assume l12: "?l1 \<and> ?l2"
    note l1 = conjunct1 [OF l12]
    note l2 = conjunct2 [OF l12]

    from l2 show ?r2 by blast

    from l2 p_nin 
    have p_disjoint : "\<And>p'. p' \<in> P \<Longrightarrow> p \<inter> p' = {}" by blast
    with l1 show ?r1 by auto
  qed
  with p_not_Emp P_not_Emp p_subset show ?thesis  
    unfolding is_partition_def
    by simp
qed

lemma is_partition_in_subset :
assumes is_part: "is_partition Q P"
    and p_in: "p \<in> P"
shows "p \<subseteq> Q"
using assms 
unfolding is_partition_def
by auto

lemma is_partition_memb_finite :
assumes fin_Q: "finite Q"
    and is_part: "is_partition Q P"
    and p_in: "p \<in> P"
shows "finite p"
by (metis finite_subset[OF _ fin_Q] is_partition_in_subset[OF is_part p_in])

lemma is_partition_distinct_subset :
assumes is_part: "is_partition Q P"
    and p_in: "p \<in> P"
    and p'_sub: "p' \<subseteq> p"
shows "p' \<notin> P - {p}"
proof (rule notI)
  assume p'_in: "p' \<in> P - {p}"
  
  with is_part have "p' \<noteq> {}"
    unfolding is_partition_def by auto
  hence "p' \<inter> p \<noteq> {}" using p'_sub by auto

  with is_part show False
    using p'_in p_in
    unfolding is_partition_def
    by blast
qed

lemma is_partition_finite :
assumes fin_Q: "finite Q"
    and is_part: "is_partition Q P"
shows "finite P"
proof -
  from is_part have "P \<subseteq> Pow Q"
    unfolding is_partition_def by auto
  moreover
  from fin_Q have "finite (Pow Q)" by blast
  ultimately show "finite P"
    by (metis finite_subset)
qed

lemma is_partition_card :
assumes fin_Q: "finite Q"
    and is_part: "is_partition Q P"
shows "card Q = sum card P"
proof -
  have fin_P: "finite P"
    using is_partition_finite [OF fin_Q is_part] 
    .

  have "finite P \<Longrightarrow> finite Q \<Longrightarrow> is_partition Q P \<Longrightarrow> card Q = sum card P"
  proof (induct arbitrary: Q rule: finite_induct)
    case empty thus ?case by simp
  next
    case (insert p P Q)
    note fin_P = insert(1)
    note p_nin_P = insert(2)
    note ind_hyp = insert(3)
    note fin_Q = insert(4)
    note is_part_pP = insert(5)

    from is_part_pP p_nin_P have is_part_P: "is_partition (Q - p) P"
      and p_neq_Nil: "p \<noteq> {}" and p_subset: "p \<subseteq> Q"  
      by (simp_all add: is_partition_Insert)

    from p_subset fin_Q have fin_p: "finite p" by (metis finite_subset)
    from fin_Q have fin_Q_p: "finite (Q - p)" by simp
    from p_subset have card_p: "card p \<le> card Q"
      using card_mono [OF fin_Q] by simp

    show ?case
      using sum.insert [OF fin_P p_nin_P, of card]
            card_Diff_subset [OF fin_p p_subset]
            ind_hyp[OF fin_Q_p is_part_P, symmetric]
            card_p
      by simp
  qed
  with fin_Q fin_P is_part
  show ?thesis by simp
qed

lemma is_partition_card_P :
assumes fin_Q: "finite Q"
    and is_part: "is_partition Q P"
shows "card P \<le> card Q"
proof -
  from is_partition_card [OF fin_Q is_part]
  have "card Q = sum card P" .
  moreover  
  have "sum (\<lambda>p. 1) P \<le> sum card P"
  proof (rule sum_mono)
    fix p
    assume "p \<in> P"
    with is_part have p_neq_Nil: "p \<noteq> {}" and p_sub: "p \<subseteq> Q"
      unfolding is_partition_def
      by auto
    from p_sub fin_Q have "finite p" by (metis finite_subset)
    with p_neq_Nil have "card p \<noteq> 0"
      by (simp add: card_eq_0_iff)
    thus "1 \<le> card p" by auto
  qed
  moreover 
  have "sum (\<lambda>p. 1) P = card P"
    by (metis card_eq_sum)  
  ultimately show ?thesis by simp
qed


lemma is_partition_find :
assumes is_part: "is_partition Q P"
    and q_in_Q: "q \<in> Q"
shows "\<exists>!p. p \<in> P \<and> q \<in> p"
using assms
unfolding is_partition_def
by auto

lemma is_partition_refine :
assumes fin_Q:         "finite Q"
    and p_nin:         "p \<notin> P"
    and is_part:       "is_partition Q (insert p P)"
    and p1_p2_neq_emp: "p1 \<noteq> {}" "p2 \<noteq> {}"
    and p1_p2_disj: "p1 \<inter> p2 = {}"
    and p1_p2_union: "p = p1 \<union> p2"
shows "is_partition Q (insert p1 (insert p2 P)) \<and>
       card (insert p1 (insert p2 P)) = Suc (card (insert p P))"
proof 
  from p1_p2_neq_emp p1_p2_disj 
  have p1_neq_p2: "p1 \<noteq> p2" by auto

  have q_disj: "\<And>p'. p' \<subseteq> p \<Longrightarrow> p' \<notin> P"
  proof (rule notI)
    fix p'
    assume p'_sub: "p' \<subseteq> p"
    assume p'_in: "p' \<in> P"

    from is_part p'_in p_nin have "p' \<inter> p = {} \<and> p' \<noteq> {}"
      unfolding is_partition_def by blast
    with p'_sub show "False" by auto
  qed
  hence p1_nin: "p1 \<notin> insert p2 P" and
        p2_nin: "p2 \<notin> P"  
    unfolding p1_p2_union using p1_neq_p2 by auto

  have "Q - p = Q - p1 - p2"
    unfolding p1_p2_union by auto
  with is_part p1_p2_disj
  show "is_partition Q (insert p1 (insert p2 P))"
    using p_nin p1_nin p2_nin
    apply (simp add: is_partition_Insert p1_p2_neq_emp)
    apply (simp add: p1_p2_union)
    apply auto
  done

  have "finite P" using is_partition_finite[OF fin_Q is_part] by simp
  thus "card (insert p1 (insert p2 P)) = Suc (card (insert p P))"
    using p_nin p2_nin p1_nin
    by (simp add: card_insert_if)
qed


subsection \<open> Partitions and Equivalence Relations \<close>

lemma quotient_of_equiv_relation_is_partition :
assumes eq_r: "equiv Q r"
shows "is_partition Q (Q//r)"
proof -
  note Q_eq = Union_quotient[OF eq_r]
  note quot_disj = quotient_disj [OF eq_r]

  from eq_r have "\<And>q. q \<in> Q \<Longrightarrow> (q, q) \<in> r"
    unfolding equiv_def refl_on_def by simp
  hence emp_nin: "{} \<notin> Q // r"
    by (simp add: quotient_def Image_def) blast

  from Q_eq quot_disj emp_nin
  show ?thesis by blast
qed

definition relation_of_partition where
  "relation_of_partition P = {(q1, q2). \<exists>Q \<in> P. q1 \<in> Q \<and> q2 \<in> Q}"

lemma relation_of_partition_is_equiv :
assumes part_P: "is_partition Q P"
shows "equiv Q (relation_of_partition P)"
using is_partition_in_subset[OF part_P] is_partition_find[OF part_P]
unfolding equiv_def relation_of_partition_def refl_on_def sym_def trans_def
by (auto simp add: subset_iff Ball_def Bex_def) metis+

definition partition_less_eq where 
"partition_less_eq P1 P2 \<longleftrightarrow> relation_of_partition P1 \<subseteq> relation_of_partition P2"

lemma relation_of_partition_inverse :
assumes part_P: "is_partition Q P"
shows "Q // (relation_of_partition P) = P"
  (is "?ls = ?rs")
proof 
  {
    fix q
    assume q_in: "q \<in> Q" 
    from is_partition_find[OF part_P q_in]
    obtain p where p_props: "p \<in> P" "q \<in> p" "\<And>p'. \<lbrakk>p' \<in> P; q \<in> p'\<rbrakk> \<Longrightarrow> p' = p" by auto

    have "{q2. \<exists>Q\<in>P. q \<in> Q \<and> q2 \<in> Q} = p" 
      apply (intro set_eqI)
      apply (simp add: Bex_def)
      apply (metis p_props)
    done
    with p_props(1)
    have "{q2. \<exists>Q\<in>P. q \<in> Q \<and> q2 \<in> Q} \<in> P" by simp 
  }
  thus "?ls \<subseteq> ?rs"
    unfolding relation_of_partition_def quotient_def
    by auto
next
  {
    fix p
    assume p_in: "p \<in> P" 
    from p_in part_P have "p \<noteq> {}" unfolding is_partition_def by blast
    then obtain q where q_in_p: "q \<in> p" by auto 

    with is_partition_in_subset[OF part_P p_in] have q_in_Q: "q \<in> Q" by blast

    from is_partition_find[OF part_P q_in_Q] p_in q_in_p
    have p_dist: "\<And>p'. \<lbrakk>p' \<in> P; q \<in> p'\<rbrakk> \<Longrightarrow> p' = p" by auto

    have "{q2. \<exists>Q\<in>P. q \<in> Q \<and> q2 \<in> Q} = p" 
      apply (intro set_eqI)
      apply (simp add: Bex_def)
      apply (metis p_dist p_in q_in_p)
    done
    hence "\<exists>q\<in>Q. p = {q2. \<exists>Q\<in>P. q \<in> Q \<and> q2 \<in> Q}" 
      unfolding Bex_def
      apply (rule_tac exI [where x = q])
      apply (simp add: q_in_Q)
    done
  }
  thus "?rs \<subseteq> ?ls"
    unfolding relation_of_partition_def quotient_def
    by auto
qed

lemma quotient_inverse :
assumes eq_r: "equiv Q r"
shows "(relation_of_partition (Q // r)) = r"
  (is "?ls = ?rs")
using eq_r
unfolding relation_of_partition_def quotient_def 
apply (rule_tac set_eqI)
apply auto
apply (metis equiv_def sym_def trans_def)
apply (simp add: equiv_def refl_on_def subset_iff sym_def)
apply metis
done

end