(*  Title:       Reachability abstract predicates
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

theory Accessible
imports Main
begin


subsection \<open> accessible\<close>

text \<open> Let's define the set of value that are accessible/reachable from
 a given value using a binary relation. \<close>
definition accessible where
  "accessible R ws \<equiv> R\<^sup>* `` ws"

lemma accessible_empty [simp] :
  "accessible R {} = {}" by (simp add: accessible_def)

lemma accessible_union :
  "accessible R (ws \<union> ws') = 
   accessible R ws \<union> accessible R ws'" 
unfolding accessible_def by (rule Image_Un)

lemma accessible_Union :
  "accessible R (\<Union> wss) = \<Union> (accessible R ` wss)" 
by (auto simp add: accessible_def)

lemma accessible_insert :
  "accessible R (insert x ws) = 
   {y. (x, y) \<in> R\<^sup>*} \<union> accessible R ws" 
by (auto simp add: accessible_def)

lemma accessible_eq_empty [simp] :
   "(accessible R ws = {}) \<longleftrightarrow> (ws = {})"
unfolding accessible_def by auto

lemma accessible_mono :
  "ws \<subseteq> ws' \<Longrightarrow> (accessible R ws \<subseteq> accessible R ws')"
unfolding accessible_def by auto

lemma accessible_subset_ws :
  "ws \<subseteq> accessible R ws"
by (auto simp add: subset_iff accessible_def)

lemma accessible_insert2 :
  "accessible R (insert x ws) = 
   insert x (accessible R (ws \<union> {y. (x, y) \<in> R}))"
apply (auto simp add: accessible_def Image_iff Bex_def)
  apply (metis converse_rtranclE)
apply (metis converse_rtrancl_into_rtrancl)
done

lemma accessible_subset_R_ws_gen : 
assumes ws_S: "ws \<subseteq> S"
    and R_S: "\<And>x y. x \<in> S \<and> (x, y) \<in> R \<Longrightarrow> y \<in> S"
shows "accessible R ws \<subseteq> S"
proof -
  have "\<And>x y. \<lbrakk>(x, y) \<in> R\<^sup>*; x \<in> S\<rbrakk> \<Longrightarrow> y \<in> S"
  proof -
    fix x y
    show "\<lbrakk>(x, y) \<in> R\<^sup>*; x \<in> S\<rbrakk> \<Longrightarrow> y \<in> S"
      apply (induct rule: converse_rtrancl_induct)
      apply simp
      apply (metis R_S)
    done
  qed
  thus ?thesis
    unfolding accessible_def
    using ws_S
    by auto
qed

lemma accessible_subset_R_ws: "accessible R ws \<subseteq> snd ` R \<union> ws"
unfolding accessible_def
by (auto simp add: image_iff Bex_def, metis rtranclE)

lemma accessible_finite___args_finite :
assumes fin_R: "finite R"
    and fin_ws: "finite ws"
shows "finite (accessible R ws)"
proof -
  have acc_subset: "accessible R ws \<subseteq> snd ` R \<union> ws" 
    by (simp add: accessible_subset_R_ws)
  
  have "finite (snd ` R \<union> ws)" 
    by (simp add: fin_ws fin_R)
  with acc_subset show ?thesis by (metis finite_subset) 
qed

lemma accessible_accessible_idempot :
   "(accessible R (accessible R ws)) = accessible R ws"
by (auto simp add: accessible_def Image_iff Bex_def,
    metis rtrancl_trans)

lemma accessible_subset_accessible :
   "accessible R ws1 \<subseteq> accessible R ws2 \<longleftrightarrow>
    ws1 \<subseteq> accessible R ws2"
unfolding accessible_def
by (auto simp add: accessible_def Image_iff Bex_def subset_iff,
    metis rtrancl_trans)

definition accessible_restrict where
  "accessible_restrict R rs ws \<equiv> 
   rs \<union> accessible (R - (rs \<times> UNIV)) ws"

lemma accessible_restrict_empty :
  "accessible_restrict R {} ws = accessible R ws"
  by (simp add: accessible_restrict_def)

lemma accessible_restrict_final [simp] :
  "accessible_restrict R rs {} = rs"
  by (simp add: accessible_restrict_def)

lemma accessible_restrict_insert_in :
  "x \<in> rs \<Longrightarrow> 
   accessible_restrict R rs (insert x ws) = 
   accessible_restrict R rs ws"
unfolding accessible_restrict_def
by (auto simp add: accessible_insert2)

lemma accessible_restrict_diff_rs :
  "accessible_restrict R rs ws = 
   accessible_restrict R rs (ws - rs)"
proof -
  { fix x y 
    have "\<lbrakk>(x, y) \<in> (R - rs \<times> UNIV)\<^sup>*;y \<notin> rs\<rbrakk> \<Longrightarrow> x \<notin> rs" 
    by (erule converse_rtranclE, simp_all)
  }
  thus ?thesis
    unfolding accessible_def accessible_restrict_def Image_def Bex_def
    by auto 
qed

lemma accessible_restrict_insert_nin :
  "x \<notin> rs \<Longrightarrow> 
   accessible_restrict R rs (insert x ws) = 
   accessible_restrict R (insert x rs) (ws \<union> {y. (x, y) \<in> R})"
proof -
  assume x_nin_rs: "x \<notin> rs" 
  obtain R_res where R_res_def: "R_res = (\<lambda>rs. (R - (rs \<times> UNIV)))" 
    by blast
   
  have "accessible (R_res (insert x rs)) (ws \<union> {y. (x, y) \<in> R}) =
        accessible (R_res rs) (ws \<union> {y. (x, y) \<in> R})"
        (is "?acc1 = ?acc2")
  proof (intro set_eqI iffI)
    fix e
    assume e_in_acc1: "e \<in> ?acc1"

    have "R_res (insert x rs) \<subseteq> R_res rs" unfolding R_res_def by force
    from rtrancl_mono[OF this] e_in_acc1 
      show "e \<in> ?acc2"
      unfolding accessible_def
      by auto
  next 
    fix e
    let ?ws' = "ws \<union> {y. (x, y) \<in> R}"

    have ind_part: "\<And>y. \<lbrakk>(y, e) \<in> (R_res rs)\<^sup>*; y \<in> ?ws'\<rbrakk> \<Longrightarrow>
                         \<exists>y'. y' \<in> ?ws' \<and> (y', e) \<in> (R_res (insert x rs))\<^sup>*"
    proof -
      fix y
      show "\<lbrakk>(y, e) \<in> (R_res rs)\<^sup>*; y \<in> ?ws'\<rbrakk> \<Longrightarrow>
             \<exists>y'. y' \<in> ?ws' \<and> (y', e) \<in> (R_res (insert x rs))\<^sup>*"
      proof (induct rule: rtrancl_induct)
        case base thus ?case by auto
      next
        case (step y2 z)
        note y2_z_in_R_res = step(2)
        note ind_hyp = step(3)[OF step(4)]

        show "\<exists>y'. y' \<in> ?ws' \<and> (y', z) \<in> (R_res (insert x rs))\<^sup>*"
        proof (cases "(y2, z) \<in> (R_res (insert x rs))")
          case True with ind_hyp show ?thesis by auto
        next
          case False
          hence "(x, z) \<in> R" using y2_z_in_R_res unfolding R_res_def
            by simp
          hence "z \<in> ?ws'" by simp
          thus ?thesis by auto
        qed
      qed
    qed

    assume e_in_acc2: "e \<in> ?acc2"
    with ind_part show "e \<in> ?acc1"
      by (auto simp add: accessible_def)
  qed

  with x_nin_rs show 
   "accessible_restrict R rs (insert x ws) = 
    accessible_restrict R (insert x rs) (ws \<union> {y. (x, y) \<in> R})"
    unfolding accessible_restrict_def R_res_def
    by (simp add: accessible_insert2)
qed


lemmas accessible_restrict_insert =
       accessible_restrict_insert_nin accessible_restrict_insert_in

lemma accessible_restrict_union :
  "accessible_restrict R rs (ws \<union> ws') = 
   (accessible_restrict R rs ws) \<union> (accessible_restrict R rs ws')" 
  unfolding accessible_restrict_def
  by (auto simp add: accessible_union)

lemma accessible_restrict_Union :
  "wss \<noteq> {} \<Longrightarrow>
   accessible_restrict R rs (\<Union> wss) = (\<Union>ws \<in> wss. (accessible_restrict R rs ws))" 
  unfolding accessible_restrict_def
  by (simp add: accessible_Union)

lemma accessible_restrict_subset_ws :
  "ws \<subseteq> accessible_restrict R rs ws"
unfolding accessible_restrict_def
using accessible_subset_ws [of ws]
by fast

subsection \<open> Define a new order \<close>

definition bounded_superset_rel where
  "bounded_superset_rel S \<equiv>
   {(x, y). (y \<subset> x \<and> x \<subseteq> S)}"

lemma wf_bounded_superset_rel [simp] :
fixes S :: "'a set"
assumes fin_S: "finite S"
shows "wf (bounded_superset_rel S)"
proof -
  have "bounded_superset_rel S \<subseteq> measure (\<lambda>s. card (S - s))"
  proof 
    fix xy :: "'a set \<times> 'a set"
    obtain x y where xy_eq: "xy = (x, y)" by (cases xy, blast)

    assume "xy \<in> bounded_superset_rel S"
    hence "y \<subset> x \<and> x \<subseteq> S" unfolding bounded_superset_rel_def xy_eq
      by simp
    hence "S - x \<subset> S - y" by auto

    hence "card (S - x) < card (S - y)"
      using psubset_card_mono finite_Diff fin_S
      by metis
    thus "xy \<in> measure (\<lambda>s. card (S - s))"
      using xy_eq
      by simp
  qed
  thus ?thesis
    using wf_measure wf_subset
    by metis
qed

end
