\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Introsort and its first Phase\<close>
theory Sorting_Quicksort_Scheme
imports Sorting_Setup Sorting_Partially_Sorted
begin


paragraph \<open>Summary\<close>
text \<open>This theory introduces the abstract quicksort-like first phase of the introsort algorithm.
  Also the abstract algorithm for introsort is introduced and proved correct.
    \<close>
  
paragraph \<open>Main Theorems/Definitions\<close>
text \<open>
\<^item> introsort_aux1: gives the abstract algorithm for the first phase
\<^item> introsort_aux_cost: specifies the cost of that algorithm
\<^item> introsort_aux1_correct': proves correctness
\<^item> introsort3: abstract introsort algorithm
\<^item> introsort3_correct: proves its correctness 
\<close>

subsection \<open>introsort_aux1\<close>


  abbreviation "is_threshold \<equiv> 16::nat"

  context weak_ordering begin

  definition "partition1_spec xs \<equiv> doN { 
    ASSERT (length xs \<ge> 4); 
    SPEC (\<lambda>(xs1,xs2). mset xs = mset xs1 + mset xs2 \<and> xs1\<noteq>[] \<and> xs2\<noteq>[] \<and> slice_LT (\<^bold>\<le>) xs1 xs2)
         (\<lambda>_. cost ''partition_c'' (enat (length xs)))
  }"

  definition introsort_aux1 :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where
    "introsort_aux1 \<mu> xs d \<equiv> RECT' (\<lambda>introsort_aux1 (xs,d). doN {
      ASSERT (xs \<noteq> []);
      lxs \<leftarrow> SPECT [length xs \<mapsto> cost ''list_length'' 1];
      if\<^sub>N SPECc2 ''lt'' (<) is_threshold (length xs) then doN {
        if\<^sub>N SPECc2 ''eq'' (=) d 0 then
          mop_call (SPEC (sort_spec (\<^bold><) xs) (\<lambda>_. cost ''sort_c'' (enat (\<mu> (length xs)))))
        else doN {
          (xs1,xs2)\<leftarrow>partition1_spec xs;
          d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
          xs1 \<leftarrow> introsort_aux1 (xs1,d');
          xs2 \<leftarrow> introsort_aux1 (xs2,d');
          SPECc2 ''list_append'' (@) xs1 xs2
        }
      }
      else
        RETURN xs 
    }) (xs,d)"


    lemma slice_strict_LT_imp_LE: "slice_LT (\<^bold><) xs ys \<Longrightarrow> slice_LT (le_by_lt (\<^bold><)) xs ys"  
      apply (erule slice_LT_mono)
      by (meson le_by_lt_def wo_less_asym)



definition introsort_aux_cost :: "_ \<Rightarrow> nat * nat \<Rightarrow> (char list, enat) acost"
  where "introsort_aux_cost \<mu> = (\<lambda>(lxs, d). lift_acost (
        ((d+1)*lxs) *m (cost ''if'' 2 + cost ''eq'' 1 + cost ''lt'' 1 + cost ''call'' 1
                    + cost ''list_length'' 1 + cost ''sub'' 1 + cost ''list_append'' 1) 
            + cost ''sort_c'' (\<mu> (lxs)) + cost ''partition_c'' (d*(lxs))
         )
        )"
 


lemma introsort_aux1_aux5: "b>0 \<Longrightarrow> (b - Suc 0) * A + (b - Suc 0) * B + (B + A) = b*(A+B)"
proof -
  assume "b>0"
  then obtain b' where b: "b=b'+1"  
    by (metis Groups.add_ac(2) Suc_eq_plus1_left Suc_pred)  
  then have "(b - Suc 0) * A + (b - Suc 0) * B + (B + A)
      = (b') * A + (b') * B + (B + A)" by simp
  also have "\<dots> = (b'+1) * (B+A)" by (auto simp: ring_distribs)
  also have "\<dots> = b * (B+A)" using b by simp
  finally show ?thesis by simp
qed

lemma lengths_sums_if_msets_do: "mset a = mset b + mset c \<Longrightarrow> length a = length b + length c"
    by (metis add.commute length_append less_or_eq_imp_le mset_append mset_eq_length)  

lemma 
  introsort_aux1_aux:
  "b>0 \<Longrightarrow> lxs+lys>(16::nat) \<Longrightarrow> Suc ((b - Suc 0) * lxs + (b - Suc 0) * lys) \<le> b * (lxs + lys)"
  by (smt One_nat_def Suc_leI add.commute add_le_cancel_left less_imp_le_nat
          introsort_aux1_aux5 neq0_conv not_numeral_le_zero plus_1_eq_Suc)
  
lemma 
  introsort_aux1_aux2:
  "b>0 \<Longrightarrow> lxs+lys>(16::nat) \<Longrightarrow> Suc ((b - Suc 0) * lys + (b - Suc 0) * lxs) \<le> b * (lxs + lys)"
  by (smt One_nat_def Suc_leI add.commute add_le_cancel_left less_imp_le_nat
          introsort_aux1_aux5 neq0_conv not_numeral_le_zero plus_1_eq_Suc)
  
lemma 
  introsort_aux1_aux4:
  assumes "b>0" "lxs+lys>(16::nat)"
  shows "Suc(Suc ((b - Suc 0) * lxs * 2 + (b - Suc 0) * lys * 2)) \<le> b * (lxs + lys) * 2"
proof - 
  have "Suc(Suc ((b - Suc 0) * lxs * 2 + (b - Suc 0) * lys * 2))
    = (Suc ((b - Suc 0) * lxs + (b - Suc 0) * lys)) + (Suc ((b - Suc 0) * lxs + (b - Suc 0) * lys))"
    by auto
  also have "\<dots> \<le> (b * (lxs + lys)) + (b * (lxs + lys))"
    apply(rule add_mono)
    subgoal apply(rule introsort_aux1_aux) using assms by auto
    subgoal apply(rule introsort_aux1_aux) using assms by auto
    done
  also have "\<dots> = b * (lxs + lys) * 2"
    by auto
  finally show ?thesis .
qed

subsubsection \<open>Correctness Theorem\<close>

definition "introsort_aux_cost' \<mu>  = (\<lambda>(xs,d). introsort_aux_cost \<mu> (length xs,d) )"

  lemma introsort_aux1_correct':
    assumes tf_suplinear: "\<And>a b. \<mu> a + \<mu> b \<le> \<mu> (a+b)"
      and "xs \<noteq> []"
    shows 
   "introsort_aux1 \<mu> xs d
     \<le> SPEC (\<lambda>xs'. mset xs' = mset xs \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs')
               (\<lambda>_. introsort_aux_cost' \<mu> (xs, d))"

    unfolding introsort_aux1_def partition1_spec_def sort_spec_def


    apply (rule RECT'_rule_arb[where V="measure (\<lambda>(xs,d). d+1)" 
                                  and pre="\<lambda>xss (xs',d). length xs' > 0 \<and> xss=xs'"])
       apply refine_mono
      apply (all \<open>(auto intro: sorted_wrt_imp_part_sorted part_sorted_wrt_init; fail)?\<close>)
    subgoal using  assms by simp

    unfolding SPEC_REST_emb'_conv SPECc2_alt
    subgoal premises prems for f xss x
      apply(rule gwp_specifies_I) 
      apply(refine_vcg \<open>-\<close> rules: prems(1)[THEN gwp_specifies_rev_I, THEN gwp_conseq_0])
      thm prems(1)[THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
      using  prems(2)
      subgoal unfolding emb'_def apply auto
        subgoal  by (simp add: sorted_wrt_imp_part_sorted)
        subgoal unfolding introsort_aux_cost_def introsort_aux_cost'_def
          apply (simp add: norm_cost lift_acost_propagate lift_acost_cost)
          apply sc_solve by (auto simp: one_enat_def)
        done
             apply simp apply simp
           apply simp apply simp
      subgoal
        apply (auto simp add: emb'_def handy_if_lemma)

        subgoal  using prems(2) by simp  
        subgoal 
          apply (rule part_sorted_concatI; assumption?) 
          apply (subst slice_LT_mset_eq1, assumption)
          apply (subst slice_LT_mset_eq2, assumption)
          using le_by_lt by blast
        subgoal premises p
          unfolding introsort_aux_cost_def introsort_aux_cost'_def
          using p(3,8)
          apply (simp add: norm_cost)
          apply sc_solve_debug apply safe apply(all \<open>((auto simp: sc_solve_debug_def),fail)?\<close>)
          subgoal (* append *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            using p(2)
            apply (simp add: one_enat_def  )
            apply(rule introsort_aux1_aux) by auto
          subgoal (* partition *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            apply auto apply(simp only: introsort_aux1_aux5) apply simp done
          subgoal (* sub *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            using p(2)
            apply (simp add: one_enat_def  )
            apply(rule introsort_aux1_aux) by auto
          subgoal (* ''sort_c'' *) unfolding sc_solve_debug_def
            apply (simp add: one_enat_def)
            apply(drule lengths_sums_if_msets_do) apply simp apply(subst add.commute)
            by(rule tf_suplinear) 
          subgoal  (* if *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            using p(2)
            apply (simp add: one_enat_def) 
            apply(rule introsort_aux1_aux4) by auto
          subgoal  (* list_length *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            using p(2)
            apply (simp add: one_enat_def  )
            apply(rule introsort_aux1_aux2) by auto
          subgoal (* eq *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            using p(2)
            apply (simp add: one_enat_def  )
            apply(rule introsort_aux1_aux) by auto
          subgoal (* call *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            using p(2)
            apply (simp add: one_enat_def  )
            apply(rule introsort_aux1_aux2) by auto
          subgoal  (* lt *)
            unfolding sc_solve_debug_def
            apply(drule lengths_sums_if_msets_do)
            using p(2)
            apply (simp add: one_enat_def  )
            apply(rule introsort_aux1_aux) by auto
          done
        done
      subgoal by auto
      subgoal
        using prems(2) apply (auto simp add: emb'_def handy_if_lemma)
        subgoal by (simp add: part_sorted_wrt_init)
        subgoal
          unfolding introsort_aux_cost_def introsort_aux_cost'_def
          apply (simp add: norm_cost)
          apply sc_solve apply (auto simp: one_enat_def)
          subgoal
            by (simp add: Suc_leI)
          subgoal  
            by (simp add: Suc_leI)
          done
        done
      subgoal using prems by simp
      done
    done

  lemma introsort_aux1_correct:
    assumes tf_suplinear: "\<And>a b. \<mu> a + \<mu> b \<le> \<mu> (a+b)"
      and "xs \<noteq> []" "lxs = length xs"
    shows 
      "introsort_aux1 \<mu> xs d
         \<le> SPEC (\<lambda>xs'. mset xs' = mset xs \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs')
                 (\<lambda>_. introsort_aux_cost \<mu> (lxs, d))"
    unfolding assms(3)
    by (rule  introsort_aux1_correct'[where \<mu>=\<mu>, OF assms(1,2), unfolded introsort_aux_cost'_def, simplified])


subsection \<open>introsort_aux2\<close>
      
    definition "partition2_spec xs \<equiv> doN { 
      ASSERT (length xs \<ge> 4); 
      SPEC (\<lambda>(xs',i). mset xs' = mset xs \<and> 0<i \<and> i<length xs \<and> slice_LT (\<^bold>\<le>) (take i xs') (drop i xs'))
             (\<lambda>_. cost ''partition_c'' (enat (length xs)))
    }"

    lemma partition2_spec_refine:
      assumes "(xs,xs')\<in>Id" 
      shows "partition2_spec xs
             \<le>  \<Down>(br (\<lambda>(xs,i). (take i xs, drop i xs)) (\<lambda>(xs,i). 0<i \<and> i<length xs))
                     (timerefine TId (partition1_spec xs'))"
      using assms
      unfolding partition1_spec_def partition2_spec_def
      apply (intro refine0 SPEC_both_refine)
       apply (auto dest: mset_eq_length simp: in_br_conv simp flip: mset_append)
      subgoal
        using mset_eq_length by fastforce
      subgoal
        using mset_eq_length by force
      done
      
  definition introsort_aux2 :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where
    "introsort_aux2 \<mu> xs d \<equiv> RECT' (\<lambda>introsort_aux (xs,d). doN {
      lxs \<leftarrow> SPECT [length xs \<mapsto> cost ''list_length'' 1];
      if\<^sub>N SPECc2 ''lt'' (<) is_threshold lxs then
        if\<^sub>N SPECc2 ''eq'' (=) d 0 then
          mop_call (SPEC (sort_spec (\<^bold><) xs) (\<lambda>_. cost ''sort_c'' (enat (\<mu> (length xs)))))
        else doN {
          (xs,m)\<leftarrow>partition2_spec xs;
          ASSERT (m\<le>length xs);
          d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
          xs1 \<leftarrow> introsort_aux (take m xs,d');
          xs2 \<leftarrow> introsort_aux (drop m xs,d');
          SPECc2 ''list_append'' (@) xs1 xs2
        }      
      else
        RETURN xs 
    }) (xs,d)"


subsubsection \<open>Refinement Theorem\<close>

    lemma introsort_aux2_refine: "introsort_aux2 \<mu> xs d \<le>\<Down>Id (timerefine TId (introsort_aux1 \<mu> xs d))"  
      unfolding introsort_aux2_def introsort_aux1_def
      apply (refine_rcg mop_call_refine partition2_spec_refine SPEC_both_refine MIf_refine SPECc2_refine RECT'_refine_t bindT_refine_conc_time_my_inres)
      apply refine_dref_type
      apply refine_mono
      apply (auto simp: in_br_conv cost_n_leq_TId_n)
      done
      
subsection \<open>introsort_aux3\<close>
    
    definition "partition3_spec xs l h \<equiv> doN { 
      ASSERT (h-l\<ge>4 \<and> h\<le>length xs); 
      SPEC (\<lambda>(xs',i). slice_eq_mset l h xs' xs \<and> l<i \<and> i<h \<and> slice_LT (\<^bold>\<le>) (slice l i xs') (slice i h xs')) (\<lambda>_. cost ''partition_c'' (enat (h-l)))
    }"
 
abbreviation "TR_i_aux \<equiv> (TId(''list_append'':=0,''list_length'':=cost ''sub'' 1))"

    lemma partition3_spec_refine: "(xsi,xs) \<in> slice_rel xs\<^sub>0 l h \<Longrightarrow> partition3_spec xsi l h  \<le>\<Down>(slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l) (timerefine TR_i_aux (partition2_spec xs))"
      unfolding partition3_spec_def partition2_spec_def
      apply (intro refine0 SPEC_both_refine)
       apply (auto simp: slice_rel_def in_br_conv) [2]
      subgoal for xs'i ii
        apply (rule exI[where x="slice l h xs'i"])
        apply (rule conjI)
        subgoal by (auto simp: slice_eq_mset_def)
        apply (simp add: idx_shift_rel_alt)
        by (auto simp: slice_eq_mset_def take_slice drop_slice intro!: cost_mono)
      done

      
    lemma partition3_spec_refine': "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h\<rbrakk> 
      \<Longrightarrow> partition3_spec xsi l h  \<le>\<Down>(slice_rel xsi' l' h' \<times>\<^sub>r idx_shift_rel l') (timerefine TR_i_aux (partition2_spec xs))"
      unfolding partition3_spec_def partition2_spec_def
      apply (intro refine0 SPEC_both_refine )
      apply (auto simp: slicep_rel_def in_br_conv) [2] 
      subgoal for xs'i ii
        apply (rule exI[where x="slice l h xs'i"])
        apply (rule conjI)
        subgoal by (auto simp: slice_eq_mset_def)
        apply (simp add: idx_shift_rel_alt)
        apply (auto simp: slice_eq_mset_def take_slice drop_slice intro!: cost_mono)
        by (smt less_or_eq_imp_le less_trans slice_eq_mset_alt slice_eq_mset_def slice_in_slice_rel slice_rel_alt)
      done

    definition introsort_aux3 :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "introsort_aux3 \<mu> xs l h d 
    \<equiv>  RECT' (\<lambda>introsort_aux (xs,l,h,d). doN {
        ASSERT (l\<le>h);
        lxs \<leftarrow> SPECc2 ''sub'' (-) h l;
        if\<^sub>N SPECc2 ''lt'' (<) is_threshold lxs then doN {
          if\<^sub>N SPECc2 ''eq'' (=) d 0 then
            mop_call (slice_sort_specT (cost ''sort_c'' (enat (\<mu> lxs))) (\<^bold><) xs l h)
          else doN {
            (xs,m)\<leftarrow>partition3_spec xs l h;
            d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
            xs \<leftarrow> introsort_aux (xs,l,m,d');
            xs \<leftarrow> introsort_aux (xs,m,h,d');
            RETURN xs
          }
        }
        else
          RETURN xs 
      }) (xs,l,h,d)"


definition "introsort_aux3d th xs l h \<equiv>
  doN {
    d \<leftarrow> SPECT [Discrete.log (h-l) * 2 \<mapsto> cost ''depth'' 1];
    introsort_aux3 th xs l h d
  }"


corollary my_slice_sort_spec_refine_sort':
  fixes T :: "nat \<Rightarrow> ecost"
  assumes "\<And>x. T x \<le> timerefineA (TId(''list_append'' := 0, ''list_length'' := cost ''sub'' 1)) (T x)"
  shows 
 "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h; xa=length xs\<rbrakk>
\<Longrightarrow> slice_sort_specT (T xa) lt xsi l h \<le>\<Down>(slice_rel xsi' l' h') (timerefine TR_i_aux (SPEC (sort_spec lt xs) (\<lambda>_. T (length xs))))"
  unfolding slice_sort_specT_def sort_spec_def
  apply(intro refine0 SPEC_both_refine)
  subgoal by (auto simp: slicep_rel_def)
  subgoal for x apply (auto simp: slice_rel_alt)
    apply(rule exI[where x="slice l h x"]) apply (auto simp: eq_outside_range_def slicep_rel_def)
    using assms by blast
  done  


subsubsection \<open>Refinement Theorem\<close>

lemma introsort_aux3_refine: "(xsi,xs)\<in>slicep_rel l h
       \<Longrightarrow> introsort_aux3 \<mu> xsi l h d \<le> \<Down>(slice_rel xsi l h) (timerefine TR_i_aux (introsort_aux2 \<mu> xs d))"  
      unfolding introsort_aux3_def introsort_aux2_def
      
      supply recref = RECT'_dep_refine[where 
          R="\<lambda>_. {((xsi::'a list, l, h, di::nat), (xs, d)). (xsi, xs) \<in> slicep_rel l h \<and> di=d}" and
          S="\<lambda>_ (xsi::'a list, l, h, di::nat). slice_rel xsi l h" and
          arb\<^sub>0 = "()"
          ]
      thm recref
      unfolding SPECc2_def
      apply (refine_rcg bindT_refine_conc_time_my_inres MIf_refine mop_call_refine
        recref 
        partition3_spec_refine'
        my_slice_sort_spec_refine_sort'
        ; (intro refl)?; (intro wfR''_TId wfR''_upd sp_TId struct_preserving_upd_I )?
        )
            apply refine_mono 

      apply(all \<open>(simp add: timerefineA_update_cost timerefineA_update_apply_same_cost;fail)?\<close>)

     focus  apply (auto simp: slicep_rel_def)    solved
     focus apply refine_dref_type apply (auto simp: slicep_rel_def)    solved
     focus apply refine_dref_type apply (auto simp: slicep_rel_def)   solved
     focus apply simp   solved
     focus apply refine_dref_type apply simp   solved
     focus   apply simp   solved
     focus apply simp solved
     focus apply simp apply (rule IdI) solved
     focus (* first recursive call *)
      apply(rprems)
      apply(auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_take)
      solved
     focus (* second recursive call *) 
      apply(rprems)
      apply(auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_eq_outside_range slicep_rel_drop)
      solved
     focus
      unfolding RETURNT_alt
      apply(rule SPECT_refine_t) 
      subgoal
        apply (clarsimp simp: slice_rel_alt idx_shift_rel_def)
        apply (rule conjI)
        subgoal
          apply (rule slicep_rel_append)
          apply (subst slicep_rel_eq_outside_range; assumption?) 
          by auto 
        subgoal 
          apply (drule (1) eq_outside_range_gen_trans[OF _ _ refl refl])
          apply (erule (1) eq_outside_range_gen_trans)
          apply (auto simp: max_def algebra_simps slicep_rel_def split: if_splits)
          done 
        done
      apply (simp add: timerefineA_update_apply_same_cost)
      solved
     focus
      subgoal by (auto simp: slicep_rel_def)
      solved
      done


    definition "slice_part_sorted_spec xsi l h \<equiv> doN { ASSERT (l<h \<and> h\<le>length xsi); SPEC (\<lambda>xsi'. 
        eq_outside_range xsi' xsi l h 
      \<and> mset (slice l h xsi') = mset (slice l h xsi) 
      \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xsi')) (\<lambda>_. cost ''slice_part_sorted'' 1)}"


  definition "slice_part_sorted_specT T xsi l h \<equiv> doN { ASSERT (l<h \<and> h\<le>length xsi); SPEC (\<lambda>xsi'. 
      eq_outside_range xsi' xsi l h 
    \<and> mset (slice l h xsi') = mset (slice l h xsi) 
    \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xsi')) (\<lambda>_. T)}"
    
lemma spss_eq1: "slice_part_sorted_spec xs l h = slice_part_sorted_specT (cost ''slice_part_sorted'' 1) xs l h"
  unfolding slice_part_sorted_specT_def slice_part_sorted_spec_def by auto

lemma spss_eq2: "timerefine R (slice_part_sorted_specT T xs l h) = slice_part_sorted_specT (timerefineA R T) xs l h"
  unfolding slice_part_sorted_specT_def 
  by(cases "l < h \<and> h \<le> length xs", auto simp add: SPEC_timerefine_conv)



definition introsort_aux_cost2 :: "_ \<Rightarrow> 'a list * nat \<Rightarrow> (char list, enat) acost"
  where "introsort_aux_cost2 \<mu> = (\<lambda>(xs, d). lift_acost (
        cost ''if'' (2^(d+1)-1) + cost ''eq'' (2^(d+1)-1) + cost ''if'' (2^(d+1)-1)
         + cost ''lt'' (2^(d+1)-1) + cost ''call'' ((2^(d+1)-1)) 
        + cost ''sub'' (2^(d+1)-1)  
        +   cost ''sort_c'' (\<mu> (length xs)) + cost ''partition_c'' (d*(length xs))
         )
        )"

lemma wfR''TR_i_aux[simp]: "wfR'' TR_i_aux"
  by (auto intro!: wfR''_upd)




subsubsection \<open>Correctness Theorem\<close>


lemma introsort_aux3_correct:
  assumes tf_sums: "\<And>a b. \<mu> a + \<mu> b \<le> \<mu> (a+b)"   
  shows 
    "introsort_aux3 \<mu> xsi l h d \<le> \<Down>Id (timerefine TR_i_aux (timerefine (TId(''slice_part_sorted'':=introsort_aux_cost \<mu> (h-l,d))) (slice_part_sorted_spec xsi l h)))"
  apply(subst timerefine_iter2)
  subgoal by simp
  subgoal by (auto intro!: wfR''_upd)
  unfolding slice_part_sorted_spec_def
  apply(rule refine0)
  apply(rule order.trans)
   apply(rule introsort_aux3_refine[of xsi "slice l h xsi" l h \<mu> d])
  subgoal by (auto simp: slicep_rel_def)
  apply(rule order.trans)
  apply(rule nrest_Rel_mono)
  apply(rule timerefine_mono2)
  subgoal by (auto intro!: wfR''_upd)
  apply(rule introsort_aux2_refine)
  apply(rule order.trans)
  apply(rule nrest_Rel_mono)
  apply(rule timerefine_mono2)
  subgoal by (auto intro!: wfR''_upd)
  apply(rule order.trans)
  apply(rule nrest_Rel_mono)
  apply(rule timerefine_mono2)
  subgoal by (auto intro!: wfR''_upd)
    apply(rule introsort_aux1_correct)
  subgoal using tf_sums by blast
  subgoal by (metis Sorting_Misc.slice_len length_greater_0_conv zero_less_diff)
   apply (simp add: timerefine_id)
   apply(rule order.refl)
  apply(simp add: SPEC_timerefine_conv introsort_aux_cost_def timerefineA_propagate lift_acost_propagate lift_acost_cost
          timerefineA_update_apply_same_cost' costmult_cost pp_fun_upd )
  unfolding slice_rel_def
  apply(subst build_rel_SPEC_conv) apply simp
  apply(rule SPEC_leq_SPEC_I_strong)
  subgoal apply auto   
    by (simp add: eq_outside_range_def)
  subgoal by(sc_solve) 
  done


lemma TR_sps_important:
  assumes "TR ''slice_part_sorted'' = timerefineA TR_i_aux (introsort_aux_cost \<mu> (h-l,d))"
  shows "(timerefine TR_i_aux (timerefine (TId(''slice_part_sorted'':=introsort_aux_cost \<mu> (h-l,d))) (slice_part_sorted_spec xsi l h)))
    = timerefine TR (slice_part_sorted_spec xsi l h)"
  unfolding slice_part_sorted_spec_def 
  apply(cases "l < h \<and> h \<le> length xsi") apply auto
  apply(simp only: SPEC_timerefine_conv)
  apply(rule SPEC_cong, simp)
  apply(rule ext)
  apply(simp add: norm_cost)
  apply(subst assms(1))
  apply simp
  done


lemma introsort_aux3_correct_flexible:
  assumes  tf_sums: "\<And>a b. \<mu> a + \<mu> b \<le> \<mu> (a+b)"
   and  "TR ''slice_part_sorted'' = timerefineA TR_i_aux (introsort_aux_cost \<mu> (h-l,d))"
  shows 
    "introsort_aux3 \<mu> xsi l h d \<le> \<Down>Id (timerefine TR (slice_part_sorted_spec xsi l h))"
  apply(subst TR_sps_important[symmetric, where TR=TR, OF assms(2)])
  apply(rule introsort_aux3_correct) by fact+

           
subsection \<open>introsort3\<close>
    
    definition "final_sort_spec xs l h \<equiv> doN {
      ASSERT (h-l>1 \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xs));
      slice_sort_spec (\<^bold><) xs l h
      }"
    
    definition "introsort3 xs l h \<equiv> doN {
      ASSERT(l\<le>h);
      hml \<leftarrow> SPECc2 ''sub'' (-) h l;
      if\<^sub>N SPECc2 ''lt'' (<) 1 hml then doN {
        xs \<leftarrow> slice_part_sorted_spec xs l h;
        xs \<leftarrow> final_sort_spec xs l h;
        RETURN xs
      } else RETURN xs
    }"  

definition "introsort3_cost =  cost ''sub'' 1 + cost ''lt'' 1 + cost ''if'' 1
                               + cost ''slice_sort'' 1 +  cost ''slice_part_sorted'' (1::enat)"
    
    
subsubsection \<open>Correctness Theorem\<close>

lemma introsort3_correct: "introsort3 xs l h \<le> \<Down>Id (timerefine (TId(''slice_sort'':=introsort3_cost)) (slice_sort_spec (\<^bold><) xs l h))"
  apply (cases "l\<le>h \<and> h\<le>length xs")
  subgoal
    apply (cases "1<h-l")
    subgoal
      unfolding introsort3_def slice_part_sorted_spec_def final_sort_spec_def slice_sort_spec_alt
      apply(auto intro: refine0 simp: SPEC_timerefine_conv)
      unfolding SPEC_REST_emb'_conv SPECc2_def
      apply(rule gwp_specifies_I) 
      apply(refine_vcg \<open>-\<close> rules: )
      subgoal unfolding emb'_def apply(rule If_le_Some_rule2)
         apply (auto simp: introsort3_cost_def timerefineA_update_apply_same_cost' add.commute)
        subgoal apply sc_solve  apply safe by auto  
        by (auto elim: eq_outside_range_gen_trans[of _ _ l h _ l h l h, simplified])
      subgoal using eq_outside_range_list_rel_on_conv by blast  
      subgoal by blast
      subgoal by linarith
      subgoal by(auto simp: emb'_def)
      done
    subgoal
      unfolding introsort3_def slice_sort_spec_alt slice_part_sorted_spec_def final_sort_spec_def
      apply(auto intro: refine0 simp: SPEC_timerefine_conv)
      unfolding SPEC_REST_emb'_conv SPECc2_def
      apply(rule gwp_specifies_I) 
      apply(refine_vcg \<open>-\<close> rules: )
      apply (auto simp add: emb'_def eq_outside_range_triv sorted_wrt01 le_fun_def ecost_nneg) 
      apply (auto simp: introsort3_cost_def timerefineA_update_apply_same_cost' add.commute)
      apply sc_solve apply auto    
      done
    done
  subgoal            
    unfolding slice_sort_spec_alt
    by(auto intro: refine0)
  done 


  end  




end
