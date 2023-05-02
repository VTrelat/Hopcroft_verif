\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Introsort (roughly libstdc++ version)\<close>
theory Sorting_Introsort
imports 
  Sorting_Final_insertion_Sort Sorting_Heapsort Sorting_Log2
  Sorting_Quicksort_Partition
  "../../lib/More_Asymptotics"
begin

context weak_ordering begin
paragraph \<open>Summary\<close>
text \<open>This theory refines @{term introsort_aux3} and @{term introsort3} down to LLVM code.
  It uses @{term heapsort2} and @{term partition_pivot} to implement the first phase of
    introsort in introsort_aux.
  Furthermore it uses @{term final_insertion_sort2} to implement the second phase.
  Finally LLVM code is synthesize with the Sepref tool.\<close>

paragraph \<open>Main Theorems/Definitions\<close>
text \<open>
\<^item> introsort_aux4 introsort4: refinements of abstract algorithms already using heapsort2 and
    partition_pivot
\<^item> upperbound_heapsort_cost: theorem upperbounding heapsort's cost, and exchanging between 
    algorithm specific ''slice_sort'' coin and operation specific ''sort_c'' coin
\<^item> heapsort_correct'': the correctness theorem for heapsort to be used during refinement of
    introsort_aux4
\<^item> introsort5_correct: the final correctness theorem for introsort5, collapsing the cost into a
    new constant introsort5_acost, which is then simplified to introsort_cost3
\<^item> introsort_impl: the LLVM program synthesized from introsort5
\<^item> final_hoare_triple: is the Hoare triple extracted for introsort_impl
\<^item> introsort3_allcost_simplified, introsort3_allcost_nlogn : the final cost bound of introsort_impl
    is displayed simplified to inspect the constants, and proved to be in \<Theta>(n log n); Note that,
    while we prove the bound to be in \<Theta>, it still is only an upper bound, as the Hoare triple
    only allows for upper bounds [excess time credits are garbage collected (@{term GC})].  
\<close>



subsection \<open>introsort_aux4 -- using heapsort and partitioner\<close>


  (* Assemble an introsort loop, using the partitioner and heap-sort *)  
  
  definition introsort_aux4 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list, ecost) nrest"
    where "introsort_aux4 xs l h d \<equiv> RECT' (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    lxs \<leftarrow> SPECc2 ''sub'' (-) h l; 
    if\<^sub>N SPECc2 ''icmp_slt'' (<) is_threshold lxs then doN {
      if\<^sub>N SPECc2 ''icmp_eq'' (=) d 0 then
        mop_call (heapsort2 xs l h)
      else doN {
        (xs,m)\<leftarrow>partition_pivot xs l h;
        d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
        xs \<leftarrow> introsort_aux (xs,l,m,d');
        xs \<leftarrow> introsort_aux (xs,m,h,d');
        RETURN xs
      }
    }
    else
      RETURN xs
  }) (xs,l,h,d)"


definition "introsort_aux4d xs hml l h \<equiv>
  doN {
    loghml \<leftarrow> mop_call (SPECT [Discrete.log hml \<mapsto> log2_iter_cost hml]);
    d \<leftarrow> SPECc2 ''mul'' (*) loghml 2;
    introsort_aux4 xs l h d
  }"



  

thm heapsort_correct' partition_pivot_correct

subsubsection \<open>Assemble Exchange rate\<close>

text \<open>Here we assemble a Timerefinement from @{term heapsort_TR} and @{term TR_pp}.\<close>

definition "Tia43 \<equiv> TId(''eq'':=cost ''icmp_eq'' 1,
          ''lt'':=cost ''icmp_slt'' 1,
        ''partition_c'':=TR_pp ''partition_c'',
        ''sort_c'':=
        cost ''call'' (enat 10)
         + cost ''if'' (enat 24) 
         + cost ''sub'' (enat 34)
         + cost ''ofs_ptr'' (enat 20) 
         + cost ''mul'' (enat 14) 
         + cost ''cmpo_v_idx'' (enat 6)
         + cost ''add'' (enat 42)
         + cost ''cmpo_idxs'' (enat 4)
         + cost ''udiv'' (enat 16)
         + cost ''and'' (enat 6)
         + cost ''icmp_slt'' (enat 21)
         + cost ''list_swap'' (enat 1)
         + cost ''load'' (enat 10)
         + cost ''store'' (enat 10))"
 

lemma cost_n_eq_TId_n: "cost n (1::enat) = TId n"
  by(auto simp:  TId_def cost_def zero_acost_def less_eq_acost_def)

lemma wfR''Tia43[simp]: "wfR'' (Tia43)"
  by(auto simp: Tia43_def intro!: wfR''_upd)
lemma spTia43[simp]: "struct_preserving (Tia43)"
  by(auto simp: Tia43_def intro!: struct_preserving_upd_I) 
lemma pcTia43[simp]: 
  "preserves_curr (Tia43) ''sub''"
  "preserves_curr (Tia43) ''icmp_slt''"
  "preserves_curr (Tia43) ''icmp_eq''"
  by(auto simp: Tia43_def preserves_curr_def cost_n_eq_TId_n) 


subsubsection \<open>Prepare Heapsort\<close>

paragraph \<open>Upper bound cost for heap sort\<close>

text \<open>rules to upperbound hs\<close>
lemma 
  assumes "1 \<le> Discrete.log (h - l)" "1 \<le> h - l"
  shows 
    hsub_aux1: "x \<le> y \<Longrightarrow> (h - l) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux3: "x \<le> y \<Longrightarrow> (h - (1+l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux4: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * (h - (1+l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux2: "x \<le> y \<Longrightarrow> p * (h - l) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux5: "x \<le> y \<Longrightarrow> (Discrete.log (h - l) * (h - (1+l))) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux6: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * (Discrete.log (h - l) * (h - (1+l))) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux13: "x \<le> y \<Longrightarrow> ((h - l) * Discrete.log (h - l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux14: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * ((h - l) * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux15: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> (h - l) * (p *  Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux7: "x \<le> y \<Longrightarrow> ((h - (1+l)) * Discrete.log (h - l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux8: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * ((h - (1+l)) * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux9: "x \<le> y \<Longrightarrow> (Discrete.log (h - l)) + x \<le> (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux10: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow> p * ( Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux11: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow>(h - (1+l)) * ( p * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux12: "x \<le> y \<Longrightarrow> p>0 \<Longrightarrow>(h - l) * ( p * Discrete.log (h - l)) + x \<le> p * (h - l) * Discrete.log (h - l) + y"
  and  hsub_aux_end: "x \<le> y \<Longrightarrow> q>0 \<Longrightarrow> q + x \<le> q * (h - l) * Discrete.log (h - l) + y"
  subgoal
    apply(rule add_mono)
    subgoal using assms by simp 
    by simp
  subgoal
    apply(rule add_mono)
    subgoal apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
    by simp
  subgoal
    apply(rule add_mono)
    subgoal apply simp apply(rule order.trans[where b="h-l"]) apply simp using assms by simp
    by simp 
  using assms
  by(auto intro!: add_mono) 

definition "hsub_STOP = (0::nat)"
lemma hsub_aux0: "a+(hsub_STOP::nat)\<le> b\<Longrightarrow> a \<le> b"
  by simp

lemma hsub_stop: "hsub_STOP \<le> 0"
  unfolding hsub_STOP_def by simp

lemmas hsub_aux = hsub_aux1 hsub_aux2 hsub_aux3 hsub_aux4 hsub_aux5 hsub_aux6
      hsub_aux13 hsub_aux14 hsub_aux15
      hsub_aux7 hsub_aux8
       hsub_aux9 hsub_aux10 hsub_aux11 hsub_aux12 
      hsub_aux_end

method hsub_solver uses assms  = (simp only: Suc_eq_plus1_left,
                    rule hsub_aux0,
                    simp only: add.assoc,
                    rule order.trans,
                    (rule hsub_aux[OF assms])+,
                    rule hsub_stop,
                    (simp_all, linarith?))

lemma upperbound_heapsort_cost':
  assumes "Discrete.log (h - l) \<ge> 1" "h-l \<ge> 1"
  shows 
  "timerefineA (heapsort_TR l h)  (cost ''slice_sort'' 1)
      \<le> timerefineA (Tia43)
       (cost ''sort_c'' (enat ((h-l) * Discrete.log (h-l))))"
  unfolding Tia43_def
    unfolding heapsort_TR_def  singleton_heap_context.sift_down3_cost_def heapsort_time_def
  unfolding pp_fun_upd pp_TId_absorbs_right 
  apply(auto simp add: timerefineA_propagate)
  unfolding Rsd_a_def heapsort_lbc_def 
  apply(auto simp:   timerefineA_update_apply_same_cost' lift_acost_cost costmult_cost
                lift_acost_propagate timerefineA_update_cost wfR''_TId intro!: wfR''_upd)
  apply(subst timerefineA_propagate, auto)+
  unfolding singleton_heap_context.sift_down3_cost_def  singleton_heap_context.E_sd3_l_def
  apply(auto simp: costmult_cost costmult_add_distrib lift_acost_propagate lift_acost_cost)
  apply(simp only: add.left_commute add.assoc cost_same_curr_left_add plus_enat_simps)
  apply(simp add: timerefineA_update_apply_same_cost' costmult_cost costmult_add_distrib)
  apply(simp only: add.left_commute)
  apply sc_solve_debug
  apply safe
  subgoal (*if*)  apply(simp add: add_mult_distrib2 add_mult_distrib 
              sc_solve_debug_def numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
    by(hsub_solver assms: assms)
  subgoal (*call*) apply(simp add: add_mult_distrib2 add_mult_distrib 
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* sub *) apply(simp add: add_mult_distrib2 add_mult_distrib 
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''ofs_ptr'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''mul'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''cmpo_v_idx'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''add'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''cmpo_idxs'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''udiv'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''icmp_slt'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''and'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''store'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''load'' *) apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps)  
    by(hsub_solver assms: assms)
  subgoal (* ''list_swap'' *)
      using assms apply(simp add: add_mult_distrib2 add_mult_distrib  add.assoc
              sc_solve_debug_def  numeral_eq_enat plus_enat_simps one_enat_def times_enat_simps) 
      done
  done
   
  
lemma upperbound_heapsort_cost: (* i guess h-l must be \<ge> 2 *)
  shows 
  "(h-l)>1 \<Longrightarrow> timerefineA (heapsort_TR l h)  (cost ''slice_sort'' 1)
      \<le> timerefineA (Tia43)
       (cost ''sort_c'' (enat ((h-l) * Discrete.log (h-l))))"
  apply(rule upperbound_heapsort_cost')
  apply auto  
  using Discrete.log.simps by auto  

paragraph \<open>Prepare correctness theorem\<close>

lemma heapsort_correct'': 
  "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id; lxs=(h'-l'); h'-l'>1\<rbrakk> \<Longrightarrow> heapsort2 xs l h \<le>
      \<Down>Id (timerefine (Tia43) (slice_sort_specT (cost ''sort_c'' (enat ((\<lambda>n. n * Discrete.log n) lxs))) (\<^bold><) xs' l' h'))"
 apply(rule order.trans)
   apply(rule heapsort_correct') apply auto [3] 
  unfolding slice_sort_spec_def slice_sort_specT_def
  apply(rule ASSERT_D3_leI)
  apply(simp add: SPEC_timerefine_conv)
  apply(rule SPEC_leq_SPEC_I)
   apply simp 
  apply(rule upperbound_heapsort_cost) apply simp
  done 

subsubsection \<open>Prepare Partition Algorithm\<close>

lemma partition_pivot_correct':
  "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> 
  \<Longrightarrow> partition_pivot xs l h \<le> \<Down>Id (timerefine (Tia43) (partition3_spec xs' l' h'))"
  apply(rule partition_pivot_correct_flexible)
  unfolding Tia43_def
  apply (auto )
  done

subsubsection \<open>Refinement Lemma for introsort_aux4\<close>

lemma introsort_aux4_refine:
    "introsort_aux4 xs l h d
         \<le> \<Down>Id (timerefine (Tia43) ((introsort_aux3 (\<lambda>n. n * Discrete.log n) xs l h d)))"
  unfolding introsort_aux4_def introsort_aux3_def 
  supply conc_Id[simp del]
  supply [refine] = mop_call_refine
  apply (refine_rcg RECT'_refine_t bindT_refine_conc_time_my_inres SPECc2_refine' SPECc2_refine MIf_refine
          heapsort_correct'' partition_pivot_correct')
  apply refine_mono
  apply refine_dref_type
  apply (simp_all add: inres_SPECc2) 
  apply(auto simp: Tia43_def )
  done

lemma nlogn_mono:
  "\<And>x y. x \<le> y \<Longrightarrow> x * Discrete.log x \<le> y * Discrete.log y"
  apply(rule mult_mono)
     apply simp
    apply (rule log_mono[THEN monoD])
  by simp_all

lemma nlogn_sums: 
  "a + b \<le> c \<Longrightarrow> a * Discrete.log a + b * Discrete.log b \<le> c * Discrete.log c"
  apply(rule order.trans)
   apply(rule add_mono[where b="a * Discrete.log c" and d="b * Discrete.log c"])
  subgoal using log_mono[THEN monoD] by simp
  subgoal using log_mono[THEN monoD] by simp
  apply(subst add_mult_distrib[symmetric])
  by simp

lemma nlogn_superlinear: 
  "a * Discrete.log a + b * Discrete.log b \<le> (a+b) * Discrete.log (a+b)"
  apply(rule nlogn_sums) by simp
 
thm introsort_aux3_correct 

definition "E_isa4 d lxs = (pp (pp Tia43 (TId(''list_append'' := 0, ''list_length'' := cost ''sub'' 1)))
             (TId(''slice_part_sorted'' := introsort_aux_cost (\<lambda>n. n * Discrete.log n) (lxs, d))))"


lemma sp_E_isa4[simp]:
  "struct_preserving (E_isa4 d hl)"
  unfolding E_isa4_def
  by (auto simp: pp_fun_upd pp_TId_absorbs_right intro!: struct_preserving_upd_I)  

lemma pc_E_isa4[simp]:
  "preserves_curr (E_isa4 d hl) ''sub''"
  "preserves_curr (E_isa4 d hl) ''icmp_slt''"
  unfolding E_isa4_def
  by(auto simp: pcTia43[unfolded preserves_curr_def] pp_fun_upd pp_TId_absorbs_right
                preserves_curr_def cost_n_eq_TId_n) 


    
subsubsection \<open>Correctness Lemma for introsort_aux4\<close>

lemma introsort_aux4_correct:
  "introsort_aux4 xs l h d \<le> \<Down> Id (timerefine (E_isa4 d (h-l)) (slice_part_sorted_spec xs l h))"
  apply(rule order.trans)
   apply(rule introsort_aux4_refine)
  apply(rule order.trans)
   apply simp apply(rule timerefine_mono2)
  apply simp
   apply(rule introsort_aux3_correct)
  subgoal apply(intro nlogn_sums) by simp
  apply (simp add: timerefine_iter2)
  apply(subst timerefine_iter2)
  subgoal
    apply(simp add: pp_fun_upd pp_TId_absorbs_right)
    apply(intro wfR''_upd)
    by simp
  subgoal by auto
  unfolding E_isa4_def apply simp
  done


schematic_goal introsort_aux4_cost_for_slice_part_sorted: "E_isa4 d lxs ''slice_part_sorted'' = ?G"
  unfolding norm_cost_tag_def[symmetric]
  unfolding E_isa4_def  
  apply(simp add: norm_cost norm_pp)
  apply(rule norm_cost_tagI)
  done


subsubsection \<open>Correctness Lemma for introsort_aux4d\<close>

definition "E_isa4d lxs = (TId(''slice_part_sorted'' := log2_iter_cost lxs + cost ''call'' 1 
                       + cost ''mul'' 1 + E_isa4 (Discrete.log lxs * 2) lxs ''slice_part_sorted''))"



lemma introsort_aux4d_correct:
  assumes "hml = h-l"
  shows "introsort_aux4d xs hml l h
           \<le> \<Down> Id (timerefine (E_isa4d hml) (slice_part_sorted_spec xs l h))"
  using assms
  unfolding introsort_aux4d_def
  unfolding spss_eq1 spss_eq2 
  apply simp
  unfolding slice_part_sorted_specT_def
  apply(cases "l < h \<and> h \<le> length xs", auto)
  unfolding SPEC_REST_emb'_conv
  apply(rule gwp_specifies_I)
  supply insort4 = introsort_aux4_correct[unfolded spss_eq1 spss_eq2,
          unfolded slice_part_sorted_specT_def SPEC_REST_emb'_conv, simplified,
          THEN le_acost_ASSERTI_otherdir, THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
  apply(refine_vcg \<open>-\<close> rules: gwp_SPECc2 insort4)
   apply(auto simp: Some_eq_emb'_conv emb_le_Some_conv )
  by(simp add: E_isa4d_def norm_cost add.left_commute add.commute add.assoc)

lemma TR_sps_important2:
  assumes "TR ''slice_part_sorted'' = E_isa4d (h - l) ''slice_part_sorted''"
  shows "timerefine TR (slice_part_sorted_spec xs l h)
             = (timerefine (E_isa4d (h-l)) (slice_part_sorted_spec xs l h))"
  unfolding slice_part_sorted_spec_def
  apply(cases "l < h \<and> h \<le> length xs"; auto)
  apply(simp only: SPEC_timerefine_conv)
  apply(rule SPEC_cong, simp)
  apply(rule ext)
  apply(simp add: norm_cost)
  apply(subst assms(1))
  apply(simp add: norm_cost)
  done

lemma introsort_aux4d_correct_flexible:
  assumes "TR ''slice_part_sorted'' = E_isa4d (h - l) ''slice_part_sorted''"
    and "hml = h-l"
  shows "introsort_aux4d xs hml l h \<le> \<Down> Id (timerefine TR (slice_part_sorted_spec xs l h))"
  apply(subst TR_sps_important2[where TR=TR, OF assms(1)])
  supply [[unify_trace_failure]]
  unfolding assms(2) 
  apply(rule introsort_aux4d_correct[where hml="h-l"])
  by simp



subsection \<open>introsort4\<close>

  definition "introsort4 xs l h \<equiv> doN {
    ASSERT(l\<le>h);
    hml \<leftarrow> SPECc2 ''sub'' (-) h l;
    if\<^sub>N SPECc2 ''icmp_slt'' (<) 1 hml then doN {
      xs \<leftarrow> introsort_aux4d xs hml l h;
      xs \<leftarrow> final_insertion_sort2 xs l h;
      RETURN xs
    } else RETURN xs
  }"  

lemmas final_insertion_sort2_correct_flexible = final_insertion_sort2_correct

abbreviation "TR_is d s == TId(''lt'':=cost ''icmp_slt'' 1,''slice_sort'' := fi2_cost s, 
            ''slice_part_sorted'':= log2_iter_cost s + cost ''call'' 1 + cost ''mul'' 1 + E_isa4 d s ''slice_part_sorted'')"

lemma pc_TR_is[simp]:
  "preserves_curr (TR_is d hl) ''sub''"
  "preserves_curr (TR_is d hl) ''icmp_slt''"
  by(auto simp: preserves_curr_def cost_n_eq_TId_n) 

lemma wfR''_TR_is[simp]: "wfR'' (TR_is d hl)"
  by (auto intro!: wfR''_upd)

lemma sp_TR_is[simp]:
  "struct_preserving (TR_is d hl)"
  by (auto intro!: struct_preserving_upd_I) 


lemma introsort4_refine:
  "introsort4 xs l h \<le> \<Down>Id (timerefine (TR_is (Discrete.log (h-l)*2) (h-l)) (introsort3 xs l h))"
  unfolding introsort4_def introsort3_def 
  supply conc_Id[simp del]
  apply (refine_rcg SPECc2_refine' SPECc2_refine bindT_refine_conc_time_my_inres MIf_refine
              introsort_aux4d_correct_flexible final_insertion_sort2_correct_flexible
             consumea_refine   )
  apply refine_dref_type                                          
 by (auto simp: E_isa4d_def norm_cost inres_SPECc2) 

end

lemma introsort_depth_limit_in_bounds_aux: (* TODO: Move depth-computation into own (inline) function *)
  assumes "n < max_snat N" "1<N" shows "Discrete.log (n) * 2 < max_snat N"
proof (cases "n=0")
  case True thus ?thesis using assms by auto
next
  case [simp]: False  
  have ?thesis if "Discrete.log (n) < max_snat (N-1)"
    using that \<open>1<N\<close> unfolding max_snat_def
    by (metis nat_mult_power_less_eq pos2 semiring_normalization_rules(33))
  moreover have "Discrete.log (n) < max_snat (N-1)"
    apply (rule discrete_log_ltI)
    using assms apply (auto simp: max_snat_def)
    by (smt Suc_diff_Suc leI le_less_trans n_less_equal_power_2 nat_power_less_imp_less
            not_less_eq numeral_2_eq_2 numeral_2_eq_2 zero_order(3))
  ultimately show ?thesis .
qed  
  


context sort_impl_context begin

subsection \<open>introsort_aux5 -- using cmp and swap\<close>

  definition introsort_aux5 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list, ecost) nrest"
    where "introsort_aux5 xs l h d \<equiv> RECT' (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    lxs \<leftarrow> SPECc2 ''sub'' (-) h l; 
    if\<^sub>N SPECc2 ''icmp_slt'' (<) is_threshold lxs then doN {
      if\<^sub>N SPECc2 ''icmp_eq'' (=) d 0 then
        mop_call (heapsort3 xs l h)
      else doN {
        (xs,m)\<leftarrow>partition_pivot2 xs l h;
        d' \<leftarrow> SPECc2 ''sub'' (-) d 1;
        xs \<leftarrow> introsort_aux (xs,l,m,d');
        xs \<leftarrow> introsort_aux (xs,m,h,d');
        RETURN xs
      }
    }
    else
      RETURN xs
  }) (xs,l,h,d)"


lemma pc_TR_cmp_swap: "x\<noteq>''cmp_idxs'' \<Longrightarrow> x\<noteq>''cmpo_idxs'' \<Longrightarrow> x\<noteq>''cmpo_v_idx'' \<Longrightarrow> x\<noteq>''list_swap''
  \<Longrightarrow> preserves_curr TR_cmp_swap x"
  apply(intro preserves_curr_other_updI)
  by auto

subsubsection \<open>refine compare and swap\<close>

lemma introsort_aux5_refine: "(xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id \<Longrightarrow> (d,d')\<in>Id 
    \<Longrightarrow> introsort_aux5 xs l h d \<le> \<Down>Id (timerefine (TR_cmp_swap) ((introsort_aux4 xs' l' h' d')))"
    unfolding introsort_aux4_def introsort_aux5_def 
    supply conc_Id[simp del]
    apply (refine_rcg RECT'_refine_t bindT_refine_conc_time_my_inres SPECc2_refine' MIf_refine
            heapsort3_refine partition_pivot2_refines  mop_call_refine)
    apply refine_mono
    apply refine_dref_type
    apply (auto simp add: inres_SPECc2 intro!: pc_TR_cmp_swap) 
    done


subsubsection \<open>synthesize program\<close>

sepref_register introsort_aux5
sepref_def introsort_aux_impl is
  "uncurry3 (PR_CONST introsort_aux5)"
    :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_aux5_def PR_CONST_def
  apply (annot_snat_const "TYPE('size_t)")
  supply [[goals_limit = 1]]
  by sepref


subsection \<open>introsort5\<close>


  definition "introsort5 xs l h \<equiv> doN {
    ASSERT(l\<le>h);
    hml \<leftarrow> SPECc2 ''sub'' (-) h l;
    if\<^sub>N SPECc2 ''icmp_slt'' (<) 1 hml then doN {
      loghml \<leftarrow> mop_call (log2_iter hml);
      d \<leftarrow> SPECc2 ''mul'' (*) loghml 2;
      xs \<leftarrow> introsort_aux5 xs l h d;
      xs \<leftarrow> final_insertion_sort3 xs l h;
      RETURN xs
    } else RETURN xs
  }"  


subsubsection \<open>refine compare and swap\<close>

  lemma introsort5_refine: "introsort5 xs l h \<le> \<Down>Id (timerefine (TR_cmp_swap) ((introsort4 xs l h )))"
    unfolding introsort4_def introsort_aux4d_def introsort5_def 
    supply conc_Id[simp del]
    apply simp
    apply (refine_rcg bindT_refine_conc_time_my_inres SPECc2_refine' MIf_refine
            introsort_aux5_refine final_insertion_sort3_refines
              log2_iter_refine_TR_cmp_swap mop_call_refine )
    apply refine_dref_type
    apply (auto simp add: inres_SPECc2 intro!: pc_TR_cmp_swap) 
    done
 

lemma mop_call_same_result:
  fixes m :: "(_,(_,enat) acost)nrest"
  shows "RETURN x \<le> mop_call m \<Longrightarrow> RETURN x \<le> m"
  unfolding mop_call_def consume_def RETURNT_def
  apply(auto split: if_splits nrest.splits simp: le_fun_def)
  subgoal for x2 apply(cases "x2 x") apply auto 
    by (simp add: ecost_nneg)
  done

lemma introsort5_synth_side_condition: (* TODO: Move depth-computation into own (inline) function *)
  assumes "hml < max_snat N" "RETURNTecost xb \<le> mop_call (log2_iter hml)" "1<N"
  shows "xb * 2 < max_snat N"
proof -
  from order_trans[OF mop_call_same_result[OF assms(2)] log2_iter_refine]
  have xb: "xb = Discrete.log hml"
    unfolding  RETURNT_def
    by (auto split: if_splits simp: le_fun_def)

  show ?thesis
    unfolding xb
    apply(rule introsort_depth_limit_in_bounds_aux)
    using assms by auto
qed
 

subsubsection \<open>synthesize program\<close>

sepref_register introsort5
sepref_def introsort_impl is 
  "uncurry2 (PR_CONST introsort5)"
    :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort5_def PR_CONST_def
  apply (annot_snat_const "TYPE('size_t)")
  supply [intro!] = introsort5_synth_side_condition 
  by sepref

subsection \<open>Compose the correctness theorems\<close>                                   

text \<open>When composing the correctness theorems of @{term introsort5},
    @{term introsort4} and @{term introsort3},
     we synthesize a compound exchange rate ?E:\<close>

schematic_goal introsort5_correct:
  "introsort5 xs l h \<le> \<Down> Id (timerefine ?E (slice_sort_spec (\<^bold><) xs l h))"
  apply(rule order.trans)
  apply(rule introsort5_refine)
  apply (rule nrest_Rel_mono)
  
  apply(rule order.trans)
  apply(rule timerefine_mono2) apply(rule wfR''E)
   apply(rule introsort4_refine)
                       
  apply(rule order.trans)
  apply(rule timerefine_mono2) apply(rule wfR''E)
  apply (rule nrest_Rel_mono)
  apply(rule timerefine_mono2) apply(rule wfR''_TR_is)
   apply(rule introsort3_correct)

  apply(simp add: conc_Id)
  apply (subst timerefine_iter2)  
    apply(rule wfR''E)
   apply(rule wfR''_TR_is)

  apply (subst timerefine_iter2)  
  apply(rule wfR''_ppI)
    apply(rule wfR''E)
    apply(rule wfR''_TR_is)
  subgoal apply auto done
  apply(rule order.refl)
  done 


text \<open>And give this exchange rate a Name:\<close>

concrete_definition introsort5_TR is introsort5_correct uses "_ \<le> \<Down> Id (timerefine \<hole> _) "

lemma pull_introsort5_TR_into_spec: "(timerefine (introsort5_TR l h) (slice_sort_spec (\<^bold><) xs l h))
    = slice_sort_specT (introsort5_TR l h ''slice_sort'') (\<^bold><) xs l h"
  unfolding slice_sort_spec_def slice_sort_specT_def
  apply(cases "l \<le> h \<and> h \<le> length xs")
   apply(auto simp: SPEC_timerefine_conv)
  apply(rule SPEC_cong) apply simp
  by (auto simp: timerefineA_cost)



text \<open>We simplify @{term introsort5_TR}\<close>


lemma sum_numeral_to_front: 
  fixes x :: "'b::{comm_monoid_add,numeral}"
  assumes "NO_MATCH (numeral X) x"  
  shows "x+numeral y = numeral y + x" "x+(numeral y+z) = numeral y + (x+z)"
  by (simp_all add: algebra_simps)

lemma prod_numeral_to_front: 
  fixes x :: "'b::{comm_monoid_mult,numeral}"
  assumes "NO_MATCH (numeral X) x"  
  shows "x*numeral y = numeral y * x" "x*(numeral y*z) = numeral y * (x*z)"
  by (simp_all add: algebra_simps)

schematic_goal ub_introsort5: "timerefineA (introsort5_TR l h) (cost ''slice_sort'' 1) \<le> ?x"
  unfolding introsort5_TR_def introsort3_cost_def
  apply(simp add: norm_pp norm_cost )
  apply summarize_and_apply_tr
  unfolding log2_iter_cost_def TR_is_insert3_def E_isa4_def Tia43_def introsort_aux_cost_def
      cost_insert_guarded_def cost_is_insert_guarded_step_def
      cost_insert_def cost_is_insert_step_def move_median_to_first_cost_def
  apply(simp add: norm_pp norm_cost )
  apply summarize_and_apply_tr
  (* TODO: Add 0+_ = and _+0= to summarize_same_cost*)
  apply (simp add: add_ac numeral_eq_enat one_enat_def left_add_twice)
  apply summarize_and_apply_tr
  apply (simp add: add_ac numeral_eq_enat one_enat_def left_add_twice)
  unfolding cmpo_v_idx2'_cost_def cmp_idxs2'_cost_def myswap_cost_def cmpo_idxs2'_cost_def
  apply(simp add: norm_pp norm_cost )
  apply summarize_same_cost
  apply (simp add: add_ac numeral_eq_enat one_enat_def left_add_twice Suc_eq_plus1 flip: One_nat_def)
  apply (simp named_ss HOL_basic_ss_nomatch: sum_numeral_to_front prod_numeral_to_front)
  by (rule order_refl)
(*  
  oops
  apply(subst timerefineA_propagate, (auto intro!: wfR''_upd)[1])+ 
  apply(simp add: norm_pp norm_cost )
  unfolding log2_iter_cost_def TR_is_insert3_def E_isa4_def Tia43_def introsort_aux_cost_def
      cost_insert_guarded_def cost_is_insert_guarded_step_def
      cost_insert_def cost_is_insert_step_def move_median_to_first_cost_def
  apply(simp add: norm_pp norm_cost )
  apply(subst timerefineA_propagate, (auto intro!: wfR''_upd)[1])+ 
  apply(simp add: norm_pp norm_cost )
  unfolding cmpo_v_idx2'_cost_def cmp_idxs2'_cost_def myswap_cost_def cmpo_idxs2'_cost_def
  apply(simp add: norm_pp norm_cost )
  apply(simp add: add.commute add.left_commute)
  apply(simp add: cost_same_curr_left_add cost_same_curr_add) 
  apply(simp add: add.assoc add.commute add.left_commute)
  apply(simp add: cost_same_curr_left_add cost_same_curr_add) 
  apply(simp add: add.assoc add.commute add.left_commute)

  apply sc_solve_upperbound
  by simp
*)

text \<open>and give it a name\<close>
concrete_definition introsort5_acost is ub_introsort5 uses "_ \<le> \<hole>"

text \<open>we pull the lifting to the outer most:\<close>
schematic_goal lift_introsort5_acost: "introsort5_acost x y = lift_acost ?y"
  unfolding introsort5_acost_def
  unfolding lift_acost_cost[symmetric]  lift_acost_propagate[symmetric] lift_acost_push_mult
  apply(rule refl)
  done

text \<open>We define the finite part of the cost expression:\<close>
concrete_definition introsort5_cost is lift_introsort5_acost uses "_ = lift_acost \<hole>"


text \<open>We display the final fine-grained cost expression:\<close>

thm introsort5_cost_def[no_vars]

definition "introsort_cost3 s \<equiv> 
(306 + (17 * s + 20 * (s * Discrete.log s))) *m lt_acost +
(cost ''and'' (6 * (s * Discrete.log s)) +
 (cost ''mul'' (1 + 14 * (s * Discrete.log s)) +
  (cost ''add'' (21 + (s + (Discrete.log s + 48 * (s * Discrete.log s)))) +
   (cost ''udiv'' (1 + (Discrete.log s + 18 * (s * Discrete.log s))) +
    (cost ''if'' (633 + (Discrete.log s + (20 * s + 40 * (s * Discrete.log s)))) +
     (cost ''sub'' (596 + (35 * s + 44 * (s * Discrete.log s))) +
      (cost ''load'' (629 + (34 * s + 54 * (s * Discrete.log s))) +
       (cost ''icmp_sle'' 1 +
        (cost ''call'' (343 + (Discrete.log s + (19 * s + 22 * (s * Discrete.log s)))) +
         (cost ''store'' (612 + (34 * s + 54 * (s * Discrete.log s))) +
          (cost ''icmp_eq'' (289 + (s + 2 * Discrete.log s * s)) +
           (cost ''ofs_ptr'' (1241 + (68 * s + 108 * (s * Discrete.log s))) +
            cost ''icmp_slt'' (20 + (Discrete.log s + (2 * s + 25 * (s * Discrete.log s))))))))))))))))
"

 
lemma introsort_cost3_eq_introsort_cost5: "introsort_cost3 (h-l) = introsort5_cost l h" 
  unfolding introsort_cost3_def introsort5_cost_def by (auto simp: algebra_simps)

definition "introsort_impl_cost n = lift_acost (introsort_cost3 n)"

lemma "introsort_impl_cost (h-l) = introsort5_acost l h"
  unfolding introsort_impl_cost_def introsort5_cost.refine introsort_cost3_eq_introsort_cost5 
  by simp
  

text \<open>Combine Refinement lemma for @{term introsort_impl} with correctness theorem\<close>

lemmas introsort_correct' = hn_refine_result[OF introsort_impl.refine[to_hnr],
                                              unfolded PR_CONST_def APP_def,
                                              OF introsort5_TR.refine ]

lemma introsort_correct:
 "hn_refine (hn_ctxt arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi)
       (introsort_impl ai bia bi)
 (hn_invalid arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi) (hr_comp arr_assn Id)
  (timerefine (introsort5_TR ba b) (slice_sort_spec (\<^bold><) a ba b))"
  apply(rule introsort_correct')
  apply(rule attains_sup_sv) by simp

text \<open>extract Hoare Triple\<close>

lemmas introsort_ht = introsort_correct[unfolded slice_sort_spec_def SPEC_REST_emb'_conv,
                                          THEN ht_from_hnr]

lemma Sum_any_cost2: "Sum_any (the_acost (cost n x)) = x"
  unfolding cost_def by (simp add: zero_acost_def)


subsection \<open>The final Hoare Triple\<close>

lemma introsort_final_hoare_triple_aux:
  assumes "l \<le> h \<and> h \<le> length xs\<^sub>0"
  shows "llvm_htriple ($introsort_impl_cost (h-l) \<and>* hn_ctxt arr_assn xs\<^sub>0 p
           \<and>* hn_val snat_rel l l' \<and>* hn_val snat_rel h h')
        (introsort_impl p l' h')
      (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>(slice_sort_aux xs\<^sub>0 xs l h) \<and>* arr_assn xs r) s)
           \<and>* hn_invalid arr_assn xs\<^sub>0 p \<and>* hn_val snat_rel l l' \<and>* hn_val snat_rel h h')"
  unfolding introsort_impl_cost_def
  using assms
  by (rule llvm_htriple_more_time[OF introsort5_acost.refine introsort_ht,
                unfolded introsort5_cost.refine introsort_cost3_eq_introsort_cost5[symmetric]
                          hr_comp_Id2])



text \<open>Calculate the cost for all currencies:\<close>

schematic_goal Sum_any_calc: 
  shows "project_all (introsort_impl_cost s) = ?x"
  unfolding norm_cost_tag_def[symmetric]
  apply(subst project_all_is_Sumany_if_lifted[OF introsort_impl_cost_def])
  unfolding introsort_cost3_def 
  apply(simp add: the_acost_propagate add.assoc) 
  
  supply acost_finiteIs = finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero finite_the_acost_mult_nonzeroI lt_acost_finite
  
  apply (subst Sum_any.distrib, (intro acost_finiteIs;fail), (intro acost_finiteIs;fail))+
  apply (simp only: Sum_any_cost sum_any_push_costmul)
  apply (simp add: add_ac)
  apply (simp named_ss HOL_basic_ss_nomatch: sum_numeral_to_front prod_numeral_to_front)
  apply(rule norm_cost_tagI)
  done

text \<open>Give the result a name:\<close>
concrete_definition (in -) introsort3_allcost is sort_impl_context.Sum_any_calc uses "_ = \<hole>"

lemma introsort3_allcost_is_projected_introsort_impl_cost:
  shows "introsort3_allcost lt_acost n = project_all (introsort_impl_cost n)"  
  apply(subst introsort3_allcost.refine[OF sort_impl_context_axioms, symmetric])
  by (simp_all)

lemma projected_introsort_cost_simplified:
  "project_all (introsort_impl_cost n) = 
    4387 + (5 * Discrete.log n + (214 * n + (435 * (n * Discrete.log n) 
  + (306 + (17 * n + 20 * (n * Discrete.log n))) * Sum_any (the_acost lt_acost))))"  
  unfolding Sum_any_calc by simp
  
end 

text \<open>The cost of introsort expanded:\<close>

thm introsort3_allcost_def[of lt_cost s]

lemma introsort3_allcost_simplified:
  "introsort3_allcost lt_cost s \<equiv> 4387 + (5 * Discrete.log s + (214 * s + (435 * (s * Discrete.log s) 
  + (306 + (17 * s + 20 * (s * Discrete.log s))) * Sum_any (the_acost lt_cost))))"
  (*"introsort3_allcost n = 4693 + 5 *  Discrete.log n + 231 * n + 455 * (n * Discrete.log n)"*)
  unfolding introsort3_allcost_def
  .

  

text \<open>The asymptotic behaviour of introsort's cost:\<close>

lemma introsort3_allcost_nlogn: (* TODO: Fix! *)
  "(\<lambda>x. real (introsort3_allcost ltc x)) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  unfolding introsort3_allcost_simplified oops
  (*by auto2*)



context sort_impl_context begin

lemma "slice_sort_aux xs\<^sub>0 xs l h \<equiv> (length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0
                    \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (\<^bold><) (slice l h xs\<^sub>0) (slice l h xs))"
  by simp


text \<open>Final correctness lemma:\<close>
lemma introsort_final_hoare_triple:
  assumes "l \<le> h \<and> h \<le> length xs\<^sub>0"
  shows "llvm_htriple ($introsort_impl_cost (h-l) \<and>* arr_assn xs\<^sub>0 p
           \<and>* pure snat_rel l l' \<and>* pure snat_rel h h')
        (introsort_impl p l' h')
      (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>(slice_sort_aux xs\<^sub>0 xs l h) \<and>* arr_assn xs r) s)
            \<and>* pure snat_rel l l' \<and>* pure snat_rel h h')"
  apply(rule cons_post_rule) (* TODO: very ugly proof to get rid of the invalid_assn! *)
   apply (rule introsort_final_hoare_triple_aux[OF assms, unfolded hn_ctxt_def]) 
  apply(simp add: pred_lift_extract_simps  invalid_assn_def pure_part_def)
  apply(subst (asm) (2) sep_conj_commute)
  apply(subst (asm) (1) sep_conj_assoc[symmetric])
  apply(subst (asm) sep_conj_pred_lift) by simp


text \<open>introsort_impl_cost projected to a function @{typ "nat \<Rightarrow> nat"} \<close>
lemma "introsort3_allcost lt_acost n = project_all (introsort_impl_cost n)"  
  by (rule introsort3_allcost_is_projected_introsort_impl_cost)

end



end
