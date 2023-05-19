\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Algorithms to calculate the logarithm of base 2\<close>
theory Sorting_Log2
imports Sorting_Setup
begin


paragraph \<open>Summary\<close>
text \<open>This theory two algorithms for calculating the logarithm for base 2.
    The first algorithm repeatedly divides by 2 until 0 is reached. This algorithm
    is linear in the log n.
    The second algorithm calculates the number of leading zeros. That algorithm thus has running
    time depending on the word size.
    We use the first algorithm for our further developments\<close>


subsection \<open>Log2 by iterated division by 2\<close>

definition log2_iter :: "nat \<Rightarrow> (nat,_) nrest"
  where "log2_iter n\<^sub>0 \<equiv> RECT' (\<lambda>log_iter n. do {
     if\<^sub>N SPECc2 ''icmp_slt'' (<) n 2 then
       RETURNT 0
     else doN {
       n' \<leftarrow> SPECc2 ''udiv'' (div) n 2;
       r \<leftarrow> log_iter n';
       ASSERT (r+1 \<le> n);
       SPECc2 ''add'' (+) r 1
     }
   }) n\<^sub>0"

abbreviation "log2_iter_body_cost n \<equiv> n *m (cost ''icmp_slt'' 1 + cost ''call'' 1 + cost ''if'' 1 + cost ''udiv'' 1 + cost ''add'' 1)"
definition "log2_iter_cost n \<equiv> log2_iter_body_cost (enat (Discrete.log n + 1))"


lemma minus_0_absorb_acost: "x - (0::(_,enat)acost) = x"
  apply(cases x)
  by(auto simp: minus_acost_alt zero_acost_def) 

lemma log2_iter_refine_aux: "n\<ge>2 \<Longrightarrow> Suc (Discrete.log n - Suc 0) = Discrete.log n" 
  using log_rec by auto  


definition "mop_log x = SPECT [Discrete.log x \<mapsto> cost ''log'' 1]"

lemma log2_iter_refine:
  shows "log2_iter x \<le> SPECT [Discrete.log x \<mapsto> log2_iter_cost x]"
  unfolding log2_iter_def
        unfolding log2_iter_cost_def
  apply(cases "x>0")
  subgoal
    apply -
    apply(induct rule: log_induct)
    subgoal 
      apply(subst RECT'_unfold)
       apply refine_mono
      apply(rule gwp_specifies_I)
      unfolding SPECc2_def

      apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET)
      subgoal apply (auto simp: norm_cost) apply sc_solve by(auto simp:  one_enat_def)
      subgoal by auto
      done
    subgoal
      apply(subst RECT'_unfold)
       apply refine_mono
      apply(rule gwp_specifies_I)
      unfolding SPECc2_def

      apply (refine_vcg \<open>-\<close>)
      subgoal by simp
      subgoal premises prems 
        apply(rule prems(2)[THEN gwp_specifies_rev_I, THEN gwp_conseq4])
        apply (refine_vcg \<open>-\<close>)
        apply(auto split: if_splits)
         apply(auto simp: norm_cost minus_0_absorb_acost)
        subgoal apply(subst log2_iter_refine_aux) using prems(1) by auto
        subgoal apply sc_solve apply (auto simp: one_enat_def)
          apply(subst log2_iter_refine_aux) using prems(1) by auto
        subgoal apply(subst log2_iter_refine_aux) using prems(1)
          apply auto
          by (metis leD less_2_cases_iff log_exp2_le nat_le_linear neq0_conv pow_mono_leq_imp_lt)
        done
      done
    done
  subgoal
    apply(subst RECT'_unfold)
     apply refine_mono
    apply(rule gwp_specifies_I)
    unfolding SPECc2_def

    apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET)
    subgoal apply (auto simp: norm_cost) apply sc_solve by(auto simp: one_enat_def)
    subgoal by auto
    done
  done

 
lemma (in sort_impl_context) log2_iter_refine_TR_cmp_swap: 
 "(x,x')\<in>Id \<Longrightarrow> log2_iter x \<le> \<Down> nat_rel (timerefine TR_cmp_swap (SPECT [Discrete.log x' \<mapsto> log2_iter_cost x']))"
  apply(rule order.trans)
   apply(rule log2_iter_refine)
  unfolding log2_iter_cost_def
  by (auto simp: timerefine_SPECT_map le_fun_def norm_cost) 
 

  

lemma log2_iter_correct: "log2_iter x \<le> \<Down>Id (timerefine (TId(''log'':=log2_iter_cost x)) (mop_log x))"
  apply(rule order_trans)
  apply(rule log2_iter_refine)
  by(auto simp: mop_log_def timerefine_SPECT_map le_fun_def norm_cost)


(* TODO: @Peter integrate this type parameter into sort_impl_context and adapt
            all other functions *)
(*experiment
begin

sepref_register log2_iter
context
  fixes wordlen :: "'l::len2 itself"
  assumes [simp]: "LENGTH('l) \<ge> 4"
begin

lemma [simp]: "2 \<in> snats LENGTH('l)"
  sorry
lemma [simp]: "2 < max_snat LENGTH('l)"
  sorry

find_in_thms "''icmp_slt''" in sepref_fr_rules


abbreviation "arb_size_assn \<equiv> snat_assn' TYPE('l)"

sepref_def log2_iter_impl is "log2_iter"
    :: "arb_size_assn\<^sup>k \<rightarrow>\<^sub>a arb_size_assn"
  unfolding log2_iter_def PR_CONST_def
  apply (annot_snat_const "TYPE('l::len2)")
  by sepref
end
end *)
  
context size_t_context
begin  

  sepref_def log2_iter_impl is "log2_iter"
      :: "size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding log2_iter_def PR_CONST_def
    apply (annot_snat_const "TYPE('size_t)")
    by sepref
end

subsection \<open>Count Leading Zeroes and Log2\<close>
(* TODO: Define semantics of llvm.ctlz intrinsic! *)

subsubsection \<open>Explicit Implementation by Loop\<close>

definition word_clz' :: "'a::len word \<Rightarrow> nat" where
  "word_clz' x \<equiv> if x=0 then 0 else word_clz x"

lemma word_clz'_eq: "x\<noteq>0 \<Longrightarrow> word_clz' x = word_clz x" 
  by (simp add: word_clz'_def)  
  
lemma of_bl_eqZ: 
  "\<lbrakk> length xs = LENGTH ('a::len) \<rbrakk> \<Longrightarrow> (of_bl xs :: 'a word) = 0 \<longleftrightarrow> (xs = replicate LENGTH('a) False)"  
  apply auto
  by (metis to_bl_0 to_bl_use_of_bl word_bl_Rep')    

lemma word_clz'_rec: "word_clz' x = (if x <=s 0 then 0 else 1 + word_clz' (x << 1))"  
  apply (clarsimp simp: word_clz'_def word_clz_def)
  apply (cases "to_bl x"; simp)
  apply safe
  subgoal by (simp add: word_msb_alt word_sle_msb_le)
  subgoal by (simp add: word_msb_alt word_sle_msb_le)
  subgoal 
    apply (simp add: word_msb_alt word_sle_msb_le shiftl_bl mult.commute[of x 2])
    apply (simp add: double_eq_zero_iff[of x])
    by (metis list.sel(1) msb_big order_refl word_msb_alt)
  subgoal
    by (simp add: word_msb_alt word_sle_msb_le)  
  subgoal for b bs 
    apply (clarsimp simp: mult.commute[of x 2] to_bl_double_eq)
    apply (subgoal_tac "True\<in>set bs")
    apply simp
    by (simp add: eq_zero_set_bl)
  done  
  
lemma word_clz'_rec2: "word_clz' x = (if 0 <s x then 1 + word_clz' (x << 1) else 0)"  
  by (meson signed.not_le word_clz'_rec)

lemma word_clz'_simps2:
  "0 <s x \<Longrightarrow> word_clz' x = 1 + word_clz' (x << 1)"
  "\<not>(0 <s x) \<Longrightarrow> word_clz' x = 0"  
  using word_clz'_rec2 by metis+
  
definition word_clz2 :: "'a::len2 word \<Rightarrow> (nat,_) nrest"
  where "word_clz2 x\<^sub>0 \<equiv> do {
    (c,_) \<leftarrow> monadic_WHILEIT (\<lambda>(c,x). word_clz' x\<^sub>0 = c + word_clz' x)
     (\<lambda>(c,x). SPECc2 ''icmp_slt'' (<s) 0 x) (\<lambda>(c,x). do {
      ASSERT (c + 1 < max_snat LENGTH('a));
      c' \<leftarrow> SPECc2 ''add'' (+) c 1;
      x' \<leftarrow> SPECc2 ''shl'' (<<) x 1;
      RETURN (c',x')
    }) (0,x\<^sub>0);
    RETURN c
  }"

lemma word_clz'_fits_snat: "word_clz' (x::'a::len2 word) < max_snat LENGTH('a)"
  unfolding word_clz'_def using word_clz_nonzero_max[of x]
  apply (auto simp: word_size max_snat_def) 
  by (meson le_def n_less_equal_power_2 nat_le_Suc_less_imp order_trans)

abbreviation "word_clz2_body_cost \<equiv> cost ''icmp_slt'' 1 + cost ''add'' 1 
                  + cost ''call'' 1 + cost ''if'' 1 + cost ''shl'' 1"

abbreviation "word_clz2_cost sw \<equiv>  (enat (1+sw)) *m word_clz2_body_cost"

(* TODO: move, DUP *)
lemma finite_sum_gtzero_nat_cost:
  "finite {a. the_acost (cost n m) a > (0::nat)}"
  unfolding cost_def by (auto simp: zero_acost_def)

lemma if_rule: "(c \<Longrightarrow> x \<le> a) \<Longrightarrow> (~c \<Longrightarrow> x \<le> b) \<Longrightarrow> x \<le> (if c then a else b)"
  by auto

lemma costmult_0_nat:
  shows "(0::nat) *m x = 0"
  by(auto simp: costmult_def zero_acost_def)

lemma word_clz2_refine: "word_clz2 x\<^sub>0 \<le> SPECT [word_clz' x\<^sub>0\<mapsto> word_clz2_cost (size x\<^sub>0)]"
  apply(rule order_trans[where y="SPECT [word_clz' x\<^sub>0\<mapsto> (enat (1+word_clz' x\<^sub>0)) *m word_clz2_body_cost]"])
  subgoal
    unfolding word_clz2_def
    apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>(c,x). ((word_clz' x)) *m word_clz2_body_cost"])
  
    apply(rule gwp_specifies_I)
    unfolding SPECc2_def
  
    apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET)
    apply(rule gwp_monadic_WHILEIET) 
    subgoal 
      by(auto simp: wfR2_def the_acost_zero_app norm_cost intro!: finite_sum_gtzero_nat_cost)
    subgoal for s
      apply clarsimp
      apply (refine_vcg \<open>-\<close> rules: if_rule)
      subgoal 
        apply(rule loop_body_conditionI)
        subgoal
          apply (auto simp: norm_cost)
          apply sc_solve
          by (auto simp add: word_clz'_rec2)
        subgoal 
          apply (auto simp: norm_cost)
          apply sc_solve 
          by (auto simp: one_enat_def word_clz'_rec2)   
        subgoal
          by (simp add: word_clz'_rec2)
        done
      subgoal using word_clz'_fits_snat[of x\<^sub>0]
        by (auto simp: word_clz'_simps2)
      subgoal
        apply(rule loop_exit_conditionI)
        apply(refine_vcg \<open>-\<close>)
        apply (auto)
        subgoal
          using word_clz'_simps2(2) by blast
        subgoal        
          apply(simp add: costmult_0_nat)
          apply(auto simp: norm_cost )
          apply sc_solve
          by (auto simp: one_enat_def)
        done
      done
    subgoal by simp
    done
  subgoal apply(simp add: le_fun_def)
    apply(rule costmult_right_mono) 
    using word_clz_max by (auto simp add: word_clz'_def )
  done

(*
lemma word_clz2_refine': "(word_clz2, RETURN o word_clz') \<in> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
  by (auto intro!: nrest_relI simp: word_clz2_refine)
*)  
  
sepref_def word_clz'_impl is word_clz2 :: "(word_assn' TYPE('b::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('b)"  
  unfolding word_clz2_def
  apply (rewrite at "(SPECc2 ''shl'' (<<) _ \<hole>)" snat_const_fold[where 'a='b])
  apply (rewrite at "(SPECc2 ''add'' (+) _ \<hole>)" snat_const_fold[where 'a='b])
  apply (rewrite at "(\<hole>,_)" snat_const_fold[where 'a='b])
  by sepref

export_llvm "word_clz'_impl :: 64 word \<Rightarrow> 64 word llM" 

sepref_register word_clz'
 
   


lemma word_clz_nonzero_max': "x\<noteq>0 \<Longrightarrow> word_clz (x::'a::len2 word) \<le> LENGTH('a) - Suc 0"
  using word_clz_nonzero_max[of x] unfolding word_size
  by simp


lemma "x - 0 = (x::(_,enat) acost)"
  apply(cases x)
  by(auto simp: zero_acost_def minus_acost_alt)

definition word_log22 where
  "word_log22 (w::'a::len2 word) = doN {
    w' \<leftarrow> SPECc2 ''sub'' (-) (snat_const TYPE('a::len2) (size w)) 1;
    wclz \<leftarrow> word_clz2 w;
    w'' \<leftarrow> SPECc2 ''sub'' (-) w' wclz;
    RETURN w''
    }"
abbreviation "word_log22_cost sw \<equiv> word_clz2_cost sw + cost ''sub'' 2"

lemma word_log22_correct:
  assumes "w>0" "LENGTH('a::len2)>2"
  shows "word_log22 w \<le> SPECT [word_log2 w \<mapsto> word_log22_cost (size w)]"
  unfolding word_log22_def
  unfolding SPECc2_def
  apply(rule gwp_specifies_I)

  using assms
  apply (refine_vcg \<open>-\<close> rules: word_clz2_refine[THEN gwp_specifies_rev_I, THEN gwp_conseq4])
  apply(auto simp: word_log2_def  word_clz'_def split: if_splits)
  apply(simp add: norm_cost needname_minus_absorb) 
  apply sc_solve by auto

(*

sepref_def word_log2_impl is 
  "word_log22" :: "[\<lambda>x. x>0 \<and> LENGTH('a)>2]\<^sub>a (word_assn' TYPE('a::len2))\<^sup>k \<rightarrow> snat_assn' TYPE('a)"
  unfolding word_log22_def word_size PR_CONST_def
  apply (annot_snat_const "TYPE('a)")
  supply [simp] = word_clz_nonzero_max'
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  by sepref  (* TODO: sepref *)

export_llvm "word_log2_impl :: 64 word \<Rightarrow> _"
*)
subsubsection \<open>Connection with \<^const>\<open>Discrete.log\<close>\<close>

lemma discrete_log_ltI: (* TODO: Check how precise this bound is! *)
  assumes "n\<noteq>0" "N\<noteq>0" "n<2^N"
  shows "Discrete.log n < N"
  using assms
  by (metis Discrete.log_le_iff leD linorder_neqE_nat log_exp log_exp2_le order_less_le zero_order(3))


lemma unat_x_div_2_conv:
  fixes x y :: "'a::len2 word"
  shows "unat x div 2 = unat y \<longleftrightarrow> y = x div 2"
proof -
  have A: "2 = unat (2::'a word)"
    by (metis le_less_trans len2_simps(2) n_less_equal_power_2 of_nat_numeral unat_of_nat_len)
  
  have B: "unat x div 2 = unat (x div 2)"
    unfolding A
    by (simp add: unat_div)

  show ?thesis  
    by (auto simp: B dest: word_unat.Rep_eqD)

qed    

lemma take_size_m1_to_bl:
  fixes x :: "'a::len word"
  shows "take (size x - Suc 0) (to_bl x) = butlast (to_bl x)"
  by (simp add: butlast_conv_take word_size_bl)
  
lemma takeWhile_butlast_eqI: "\<lbrakk>x\<in>set xs; \<not>P x\<rbrakk> \<Longrightarrow> takeWhile P (butlast xs) = takeWhile P xs"  
  by (metis append_Nil2 butlast.simps(2) butlast_append list.simps(3) split_list_last takeWhile_tail)

lemma takeWhile_butlast_eqI': "\<lbrakk>\<exists>x\<in>set xs. \<not>P x\<rbrakk> \<Longrightarrow> takeWhile P (butlast xs) = takeWhile P xs"  
  by (metis append_Nil2 butlast.simps(2) butlast_append list.simps(3) split_list_last takeWhile_tail)
  
  
lemma ex_True_in_set_conv: "(\<exists>x\<in>S. x) \<longleftrightarrow> True\<in>S" by auto  
  
lemma word_clz_rec: 
  fixes x :: "'a::len2 word" 
  shows "2\<le>x \<Longrightarrow> word_clz (x div 2) = word_clz x + 1"
  unfolding word_clz_def shiftr1_is_div_2[symmetric]
  apply (auto simp: bl_shiftr word_size)
  apply (subst bl_shiftr)
  apply (simp add: word_size Suc_leI)
  apply (auto simp: take_size_m1_to_bl)
  apply (subst takeWhile_butlast_eqI')
  apply (simp_all add: ex_True_in_set_conv)
  apply (rule ccontr)
  apply (simp only: eq_zero_set_bl[symmetric])
  by (metis le_unat_uoi len2_simps(2) n_less_equal_power_2 of_nat_numeral unat_0 unat_of_nat_len word_le_0_iff zero_neq_numeral)


lemma overflow_safe_hbound_check: "2*k\<le>n \<longleftrightarrow> k\<le>n div 2" for k n :: nat by auto

lemma word_clz_ge2_max: "2\<le>(x::'a::len2 word) \<Longrightarrow> word_clz x + 1 < size x"  
  apply (simp only: word_clz_rec[symmetric] word_size)
  apply (rule word_clz_nonzero_max[of "x div 2", unfolded word_size])
  by (smt One_nat_def Suc_pred add.left_neutral add.right_neutral add_diff_cancel_left' add_diff_cancel_right'
        add_left_cancel diff_Suc_Suc div_less div_of_0_id div_self lessI less_eq_Suc_le less_one linorder_neqE_nat
        linorder_not_le mult.right_neutral not_numeral_le_zero numeral_2_eq_2 numeral_One numeral_le_one_iff order_less_le
        overflow_safe_hbound_check pos2 power.simps(1) power.simps(2) semiring_norm(69) unat_0 unat_div unat_eq_zero unat_gt_0
        unat_x_div_2_conv word_clz_rec word_gt_0_no word_le_nat_alt zero_less_one zero_neq_one)
  
  
  
lemma word_log2_rec: 
  fixes x :: "'a::len2 word" shows "2\<le>x \<Longrightarrow> word_log2 x = Suc (word_log2 (x div 2))"
  apply (auto simp: word_log2_def word_size word_clz_rec)
  using word_clz_ge2_max[unfolded word_size, of x]
  by auto

lemma word_log2_is_discrete_log:
  fixes x :: "'a::len2 word"
  shows "word_log2 x = Discrete.log (unat x)"
  apply (cases "x=0")
  apply simp
  subgoal proof -
    assume "x \<noteq> 0"
    hence "unat x > 0" by (simp add: unat_gt_0)
    then show ?thesis
    proof (induction "unat x" arbitrary: x rule: log_induct)
      case one
      hence "x=1" using word_unat_Rep_inject1 by auto
      then show ?case 
        unfolding word_log2_def
        by (auto simp: word_size)  
      
    next
      case double
      
      from double.hyps(2) have "Discrete.log (unat x div 2) = word_log2 (x div 2)"
        by (metis unat_x_div_2_conv)
      
      then show ?case  
        apply (subst log_rec, simp add: \<open>2 \<le> unat x\<close>)
        apply simp
        apply (subst word_log2_rec)
        apply auto
        using double.hyps(1) le_unat_uoi word_le_nat_alt by fastforce
      
    qed
  qed
  done      

lemma word_log2_refine_unat: "(word_log2, Discrete.log) \<in> unat_rel' TYPE('a::len2) \<rightarrow> nat_rel"
  using word_log2_is_discrete_log
  by (fastforce simp: unat_rel_def unat.rel_def in_br_conv)
  
lemma word_log2_refine_snat: "(word_log2, Discrete.log) \<in> snat_rel' TYPE('a::len2) \<rightarrow> nat_rel"
  using word_log2_is_discrete_log
  by (fastforce simp: snat_rel_def snat.rel_def in_br_conv snat_eq_unat)



end
