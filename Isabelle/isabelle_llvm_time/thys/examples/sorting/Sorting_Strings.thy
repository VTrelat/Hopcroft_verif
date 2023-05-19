theory Sorting_Strings
  imports "HOL-Library.List_Lexorder" Sorting_Setup 
  "../dynarray/Dynamic_Array" 
begin

  text \<open>The string comparison algorithm from libstdc++, abstractly: Compare min-length first, then compare lengths to break tie\<close>
  lemma list_lexorder_alt: "xs < ys \<longleftrightarrow> (let n=min (length xs) (length ys) in (take n xs < take n ys) \<or> (take n xs = take n ys \<and> length xs < length ys))"
  proof (cases "length xs < length ys")
    case True
    then show ?thesis
      apply (simp add: Let_def)
    proof (induction xs arbitrary: ys)
      case Nil
      then show ?case by (cases ys) auto 
    next
      case (Cons a xs)
      then show ?case by (cases ys) auto
    qed
  next
    case False
    then show ?thesis
      apply (simp add: Let_def)
    proof (induction xs arbitrary: ys)
      case Nil
      then show ?case by (cases ys) auto 
    next
      case (Cons a xs)
      then show ?case by (cases ys) auto
    qed
  qed
    
    
  definition cmpi :: "'a::preorder \<Rightarrow> 'a \<Rightarrow> int" where "cmpi x y \<equiv> if x = y then 0 else if x < y then -1 else (1::int)"
  
  lemma cmpi_simps[simp]: 
    "cmpi x y = 0 \<longleftrightarrow> x=y"
    "cmpi x y = -1 \<longleftrightarrow> x<y"
    "cmpi x y = 1 \<longleftrightarrow> x\<noteq>y \<and> (\<not>x<y)"
    "0 = cmpi x y \<longleftrightarrow> x=y"
    "-1 = cmpi x y \<longleftrightarrow> x<y"
    "1 = cmpi x y \<longleftrightarrow> x\<noteq>y \<and> (\<not>x<y)"
    "x=y \<Longrightarrow> cmpi x y = 0"
    "x<y \<Longrightarrow> cmpi x y = -1"
    unfolding cmpi_def by auto

 
  term "m *m e"
(*  definition "compare_cost xs ys n = (enat n) *m (cost ''ult_lt'' 1 
              + lift_acost mop_array_nth_cost + lift_acost mop_array_nth_cost 
              + cost ''ult_eq'' 1 + cost ''ult_add'' 1)"
*)              

  definition "compare1_body_cost :: (char list, nat) acost \<equiv> 
      cost ''add'' 1 +
        (cost ''call'' 1 +
         (cost ''icmp_eq'' 2 +
          (cost ''icmp_slt'' 1 +
            (cost ''icmp_ult'' 1 +
           (cost ''if'' 4 +
            (cost ''load'' 2 + (cost ''ofs_ptr'' 2)))))))"

  definition "compare_cost n = 
    (n *m compare1_body_cost ) +
        (cost ''if'' 1 + cost ''icmp_slt'' 1 + cost ''icmp_eq'' 1 + cost ''if'' 1 + cost ''call'' 1)"
  
  definition "compare_spec xs ys n \<equiv> doN {ASSERT (n\<le>length xs \<and> n\<le>length ys); SPECT [ (cmpi (take n xs) (take n ys)) \<mapsto> lift_acost (compare_cost n)]}"

  
  definition "compare1 xs ys n \<equiv> doN {
    ASSERT (n\<le>length xs \<and> n\<le>length ys);
    (i,r)\<leftarrow> monadic_WHILEIET (\<lambda>(i,r). i\<le>n \<and> r=cmpi (take i xs) (take i ys) )
        (\<lambda>(i::nat,r::int). (n-i) *m (compare1_body_cost))
       (\<lambda>(i,r).doN { 
              if\<^sub>N SPECc2 ''icmp_slt'' (<) i n 
                then SPECc2 ''icmp_eq'' (=) r 0
                else RETURNT False
            } )
       (\<lambda>(i,r). doN {
      x \<leftarrow> mop_array_nth xs i;
      y \<leftarrow> mop_array_nth ys i;
      ASSERT (i<n);
      if\<^sub>N SPECc2 ''icmp_eq'' (=) x y
        then doN {
            i' \<leftarrow> SPECc2 ''add'' (+) i 1;
            RETURNT (i',0) }
      else if\<^sub>N SPECc2 ''icmp_ult'' (<) x y then doN {
            i' \<leftarrow> SPECc2 ''add'' (+) i 1;
            RETURNT (i',-1) }
      else doN {
            i' \<leftarrow> SPECc2 ''add'' (+) i 1;
            RETURNT (i',1) }
    }) (0,0);
    RETURN r
  }"

  (* TODO: fix type of monadic_WHILEIET *)


  (* TODO: Move *)    
  lemma irreflD: "irrefl R \<Longrightarrow> (x,x)\<notin>R" by (auto simp: irrefl_def) 
  
  (* TODO: Move *)
  lemma lexord_append: "length u = length w \<Longrightarrow> (u@v,w@x)\<in>lexord R \<longleftrightarrow> (u,w)\<in>lexord R \<or> (u=w \<and> (v,x)\<in>lexord R)"  
    by (induction u w rule: list_induct2) auto

  lemma lexord_irreflD: "irrefl R \<Longrightarrow> \<not>(u,u)\<in>lexord R"
    by (simp add: irreflD lexord_irrefl) 
    
  lemma lexord_irrefl_common_prefix: "irrefl R \<Longrightarrow> (u@v,u@w)\<in>lexord R \<longleftrightarrow> (v,w)\<in>lexord R"
    by (auto simp: lexord_append lexord_irreflD)
    
  (* TODO: Move, TODO: simp-lemma! *)  
  lemma lift_acost_le_iff: "lift_acost A \<le> lift_acost B \<longleftrightarrow> A\<le>B"  
    by (meson lift_acost_mono lift_acost_mono')
    
  (* TODO: Move *)  
  lemma finite_the_acost_cost[simp]: "finite {n. 0 < the_acost (cost nx (c::_::order)) n}"  
    by (auto simp: cost_def zero_acost_def)
    
  (* TODO: Move *)  
  declare the_acost_zero_app[simp]    
    
  lemma cost_mono': "(x::_::needname_zero)\<le>y \<Longrightarrow> cost n x \<le> cost n y"
    by(auto simp: cost_def less_eq_acost_def)
  
  lemma same_cost_add_mono: "c\<le>c' \<Longrightarrow> x\<le>x' \<Longrightarrow> cost n c + x \<le> cost n c' + x'" for c :: "'a::{needname_zero}"
    apply (rule add_mono)
    apply (rule cost_mono')
    . 
  
  lemma diff_cost_drop: "x \<le> x' \<Longrightarrow> x \<le> cost n' c' + x'" for c' :: "'a::{needname_zero}" 
    by (simp add: add_increasing needname_nonneg)
    
  
  
  context begin
    private lemma take_smaller: "m\<le>n \<Longrightarrow> take n xs = take m xs @ (take (n-m) (drop m xs))"
      by (metis le_add_diff_inverse take_add)
      
    private lemma compare_impl_aux1:  "\<lbrakk>aa\<le>n; aa \<le> length xs; aa\<le>length ys; take aa xs \<noteq> take aa ys\<rbrakk> \<Longrightarrow> cmpi (take n xs) (take n ys) = cmpi (take aa xs) (take aa ys)"  
      by (auto simp: take_smaller cmpi_def list_less_def lexord_append)
    
    private lemma preorder_less_irrefl: "irrefl {(x, y::_::preorder). x < y}" by (auto simp: irrefl_def) 
      
    lemma compare1_refine: "(compare1, compare_spec) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel" (*
      apply (intro fun_relI, clarsimp)
      subgoal for xs ys n
        unfolding compare1_def compare_spec_def
        apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). n-i)"])
        by (auto simp: take_Suc_conv_app_nth list_less_def lexord_append compare_impl_aux1 lexord_irreflD[OF preorder_less_irrefl])
      done *)      
      apply(intro fun_relI nrest_relI)
      unfolding compare_spec_def 
      unfolding compare1_def
      unfolding SPECc2_def
      unfolding mop_array_nth_def
      apply(rule ASSERT_D2_leI)
      apply simp
      apply(rule gwp_specifies_I)
      apply(refine_vcg \<open>(simp; fail)?\<close> rules: gwp_monadic_WHILEIET If_le_rule)
      subgoal by (auto simp: wfR2_def norm_cost compare1_body_cost_def)
      subgoal 
        apply(rule loop_body_conditionI)
        subgoal by (auto intro!: costmult_right_mono simp: lift_acost_le_iff)
        subgoal
          unfolding compare1_body_cost_def
          apply (auto simp: norm_cost)
          apply sc_solve
          apply (auto simp: one_enat_def algebra_simps numeral_eq_enat) 
          done
        subgoal 
          apply auto
          by (metis less_le_trans take_Suc_conv_app_nth)
        done
      subgoal 
        apply(rule loop_body_conditionI)
        subgoal by (auto intro!: costmult_right_mono simp: lift_acost_le_iff)
        subgoal
          unfolding compare1_body_cost_def
          apply (auto simp: norm_cost)
          apply sc_solve
          apply (auto simp: one_enat_def algebra_simps numeral_eq_enat) 
          done
        subgoal 
          by (auto simp: take_Suc_conv_app_nth list_less_def lexord_append)
        done  
      subgoal 
        apply(rule loop_body_conditionI)
        subgoal by (auto intro!: costmult_right_mono simp: lift_acost_le_iff)
        subgoal
          unfolding compare1_body_cost_def
          apply (auto simp: norm_cost)
          apply sc_solve
          apply (auto simp: one_enat_def algebra_simps numeral_eq_enat) 
          done
        subgoal 
          by (auto simp: take_Suc_conv_app_nth list_less_def lexord_append compare_impl_aux1 lexord_irreflD[OF preorder_less_irrefl])
        done
      subgoal 
        apply(rule loop_exit_conditionI)
        apply (refine_vcg \<open>-\<close>)
        apply (auto)
        apply (smt (z3) compare_impl_aux1 dual_order.trans nat_less_le)
        unfolding compare_cost_def
        apply (subst costmult_minus_distrib)
        by (simp add: Dynamic_Array.costmult_right_mono add_right_mono lift_acost_cost lift_acost_mono norm_cost(3) one_enat_def)
      subgoal 
        apply(rule loop_exit_conditionI)
        apply (refine_vcg \<open>-\<close>)
        apply (auto)
        unfolding compare_cost_def
        apply (auto simp: norm_cost one_enat_def algebra_simps)
        apply summarize_same_cost
        (* TODO: Use to build general solver for such inequations! *)
        apply (intro cost_mono' same_cost_add_mono order_refl | rule diff_cost_drop)+
        done
      done  
      
  end


  abbreviation "string_assn' TYPE('size_t::len2) TYPE('w::len) \<equiv> al_assn' TYPE('size_t::len2) (unat_assn' TYPE('w::len))"


  sepref_definition compare_impl2 [llvm_inline, llvm_code] is "uncurry2 compare1" :: 
    "[\<lambda>_. 8\<le>LENGTH('size_t::len2)]\<^sub>a (string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k *\<^sub>a (snat_assn' TYPE('size_t))\<^sup>k \<rightarrow> sint_assn' TYPE('r::len2)"  
    unfolding compare1_def
    unfolding monadic_WHILEIET_def
    apply (annot_snat_const "TYPE('size_t)")
    apply (annot_sint_const "TYPE('r)")
    by sepref 

  term b_assn
  term nbn_assn

definition "bstring_assn n TYPE('size_t::len2) TYPE('w::len)
       = b_assn (string_assn' TYPE('size_t::len2) TYPE('w::len)) (\<lambda>ls. length ls \<le> n)"


  
find_theorems hr_comp b_rel  
  
(* TODO: Move *)
lemma hr_comp_brel[fcomp_norm_simps]: "hr_comp A (b_rel B P) = b_assn (hr_comp A B) P"
  by (auto simp: hr_comp_def fun_eq_iff sep_algebra_simps pred_lift_extract_simps)

  
lemma mop_array_nth_len_bound:
  fixes nth_impl A B
  assumes "(uncurry nth_impl, uncurry mop_array_nth) \<in> [Q]\<^sub>a A\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> B"
  shows "(uncurry nth_impl, uncurry mop_array_nth) \<in> [Q]\<^sub>a (b_assn A P)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> B"
proof -
  have A: "(mop_array_nth, mop_array_nth) \<in> b_rel Id P \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    by (auto simp add: refine_pw_simps fun_rel_def pw_acost_nrest_rel_iff)
    
  from assms(1)[FCOMP A[to_fref]] show ?thesis by simp
qed    
    
lemma mop_array_upd_len_bound:
  fixes upd_impl A B
  assumes "(uncurry2 upd_impl, uncurry2 mop_array_upd) \<in> [Q]\<^sub>a A\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> A"
  shows "(uncurry2 upd_impl, uncurry2 mop_array_upd) \<in> [Q]\<^sub>a (b_assn A (\<lambda>xs. P (length xs)))\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> (b_assn A (\<lambda>xs. P (length xs)))"
proof -
  have A: "(mop_array_upd, mop_array_upd) \<in> b_rel Id (\<lambda>xs. P (length xs)) \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>b_rel Id (\<lambda>xs. P (length xs))\<rangle>nrest_rel"
    by (auto simp add: refine_pw_simps fun_rel_def pw_acost_nrest_rel_iff mop_array_upd_def)

  have *: "(\<lambda>((a, b), ba). Q ((a, b), ba)) = Q" by auto
  from assms(1)[FCOMP A[to_fref]] show ?thesis unfolding * .
qed    

lemma bstring_nth[sepref_fr_rules]:
  "(uncurry dyn_array_nth_impl, uncurry mop_array_nth)
     \<in> [\<lambda>_. 8\<le>LENGTH('size_t::len2)]\<^sub>a (bstring_assn n TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('w::len)" 
  unfolding bstring_assn_def    
  apply (rule mop_array_nth_len_bound)
  apply (rule dyn_array_nth[of unat_assn]) (* TODO: delete of dyn_array_nth when rule is complete *)
  by simp
  
  (*
  sepref_definition compare_impl [llvm_inline, llvm_code] is "uncurry2 compare1" :: 
    "[\<lambda>_. 8<LENGTH('size_t::len2)]\<^sub>a 
      (bstring_assn n TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (bstring_assn n TYPE('size_t) TYPE('w))\<^sup>k *\<^sub>a (snat_assn' TYPE('size_t))\<^sup>k
       \<rightarrow> sint_assn' TYPE('r::len2)"  
    unfolding compare1_def
    unfolding monadic_WHILEIET_def 
    apply (annot_snat_const "TYPE('size_t)")
    apply (annot_sint_const "TYPE('r) ")
    by sepref 
  *)
     
  lemmas compare_hnr[sepref_fr_rules] = compare_impl2.refine[FCOMP compare1_refine]
  
  find_theorems "(+)" hn_refine
  
  definition min_cost :: "(char list, nat) acost" where "min_cost \<equiv> cost ''if'' 1 + cost ''icmp_slt'' 1"
  
  definition min1 :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder, ecost) nrest" 
    where "min1 a b \<equiv> if\<^sub>N SPECc2 ''icmp_slt'' (<) a b then RETURNT a else RETURNT b"
  
  lemma min_refine1: "min1 a b \<le> SPECT [min a b \<mapsto> lift_acost min_cost]"
    unfolding min1_def
    apply(rule gwp_specifies_I)
    apply (refine_vcg \<open>-\<close> rules: gwp_SPECc2)
    unfolding min_cost_def
    apply (auto simp: norm_cost one_enat_def)
    done

  sepref_def min_impl is "uncurry min1" :: "(snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l::len2)"
    unfolding min1_def
    by sepref
    

  abbreviation "icmp_eq x y \<equiv> SPECc2 ''icmp_eq'' (=) x y"
  abbreviation "icmp_ult x y \<equiv> SPECc2 ''icmp_ult'' (<) x y"
  abbreviation "icmp_slt x y \<equiv> SPECc2 ''icmp_slt'' (<) x y"
    
  term mop_list_get
  
  definition "strcmp xs ys \<equiv> doN {
    lx \<leftarrow> mop_list_length xs;
    ly \<leftarrow> mop_list_length ys;
    n \<leftarrow> min1 lx ly;
    i \<leftarrow> compare_spec xs ys n;
    if\<^sub>N icmp_eq i (-1) then RETURNT True
    else if\<^sub>N icmp_eq i 0 then icmp_slt lx ly
    else RETURNT False
  }"

  thm gwp_specifies_rev_I[OF min_refine1]

  definition "strcmp_cost lxs lys = cost ''if'' 2 + (min_cost + compare_cost (min lxs lys) + cost ''icmp_eq'' 2 + cost ''icmp_slt'' 1)"

  (* TODO: Move *)
  lemma zero_minus_acost_eq_zero[simp]: "(0::ecost) - x = 0"
    by(cases x; auto simp: zero_acost_def minus_acost_alt)

  lemma strcmp_correct: "strcmp xs ys \<le> SPECT [xs<ys \<mapsto> lift_acost (strcmp_cost (length xs) (length ys))]"  
    unfolding strcmp_def compare_spec_def mop_list_length_def
    apply (rewrite in "_ \<le> \<hole>" list_lexorder_alt)
    apply(rule gwp_specifies_I)

    
    apply (refine_vcg simp rules: gwp_SPECc2 
      \<comment> \<open>TODO: put these things in preprocessor for rules!\<close>
      gwp_specifies_rev_I[OF min_refine1, THEN gwp_conseq4]
    )

       apply (auto simp: Let_def split: if_splits)
    unfolding strcmp_cost_def
        apply (auto simp: algebra_simps)
    subgoal
      apply(auto simp: min_cost_def compare_cost_def compare1_body_cost_def norm_cost one_enat_def)
      apply(sc_solve) by auto
    subgoal   
      apply(auto simp: min_cost_def compare_cost_def compare1_body_cost_def norm_cost one_enat_def)
      apply(sc_solve) by auto
        (* alternative: 
            apply(summarize_same_cost) then use bohua's component in Imperative-HOL-Time *)
    subgoal   
      apply(auto simp: min_cost_def compare_cost_def compare1_body_cost_def norm_cost one_enat_def)
      apply(sc_solve) by auto
    done
     
    
  lemma strcmp_refines_aux: "(strcmp,\<lambda>xs ys. SPECT [xs<ys \<mapsto> lift_acost (strcmp_cost (length xs) (length ys))]) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    using strcmp_correct apply (auto intro!: nrest_relI) by blast

      
    
  lemma strcmp_cost_mono: "\<lbrakk>N' \<le> N; M' \<le> M\<rbrakk> \<Longrightarrow> strcmp_cost N' M' \<le> strcmp_cost N M"
    unfolding strcmp_cost_def min_def compare_cost_def
    apply clarsimp
    by (smt (verit) Dynamic_Array.costmult_right_mono add_left_mono add_mono_thms_linordered_semiring(3) dual_order.trans lift_acost_le_iff nat_le_linear norm_cost(3))
    
  (* hier passiert die überabschätzung *)
  lemma strcmp_refines_aux2: "(\<lambda>xs ys. SPECT [xs<ys \<mapsto> lift_acost (strcmp_cost (length xs) (length ys))],\<lambda>xs ys. SPECT [xs<ys \<mapsto> lift_acost (strcmp_cost N N)]) 
    \<in> b_rel Id (\<lambda>xs. length xs \<le> N) \<rightarrow> b_rel Id (\<lambda>xs. length xs \<le> N) \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    apply (auto simp: pw_acost_nrest_rel_iff refine_pw_simps)
    apply (erule order_trans)
    apply (rule the_acost_mono)
    by (auto intro: strcmp_cost_mono lift_acost_mono)
    
    
    
    
  find_theorems compare_spec
  
  sepref_def strcmp_impl is "uncurry strcmp" 
    :: "[\<lambda>_. 8\<le>LENGTH('size_t)]\<^sub>a (string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k \<rightarrow> bool1_assn"
    unfolding strcmp_def min_def 
    apply (annot_sint_const "TYPE(2)")
    by sepref
   
definition "mop_str_cmp N = (\<lambda>xs ys.  (SPECT [xs < ys \<mapsto> lift_acost (strcmp_cost N N)]))"

context
  fixes N :: nat
begin
  sepref_register "mop_str_cmp N"
end

  lemma strcmp_impl_refine'[sepref_fr_rules]: 
    "(uncurry strcmp_impl, uncurry (PR_CONST (mop_str_cmp N)))
    \<in> [\<lambda>b. 8 \<le> LENGTH('size_t::len2)]\<^sub>a (bstring_assn N TYPE('size_t) TYPE('w::len))\<^sup>k *\<^sub>a (bstring_assn N TYPE('size_t) TYPE('w))\<^sup>k \<rightarrow> bool1_assn"
    unfolding PR_CONST_def mop_str_cmp_def
    using strcmp_impl.refine[FCOMP strcmp_refines_aux,FCOMP strcmp_refines_aux2, folded bstring_assn_def, of N]
    .
    
  (* TODO: Move! *)  
  lemmas [llvm_inline] = dyn_array_nth_impl_def dyn_array_length_impl_def 
  
  lemmas [llvm_inline] = min_impl_def 
    
  export_llvm "strcmp_impl :: 8 word ptr \<times> 64 word \<times> 64 word \<Rightarrow> 8 word ptr \<times> 64 word \<times> 64 word \<Rightarrow> 1 word llM"


(* TEST
 strcmp_impl_def

definition [llvm_code]: "foo xs ys = ll_call (strcmp_impl xs ys)"


  export_llvm "foo :: 8 word ptr \<times> 64 word \<times> 64 word \<Rightarrow> 8 word ptr \<times> 64 word \<times> 64 word \<Rightarrow> 1 word llM"
 *)

definition "strcmp_cost' m = strcmp_cost m m + cost ''call'' 1" 


definition "mop_str_cmp' N = (\<lambda>xs ys. (mop_call (mop_str_cmp N xs ys)))"

context
  fixes N :: nat
begin
  sepref_register "mop_str_cmp' N"
end

  sepref_def strcmp_impl' is "uncurry (PR_CONST (mop_str_cmp' N)) " 
    :: "[\<lambda>_. 8\<le>LENGTH('size_t::len2)]\<^sub>a (bstring_assn N TYPE('size_t) TYPE('w::len))\<^sup>k *\<^sub>a (bstring_assn N TYPE('size_t) TYPE('w))\<^sup>k \<rightarrow> bool1_assn"
    unfolding strcmp_def min_def  mop_str_cmp'_def PR_CONST_def
    by sepref

lemmas [llvm_inline] = strcmp_impl'_def

thm strcmp_impl'.refine
lemma consume_SPEC_map: "NREST.consume (SPECT [x \<mapsto> T]) t = SPECT [x \<mapsto> t+T]"
  unfolding consume_def by auto

lemma strcmp_refines_relp_aux: "PR_CONST (mop_str_cmp' n) = (\<lambda>a b. SPECT [a < b \<mapsto> lift_acost (strcmp_cost' n)])"
  unfolding mop_str_cmp'_def strcmp_cost'_def PR_CONST_def mop_call_def mop_str_cmp_def
  by(auto simp: consume_SPEC_map norm_cost one_enat_def algebra_simps intro!: ext)


lemma strcmp_refines_relp: "8 \<le> LENGTH('size_t::len2) \<Longrightarrow> GEN_ALGO strcmp_impl' (refines_relp (bstring_assn n TYPE('size_t::len2) TYPE('w::len2))
                    (lift_acost (strcmp_cost' n)) (<))"
    apply rule
    using strcmp_impl'.refine[of n, where 'b='size_t] 
    unfolding SPECc3_def strcmp_refines_relp_aux
    by simp
 
lemma the_acost_apply_neq[simp]: "n\<noteq>n' \<Longrightarrow> the_acost (cost n c) n' = 0"
  unfolding the_acost_def apply (auto split: simp: cost_def) done
    
(* TODO: Dup, also in Heapsort. JOIN! *)  
lemma the_acost_mult_eq_z_iff: "the_acost (n *m c) a = 0 \<longleftrightarrow> the_acost c a = 0 \<or> n=0" for n :: nat 
  apply (cases c)
  apply (auto simp: costmult_def)
  done
  
(* TODO: Dup, also in Heapsort. JOIN! *)  
lemma finite_the_acost_mult_nonzeroI: "finite {a. the_acost c a \<noteq> 0} \<Longrightarrow> finite {a. the_acost (n *m c) a \<noteq> 0}" for n :: nat 
  apply (erule finite_subset[rotated])
  by (auto simp: the_acost_mult_eq_z_iff)
  
  
lemma strcmp_sort_impl_context: "8 \<le> LENGTH('size_t::len2) \<Longrightarrow> sort_impl_context TYPE('size_t) (\<le>) (<)
           strcmp_impl'  (strcmp_cost' n)
               (bstring_assn n TYPE('size_t) TYPE('w::len2))"
    apply unfold_locales
    apply (auto simp: strcmp_refines_relp) [10]
  subgoal by   (auto simp: strcmp_cost'_def  strcmp_cost_def min_cost_def compare_cost_def norm_cost compare1_body_cost_def)
    subgoal by (auto simp: strcmp_cost'_def strcmp_cost_def min_cost_def compare_cost_def norm_cost compare1_body_cost_def)
    subgoal
      unfolding strcmp_cost'_def strcmp_cost_def min_cost_def compare_cost_def compare1_body_cost_def
      apply(simp only: add.assoc norm_cost)  
      (* TODO: Solver for these equations. See DUPs in Heapsort, Introsort *)
      supply acost_finiteIs = finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero finite_the_acost_mult_nonzeroI
      apply ((intro acost_finiteIs))+
      done
  done    
  
end
