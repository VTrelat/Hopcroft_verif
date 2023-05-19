theory Remdups
  imports
    NREST_Main
    Monadic_Operations
begin        



definition "rbt_search_time_logN = undefined"
definition "rbt_insert_logN = undefined"


definition "rd_inv as \<equiv> (\<lambda>(xs,ys,S). (\<exists>zs. as = zs@xs \<and> S = set ys \<and> distinct ys \<and> set zs = set ys))"

datatype RD_curr = RBT_search | RBT_insert | REST


instantiation RD_curr :: enum
begin
definition "enum_RD_curr = [RBT_search, RBT_insert, REST]"
definition "enum_all_RD_curr P = (P RBT_search \<and> P RBT_insert \<and> P REST)"
definition "enum_ex_RD_curr P = (P RBT_search \<or> P RBT_insert \<or> P REST)"
instance apply standard apply (auto simp: enum_RD_curr_def enum_ex_RD_curr_def enum_all_RD_curr_def)
  subgoal for x apply (cases x) by auto
  subgoal for P x apply (cases x) by auto  
  subgoal for P x apply (cases x) by auto  
  done
end


definition body_time :: "nat \<Rightarrow> (RD_curr,enat) acost" where                                           
  "body_time n = acostC ((\<lambda>_.0)(REST := 60, RBT_search := 1+rbt_search_time_logN (n+1), RBT_insert := rbt_insert_logN (n+1)))"
definition body_time_abs :: "(RD_curr,nat) acost" where 
  "body_time_abs = acostC ((\<lambda>_.0)(REST := 60, RBT_search := 1, RBT_insert := 1))"

definition "rd_ta as = (\<lambda>(xs,ys,S). acostC (\<lambda>x. enat (length xs) * the_acost (body_time (length as)) x) )"
definition "rd_ta_abs = (\<lambda>(xs,ys,S). acostC (\<lambda>x. (length xs) * the_acost body_time_abs x) )"

definition rd_impl1 :: "('a::{linorder}) list \<Rightarrow> ('a list, _ ) nrest" where
"rd_impl1 as = do {
  ys \<leftarrow> mop_empty_list (\<lambda>_. cost REST (12::enat));
  S \<leftarrow> mop_set_empty (\<lambda>_. cost REST 1);
  zs \<leftarrow> RETURNT as;
  (zs,ys,S) \<leftarrow> whileIET (rd_inv as) (rd_ta_abs) (\<lambda>(xs,ys,S). length xs > 0) (\<lambda>(xs,ys,S). do {                          
    ASSERT (length xs > 0);
    ASSERT (length xs + length ys \<le> length as);
    ASSERT (card S \<le> length ys);
    x \<leftarrow> RETURNT (hd xs);
    xs \<leftarrow> RETURNT (tl xs);
    b \<leftarrow> mop_set_member (\<lambda>_. cost RBT_search 1) x S;
    if b then
      RETURNT (xs,ys,S)
    else do {
      S \<leftarrow> mop_set_insert (\<lambda>_. cost RBT_insert 1 ) x S;
      ys \<leftarrow> mop_push_list (\<lambda>_. cost REST 23 ) x ys;  
      RETURNT (xs,ys,S)
    } 
  }) (zs,ys,S);
  RETURNT ys
  }"

abbreviation "skalar n ac \<equiv> acostC (\<lambda>x. n * the_acost ac x)"
abbreviation "skalare n ac \<equiv> acostC (\<lambda>x. enat n * the_acost ac x)"

definition "remdups_time (n::nat) = skalare n (body_time n) + cost REST 20"
definition "remdups_time_abs (n::nat) = skalar n body_time_abs + cost REST 20"

definition "remdups_spec_abs as = SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( lift_acost ( remdups_time_abs (length as)) ))"
definition "remdups_spec as = SPECT (emb (\<lambda>ys. set as = set ys \<and> distinct ys)
                   ( remdups_time (length as) ))"

fun RR where
  "RR n REST REST = (1::enat)"
| "RR n RBT_search RBT_search = 1+rbt_search_time_logN (n+1)"
| "RR n RBT_insert RBT_insert = rbt_insert_logN (n+1)"
| "RR n _ _  = 0" 

abbreviation "RR' n \<equiv> (\<lambda>x. acostC (\<lambda>y. RR n x y))"

lemma timerefine_SPECT_emb': 
  "timerefine F (SPECT (emb' P TT)) = SPECT (emb' P (\<lambda>r. acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost (TT r) ac * the_acost (F ac) cc))))"
  unfolding timerefine_def  apply auto
  unfolding emb'_def apply(rule ext) by simp


lemma "acostC a = acostC b \<longleftrightarrow> a = b"
  by simp 

lemma emb'_eqI: "P=P' \<Longrightarrow> X=X' \<Longrightarrow> emb' P X = emb' P' X'" unfolding emb'_def by auto
lemma finer: "remdups_spec as = timerefine (RR' (length as)) (remdups_spec_abs as)"
  unfolding remdups_spec_abs_def lift_acost_def apply(simp only: timerefine_SPECT_emb')
  unfolding remdups_spec_def apply simp
  apply(rule emb'_eqI) apply simp
  apply(rule ext)+
  apply(auto simp: remdups_time_def remdups_time_abs_def body_time_def body_time_abs_def)
  apply (simp_all add: Sum_any_to_foldr enum_RD_curr_def)
  apply (simp add: cost_def fun_eq_iff the_acost_zero_app)
  apply (auto simp: numeral_eq_enat  split: RD_curr.splits) 
  subgoal for x apply (cases x) by auto
  subgoal for x apply (cases x) by auto
  subgoal for x apply (cases x) by auto
  done
  
(*
lemma finer: "remdups_spec as = timerefine (RR' (length as)) (remdups_spec_abs as)"
  unfolding remdups_spec_def remdups_spec_abs_def timerefine_def
      remdups_time_def remdups_time_abs_def body_time_def body_time_abs_def
  apply auto apply(rule ext)
  unfolding emb'_def apply auto
  apply(rule ext) apply auto
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply simp
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply simp
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply simp
  apply (simp only: Sum_any_to_foldr enum_RD_curr_def) apply auto
  subgoal for r x apply (cases x) by auto
  subgoal for r x apply (cases x) by auto
  subgoal for r x apply (cases x) by auto
  done *)

lemma enat_neq_Z_iff[simp]: "enat x \<noteq> 0 \<longleftrightarrow> x\<noteq>0"
  by (auto simp: zero_enat_def)

lemma the_acost_cost: "the_acost (cost n c) x = (if n=x then c else 0)"
  unfolding cost_def by (auto simp: zero_acost_def) 

lemma rd_impl1_correct: "rd_impl1 as \<le> remdups_spec_abs as"
  unfolding remdups_spec_abs_def
  unfolding rd_impl1_def mop_empty_list_def mop_set_empty_def
      mop_set_member_def mop_set_insert_def mop_push_list_def
      rd_ta_abs_def rd_inv_def
  apply(rule gwp_specifies_I)
  apply (refine_vcg \<open>simp\<close> )  
  subgoal
    by(rule wfR2_enum) 
    unfolding Some_le_emb'_conv  
  supply [simp] = neq_Nil_conv distinct_length_le card_length
        apply (auto simp: less_eq_acost_def the_acost_cost the_acost_plus
              Some_le_mm3_Some_conv numeral_eq_enat lift_acost_def
          body_time_abs_def one_enat_def remdups_time_abs_def plus_enat_simps intro!: le_funI)
    subgoal      
      by (progress \<open>simp add: cost_def lift_acost_def less_acost_def the_acost_zero_app\<close>) 
    subgoal  
      by (meson list.set_cases)  
    done

end