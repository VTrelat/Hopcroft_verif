(*  Title:       Presburger Example Implementation
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

header {* Presburger Automata Implementation *}

theory RBT_Presburger_Impl
imports Main 
        "../../../Presburger_Adapt"
        RBT_NFAImpl
        
begin

instantiation "bool" :: linorder
begin
  instance by (intro_classes, auto)
end

definition lexord_lexord_less where
  "lexord_lexord_less (l1::('a::linorder) list) l2 = ((l1, l2) \<in> lexord {(x,y) |x y. x < y})"
 
definition lexord_lexord_less_eq where
  "lexord_lexord_less_eq l1 l2 \<longleftrightarrow> (lexord_lexord_less l1 l2) \<or> (l1 = l2)"

lemma [simp] : "lexord_lexord_less_eq l l" unfolding lexord_lexord_less_eq_def by simp

lemma lexord_lexord_less_irreflexive [simp] : "\<not>(lexord_lexord_less l l)"
proof -
  have R_irreflexive: "\<forall>x. (x::('a::linorder), x) \<notin> {(x,y) |x y. x < y}"
    by simp
  note this_irrefl = lexord_irreflexive [OF R_irreflexive]

  thus ?thesis unfolding lexord_lexord_less_def by simp
qed

lemma lexord_lexord_less_trans :
assumes l1_l2_less: "lexord_lexord_less l1 l2"
    and l2_l3_less: "lexord_lexord_less l2 l3" 
shows "lexord_lexord_less l1 l3"
proof -
  have R_trans : "trans {(x::('a::linorder),y) |x y. x < y}" unfolding trans_def by auto
  note this_trans = lexord_trans [OF _ _ R_trans]

  with l1_l2_less l2_l3_less show ?thesis
    unfolding lexord_lexord_less_def by blast
qed

lemma lexord_lexord_less_linear :
shows "lexord_lexord_less l1 l2 \<or> (l1 = l2) \<or> lexord_lexord_less l2 l1"
proof -
  def R \<equiv> "{(x::('a::linorder),y::'a). x < y}"
  have R_linear : "\<forall>a b. (a, b) \<in> R \<or> a = b \<or> (b, a) \<in> R"
    unfolding R_def trans_def by auto
  note this_linear = lexord_linear[OF R_linear]
  thus ?thesis
    unfolding lexord_lexord_less_def unfolding R_def by simp
qed

lemma lexord_lexord_less_eval [simp, code] :
  "lexord_lexord_less [] [] = False"
  "lexord_lexord_less [] (y # ys) = True"
  "lexord_lexord_less (x # xs) [] = False" 
  "lexord_lexord_less (x # xs) (y # ys) = 
    (if (x < y) then True else
    (if (x = y) then lexord_lexord_less xs ys else False))"
unfolding lexord_lexord_less_def by simp_all

lemma lexord_lexord_less_eq_eval [simp, code] :
  "lexord_lexord_less_eq [] [] = True"
  "lexord_lexord_less_eq [] (y # ys) = True"
  "lexord_lexord_less_eq (x # xs) [] = False" 
  "lexord_lexord_less_eq (x # xs) (y # ys) = 
    (if (x < y) then True else
    (if (x = y) then lexord_lexord_less_eq xs ys else False))"
unfolding lexord_lexord_less_eq_def by simp_all

instantiation "list" :: (linorder) linorder
begin

  definition [simp] : "less (l1::'a list) (l2::'a list) == lexord_lexord_less l1 l2"
  definition [simp] : "less_eq (l1::'a list) l2 == lexord_lexord_less_eq l1 l2"

  instance proof (intro_classes)
    fix xs :: "'a list"
    show "xs \<le> xs" by (auto simp add: lexord_lexord_less_eq_def)
  next
    fix xs :: "'a list" 
    fix ys :: "'a list"
    show "(xs < ys) = (xs \<le> ys \<and> \<not> ys \<le> xs)" 
      apply (auto simp add: lexord_lexord_less_eq_def)
      apply (metis lexord_lexord_less_trans lexord_lexord_less_irreflexive)
    done

    show "xs \<le> ys \<or> ys \<le> xs"
      apply (simp add: lexord_lexord_less_eq_def)
      apply (metis lexord_lexord_less_linear)
    done

    {
      assume "xs \<le> ys" "ys \<le> xs"
      thus "xs = ys"
        apply (simp add: lexord_lexord_less_eq_def)
        apply (metis lexord_lexord_less_trans lexord_lexord_less_irreflexive)
      done
    }

    {
      fix zs
      assume "xs \<le> ys" "ys \<le> zs"
      thus "xs \<le> zs"
        apply (simp add: lexord_lexord_less_eq_def)
        apply (metis lexord_lexord_less_trans)
      done
    }
  qed
end

interpretation label_set!: presburger_label_set_cache_by_map_set rs_ops rm_ops rs_image
  by (simp add: presburger_label_set_cache_by_map_set_def
                rs_ops_unfold rs_image_impl rsr.StdSet_axioms rmr.StdMap_axioms)

lemmas set_cache_impl = label_set.presburger_label_set_cache_OK

interpretation rs_pres! : 
  presburger_locale rs_\<alpha> rm_invar rm_empty 
    "presburger_label_set_cache_by_map_set.c_\<alpha> rs_ops rm_ops rs_image"
    "presburger_label_set_cache_by_map_set.c_invar rs_ops rm_ops" rs_nfa_ops rs_dfa_construct_reachable_fun 
    "rs_nfa_rename_labels_gen False"
using presburger_locale.intro [OF rs_nfa_StdNFA_impl set_cache_impl,
   unfolded rs_nfa_ops_unfold rs_ops_unfold rm_ops_unfold, 
   OF rs_dfa_construct_reachable_no_enc_fun_impl
      rs_nfa_rename_labels_gen_impl]
by simp


definition "rs_cache_\<alpha> \<equiv> label_set.c_\<alpha>"
declare label_set.c_\<alpha>.simps [folded rs_cache_\<alpha>_def, code]

definition "rs_DFA_eq_ineq \<equiv> rs_pres.pres_DFA_eq_ineq_impl"
declare rs_pres.pres_DFA_eq_ineq_impl_def[folded rs_DFA_eq_ineq_def, code]

definition "rs_pres_nfa_of_pf \<equiv> rs_pres.nfa_of_pf"
declare rs_pres.nfa_of_pf.simps [folded rs_pres_nfa_of_pf_def rs_cache_\<alpha>_def rs_DFA_eq_ineq_def,
   unfolded rs_pres.pres_DFA_forall_min_impl_def rs_pres.pres_DFA_exists_min_impl_def, code]

definition rs_pres_pf_to_nfa :: "nat \<Rightarrow> pf \<Rightarrow> (bool list) rs_nfa" where
"rs_pres_pf_to_nfa \<equiv> rs_pres.pf_to_nfa"

lemma [code]: "rs_pres_pf_to_nfa n pf = fst (rs_pres_nfa_of_pf n pf (rm_empty ()))"
by (simp add: rs_pres_pf_to_nfa_def rs_pres.pf_to_nfa_def rs_pres_nfa_of_pf_def)

definition rs_eval_pf where
  "rs_eval_pf pf = rs_nfa_accept (rs_pres_pf_to_nfa 0 pf) []" 

definition eval_pf_dfa where
  "eval_pf_dfa pf = dfa_accepts (dfa_of_pf' 0 pf) []" 

lemma rs_eval_pf_correct :
  "rs_eval_pf pf = (eval_pf pf [])"
using rs_pres.eval_pf_impl[of pf,symmetric]
by (simp add: rs_eval_pf_def rs_nfa_ops_unfold rs_pres_pf_to_nfa_def)

lemma rs_eval_pf_correct2 :
  "eval_pf_dfa pf = rs_eval_pf pf"
unfolding rs_eval_pf_correct eval_pf_dfa_def
using dfa_of_pf'_correctness [of 0 "[]" pf]
by simp

end
