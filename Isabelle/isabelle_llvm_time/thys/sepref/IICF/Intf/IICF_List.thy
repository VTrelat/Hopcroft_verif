theory IICF_List
imports 
  "../../Sepref"
  "List-Index.List_Index"
begin

lemma param_index[param]: 
  "\<lbrakk>single_valued A; single_valued (A\<inverse>)\<rbrakk> \<Longrightarrow> (index,index) \<in> \<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel"
  unfolding index_def[abs_def] find_index_def 
  apply (subgoal_tac "(((=), (=)) \<in> A \<rightarrow> A \<rightarrow> bool_rel)")
  apply parametricity
  by (simp add: pres_eq_iff_svb)


(* TODO: Move? *)

lemma swap_param[param]: "\<lbrakk> i<length l; j<length l; (l',l)\<in>\<langle>A\<rangle>list_rel; (i',i)\<in>nat_rel; (j',j)\<in>nat_rel\<rbrakk>
  \<Longrightarrow> (swap l' i' j', swap l i j)\<in>\<langle>A\<rangle>list_rel"
  unfolding swap_def
  by parametricity

lemma swap_param_fref: "(uncurry2 swap,uncurry2 swap) \<in> 
  [\<lambda>((l,i),j). i<length l \<and> j<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>A\<rangle>list_rel"
  apply rule apply clarsimp
  unfolding swap_def
  apply parametricity
  by simp_all

lemma param_list_null[param]: "(List.null,List.null) \<in> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
proof -
  have 1: "List.null = (\<lambda>[] \<Rightarrow> True | _ \<Rightarrow> False)" 
    apply (rule ext) subgoal for l by (cases l) (auto simp: List.null_def)
    done 
  show ?thesis unfolding 1 by parametricity
qed

subsection \<open>Operations\<close>

find_theorems INTF_OF_REL


sepref_decl_op list_empty: "[]" :: "\<langle>A\<rangle>list_rel" .
context notes [simp] = eq_Nil_null begin
  sepref_decl_op list_is_empty: "\<lambda>l. l=[]" :: "\<langle>A\<rangle>list_rel \<rightarrow>\<^sub>f bool_rel" .
end
  
sepref_decl_op list_replicate: replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .


definition op_list_copy :: "'a list \<Rightarrow> 'a list" where [simp]:  "op_list_copy l \<equiv> l"
sepref_decl_op (no_def) list_copy: "op_list_copy" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_prepend: "(#)" :: "A \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_append: "\<lambda>xs x. xs@[x]" :: "\<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_concat: "(@)" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_take: take :: "[\<lambda>(i,l). i\<le>length l]\<^sub>f nat_rel \<times>\<^sub>r \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_drop: drop :: "[\<lambda>(i,l). i\<le>length l]\<^sub>f nat_rel \<times>\<^sub>r \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_length: length :: "\<langle>A\<rangle>list_rel \<rightarrow> nat_rel" .
sepref_decl_op list_get: nth :: "[\<lambda>(l,i). i<length l]\<^sub>f \<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> A" .
sepref_decl_op list_set: list_update :: "[\<lambda>((l,i),_). i<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r A \<rightarrow> \<langle>A\<rangle>list_rel" .
context notes [simp] = eq_Nil_null begin
  sepref_decl_op list_hd: hd :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A" .
  sepref_decl_op list_tl: tl :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
  sepref_decl_op list_last: last :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A" .
  sepref_decl_op list_butlast: butlast :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
  sepref_decl_op list_pop_last: "(\<lambda>l. (last l, butlast l))" :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>list_rel" .
end
sepref_decl_op list_contains: "\<lambda>x l. x\<in>set l" :: "A \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel" 
  where "single_valued A" "single_valued (A\<inverse>)" .
sepref_decl_op list_swap: swap :: "[\<lambda>((l,i),j). i<length l \<and> j<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_rotate1: rotate1 :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_rev: rev :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_index: index :: "\<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel" 
  where "single_valued A" "single_valued (A\<inverse>)" .

subsection \<open>Patterns\<close>
lemma [def_pat_rules]:
  "[] \<equiv> op_list_empty"
  "(=) $l$[] \<equiv> op_list_is_empty$l"
  "(=) $[]$l \<equiv> op_list_is_empty$l"
  "replicate$n$v \<equiv> op_list_replicate$n$v"
  "Cons$x$xs \<equiv> op_list_prepend$x$xs"
  "(@) $xs$(Cons$x$[]) \<equiv> op_list_append$xs$x"
  "(@) $xs$ys \<equiv> op_list_concat$xs$ys"
  "take$i$l \<equiv> op_list_take$i$l"
  "drop$i$l \<equiv> op_list_drop$i$l"
  "op_list_concat$xs$(Cons$x$[]) \<equiv> op_list_append$xs$x"
  "length$xs \<equiv> op_list_length$xs"
  "nth$l$i \<equiv> op_list_get$l$i"
  "list_update$l$i$x \<equiv> op_list_set$l$i$x"
  "hd$l \<equiv> op_list_hd$l"
  "hd$l \<equiv> op_list_hd$l"
  "tl$l \<equiv> op_list_tl$l"
  "tl$l \<equiv> op_list_tl$l"
  "last$l \<equiv> op_list_last$l"
  "butlast$l \<equiv> op_list_butlast$l"
  "(\<in>) $x$(set$l) \<equiv> op_list_contains$x$l"
  "swap$l$i$j \<equiv> op_list_swap$l$i$j"
  "rotate1$l \<equiv> op_list_rotate1$l"
  "rev$l \<equiv> op_list_rev$l"
  "index$l$x \<equiv> op_list_index$l$x"
  by (auto intro!: eq_reflection)

text \<open>Standard preconditions are preserved by list-relation. These lemmas are used for
  simplification of preconditions after composition.\<close>
lemma list_rel_pres_neq_nil[fcomp_prenorm_simps]: "(x',x)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> x'\<noteq>[] \<longleftrightarrow> x\<noteq>[]" by auto
lemma list_rel_pres_length[fcomp_prenorm_simps]: "(x',x)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> length x' = length x" by (rule list_rel_imp_same_length)

declare list_rel_imp_same_length[sepref_bounds_dest]

locale list_custom_empty = 
  fixes rel empty and op_custom_empty :: "'a list"
  assumes customize_hnr_aux: "(uncurry0 empty,uncurry0 (RETURN (op_list_empty::'a list))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a rel"
  assumes op_custom_empty_def: "op_custom_empty = op_list_empty"
begin
  sepref_register op_custom_empty :: "'c list"

  lemma fold_custom_empty:
    "[] = op_custom_empty"
    "op_list_empty = op_custom_empty"
    "mop_list_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all

  lemmas custom_hnr[sepref_fr_rules] = customize_hnr_aux[folded op_custom_empty_def]
end


lemma gen_swap: "swap xs i j = (let
  xi = op_list_get xs i;
  xj = op_list_get xs j;
  xs = op_list_set xs i xj;
  xs = op_list_set xs j xi 
  in xs)"
  by (auto simp: swap_def)

lemma gen_mop_list_swap: "mop_list_swap l i j = do {
    xi \<leftarrow> mop_list_get l i;
    xj \<leftarrow> mop_list_get l j;
    l \<leftarrow> mop_list_set l i xj;
    l \<leftarrow> mop_list_set l j xi;
    RETURN l
  }"
  unfolding mop_list_swap_def
  by (auto simp: pw_acost_eq_iff' refine_pw_simps gen_swap)

lemmas gen_op_list_swap = gen_swap[folded op_list_swap_def]
  
  
end
