header {* LTS by Hashmaps *}
theory RBT_DLTSImpl
imports "../../LTS_Impl" "../../DLTSByMap"
begin


subsection {*DLTS*}
interpretation rs_dlts_defs!: dltsbm_defs rm_ops rm_ops  
  apply intro_locales
done

type_synonym ('V,'E) rs_dlts = "('V, ('E, 'V) RBT.rbt) RBT.rbt"

definition rs_dlts_\<alpha> :: "('V::linorder,'E::linorder) rs_dlts \<Rightarrow> ('V \<times> 'E \<times> 'V) set" 
  where "rs_dlts_\<alpha> \<equiv> rs_dlts_defs.dltsbm_\<alpha>"

definition "rs_dlts_invar \<equiv> rs_dlts_defs.dltsbm_invar"
definition "rs_dlts_empty \<equiv> rs_dlts_defs.dltsbm_empty"
definition "rs_dlts_memb \<equiv> rs_dlts_defs.dltsbm_memb"
definition "rs_dlts_add \<equiv> rs_dlts_defs.dltsbm_add"
definition "rs_dlts_succ \<equiv> rs_dlts_defs.dltsbm_succ"
definition "rs_dlts_add_succs \<equiv> rs_dlts_defs.dltsbm_add_succs"
definition "rs_dlts_delete \<equiv> rs_dlts_defs.dltsbm_delete"

definition "rs_dlts_it \<equiv> rs_dlts_defs.dltsbm_it rm_iteratei rm_iteratei"
definition "rs_dlts_filter_it \<equiv> rs_dlts_defs.dltsbm_filter_it rm_iteratei rm_iteratei"
definition "rs_dlts_succ_it \<equiv> rs_dlts_defs.dltsbm_succ_it"
definition "rs_dlts_succ_label_it \<equiv> rs_dlts_defs.dltsbm_succ_label_it rm_iteratei"
definition "rs_dlts_pre_it \<equiv> rs_dlts_defs.dltsbm_pre_it rm_iteratei"
definition "rs_dlts_pre_label_it \<equiv> rs_dlts_defs.dltsbm_pre_label_it rm_iteratei rm_iteratei"

definition "rs_dlts_from_list \<equiv>  ltsga_from_list rs_dlts_empty rs_dlts_add"
definition "rs_dlts_to_list \<equiv> ltsga_to_list rs_dlts_it"
definition "rs_dlts_from_collect_list \<equiv>  ltsga_from_collect_list rs_dlts_empty rs_dlts_add"
definition "rs_dlts_to_collect_list \<equiv> ltsga_to_collect_list rs_dlts_to_list"
definition "rs_dlts_succ_ball \<equiv> ltsga_succ_ball rs_dlts_succ_it"
definition "rs_dlts_succ_bex \<equiv> ltsga_succ_bex rs_dlts_succ_it"
definition "rs_dlts_pre_ball \<equiv> ltsga_pre_ball rs_dlts_pre_it"
definition "rs_dlts_pre_bex \<equiv> ltsga_pre_bex rs_dlts_pre_it"
definition "rs_dlts_image_filter \<equiv> ltsga_image_filter rs_dlts_empty rs_dlts_add rs_dlts_filter_it"
definition "rs_dlts_filter \<equiv> ltsga_filter rs_dlts_empty rs_dlts_add rs_dlts_filter_it"
definition "rs_dlts_image \<equiv> ltsga_image rs_dlts_image_filter"

lemmas rs_dlts_defs_raw = 
  rs_dlts_defs.dltsbm_empty_def[abs_def]
  rs_dlts_defs.dltsbm_succ_def[abs_def]
  rs_dlts_defs.dltsbm_memb_def[abs_def]
  rs_dlts_defs.dltsbm_add_def[abs_def]
  rs_dlts_defs.dltsbm_add_succs_def[abs_def]
  rs_dlts_defs.dltsbm_delete_def[abs_def]
  rs_dlts_defs.dltsbm_it_alt_def
  rs_dlts_defs.dltsbm_filter_it_alt_def
  rs_dlts_defs.dltsbm_succ_it_def[abs_def]
  rs_dlts_defs.dltsbm_succ_label_it_alt_def
  rs_dlts_defs.dltsbm_pre_it_alt_def
  rs_dlts_defs.dltsbm_pre_label_it_alt_def
  ltsga_from_list_def[abs_def]
  ltsga_to_list_def[abs_def]
  ltsga_to_collect_list_def[abs_def]
  ltsga_succ_ball_def[abs_def]
  ltsga_succ_bex_def[abs_def]
  ltsga_pre_ball_def[abs_def]
  ltsga_pre_bex_def[abs_def]
  ltsga_reverse_def[abs_def]
  ltsga_image_filter_def[abs_def]
  ltsga_filter_def[abs_def]
  ltsga_image_def[abs_def]
  iterate_to_list_def[abs_def] o_def
  iterate_ball_def[abs_def] iterate_bex_def

lemmas rs_dlts_defs = 
  rs_dlts_\<alpha>_def
  rs_dlts_invar_def
  rs_dlts_empty_def
  rs_dlts_succ_def
  rs_dlts_memb_def
  rs_dlts_add_def
  rs_dlts_add_succs_def
  rs_dlts_delete_def
  rs_dlts_from_list_def
  rs_dlts_to_list_def
  rs_dlts_from_collect_list_def
  rs_dlts_to_collect_list_def
  rs_dlts_it_def
  rs_dlts_filter_it_def
  rs_dlts_succ_it_def
  rs_dlts_succ_label_it_def
  rs_dlts_pre_it_def
  rs_dlts_pre_label_it_def
  rs_dlts_succ_ball_def
  rs_dlts_succ_bex_def
  rs_dlts_pre_ball_def
  rs_dlts_pre_bex_def
  rs_dlts_image_filter_def
  rs_dlts_filter_def
  rs_dlts_image_def

lemmas [code] = rs_dlts_defs[unfolded rs_dlts_defs_raw, simplified]

lemmas rs_dlts_is_dlts_impl = rs_dlts_defs.dlts_correct[folded rs_dlts_defs]
interpretation rs_dlts!: dlts rs_dlts_\<alpha> rs_dlts_invar  
  using rs_dlts_is_dlts_impl .
lemmas rs_dlts_empty_impl = rs_dlts_defs.dltsbm_empty_correct[folded rs_dlts_defs]
interpretation rs_dlts!: lts_empty rs_dlts_\<alpha> rs_dlts_invar rs_dlts_empty 
  using rs_dlts_empty_impl .
lemmas rs_dlts_memb_impl = rs_dlts_defs.dltsbm_memb_correct[folded rs_dlts_defs]
interpretation rs_dlts!: lts_memb rs_dlts_\<alpha> rs_dlts_invar rs_dlts_memb
  using rs_dlts_memb_impl .
lemmas rs_dlts_add_impl = rs_dlts_defs.dltsbm_add_correct[folded rs_dlts_defs]
interpretation rs_dlts!: dlts_add rs_dlts_\<alpha> rs_dlts_invar rs_dlts_add
  using rs_dlts_add_impl .
lemmas rs_dlts_succ_impl = rs_dlts_defs.dltsbm_succ_correct[folded rs_dlts_defs]
interpretation rs_dlts!: dlts_succ rs_dlts_\<alpha> rs_dlts_invar rs_dlts_succ
  using rs_dlts_succ_impl .
lemmas rs_dlts_add_succs_impl = rs_dlts_defs.dltsbm_add_succs_correct[folded rs_dlts_defs]
interpretation rs_dlts!: dlts_add_succs rs_dlts_\<alpha> rs_dlts_invar rs_dlts_add_succs
  using rs_dlts_add_succs_impl .
lemmas rs_dlts_delete_impl = rs_dlts_defs.dltsbm_delete_correct[folded rs_dlts_defs]
interpretation rs_dlts!: lts_delete rs_dlts_\<alpha> rs_dlts_invar rs_dlts_delete 
  using rs_dlts_delete_impl .

lemmas rs_dlts_from_list_impl = 
  dltsga_from_list_correct [OF rs_dlts_empty_impl rs_dlts_add_impl, folded rs_dlts_defs]
interpretation rs_dlts!: dlts_from_list rs_dlts_\<alpha> rs_dlts_invar rs_dlts_from_list 
  using rs_dlts_from_list_impl .
lemmas rs_dlts_from_collect_list_impl = 
  dltsga_from_collect_list_correct [OF rs_dlts_empty_impl rs_dlts_add_impl, folded rs_dlts_defs]
interpretation rs_dlts!: dlts_from_collect_list rs_dlts_\<alpha> rs_dlts_invar rs_dlts_from_collect_list 
  using rs_dlts_from_collect_list_impl .

lemmas rs_dlts_it_impl = rs_dlts_defs.dltsbm_it_correct[folded rs_dlts_defs, 
  simplified, 
  OF rm.v1_iteratei_impl rm.v1_iteratei_impl,
  folded rs_dlts_defs]
interpretation rs_dlts!: lts_iterator rs_dlts_\<alpha> rs_dlts_invar rs_dlts_it 
  using rs_dlts_it_impl .

interpretation rs_dlts!: finite_lts rs_dlts_\<alpha> rs_dlts_invar  
  using ltsga_it_implies_finite[OF rs_dlts_it_impl] .

lemmas rs_dlts_filter_it_impl = rs_dlts_defs.dltsbm_filter_it_correct[folded rs_dlts_defs, 
  simplified, 
  OF rm.v1_iteratei_impl rm.v1_iteratei_impl,
  folded rs_dlts_defs]
interpretation rs_dlts!: lts_filter_it rs_dlts_\<alpha> rs_dlts_invar rs_dlts_filter_it 
  using rs_dlts_filter_it_impl .

lemmas rs_dlts_succ_it_impl = rs_dlts_defs.dltsbm_succ_it_correct[folded rs_dlts_defs,
  simplified, 
  folded rm_ops_def rs_ops_def rs_dlts_defs]
interpretation rs_dlts!: lts_succ_it rs_dlts_\<alpha> rs_dlts_invar rs_dlts_succ_it 
  using rs_dlts_succ_it_impl .

lemmas rs_dlts_succ_label_it_impl = rs_dlts_defs.dltsbm_succ_label_it_correct[folded rs_dlts_defs,
  simplified, 
  OF rm.v1_iteratei_impl,
  folded rm_ops_def rs_ops_def rs_dlts_defs]
interpretation rs_dlts!: lts_succ_label_it rs_dlts_\<alpha> rs_dlts_invar rs_dlts_succ_label_it 
  using rs_dlts_succ_label_it_impl .

lemmas rs_dlts_pre_it_impl = rs_dlts_defs.dltsbm_pre_it_correct[folded rs_dlts_defs,
  simplified, 
  OF rm.v1_iteratei_impl,
  folded rm_ops_def rs_ops_def rs_dlts_defs]
interpretation rs_dlts!: lts_pre_it rs_dlts_\<alpha> rs_dlts_invar rs_dlts_pre_it 
  using rs_dlts_pre_it_impl .

lemmas rs_dlts_pre_label_it_impl = rs_dlts_defs.dltsbm_pre_label_it_correct[folded rs_dlts_defs,
  simplified, 
  OF rm.v1_iteratei_impl rm.v1_iteratei_impl,
  folded rm_ops_def rs_ops_def rs_dlts_defs]
interpretation rs_dlts!: lts_pre_label_it rs_dlts_\<alpha> rs_dlts_invar rs_dlts_pre_label_it 
  using rs_dlts_pre_label_it_impl .

lemmas rs_dlts_to_list_impl = ltsga_to_list_correct [OF rs_dlts_it_impl, folded rs_dlts_defs]
interpretation rs_dlts!: lts_to_list rs_dlts_\<alpha> rs_dlts_invar rs_dlts_to_list 
  using rs_dlts_to_list_impl .

lemmas rs_dlts_to_collect_list_impl = ltsga_to_collect_list_correct 
  [OF rs_dlts_to_list_impl, folded rs_dlts_defs]
interpretation rs_dlts!: lts_to_collect_list rs_dlts_\<alpha> rs_dlts_invar rs_dlts_to_collect_list 
  using rs_dlts_to_collect_list_impl .

lemmas rs_dlts_succ_ball_impl = ltsga_succ_ball_correct [OF rs_dlts_succ_it_impl, folded rs_dlts_defs]
interpretation rs_dlts!: lts_succ_ball rs_dlts_\<alpha> rs_dlts_invar rs_dlts_succ_ball 
  using rs_dlts_succ_ball_impl .

lemmas rs_dlts_succ_bex_impl = ltsga_succ_bex_correct [OF rs_dlts_succ_it_impl, folded rs_dlts_defs]
interpretation rs_dlts!: lts_succ_bex rs_dlts_\<alpha> rs_dlts_invar rs_dlts_succ_bex 
  using rs_dlts_succ_bex_impl .

lemmas rs_dlts_pre_ball_impl = ltsga_pre_ball_correct [OF rs_dlts_pre_it_impl, folded rs_dlts_defs]
interpretation rs_dlts!: lts_pre_ball rs_dlts_\<alpha> rs_dlts_invar rs_dlts_pre_ball 
  using rs_dlts_pre_ball_impl .

lemmas rs_dlts_pre_bex_impl = ltsga_pre_bex_correct [OF rs_dlts_pre_it_impl, folded rs_dlts_defs]
interpretation rs_dlts!: lts_pre_bex rs_dlts_\<alpha> rs_dlts_invar rs_dlts_pre_bex 
  using rs_dlts_pre_bex_impl .

lemmas rs_dlts_image_filter_impl = dltsga_image_filter_correct [OF rs_dlts_empty_impl 
   rs_dlts_add_impl rs_dlts_filter_it_impl, folded rs_dlts_image_filter_def]
interpretation rs_dlts!: dlts_image_filter rs_dlts_\<alpha> rs_dlts_invar rs_dlts_\<alpha> rs_dlts_invar rs_dlts_image_filter
  using rs_dlts_image_filter_impl .

lemmas rs_dlts_inj_image_filter_impl = dltsga_inj_image_filter_correct [OF rs_dlts_empty_impl 
   rs_dlts_add_impl rs_dlts_filter_it_impl rs_dlts_is_dlts_impl, folded rs_dlts_image_filter_def]
interpretation rs_dlts!: lts_inj_image_filter rs_dlts_\<alpha> rs_dlts_invar 
  rs_dlts_\<alpha> rs_dlts_invar rs_dlts_image_filter
  using rs_dlts_inj_image_filter_impl .

lemmas rs_dlts_filter_impl = dltsga_filter_correct [OF rs_dlts_empty_impl 
   rs_dlts_add_impl rs_dlts_filter_it_impl rs_dlts_is_dlts_impl, folded rs_dlts_filter_def]
interpretation rs_dlts!: lts_filter rs_dlts_\<alpha> rs_dlts_invar rs_dlts_filter
  using rs_dlts_filter_impl .

lemmas rs_dlts_image_impl = dltsga_image_correct [OF rs_dlts_image_filter_impl, folded rs_dlts_image_def]
interpretation rs_dlts!: dlts_image rs_dlts_\<alpha> rs_dlts_invar rs_dlts_\<alpha> rs_dlts_invar rs_dlts_image
  using rs_dlts_image_impl .

definition rs_dlts_ops :: "('V::{linorder},'E::{linorder},('V,'E) rs_dlts) lts_ops" where
   "rs_dlts_ops \<equiv> \<lparr>
    lts_op_\<alpha> = rs_dlts_\<alpha>,
    lts_op_invar = rs_dlts_invar,
    lts_op_empty = rs_dlts_empty,
    lts_op_memb = rs_dlts_memb,
    lts_op_iterator = rs_dlts_it,
    lts_op_add = rs_dlts_add,
    lts_op_add_succs = rs_dlts_add_succs,
    lts_op_delete = rs_dlts_delete,
    lts_op_succ_ball = rs_dlts_succ_ball,
    lts_op_succ_bex = rs_dlts_succ_bex,
    lts_op_pre_ball = rs_dlts_pre_ball,
    lts_op_pre_bex = rs_dlts_pre_bex,
    lts_op_to_list = rs_dlts_to_list,
    lts_op_to_collect_list = rs_dlts_to_collect_list,
    lts_op_from_list = rs_dlts_from_list,
    lts_op_from_collect_list = rs_dlts_from_collect_list,
    lts_op_image_filter = rs_dlts_image_filter,
    lts_op_filter = rs_dlts_filter,
    lts_op_image = rs_dlts_image,
    lts_op_succ = rs_dlts_succ\<rparr>"

lemma rs_dlts_ops_unfold[code_unfold] :
    "lts_op_\<alpha> rs_dlts_ops = rs_dlts_\<alpha>"
    "lts_op_invar rs_dlts_ops = rs_dlts_invar"
    "lts_op_empty rs_dlts_ops = rs_dlts_empty"
    "lts_op_memb rs_dlts_ops = rs_dlts_memb"
    "lts_op_iterator rs_dlts_ops = rs_dlts_it"
    "lts_op_add rs_dlts_ops = rs_dlts_add"
    "lts_op_succ rs_dlts_ops = rs_dlts_succ"
    "lts_op_add_succs rs_dlts_ops = rs_dlts_add_succs"
    "lts_op_delete rs_dlts_ops = rs_dlts_delete"
    "lts_op_succ_ball rs_dlts_ops = rs_dlts_succ_ball"
    "lts_op_succ_bex rs_dlts_ops = rs_dlts_succ_bex"
    "lts_op_pre_ball rs_dlts_ops = rs_dlts_pre_ball"
    "lts_op_pre_bex rs_dlts_ops = rs_dlts_pre_bex"
    "lts_op_to_list rs_dlts_ops = rs_dlts_to_list"
    "lts_op_to_collect_list rs_dlts_ops = rs_dlts_to_collect_list"
    "lts_op_from_list rs_dlts_ops = rs_dlts_from_list"
    "lts_op_from_collect_list rs_dlts_ops = rs_dlts_from_collect_list"
    "lts_op_image_filter rs_dlts_ops = rs_dlts_image_filter"
    "lts_op_filter rs_dlts_ops = rs_dlts_filter"
  by (simp_all add: rs_dlts_ops_def)

lemma rs_dlts_impl: "StdDLTS rs_dlts_ops"
  apply (rule StdDLTS.intro)
  apply (simp_all add: rs_dlts_ops_def)
  apply unfold_locales
done

interpretation rs_dltsr!: StdDLTS rs_dlts_ops by (rule rs_dlts_impl)

end
