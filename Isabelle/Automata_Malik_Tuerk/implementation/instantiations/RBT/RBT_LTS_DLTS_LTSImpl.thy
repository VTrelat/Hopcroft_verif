header {* LTS by RBTs *}
theory RBT_LTS_DLTS_LTSImpl
imports "../../LTSByLTS_DLTS" "../../LTSGA" "../../LTS_Impl" "RBT_QAQ_LTSImpl"
  "RBT_DLTSImpl"
begin

interpretation rs_lts_dlts_defs!: ltsbc_defs rs_lts_\<alpha> rs_lts_invar rs_dlts_\<alpha> rs_dlts_invar 
unfolding ltsbc_defs_def by (simp add: rs_dlts_is_dlts_impl)

definition "rs_dlts_lts_copy \<equiv> ltsga_copy rs_dlts_it rs_lts_empty rs_lts_add"

definition "rs_lts_dlts_\<alpha> \<equiv> LTS_choice_case rs_lts_\<alpha> rs_dlts_\<alpha>"
lemma rs_lts_dlts_\<alpha>_alt_def :
  "rs_lts_dlts_\<alpha> = rs_lts_dlts_defs.ltsbc_\<alpha>"
unfolding rs_lts_dlts_\<alpha>_def rs_lts_dlts_defs.ltsbc_\<alpha>_def by simp

definition "rs_lts_dlts_invar \<equiv> LTS_choice_case rs_lts_invar rs_dlts_invar"
lemma rs_lts_dlts_invar_alt_def :
  "rs_lts_dlts_invar = rs_lts_dlts_defs.ltsbc_invar"
unfolding rs_lts_dlts_invar_def rs_lts_dlts_defs.ltsbc_invar_def by simp

definition "rs_lts_dlts_empty_dlts \<equiv> ltsbc_emp_dlts rs_dlts_empty"
definition "rs_lts_dlts_empty_lts \<equiv> ltsbc_emp_lts rs_lts_empty"
definition "rs_lts_dlts_add_dlts \<equiv> dltsbc_add rs_lts_add rs_dlts_add"
definition "rs_lts_dlts_add \<equiv> ltsbc_add rs_lts_add rs_dlts_add rs_dlts_succ rs_dlts_lts_copy"
definition "rs_lts_dlts_add_simple \<equiv> ltsbc_add_simple rs_lts_add rs_dlts_lts_copy"
definition "rs_lts_dlts_add_choice b \<equiv> if b then rs_lts_dlts_add_dlts else rs_lts_dlts_add_simple"

definition "rs_lts_dlts_add_succs \<equiv> ltsbc_add_succs rs_lts_add_succs rs_dlts_lts_copy"
definition[code_unfold]: "rs_lts_dlts_memb \<equiv> LTS_choice_case rs_lts_memb rs_dlts_memb"
definition "rs_lts_dlts_delete \<equiv> ltsbc_delete rs_lts_delete rs_dlts_delete"

definition[code_unfold]: "rs_lts_dlts_it \<equiv> LTS_choice_case rs_lts_it rs_dlts_it"
definition "rs_lts_dlts_filter_it \<equiv> ltsbc_filter_it rs_lts_filter_it rs_dlts_filter_it"
definition[code_unfold]: "rs_lts_dlts_succ_it \<equiv> LTS_choice_case rs_lts_succ_it rs_dlts_succ_it"
definition "rs_lts_dlts_succ \<equiv> LTSGA.ltsga_succ rs_lts_dlts_succ_it"
definition[code_unfold]: "rs_lts_dlts_succ_label_it \<equiv> LTS_choice_case rs_lts_succ_label_it rs_dlts_succ_label_it"
definition[code_unfold]: "rs_lts_dlts_pre_it \<equiv> LTS_choice_case rs_lts_pre_it rs_dlts_pre_it"
definition[code_unfold]: "rs_lts_dlts_pre_label_it \<equiv> LTS_choice_case rs_lts_pre_label_it rs_dlts_pre_label_it"

definition "rs_lts_dlts_from_list \<equiv> ltsga_from_list rs_lts_dlts_empty_lts rs_lts_dlts_add_simple"
definition "rs_lts_dlts_to_list \<equiv> ltsga_to_list rs_lts_dlts_it"
definition "rs_lts_dlts_from_collect_list \<equiv>  ltsga_from_collect_list rs_lts_dlts_empty_lts rs_lts_dlts_add_simple"
definition "rs_lts_dlts_to_collect_list \<equiv> ltsga_to_collect_list rs_lts_dlts_to_list"
definition "rs_lts_dlts_succ_ball \<equiv> ltsga_succ_ball rs_lts_dlts_succ_it"
definition "rs_lts_dlts_succ_bex \<equiv> ltsga_succ_bex rs_lts_dlts_succ_it"
definition "rs_lts_dlts_pre_ball \<equiv> ltsga_pre_ball rs_lts_dlts_pre_it"
definition "rs_lts_dlts_pre_bex \<equiv> ltsga_pre_bex rs_lts_dlts_pre_it"
definition "rs_lts_dlts_reverse \<equiv> ltsga_reverse rs_lts_dlts_empty_lts rs_lts_dlts_add_simple rs_lts_dlts_it"
definition "rs_lts_dlts_image_filter \<equiv> ltsga_image_filter rs_lts_dlts_empty_lts rs_lts_dlts_add_simple rs_lts_dlts_filter_it"
definition "rs_lts_dlts_filter \<equiv> ltsga_filter rs_lts_dlts_empty_lts rs_lts_dlts_add_simple rs_lts_dlts_filter_it"
definition "rs_lts_dlts_image \<equiv> ltsga_image rs_lts_dlts_image_filter"

definition "rs_lts_dlts_image_filter_dlts \<equiv> ltsga_image_filter rs_lts_dlts_empty_dlts rs_lts_dlts_add_dlts rs_lts_dlts_filter_it"
definition "rs_lts_dlts_filter_dlts \<equiv> ltsga_filter rs_lts_dlts_empty_dlts rs_lts_dlts_add_dlts rs_lts_dlts_filter_it"
definition "rs_lts_dlts_image_dlts \<equiv> ltsga_image rs_lts_dlts_image_filter_dlts"

lemmas rs_lts_dlts_defs_raw = 
  ltsga_succ_alt_def
  ltsga_from_list_def[abs_def]
  ltsga_from_collect_list_def[abs_def]
  ltsga_from_list_aux_def[abs_def]
  ltsga_to_list_def[abs_def]
  ltsga_to_collect_list_def[abs_def]
  ltsga_succ_ball_def[abs_def]
  ltsga_succ_bex_def[abs_def]
  ltsga_pre_ball_def[abs_def]
  ltsga_pre_bex_def[abs_def]
  ltsga_reverse_def[abs_def]
  ltsga_image_filter_def[abs_def]
  ltsga_image_def[abs_def]
  ltsga_filter_def[abs_def]
  iterate_to_list_def[abs_def] o_def
  iterate_ball_def[abs_def] iterate_bex_def

lemmas rs_lts_dlts_defs = 
  rs_lts_dlts_empty_lts_def
  rs_lts_dlts_empty_dlts_def
  rs_lts_dlts_memb_def
  rs_dlts_lts_copy_def
  rs_lts_dlts_add_def
  rs_lts_dlts_add_succs_def
  rs_lts_dlts_add_dlts_def
  rs_lts_dlts_add_simple_def
  rs_lts_dlts_delete_def
  rs_lts_dlts_from_list_def
  rs_lts_dlts_to_list_def
  rs_lts_dlts_from_collect_list_def
  rs_lts_dlts_to_collect_list_def
  rs_lts_dlts_it_def
  rs_lts_dlts_filter_it_def
  rs_lts_dlts_succ_it_def
  rs_lts_dlts_succ_def
  rs_lts_dlts_succ_label_it_def
  rs_lts_dlts_pre_it_def
  rs_lts_dlts_pre_label_it_def
  rs_lts_dlts_succ_ball_def
  rs_lts_dlts_succ_bex_def
  rs_lts_dlts_pre_ball_def
  rs_lts_dlts_pre_bex_def
  rs_lts_dlts_reverse_def
  rs_lts_dlts_image_filter_def
  rs_lts_dlts_filter_def
  rs_lts_dlts_image_def
  rs_lts_dlts_image_filter_dlts_def
  rs_lts_dlts_filter_dlts_def
  rs_lts_dlts_image_dlts_def

lemmas rs_lts_dlts_folds = 
  rs_lts_dlts_\<alpha>_alt_def
  rs_lts_dlts_invar_alt_def
  rs_lts_dlts_defs

lemmas [code] 
  = rs_lts_dlts_defs[unfolded rs_lts_dlts_defs_raw rs_ts_ops_unfold, simplified]

(*
lemmas [code] = rs_lts_dlts_defs[unfolded rs_lts_dlts_defs_raw rs_ts_ops_unfold
                         rm_ops_unfold rs_ops_unfold, simplified]
*)

lemmas rs_lts_dlts_empty_lts_impl = rs_lts_dlts_defs.ltsbc_empty_correct_lts[OF rs_lts_empty_impl, folded rs_lts_dlts_folds]
lemmas rs_lts_dlts_empty_dlts_impl = rs_lts_dlts_defs.ltsbc_empty_correct_dlts[OF rs_dlts_empty_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_empty rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_empty_dlts 
  using rs_lts_dlts_empty_dlts_impl .

lemmas rs_lts_dlts_memb_impl = rs_lts_dlts_defs.ltsbc_memb_correct[OF rs_lts_memb_impl rs_dlts_memb_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_memb rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_memb
  using rs_lts_dlts_memb_impl .

lemmas rs_dlts_lts_copy_impl = ltsga_copy_correct [OF rs_dlts_it_impl rs_lts_empty_impl rs_lts_add_impl, folded rs_lts_dlts_folds]

lemmas rs_lts_dlts_add_impl = rs_lts_dlts_defs.ltsbc_add_correct[OF rs_lts_add_impl rs_dlts_add_impl
  rs_dlts_succ_impl rs_dlts_lts_copy_impl, folded rs_lts_dlts_folds]
lemmas rs_lts_dlts_add_simple_impl = rs_lts_dlts_defs.ltsbc_add_correct_simple[OF rs_lts_add_impl 
  rs_dlts_lts_copy_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_add rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_add_simple
  using rs_lts_dlts_add_simple_impl .

lemmas rs_lts_dlts_add_succs_impl = rs_lts_dlts_defs.ltsbc_add_succs_correct[OF rs_lts_add_succs_impl 
  rs_dlts_lts_copy_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_add_succs rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_add_succs
  using rs_lts_dlts_add_succs_impl .

lemmas rs_lts_dlts_add_dlts_impl = rs_lts_dlts_defs.dltsbc_add_correct 
[OF lts_add_sublocale[OF rs_lts_add_impl] 
  rs_dlts_add_impl, folded rs_lts_dlts_folds]

lemma rs_lts_dlts_add_choice_impl :
"lts_dlts_add rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_add_choice"
unfolding lts_dlts_add_def rs_lts_dlts_add_choice_def
by (simp add: rs_lts_dlts_add_dlts_impl rs_lts_dlts_add_simple_impl)

lemmas rs_lts_dlts_delete_impl = rs_lts_dlts_defs.ltsbc_delete_correct[OF rs_lts_delete_impl rs_dlts_delete_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_delete rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_delete 
  using rs_lts_dlts_delete_impl .

lemmas rs_lts_dlts_from_list_impl = 
  ltsga_from_list_correct [OF rs_lts_dlts_empty_lts_impl rs_lts_dlts_add_simple_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_from_list rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_from_list 
  using rs_lts_dlts_from_list_impl .
lemmas rs_lts_dlts_from_collect_list_impl = 
  ltsga_from_collect_list_correct [OF rs_lts_dlts_empty_lts_impl rs_lts_dlts_add_simple_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_from_collect_list rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_from_collect_list 
  using rs_lts_dlts_from_collect_list_impl .

lemmas rs_lts_dlts_it_impl = rs_lts_dlts_defs.ltsbc_it_correct[OF rs_lts_it_impl rs_dlts_it_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_iterator rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_it 
  using rs_lts_dlts_it_impl .

interpretation rs_lts_dlts!: finite_lts rs_lts_dlts_\<alpha> rs_lts_dlts_invar  
  using ltsga_it_implies_finite[OF rs_lts_dlts_it_impl] .

lemmas rs_lts_dlts_filter_it_impl = rs_lts_dlts_defs.ltsbc_filter_it_correct[OF 
  rs_lts_filter_it_impl rs_dlts_filter_it_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_filter_it rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_filter_it 
  using rs_lts_dlts_filter_it_impl .

lemmas rs_lts_dlts_succ_it_impl = rs_lts_dlts_defs.ltsbc_succ_it_correct[OF 
  rs_lts_succ_it_impl rs_dlts_succ_it_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_succ_it rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_succ_it 
  using rs_lts_dlts_succ_it_impl .

lemmas rs_lts_dlts_succ_impl = ltsga_succ_correct[OF rs_lts_dlts_succ_it_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_succ rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_succ 
  using rs_lts_dlts_succ_impl .

lemmas rs_lts_dlts_succ_label_it_impl = rs_lts_dlts_defs.ltsbc_succ_label_it_correct[OF 
  rs_lts_succ_label_it_impl rs_dlts_succ_label_it_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_succ_label_it rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_succ_label_it 
  using rs_lts_dlts_succ_label_it_impl .

lemmas rs_lts_dlts_pre_it_impl = rs_lts_dlts_defs.ltsbc_pre_it_correct[OF 
  rs_lts_pre_it_impl rs_dlts_pre_it_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_pre_it rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_pre_it 
  using rs_lts_dlts_pre_it_impl .

lemmas rs_lts_dlts_pre_label_it_impl = rs_lts_dlts_defs.ltsbc_pre_label_it_correct[OF 
  rs_lts_pre_label_it_impl rs_dlts_pre_label_it_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: lts_pre_label_it rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_pre_label_it 
  using rs_lts_dlts_pre_label_it_impl .

lemmas rs_lts_dlts_to_list_impl = ltsga_to_list_correct [OF rs_lts_dlts_it_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_to_list rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_to_list 
  using rs_lts_dlts_to_list_impl .

lemmas rs_lts_dlts_to_collect_list_impl = ltsga_to_collect_list_correct 
  [OF rs_lts_dlts_to_list_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_to_collect_list rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_to_collect_list 
  using rs_lts_dlts_to_collect_list_impl .

lemmas rs_lts_dlts_succ_ball_impl = ltsga_succ_ball_correct [OF rs_lts_dlts_succ_it_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_succ_ball rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_succ_ball 
  using rs_lts_dlts_succ_ball_impl .

lemmas rs_lts_dlts_succ_bex_impl = ltsga_succ_bex_correct [OF rs_lts_dlts_succ_it_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_succ_bex rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_succ_bex 
  using rs_lts_dlts_succ_bex_impl .

lemmas rs_lts_dlts_pre_ball_impl = ltsga_pre_ball_correct [OF rs_lts_dlts_pre_it_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_pre_ball rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_pre_ball 
  using rs_lts_dlts_pre_ball_impl .

lemmas rs_lts_dlts_pre_bex_impl = ltsga_pre_bex_correct [OF rs_lts_dlts_pre_it_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_pre_bex rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_pre_bex 
  using rs_lts_dlts_pre_bex_impl .

lemmas rs_lts_dlts_reverse_impl = ltsga_reverse_correct [OF rs_lts_dlts_empty_lts_impl rs_lts_dlts_add_simple_impl 
   rs_lts_dlts_it_impl, folded rs_lts_dlts_defs]
interpretation rs_lts_dlts!: lts_reverse rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_reverse 
  using rs_lts_dlts_reverse_impl .

lemmas rs_lts_dlts_image_filter_impl = ltsga_image_filter_correct [OF rs_lts_dlts_empty_lts_impl 
   rs_lts_dlts_add_simple_impl rs_lts_dlts_filter_it_impl, folded rs_lts_dlts_image_filter_def]
interpretation rs_lts_dlts!: lts_image_filter rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_image_filter
  using rs_lts_dlts_image_filter_impl .

lemmas rs_lts_dlts_filter_impl = ltsga_filter_correct [OF rs_lts_dlts_empty_lts_impl 
   rs_lts_dlts_add_simple_impl rs_lts_dlts_filter_it_impl, folded rs_lts_dlts_filter_def]
interpretation rs_lts_dlts!: lts_filter rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_filter
  using rs_lts_dlts_filter_impl .

lemmas rs_lts_dlts_image_impl = ltsga_image_correct [OF rs_lts_dlts_image_filter_impl, folded rs_lts_dlts_image_def]
interpretation rs_lts_dlts!: lts_image rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_image
  using rs_lts_dlts_image_impl .

lemmas rs_lts_dlts_image_filter_dlts_impl = dltsga_image_filter_correct [OF rs_lts_dlts_empty_dlts_impl 
   rs_lts_dlts_add_dlts_impl rs_lts_dlts_filter_it_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: dlts_image_filter rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_image_filter_dlts
  using rs_lts_dlts_image_filter_dlts_impl .

lemmas rs_lts_dlts_image_dlts_impl = dltsga_image_correct [OF rs_lts_dlts_image_filter_dlts_impl, folded rs_lts_dlts_folds]
interpretation rs_lts_dlts!: dlts_image rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_\<alpha> rs_lts_dlts_invar rs_lts_dlts_image_dlts
  using rs_lts_dlts_image_dlts_impl .

type_synonym ('V,'E) rs_lts_dlts = 
  "('V, ('E, ('V, unit) RBT.rbt) RBT.rbt) RBT.rbt"

definition rs_lts_dlts_ops where
   "rs_lts_dlts_ops \<equiv> \<lparr>
    lts_op_\<alpha> = rs_lts_dlts_\<alpha>,
    lts_op_invar = rs_lts_dlts_invar,
    lts_op_empty = rs_lts_dlts_empty_dlts,
    lts_op_memb = rs_lts_dlts_memb,
    lts_op_iterator = rs_lts_dlts_it,
    lts_op_add = rs_lts_dlts_add_simple,
    lts_op_add_succs = rs_lts_dlts_add_succs,
    lts_op_delete = rs_lts_dlts_delete,
    lts_op_succ_ball = rs_lts_dlts_succ_ball,
    lts_op_succ_bex = rs_lts_dlts_succ_bex,
    lts_op_pre_ball = rs_lts_dlts_pre_ball,
    lts_op_pre_bex = rs_lts_dlts_pre_bex,
    lts_op_to_list = rs_lts_dlts_to_list,
    lts_op_to_collect_list = rs_lts_dlts_to_collect_list,
    lts_op_from_list = rs_lts_dlts_from_list,
    lts_op_from_collect_list = rs_lts_dlts_from_collect_list,
    lts_op_image_filter = rs_lts_dlts_image_filter,
    lts_op_filter = rs_lts_dlts_filter,
    lts_op_image = rs_lts_dlts_image,
    lts_op_succ = rs_lts_dlts_succ \<rparr>"

lemma rs_lts_dlts_ops_unfold[code_unfold] :
    "lts_op_\<alpha> rs_lts_dlts_ops = rs_lts_dlts_\<alpha>"
    "lts_op_invar rs_lts_dlts_ops = rs_lts_dlts_invar"
    "lts_op_empty rs_lts_dlts_ops = rs_lts_dlts_empty_dlts"
    "lts_op_memb rs_lts_dlts_ops = rs_lts_dlts_memb"
    "lts_op_iterator rs_lts_dlts_ops = rs_lts_dlts_it"
    "lts_op_add rs_lts_dlts_ops = rs_lts_dlts_add_simple"
    "lts_op_add_succs rs_lts_dlts_ops = rs_lts_dlts_add_succs"
    "lts_op_delete rs_lts_dlts_ops = rs_lts_dlts_delete"
    "lts_op_succ_ball rs_lts_dlts_ops = rs_lts_dlts_succ_ball"
    "lts_op_succ_bex rs_lts_dlts_ops = rs_lts_dlts_succ_bex"
    "lts_op_pre_ball rs_lts_dlts_ops = rs_lts_dlts_pre_ball"
    "lts_op_pre_bex rs_lts_dlts_ops = rs_lts_dlts_pre_bex"
    "lts_op_to_list rs_lts_dlts_ops = rs_lts_dlts_to_list"
    "lts_op_to_collect_list rs_lts_dlts_ops = rs_lts_dlts_to_collect_list"
    "lts_op_from_list rs_lts_dlts_ops = rs_lts_dlts_from_list"
    "lts_op_from_collect_list rs_lts_dlts_ops = rs_lts_dlts_from_collect_list"
    "lts_op_image_filter rs_lts_dlts_ops = rs_lts_dlts_image_filter"
    "lts_op_filter rs_lts_dlts_ops = rs_lts_dlts_filter"
    "lts_op_image rs_lts_dlts_ops = rs_lts_dlts_image"
    "lts_op_succ rs_lts_dlts_ops = rs_lts_dlts_succ"
  by (simp_all add: rs_lts_dlts_ops_def)

lemma rs_lts_dlts_impl: "StdLTS rs_lts_dlts_ops"
  apply (rule StdLTS.intro)
  apply (simp_all add: rs_lts_dlts_ops_def)
  apply unfold_locales
  done

interpretation rs_lts_dltsr!: StdLTS rs_lts_dlts_ops by (rule rs_lts_dlts_impl)

definition "rs_lts_dlts_is_reachable \<equiv> rs_lts_dltsr.is_reachable_impl"
lemmas rs_lts_dlts_is_reachable_code[code] = rs_lts_dltsr.is_reachable_impl.simps [folded rs_lts_dlts_is_reachable_def rs_lts_dlts_defs, unfolded rs_lts_dlts_ops_unfold]
declare rs_lts_dlts_is_reachable_def [symmetric, code_unfold]

end
