header {* LTS by RBTs *}
theory RBT_QAQ_LTSImpl
imports 
  "../../LTSByTripleSetQAQ" 
  "../../LTSGA" 
  "../../LTS_Impl" 
  "RBT_TripleSetImpl"
begin

interpretation rs_lts_defs!: ltsbm_QAQ_defs rs_ts_\<alpha> rs_ts_invar .

definition "rs_lts_\<alpha> \<equiv> rs_ts_\<alpha>"
definition "rs_lts_invar \<equiv> rs_ts_invar"
definition[code_unfold]: "rs_lts_empty \<equiv> rs_ts_empty"
definition[code_unfold]: "rs_lts_add \<equiv> rs_ts_add"
definition[code_unfold]: "rs_lts_memb \<equiv> rs_ts_memb"
definition[code_unfold]: "rs_lts_add_succs \<equiv> rs_ts_add_Cl"
definition[code_unfold]: "rs_lts_delete \<equiv> rs_ts_delete"

definition[code_unfold]: "rs_lts_it \<equiv> rs_ts_it"
definition[code_unfold]: "rs_lts_filter_it \<equiv> rs_ts_filter_it"
definition[code_unfold]: "rs_lts_succ_it \<equiv> rs_ts_C_it"
definition "rs_lts_succ \<equiv> LTSGA.ltsga_succ rs_lts_succ_it"
definition[code_unfold]: "rs_lts_succ_label_it \<equiv> rs_ts_BC_it"
definition "rs_lts_pre_it \<equiv> rs_lts_defs.ltsbm_pre_it rs_ts_A_it"
definition[code_unfold]: "rs_lts_pre_label_it \<equiv> rs_ts_AB_it"

definition "rs_lts_from_list \<equiv>  ltsga_from_list rs_lts_empty rs_lts_add"
definition "rs_lts_to_list \<equiv> ltsga_to_list rs_lts_it"
definition "rs_lts_from_collect_list \<equiv>  ltsga_from_collect_list rs_lts_empty rs_lts_add"
definition "rs_lts_to_collect_list \<equiv> ltsga_to_collect_list rs_lts_to_list"
definition "rs_lts_succ_ball \<equiv> ltsga_succ_ball rs_lts_succ_it"
definition "rs_lts_succ_bex \<equiv> ltsga_succ_bex rs_lts_succ_it"
definition "rs_lts_pre_ball \<equiv> ltsga_pre_ball rs_lts_pre_it"
definition "rs_lts_pre_bex \<equiv> ltsga_pre_bex rs_lts_pre_it"
definition "rs_lts_reverse \<equiv> ltsga_reverse rs_lts_empty rs_lts_add rs_lts_it"
definition "rs_lts_image_filter \<equiv> ltsga_image_filter rs_lts_empty rs_lts_add rs_lts_filter_it"
definition "rs_lts_filter \<equiv> ltsga_filter rs_lts_empty rs_lts_add rs_lts_filter_it"
definition "rs_lts_image \<equiv> ltsga_image rs_lts_image_filter"

lemmas rs_lts_defs_raw = 
  rs_lts_defs.ltsbm_pre_it_def[abs_def]
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

lemmas rs_lts_defs = 
  rs_lts_\<alpha>_def
  rs_lts_invar_def
  rs_lts_empty_def
  rs_lts_memb_def
  rs_lts_add_def
  rs_lts_add_succs_def
  rs_lts_delete_def
  rs_lts_from_list_def
  rs_lts_to_list_def
  rs_lts_from_collect_list_def
  rs_lts_to_collect_list_def
  rs_lts_it_def
  rs_lts_filter_it_def
  rs_lts_succ_it_def
  rs_lts_succ_def
  rs_lts_succ_label_it_def
  rs_lts_pre_it_def
  rs_lts_pre_label_it_def
  rs_lts_succ_ball_def
  rs_lts_succ_bex_def
  rs_lts_pre_ball_def
  rs_lts_pre_bex_def
  rs_lts_reverse_def
  rs_lts_image_filter_def
  rs_lts_filter_def
  rs_lts_image_def

lemmas [code] = 
  rs_lts_defs[unfolded rs_lts_defs_raw rs_ts_ops_unfold, simplified]

(*lemmas [code] = rs_lts_defs[unfolded rs_lts_defs_raw rs_ts_ops_unfold
                         rm_ops_unfold rs_ops_unfold, simplified]
*)

lemmas rs_lts_empty_impl = rs_lts_defs.ltsbm_empty_correct[OF rs_ts_empty_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_empty rs_lts_\<alpha> rs_lts_invar rs_lts_empty 
  using rs_lts_empty_impl .
lemmas rs_lts_memb_impl = rs_lts_defs.ltsbm_memb_correct[OF rs_ts_memb_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_memb rs_lts_\<alpha> rs_lts_invar rs_lts_memb
  using rs_lts_memb_impl .
lemmas rs_lts_add_impl = rs_lts_defs.ltsbm_add_correct[OF rs_ts_add_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_add rs_lts_\<alpha> rs_lts_invar rs_lts_add
  using rs_lts_add_impl .
lemmas rs_lts_add_succs_impl = rs_lts_defs.ltsbm_add_succs_correct[OF rs_ts_add_Cl_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_add_succs rs_lts_\<alpha> rs_lts_invar rs_lts_add_succs
  using rs_lts_add_succs_impl .
lemmas rs_lts_delete_impl = rs_lts_defs.ltsbm_delete_correct[OF rs_ts_delete_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_delete rs_lts_\<alpha> rs_lts_invar rs_lts_delete 
  using rs_lts_delete_impl .

lemmas rs_lts_from_list_impl = 
  ltsga_from_list_correct [OF rs_lts_empty_impl rs_lts_add_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_from_list rs_lts_\<alpha> rs_lts_invar rs_lts_from_list 
  using rs_lts_from_list_impl .
lemmas rs_lts_from_collect_list_impl = 
  ltsga_from_collect_list_correct [OF rs_lts_empty_impl rs_lts_add_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_from_collect_list rs_lts_\<alpha> rs_lts_invar rs_lts_from_collect_list 
  using rs_lts_from_collect_list_impl .

lemmas rs_lts_it_impl = rs_lts_defs.ltsbm_it_correct[OF rs_ts_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_iterator rs_lts_\<alpha> rs_lts_invar rs_lts_it 
  using rs_lts_it_impl .

interpretation rs_lts!: finite_lts rs_lts_\<alpha> rs_lts_invar  
  using ltsga_it_implies_finite[OF rs_lts_it_impl] .

lemmas rs_lts_filter_it_impl = rs_lts_defs.ltsbm_filter_it_correct[OF rs_ts_filter_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_filter_it rs_lts_\<alpha> rs_lts_invar rs_lts_filter_it 
  using rs_lts_filter_it_impl .

lemmas rs_lts_succ_it_impl = rs_lts_defs.ltsbm_succ_it_correct[OF rs_ts_C_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_succ_it rs_lts_\<alpha> rs_lts_invar rs_lts_succ_it 
  using rs_lts_succ_it_impl .

lemmas rs_lts_succ_impl = ltsga_succ_correct[OF rs_lts_succ_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_succ rs_lts_\<alpha> rs_lts_invar rs_lts_succ 
  using rs_lts_succ_impl .

lemmas rs_lts_succ_label_it_impl = rs_lts_defs.ltsbm_succ_label_it_correct[OF rs_ts_BC_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_succ_label_it rs_lts_\<alpha> rs_lts_invar rs_lts_succ_label_it 
  using rs_lts_succ_label_it_impl .

lemmas rs_lts_pre_it_impl = rs_lts_defs.ltsbm_pre_it_correct[OF rs_ts_A_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_pre_it rs_lts_\<alpha> rs_lts_invar rs_lts_pre_it 
  using rs_lts_pre_it_impl .

lemmas rs_lts_pre_label_it_impl = rs_lts_defs.ltsbm_pre_label_it_correct[OF rs_ts_AB_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_pre_label_it rs_lts_\<alpha> rs_lts_invar rs_lts_pre_label_it 
  using rs_lts_pre_label_it_impl .

lemmas rs_lts_to_list_impl = ltsga_to_list_correct [OF rs_lts_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_to_list rs_lts_\<alpha> rs_lts_invar rs_lts_to_list 
  using rs_lts_to_list_impl .

lemmas rs_lts_to_collect_list_impl = ltsga_to_collect_list_correct 
  [OF rs_lts_to_list_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_to_collect_list rs_lts_\<alpha> rs_lts_invar rs_lts_to_collect_list 
  using rs_lts_to_collect_list_impl .

lemmas rs_lts_succ_ball_impl = ltsga_succ_ball_correct [OF rs_lts_succ_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_succ_ball rs_lts_\<alpha> rs_lts_invar rs_lts_succ_ball 
  using rs_lts_succ_ball_impl .

lemmas rs_lts_succ_bex_impl = ltsga_succ_bex_correct [OF rs_lts_succ_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_succ_bex rs_lts_\<alpha> rs_lts_invar rs_lts_succ_bex 
  using rs_lts_succ_bex_impl .

lemmas rs_lts_pre_ball_impl = ltsga_pre_ball_correct [OF rs_lts_pre_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_pre_ball rs_lts_\<alpha> rs_lts_invar rs_lts_pre_ball 
  using rs_lts_pre_ball_impl .

lemmas rs_lts_pre_bex_impl = ltsga_pre_bex_correct [OF rs_lts_pre_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_pre_bex rs_lts_\<alpha> rs_lts_invar rs_lts_pre_bex 
  using rs_lts_pre_bex_impl .

lemmas rs_lts_reverse_impl = ltsga_reverse_correct [OF rs_lts_empty_impl rs_lts_add_impl 
   rs_lts_it_impl, folded rs_lts_defs]
interpretation rs_lts!: lts_reverse rs_lts_\<alpha> rs_lts_invar rs_lts_\<alpha> rs_lts_invar rs_lts_reverse 
  using rs_lts_reverse_impl .

lemmas rs_lts_image_filter_impl = ltsga_image_filter_correct [OF rs_lts_empty_impl 
   rs_lts_add_impl rs_lts_filter_it_impl, folded rs_lts_image_filter_def]
interpretation rs_lts!: lts_image_filter rs_lts_\<alpha> rs_lts_invar rs_lts_\<alpha> rs_lts_invar rs_lts_image_filter
  using rs_lts_image_filter_impl .

lemmas rs_lts_filter_impl = ltsga_filter_correct [OF rs_lts_empty_impl 
   rs_lts_add_impl rs_lts_filter_it_impl, folded rs_lts_filter_def]
interpretation rs_lts!: lts_filter rs_lts_\<alpha> rs_lts_invar rs_lts_filter
  using rs_lts_filter_impl .

lemmas rs_lts_image_impl = ltsga_image_correct [OF rs_lts_image_filter_impl, folded rs_lts_image_def]
interpretation rs_lts!: lts_image rs_lts_\<alpha> rs_lts_invar rs_lts_\<alpha> rs_lts_invar rs_lts_image
  using rs_lts_image_impl .

type_synonym ('V,'E) rs_lts = 
  "('V, ('E, ('V, unit) RBT.rbt) RBT.rbt) RBT.rbt"

definition rs_lts_ops :: "('V::{linorder},'E::{linorder},('V,'E) rs_lts) lts_ops" where
   "rs_lts_ops \<equiv> \<lparr>
    lts_op_\<alpha> = rs_lts_\<alpha>,
    lts_op_invar = rs_lts_invar,
    lts_op_empty = rs_lts_empty,
    lts_op_memb = rs_lts_memb,
    lts_op_iterator = rs_lts_it,
    lts_op_add = rs_lts_add,
    lts_op_add_succs = rs_lts_add_succs,
    lts_op_delete = rs_lts_delete,
    lts_op_succ_ball = rs_lts_succ_ball,
    lts_op_succ_bex = rs_lts_succ_bex,
    lts_op_pre_ball = rs_lts_pre_ball,
    lts_op_pre_bex = rs_lts_pre_bex,
    lts_op_to_list = rs_lts_to_list,
    lts_op_to_collect_list = rs_lts_to_collect_list,
    lts_op_from_list = rs_lts_from_list,
    lts_op_from_collect_list = rs_lts_from_collect_list,
    lts_op_image_filter = rs_lts_image_filter,
    lts_op_filter = rs_lts_filter,
    lts_op_image = rs_lts_image,
    lts_op_succ = rs_lts_succ \<rparr>"

lemma rs_lts_ops_unfold[code_unfold] :
    "lts_op_\<alpha> rs_lts_ops = rs_lts_\<alpha>"
    "lts_op_invar rs_lts_ops = rs_lts_invar"
    "lts_op_empty rs_lts_ops = rs_lts_empty"
    "lts_op_memb rs_lts_ops = rs_lts_memb"
    "lts_op_iterator rs_lts_ops = rs_lts_it"
    "lts_op_add rs_lts_ops = rs_lts_add"
    "lts_op_add_succs rs_lts_ops = rs_lts_add_succs"
    "lts_op_delete rs_lts_ops = rs_lts_delete"
    "lts_op_succ_ball rs_lts_ops = rs_lts_succ_ball"
    "lts_op_succ_bex rs_lts_ops = rs_lts_succ_bex"
    "lts_op_pre_ball rs_lts_ops = rs_lts_pre_ball"
    "lts_op_pre_bex rs_lts_ops = rs_lts_pre_bex"
    "lts_op_to_list rs_lts_ops = rs_lts_to_list"
    "lts_op_to_collect_list rs_lts_ops = rs_lts_to_collect_list"
    "lts_op_from_list rs_lts_ops = rs_lts_from_list"
    "lts_op_from_collect_list rs_lts_ops = rs_lts_from_collect_list"
    "lts_op_image_filter rs_lts_ops = rs_lts_image_filter"
    "lts_op_filter rs_lts_ops = rs_lts_filter"
    "lts_op_image rs_lts_ops = rs_lts_image"
    "lts_op_succ rs_lts_ops = rs_lts_succ"
  by (simp_all add: rs_lts_ops_def)

lemma rs_lts_impl: "StdLTS rs_lts_ops"
  apply (rule StdLTS.intro)
  apply (simp_all add: rs_lts_ops_def)
  apply unfold_locales
  done

interpretation rs_ltsr!: StdLTS rs_lts_ops by (rule rs_lts_impl)

definition "rs_lts_is_reachable \<equiv> rs_ltsr.is_reachable_impl"
lemmas rs_lts_is_reachable_code[code] = rs_ltsr.is_reachable_impl.simps [folded rs_lts_is_reachable_def rs_lts_defs, unfolded rs_lts_ops_unfold]
declare rs_lts_is_reachable_def [symmetric, code_unfold]

end
