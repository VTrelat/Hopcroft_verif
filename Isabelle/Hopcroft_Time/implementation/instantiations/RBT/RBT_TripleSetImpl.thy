section \<open> TripleSet by RBTs \<close>
theory RBT_TripleSetImpl
imports "../../TripleSetGA" 
begin

subsection \<open>Triple Set\<close>

interpretation rs_ts_defs: tsbm_defs rm_ops rm_ops rs_ops 
  by intro_locales

definition "rs_ts_\<alpha> \<equiv> rs_ts_defs.tsbm_\<alpha>"
definition "rs_ts_invar \<equiv> rs_ts_defs.tsbm_invar"
definition "rs_ts_empty \<equiv> rs_ts_defs.tsbm_empty"
definition "rs_ts_memb \<equiv> rs_ts_defs.tsbm_memb"
definition "rs_ts_add \<equiv> rs_ts_defs.tsbm_add"
definition "rs_ts_add_Al \<equiv> rs_ts_defs.tsbm_add_Al"
definition "rs_ts_add_Bl \<equiv> rs_ts_defs.tsbm_add_Bl"
definition "rs_ts_add_Cl \<equiv> rs_ts_defs.tsbm_add_Cl"
definition "rs_ts_add_Cs \<equiv> rs_ts_defs.tsbm_add_Cs"
definition "rs_ts_set_Cs \<equiv> rs_ts_defs.tsbm_set_Cs"
definition "rs_ts_delete \<equiv> rs_ts_defs.tsbm_delete"
definition "rs_ts_filter_it \<equiv> rs_ts_defs.tsbm_filter_it rm_iteratei rm_iteratei rs_iteratei"
definition "rs_ts_it \<equiv> rs_ts_defs.tsbm_it rm_iteratei rm_iteratei rs_iteratei"
definition "rs_ts_A_it \<equiv> rs_ts_defs.tsbm_A_it rm_iteratei"
definition "rs_ts_B_it \<equiv> rs_ts_defs.tsbm_B_it rm_iteratei"
definition "rs_ts_C_it \<equiv> rs_ts_defs.tsbm_C_it rs_iteratei"
definition "rs_ts_AB_it \<equiv> rs_ts_defs.tsbm_AB_it rm_iteratei rm_iteratei"
definition "rs_ts_AC_it \<equiv> rs_ts_defs.tsbm_AC_it rm_iteratei rs_iteratei"
definition "rs_ts_BC_it \<equiv> rs_ts_defs.tsbm_BC_it rm_iteratei rs_iteratei"

definition "rs_ts_from_list \<equiv>  tsga_from_list rs_ts_empty rs_ts_add"
definition "rs_ts_to_list \<equiv> tsga_to_list rs_ts_it"
definition "rs_ts_image_filter \<equiv> tsga_image_filter rs_ts_empty rs_ts_add rs_ts_filter_it"
definition "rs_ts_filter \<equiv> tsga_filter rs_ts_empty rs_ts_add rs_ts_filter_it"
definition "rs_ts_image \<equiv> tsga_image rs_ts_image_filter"

lemmas rs_ts_defs = 
  rs_ts_\<alpha>_def
  rs_ts_invar_def
  rs_ts_empty_def
  rs_ts_memb_def
  rs_ts_add_def
  rs_ts_add_Al_def
  rs_ts_add_Bl_def
  rs_ts_add_Cl_def
  rs_ts_add_Cs_def
  rs_ts_set_Cs_def
  rs_ts_delete_def
  rs_ts_filter_it_def
  rs_ts_it_def
  rs_ts_A_it_def
  rs_ts_B_it_def
  rs_ts_C_it_def
  rs_ts_AB_it_def
  rs_ts_AC_it_def
  rs_ts_BC_it_def
  rs_ts_from_list_def
  rs_ts_to_list_def
  rs_ts_image_filter_def[unfolded rs_ts_filter_it_def]
  rs_ts_filter_def[unfolded rs_ts_filter_it_def]
  rs_ts_image_def[unfolded rs_ts_image_filter_def rs_ts_filter_it_def]

lemmas rs_ts_defs_raw = 
  rs_ts_defs.tsbm_empty_def[abs_def]
  rs_ts_defs.tsbm_memb_def[abs_def]
  rs_ts_defs.tsbm_add_def[abs_def]
  rs_ts_defs.tsbm_add_Al_def[abs_def]
  rs_ts_defs.tsbm_add_Bl_def[abs_def]
  rs_ts_defs.tsbm_add_Cl_def[abs_def]
  rs_ts_defs.tsbm_add_Cs_def[abs_def]
  rs_ts_defs.tsbm_set_Cs_def[abs_def]
  rs_ts_defs.tsbm_delete_def[abs_def]
  rs_ts_defs.tsbm_filter_it_alt_def
  rs_ts_defs.tsbm_it_alt_def
  rs_ts_defs.tsbm_A_it_alt_def
  rs_ts_defs.tsbm_B_it_alt_def
  rs_ts_defs.tsbm_C_it_alt_def
  rs_ts_defs.tsbm_AB_it_alt_def
  rs_ts_defs.tsbm_AC_it_alt_def
  rs_ts_defs.tsbm_BC_it_alt_def
  tsga_from_list_alt_def
  tsga_to_list_alt_def
  tsga_image_filter_def[abs_def]
  tsga_image_def[abs_def]
  tsga_filter_def[abs_def]

lemmas [code] = rs_ts_defs[unfolded rs_ts_defs_raw, simplified]

(*lemmas [code] = rs_ts_defs[unfolded rs_ts_defs_raw rm_ops_unfold rs_ops_unfold, simplified]*)

lemmas rs_ts_empty_impl = rs_ts_defs.tsbm_empty_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_empty rs_ts_\<alpha> rs_ts_invar rs_ts_empty 
  using rs_ts_empty_impl .
lemmas rs_ts_memb_impl = rs_ts_defs.tsbm_memb_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_memb rs_ts_\<alpha> rs_ts_invar rs_ts_memb
  using rs_ts_memb_impl .
lemmas rs_ts_add_impl = rs_ts_defs.tsbm_add_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_add rs_ts_\<alpha> rs_ts_invar rs_ts_add
  using rs_ts_add_impl .
lemmas rs_ts_add_Al_impl = rs_ts_defs.tsbm_add_Al_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_add_Al rs_ts_\<alpha> rs_ts_invar rs_ts_add_Al
  using rs_ts_add_Al_impl .
lemmas rs_ts_add_Bl_impl = rs_ts_defs.tsbm_add_Bl_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_add_Bl rs_ts_\<alpha> rs_ts_invar rs_ts_add_Bl
  using rs_ts_add_Bl_impl .
lemmas rs_ts_add_Cl_impl = rs_ts_defs.tsbm_add_Cl_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_add_Cl rs_ts_\<alpha> rs_ts_invar rs_ts_add_Cl
  using rs_ts_add_Cl_impl .
lemmas rs_ts_add_Cs_impl = rs_ts_defs.tsbm_add_Cs_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_add_Cs rs_\<alpha> rs_invar rs_ts_\<alpha> rs_ts_invar rs_ts_add_Cs
  using rs_ts_add_Cs_impl .
lemmas rs_ts_set_Cs_impl = rs_ts_defs.tsbm_set_Cs_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_set_Cs rs_\<alpha> rs_invar rs_ts_\<alpha> rs_ts_invar rs_ts_set_Cs
  using rs_ts_set_Cs_impl .
lemmas rs_ts_delete_impl = rs_ts_defs.tsbm_delete_correct[folded rs_ts_defs]
interpretation rs_ts: triple_set_delete rs_ts_\<alpha> rs_ts_invar rs_ts_delete
  using rs_ts_delete_impl .

lemmas rs_ts_filter_it_impl = rs_ts_defs.tsbm_filter_it_correct[
  OF rm.v1_iteratei_impl rm.v1_iteratei_impl rs.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_filter_it rs_ts_\<alpha> rs_ts_invar rs_ts_filter_it 
  using rs_ts_filter_it_impl .
lemmas rs_ts_it_impl = rs_ts_defs.tsbm_it_correct[
  OF rm.v1_iteratei_impl rm.v1_iteratei_impl rs.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_iterator rs_ts_\<alpha> rs_ts_invar rs_ts_it 
  using rs_ts_it_impl .
lemmas rs_ts_A_it_impl = rs_ts_defs.tsbm_A_it_correct[
  OF rm.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_A_it rs_ts_\<alpha> rs_ts_invar rs_ts_A_it 
  using rs_ts_A_it_impl .
lemmas rs_ts_B_it_impl = rs_ts_defs.tsbm_B_it_correct[
  OF rm.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_B_it rs_ts_\<alpha> rs_ts_invar rs_ts_B_it 
  using rs_ts_B_it_impl .
lemmas rs_ts_C_it_impl = rs_ts_defs.tsbm_C_it_correct[
  OF rs.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_C_it rs_ts_\<alpha> rs_ts_invar rs_ts_C_it 
  using rs_ts_C_it_impl .
lemmas rs_ts_AB_it_impl = rs_ts_defs.tsbm_AB_it_correct[
  OF rm.v1_iteratei_impl rm.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_AB_it rs_ts_\<alpha> rs_ts_invar rs_ts_AB_it 
  using rs_ts_AB_it_impl .
lemmas rs_ts_AC_it_impl = rs_ts_defs.tsbm_AC_it_correct[
  OF rm.v1_iteratei_impl rs.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_AC_it rs_ts_\<alpha> rs_ts_invar rs_ts_AC_it 
  using rs_ts_AC_it_impl .
lemmas rs_ts_BC_it_impl = rs_ts_defs.tsbm_BC_it_correct[
  OF rm.v1_iteratei_impl rs.v1_iteratei_impl,
  folded rs_ts_defs]
interpretation rs_ts: triple_set_BC_it rs_ts_\<alpha> rs_ts_invar rs_ts_BC_it 
  using rs_ts_BC_it_impl .

lemmas rs_ts_from_list_impl = 
  tsga_from_list_correct [OF rs_ts_empty_impl rs_ts_add_impl, folded rs_ts_defs]
interpretation rs_ts: triple_set_from_list rs_ts_\<alpha> rs_ts_invar rs_ts_from_list 
  using rs_ts_from_list_impl .
lemmas rs_ts_to_list_impl = tsga_to_list_correct [OF rs_ts_it_impl, folded rs_ts_defs]
interpretation rs_ts: triple_set_to_list rs_ts_\<alpha> rs_ts_invar rs_ts_to_list 
  using rs_ts_to_list_impl .
lemmas rs_ts_image_filter_impl = 
  tsga_image_filter_correct [OF rs_ts_empty_impl rs_ts_add_impl rs_ts_filter_it_impl, 
        folded rs_ts_defs rs_ts_image_filter_def]
interpretation rs_ts: triple_set_image_filter rs_ts_\<alpha> rs_ts_invar rs_ts_\<alpha> rs_ts_invar rs_ts_image_filter 
  using rs_ts_image_filter_impl .
lemmas rs_ts_image_impl = tsga_image_correct [OF rs_ts_image_filter_impl, folded rs_ts_defs rs_ts_image_def]
interpretation rs_ts: triple_set_image rs_ts_\<alpha> rs_ts_invar rs_ts_\<alpha> rs_ts_invar rs_ts_image 
  using rs_ts_image_impl .
lemmas rs_ts_filter_impl = tsga_filter_correct [OF rs_ts_empty_impl rs_ts_add_impl rs_ts_filter_it_impl, folded rs_ts_defs rs_ts_filter_def]
interpretation rs_ts: triple_set_filter rs_ts_\<alpha> rs_ts_invar rs_ts_filter
  using rs_ts_filter_impl .


subsection \<open> Record \<close>

  definition rs_ts_ops where
    "rs_ts_ops = \<lparr>
    triple_set_op_\<alpha> = rs_ts_\<alpha>,
    triple_set_op_invar = rs_ts_invar,
    triple_set_op_empty = rs_ts_empty,
    triple_set_op_memb = rs_ts_memb,
    triple_set_op_add = rs_ts_add,
    triple_set_op_add_Al = rs_ts_add_Al,
    triple_set_op_add_Bl = rs_ts_add_Bl,
    triple_set_op_add_Cl = rs_ts_add_Cl,
    triple_set_op_delete = rs_ts_delete,
    triple_set_op_to_list = rs_ts_to_list,
    triple_set_op_from_list = rs_ts_from_list,
    triple_set_op_image_filter = rs_ts_image_filter,
    triple_set_op_filter = rs_ts_filter,
    triple_set_op_image = rs_ts_image \<rparr>"

  lemma rs_ts_ops_unfold :
    shows 
      "triple_set_op_\<alpha> rs_ts_ops = rs_ts_\<alpha>"
      "triple_set_op_invar rs_ts_ops = rs_ts_invar"
      "triple_set_op_empty rs_ts_ops = rs_ts_empty"
      "triple_set_op_memb rs_ts_ops = rs_ts_memb"
      "triple_set_op_add rs_ts_ops = rs_ts_add"
      "triple_set_op_add_Al rs_ts_ops = rs_ts_add_Al"
      "triple_set_op_add_Bl rs_ts_ops = rs_ts_add_Bl"
      "triple_set_op_add_Cl rs_ts_ops = rs_ts_add_Cl"
      "triple_set_op_delete rs_ts_ops = rs_ts_delete"
      "triple_set_op_to_list rs_ts_ops = rs_ts_to_list"
      "triple_set_op_from_list rs_ts_ops = rs_ts_from_list"
      "triple_set_op_image_filter rs_ts_ops = rs_ts_image_filter"
      "triple_set_op_filter rs_ts_ops = rs_ts_filter"
      "triple_set_op_image rs_ts_ops = rs_ts_image"
     unfolding rs_ts_ops_def by simp_all

  lemma rs_ts_ops_impl :
    shows "StdTripleSet rs_ts_ops"
   unfolding StdTripleSet_def rs_ts_ops_def
     apply (simp)
     apply (intro conjI rs_ts_it_impl rs_ts_empty_impl
                rs_ts_add_impl rs_ts_delete_impl
                rs_ts_add_Al_impl rs_ts_add_Bl_impl rs_ts_add_Cl_impl
                rs_ts_to_list_impl rs_ts_from_list_impl rs_ts_filter_impl
                rs_ts_image_filter_impl rs_ts_image_impl rs_ts_memb_impl 
                tsga_it_implies_finite[of _ _ rs_ts_it])                
   done

   interpretation rs_tsr: StdTripleSet rs_ts_ops by (rule rs_ts_ops_impl)

end
