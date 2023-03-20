section \<open> NFA by RBTs \<close>
theory RBT_NFAImpl 
imports "../../NFAByLTS" "../../NFAGA" RBT_LTS_DLTS_LTSImpl  
        (* "HOL-Library.Efficient_Nat" *)
begin

subsection \<open> NFAs \<close>

interpretation rs_nfa_defs: nfa_by_lts_defs "rs_ops :: (nat, (nat, unit) RBT.rbt) oset_ops" 
  rs_ops rs_lts_dlts_ops  
  unfolding nfa_by_lts_defs_def
  apply (simp add: rs.StdSet_axioms rs_lts_dlts_impl)
done

type_synonym 'b rs_nfa =                  
   "(nat, unit) RBT.rbt \<times>
    ('b, unit) RBT.rbt \<times>
    ((nat, ('b, (nat, unit) RBT.rbt) RBT.rbt) RBT.rbt,
     (nat, ('b, nat) RBT.rbt) RBT.rbt) LTS_choice \<times>
    (nat, unit) RBT.rbt \<times> (nat, unit) RBT.rbt \<times> nfa_props"

definition rs_nfa_\<alpha> :: "('a::linorder) rs_nfa \<Rightarrow> (nat, 'a) NFA_rec" 
  where "rs_nfa_\<alpha> \<equiv> rs_nfa_defs.nfa_\<alpha>"
definition "rs_nfa_invar \<equiv> rs_nfa_defs.nfa_invar"
definition "rs_nfa_states \<equiv> rs_nfa_defs.nfa_states"
definition "rs_nfa_labels \<equiv> rs_nfa_defs.nfa_labels"
definition "rs_nfa_trans \<equiv> rs_nfa_defs.nfa_trans"
definition "rs_nfa_initial \<equiv> rs_nfa_defs.nfa_initial"
definition "rs_nfa_accepting \<equiv> rs_nfa_defs.nfa_accepting"
definition "rs_nfa_props \<equiv> rs_nfa_defs.nfa_props"
definition "rs_nfa_construct_gen \<equiv> rs_nfa_defs.nfa_construct_gen"
definition "rs_nfa_construct \<equiv> rs_nfa_defs.nfa_construct"
definition "rs_dfa_construct \<equiv> rs_nfa_defs.dfa_construct"
definition "rs_nfa_destruct \<equiv> rs_nfa_defs.nfa_destruct"
definition "rs_nfa_destruct_simple \<equiv> rs_nfa_defs.nfa_destruct_simple"
definition "rs_nfa_states_no \<equiv> rs_nfa_defs.nfa_states_no"
definition "rs_nfa_labels_no \<equiv> rs_nfa_defs.nfa_labels_no"
definition "rs_nfa_trans_no \<equiv> rs_nfa_defs.nfa_trans_no rs_lts_dlts_it"
definition "rs_nfa_initial_no \<equiv> rs_nfa_defs.nfa_initial_no"
definition "rs_nfa_final_no \<equiv> rs_nfa_defs.nfa_final_no"
definition "rs_nfa_accept \<equiv> rs_nfa_defs.accept_impl rs_iteratei rs_lts_dlts_succ_it"

definition "rs_nfa_accept_nfa \<equiv> rs_nfa_defs.accept_nfa_impl rs_iteratei rs_lts_dlts_succ_it"
definition "rs_nfa_accept_dfa \<equiv> rs_nfa_defs.accept_dfa_impl"

definition "rs_nfa_rename_states \<equiv> rs_nfa_defs.rename_states_impl rs_image rs_lts_dlts_image False"
definition "rs_nfa_rename_states_dfa \<equiv> rs_nfa_defs.rename_states_impl rs_image rs_lts_dlts_image_dlts True"
definition "rs_nfa_rename_labels_gen \<equiv> rs_nfa_defs.rename_labels_impl_gen rs_lts_dlts_image"
definition "rs_nfa_rename_labels \<equiv> rs_nfa_defs.rename_labels_impl rs_lts_dlts_image rs_image"
definition "rs_nfa_dfa_construct_reachable \<equiv> rs_nfa_defs.NFA_construct_reachable_impl_code 
  rs_lts_dlts_add_choice rm_ops"
definition "rs_nfa_construct_reachable \<equiv> rs_nfa_dfa_construct_reachable False"
definition "rs_dfa_construct_reachable \<equiv> rs_nfa_dfa_construct_reachable True"
definition "rs_dfa_construct_reachable_fun \<equiv> NFAGA.construct_by_fun rs_dfa_construct_reachable rs_iteratei"
definition "rs_nfa_normalise \<equiv> rs_nfa_defs.nfa_normalise_impl rs_lts_dlts_add_choice rm_ops rs_lts_dlts_succ_label_it"
definition "rs_nfa_reverse \<equiv> rs_nfa_defs.nfa_reverse_impl rs_lts_dlts_reverse"
definition "rs_nfa_complement \<equiv> rs_nfa_defs.nfa_complement_impl"
definition "rs_nfa_bool_comb_gen \<equiv> rs_nfa_defs.bool_comb_gen_impl rs_lts_dlts_add_choice rm_ops  
   rs_lts_dlts_succ_label_it rs_lts_dlts_succ_it" 
definition "rs_nfa_bool_comb \<equiv> rs_nfa_defs.bool_comb_impl rs_lts_dlts_add_choice rm_ops  
   rs_lts_dlts_succ_label_it rs_lts_dlts_succ_it" 
definition "rs_nfa_right_quotient_lists \<equiv> rs_nfa_defs.right_quotient_lists_impl
   rm_ops rs_lts_dlts_filter_it"
definition "rs_nfa_determinise \<equiv> rs_nfa_defs.determinise_impl rs_lts_dlts_add_choice rm_ops rm_ops
  rs_iteratei rs_iteratei rs_iteratei rs_iteratei rs_lts_dlts_succ_it"
definition "rs_nfa_Brzozowski \<equiv> NFAGA.Brzozowski_impl rs_nfa_reverse rs_nfa_determinise"

definition "rs_nfa_language_is_empty \<equiv> rs_nfa_defs.language_is_empty_impl rs_nfa_normalise"
definition "rs_nfa_language_is_univ \<equiv> NFAGA.NFAGA_language_is_univ rs_nfa_determinise rs_nfa_complement
  rs_nfa_language_is_empty"
definition "rs_nfa_language_is_subset \<equiv> 
  NFAGA.NFAGA_language_is_subset rs_nfa_determinise rs_nfa_complement
   (rs_nfa_bool_comb op\<and>) rs_nfa_language_is_empty"
definition "rs_nfa_language_is_eq \<equiv> NFAGA.NFAGA_language_is_eq rs_nfa_language_is_subset"


text \<open> Prepare lts for Hopcroft \<close>

definition lsnd_lss_copy where
  "lsnd_lss_copy = mergesort"

lemma lsnd_lss_copy_impl :
  "set_copy lsnd_\<alpha> lsnd_invar lss_\<alpha> lss_invar lsnd_lss_copy"
unfolding set_copy_def lsnd_invar_def lss_\<alpha>_def lsnd_\<alpha>_def lss_invar_def lsnd_lss_copy_def
by (simp add: mergesort_correct)

lemma lss_lss_copy_impl :
  "set_copy lss_\<alpha> lss_invar lss_\<alpha> lss_invar id"
unfolding set_copy_def 
by simp

interpretation rs_hop_ltsr! :  Hopcroft_lts rm_ops rm_ops iam_ops lss_ops lss_ops 
  id rm_iteratei iam_iteratei lss_union_list
  unfolding Hopcroft_lts_def 
  by (simp add: lssr.StdSet_axioms rmr.StdMap_axioms lss_ops_unfold lss_union_list_impl
                rm_ops_unfold lsndr.StdSet_axioms rm_iteratei_impl lsnd_ops_unfold
                lss_lss_copy_impl iamr.StdMap_axioms iam_iteratei_impl iam_ops_unfold)

definition "rs_hop_lts_\<alpha> \<equiv> rs_hop_ltsr.hopcroft_lts_\<alpha>"
definition "rs_hop_lts_invar \<equiv> rs_hop_ltsr.hopcroft_lts_invar"
definition "rs_hop_lts_\<alpha>2 \<equiv> rs_hop_ltsr.hopcroft_lts_\<alpha>2"
definition "rs_hop_lts_invar2 \<equiv> rs_hop_ltsr.hopcroft_lts_invar2"

lemma rs_hop_no_copy : 
  "rs_hop_lts_\<alpha>2 = rs_hop_lts_\<alpha>"
  "rs_hop_lts_invar2 = rs_hop_lts_invar"
unfolding rs_hop_lts_invar2_def rs_hop_lts_invar_def
          rs_hop_lts_\<alpha>2_def rs_hop_lts_\<alpha>_def
          rs_hop_ltsr.hopcroft_lts_invar_def
          rs_hop_ltsr.hopcroft_lts_invar2_def
          rs_hop_ltsr.hopcroft_lts_\<alpha>_def
          rs_hop_ltsr.hopcroft_lts_\<alpha>2_def
by simp_all

definition "rs_hop_lts_empty \<equiv> rs_hop_ltsr.hopcroft_lts_empty"
definition "rs_hop_lts_add \<equiv> rs_hop_ltsr.hopcroft_lts_add"
definition "rs_hop_lts_copy \<equiv> id"
definition "rs_hop_lts_get_succs \<equiv> rs_hop_ltsr.hopcroft_lts_get_succ_set"

interpretation rs_hop!: nfa_by_lts_hop "rs_ops :: (nat, (nat, unit) RBT.rbt) oset_ops" 
  rs_ops rs_lts_dlts_ops lss_\<alpha> lss_invar iam_ops iam_ops iam_ops iam_ops rm_ops rs_iteratei rs_iteratei lss_iteratei lss_iteratei rm_iteratei
  by unfold_locales

definition "rs_nfa_sm_update \<equiv> rs_hop.sm_update"
definition "rs_nfa_Hopcroft \<equiv> rs_hop.Hopcroft_minimise_impl rs_hop_lts_empty
   rs_hop_lts_add rs_hop_lts_get_succs rs_hop_lts_copy
   rs_image rs_lts_dlts_it rs_lts_dlts_image_dlts"

definition "rs_nfa_Hopcroft_NFA \<equiv> \<lambda>A. rs_nfa_Hopcroft (rs_nfa_determinise A)"

lemmas rs_nfa_defs =
  rs_nfa_props_def
  rs_nfa_\<alpha>_def
  rs_nfa_invar_def 
  rs_nfa_states_def
  rs_nfa_labels_def
  rs_nfa_trans_def
  rs_nfa_initial_def
  rs_nfa_accepting_def
  rs_nfa_construct_gen_def
  rs_nfa_construct_def
  rs_dfa_construct_def
  rs_nfa_destruct_def
  rs_nfa_destruct_simple_def
  rs_nfa_states_no_def
  rs_nfa_labels_no_def
  rs_nfa_trans_no_def
  rs_nfa_initial_no_def
  rs_nfa_final_no_def
  rs_nfa_accept_def
  rs_nfa_accept_nfa_def
  rs_nfa_accept_dfa_def
  rs_nfa_rename_labels_gen_def
  rs_nfa_rename_labels_def
  rs_nfa_rename_states_def
  rs_nfa_rename_states_dfa_def
  rs_nfa_dfa_construct_reachable_def
  rs_nfa_construct_reachable_def
  rs_dfa_construct_reachable_def
  rs_dfa_construct_reachable_fun_def
  rs_nfa_normalise_def
  rs_nfa_reverse_def
  rs_nfa_complement_def
  rs_nfa_bool_comb_gen_def
  rs_nfa_bool_comb_def
  rs_nfa_right_quotient_lists_def
  rs_nfa_determinise_def
  rs_nfa_Brzozowski_def
  rs_hop_lts_\<alpha>_def
  rs_hop_lts_invar_def
  rs_hop_lts_\<alpha>2_def
  rs_hop_lts_invar2_def
  rs_hop_lts_empty_def
  rs_hop_lts_add_def
  rs_hop_lts_get_succs_def
  rs_hop_lts_copy_def
  rs_nfa_Hopcroft_def
  rs_nfa_Hopcroft_NFA_def
  rs_nfa_language_is_empty_def
  rs_nfa_language_is_univ_def
  rs_nfa_language_is_subset_def
  rs_nfa_language_is_eq_def
  rs_nfa_sm_update_def


lemmas rs_nfa_states_code[code] = rs_nfa_defs.nfa_states_def[folded rs_nfa_defs]
lemmas rs_nfa_labels_code[code] = rs_nfa_defs.nfa_labels_def[folded rs_nfa_defs]
lemmas rs_nfa_trans_code[code] = rs_nfa_defs.nfa_trans_def[folded rs_nfa_defs]
lemmas rs_nfa_initial_code[code] = rs_nfa_defs.nfa_initial_def[folded rs_nfa_defs]
lemmas rs_nfa_accepting_code[code] = rs_nfa_defs.nfa_accepting_def[folded rs_nfa_defs]
lemmas rs_nfa_props_code[code] = rs_nfa_defs.nfa_props_simp[folded rs_nfa_defs]

lemmas rs_nfa_impl = rs_nfa_defs.nfa_by_lts_correct [folded rs_nfa_defs]
interpretation rs_nfa!: nfa rs_nfa_\<alpha> rs_nfa_invar  
  using rs_nfa_impl .

lemmas rs_nfa_construct_gen_code[code] = rs_nfa_defs.nfa_construct_gen.simps 
   [folded rs_nfa_defs, unfolded rs_nfa_defs.nfa_construct_aux_def]

lemmas rs_nfa_construct_code[code] = rs_nfa_defs.nfa_construct_def [folded rs_nfa_defs]
lemmas rs_dfa_construct_code[code] = rs_nfa_defs.dfa_construct_def [folded rs_nfa_defs]
lemmas rs_nfa_construct_impl = rs_nfa_defs.nfa_construct_correct[folded rs_nfa_defs]
interpretation rs_nfa!: nfa_from_list rs_nfa_\<alpha> rs_nfa_invar rs_nfa_construct 
  using rs_nfa_construct_impl .
lemmas rs_dfa_construct_impl = rs_nfa_defs.dfa_construct_correct[folded rs_nfa_defs]
interpretation rs_nfa!: dfa_from_list rs_nfa_\<alpha> rs_nfa_invar rs_dfa_construct 
  using rs_dfa_construct_impl .

lemmas rs_nfa_destruct_code[code] = rs_nfa_defs.nfa_destruct.simps [folded rs_nfa_defs]
lemmas rs_nfa_destruct_impl = rs_nfa_defs.nfa_destruct_correct[folded rs_nfa_defs]
interpretation rs_nfa!: nfa_to_list rs_nfa_\<alpha> rs_nfa_invar rs_nfa_destruct 
  using rs_nfa_destruct_impl .

lemmas rs_nfa_destruct_simple_code[code] = rs_nfa_defs.nfa_destruct_simple.simps [folded rs_nfa_defs]
lemmas rs_nfa_destruct_simple_impl = rs_nfa_defs.nfa_destruct_simple_correct[folded rs_nfa_defs]
interpretation rs_nfa!: nfa_to_list_simple rs_nfa_\<alpha> rs_nfa_invar rs_nfa_destruct_simple
  using rs_nfa_destruct_simple_impl .

lemmas rs_nfa_states_no_code[code] = rs_nfa_defs.nfa_states_no.simps [folded rs_nfa_defs]
lemmas rs_nfa_labels_no_code[code] = rs_nfa_defs.nfa_labels_no.simps [folded rs_nfa_defs]
lemmas rs_nfa_trans_no_code[code] = rs_nfa_defs.nfa_trans_no.simps [of rs_lts_dlts_it, folded rs_nfa_defs]
lemmas rs_nfa_final_no_code[code] = rs_nfa_defs.nfa_final_no.simps [folded rs_nfa_defs]
lemmas rs_nfa_initial_no_code[code] = rs_nfa_defs.nfa_initial_no.simps [folded rs_nfa_defs]

lemmas rs_nfa_stats_impl = rs_nfa_defs.nfa_stats_correct[unfolded rs_lts_dlts_ops_unfold rs_dlts_ops_unfold, 
    OF rs_lts_dlts_it_impl, folded rs_nfa_defs]
interpretation rs_nfa!:  nfa_stats rs_nfa_\<alpha> rs_nfa_invar rs_nfa_states_no 
  rs_nfa_labels_no rs_nfa_trans_no rs_nfa_initial_no rs_nfa_final_no 
  using rs_nfa_stats_impl .

lemmas rs_nfa_accept_nfa_code[code] = rs_nfa_defs.accept_nfa_impl_code [of rs_iteratei rs_lts_dlts_succ_it, folded rs_nfa_defs]
lemmas rs_nfa_accept_dfa_code[code] = rs_nfa_defs.accept_dfa_impl_code [folded rs_nfa_defs]
lemmas rs_nfa_accept_code[code] = rs_nfa_defs.accept_impl_def [of rs_iteratei rs_lts_dlts_succ_it, folded rs_nfa_defs]

lemmas rs_nfa_accept_impl = rs_nfa_defs.accept_impl_correct[unfolded rs_ops_unfold rs_lts_dlts_ops_unfold,
OF rs_iteratei_impl, OF rs_lts_dlts_succ_it_impl, folded rs_nfa_defs]
interpretation rs_nfa!: nfa_accept rs_nfa_\<alpha> rs_nfa_invar rs_nfa_accept 
  using rs_nfa_accept_impl .

lemmas rs_nfa_rename_labels_gen_code [code] = rs_nfa_defs.rename_labels_impl_gen_code [of rs_lts_dlts_image, folded rs_nfa_defs, unfolded rs_lts_dlts_ops_unfold]
lemmas rs_nfa_rename_labels_gen_impl = rs_nfa_defs.rename_labels_impl_gen_correct
   [OF rs_nfa_defs.nfa_by_lts_defs_axioms,
    unfolded rs_ops_unfold rs_dlts_ops_unfold rs_lts_dlts_ops_unfold,
    OF rs_lts_dlts_image_impl,
    folded rs_lts_dlts_defs rs_nfa_defs]

lemmas rs_nfa_rename_labels_code [code] = rs_nfa_defs.rename_labels_impl_def
   [of rs_lts_dlts_image rs_image, folded rs_lts_dlts_defs rs_nfa_defs]
lemmas rs_nfa_rename_labels_impl = rs_nfa_defs.rename_labels_impl_correct
   [OF rs_nfa_defs.nfa_by_lts_defs_axioms,
    unfolded rs_ops_unfold rs_dlts_ops_unfold rs_lts_dlts_ops_unfold, 
    OF rs_lts_dlts_image_impl rs_image_impl,
    folded rs_lts_dlts_defs rs_nfa_defs]
interpretation rs_nfa!: nfa_rename_labels rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar 
   "rs_nfa_rename_labels False" using rs_nfa_rename_labels_impl .

lemmas rs_nfa_rename_states_code [code] = rs_nfa_defs.rename_states_impl_code
   [of rs_image rs_lts_dlts_image False, folded rs_lts_dlts_defs rs_nfa_defs]
lemmas rs_nfa_rename_states_impl = rs_nfa_defs.rename_states_impl_correct
   [OF rs_nfa_defs.nfa_by_lts_defs_axioms,
    unfolded rs_ops_unfold rs_dlts_ops_unfold rs_lts_dlts_ops_unfold, 
    OF rs_image_impl rs_lts_dlts_image_impl,
    folded rs_lts_dlts_defs rs_nfa_defs]
interpretation rs_nfa!: nfa_rename_states rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar 
   rs_nfa_rename_states using rs_nfa_rename_states_impl .

lemmas rs_nfa_rename_states_dfa_code [code] = rs_nfa_defs.rename_states_impl_code
   [of rs_image rs_lts_dlts_image_dlts True, folded rs_lts_dlts_defs rs_nfa_defs]
lemmas rs_nfa_rename_states_dfa_impl = rs_nfa_defs.rename_states_impl_correct_dfa
   [OF rs_nfa_defs.nfa_by_lts_defs_axioms,
    unfolded rs_ops_unfold rs_dlts_ops_unfold rs_lts_dlts_ops_unfold, 
    OF rs_image_impl rs_lts_dlts_image_dlts_impl,
    folded rs_lts_dlts_defs rs_nfa_defs]
interpretation rs_nfa!: dfa_rename_states rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar 
   rs_nfa_rename_states_dfa using rs_nfa_rename_states_dfa_impl .

lemmas rs_nfa_dfa_construct_reachable_code [code] = rs_nfa_defs.NFA_construct_reachable_impl_code_def 
  [of rs_lts_dlts_add_choice rm_ops, folded rs_nfa_defs]

lemmas rs_nfa_dfa_construct_reachable_impl = rs_nfa_defs.NFA_construct_reachable_impl_code_correct
   [OF rmr.StdMap_axioms, unfolded rs_lts_dlts_ops_unfold, OF rs_lts_dlts_add_choice_impl,
   folded rs_nfa_defs, unfolded rs_ops_unfold]
lemmas rs_nfa_construct_reachable_impl = nfa_dfa_construct_sublocale_nfa [OF rs_nfa_dfa_construct_reachable_impl, folded rs_nfa_defs]
lemmas rs_dfa_construct_reachable_impl = nfa_dfa_construct_sublocale_dfa [OF 
   rs_nfa_dfa_construct_reachable_impl, of _ _ True, folded rs_nfa_defs]
lemmas rs_nfa_construct_reachable_no_enc_impl = 
   nfa_construct_no_enc_default [OF rs_nfa_construct_reachable_impl]
lemmas rs_dfa_construct_reachable_no_enc_impl = 
   dfa_construct_no_enc_default [OF rs_dfa_construct_reachable_impl]

lemmas rs_dfa_construct_reachable_fun_code [code] = construct_by_fun_alt_def 
  [of rs_dfa_construct_reachable rs_iteratei, folded rs_nfa_defs]
lemmas rs_dfa_construct_reachable_fun_impl = construct_by_fun_correct [OF rs_dfa_construct_reachable_impl rs_iteratei_impl,
  folded rs_nfa_defs]
lemmas rs_dfa_construct_reachable_no_enc_fun_impl =
   dfa_construct_no_enc_fun_default [OF rs_dfa_construct_reachable_fun_impl]

lemmas rs_nfa_normalise_code [code] = rs_nfa_defs.nfa_normalise_impl_def 
  [of rs_lts_dlts_add_choice rm_ops rs_lts_dlts_succ_label_it, unfolded rs_lts_dlts_ops_unfold, folded rs_nfa_defs]

lemmas rs_nfa_normalise_impl = rs_nfa_defs.nfa_normalise_correct
   [unfolded rs_lts_dlts_ops_unfold rs_dlts_ops_unfold rs_ops_unfold, 
    OF rmr.StdMap_axioms  rs_lts_dlts_add_choice_impl rs_lts_dlts_succ_label_it_impl, folded rs_nfa_defs]
interpretation rs_nfa!: nfa_normalise rs_nfa_\<alpha> rs_nfa_invar rs_nfa_normalise  
  using rs_nfa_normalise_impl .

lemmas rs_nfa_reverse_code [code] = rs_nfa_defs.nfa_reverse_impl_def
  [of rs_lts_dlts_reverse, folded rs_nfa_defs, unfolded rs_lts_dlts_ops_unfold]
lemmas rs_nfa_reverse_impl = rs_nfa_defs.nfa_reverse_impl_correct
   [OF rs_nfa_defs.nfa_by_lts_defs_axioms, unfolded rs_lts_dlts_ops_unfold rs_dlts_ops_unfold rs_ops_unfold, 
    OF rs_lts_dlts_reverse_impl,folded rs_nfa_defs]
interpretation rs_nfa!: nfa_reverse rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar rs_nfa_reverse  
  using rs_nfa_reverse_impl .

lemmas rs_nfa_complement_code [code] = rs_nfa_defs.nfa_complement_impl_def [folded rs_nfa_defs]
lemmas rs_nfa_complement_impl = rs_nfa_defs.nfa_complement_impl_correct
   [folded rs_nfa_defs]
interpretation rs_nfa!: nfa_complement rs_nfa_\<alpha> rs_nfa_invar rs_nfa_complement 
  using rs_nfa_complement_impl .

lemmas rs_nfa_bool_comb_gen_code [code] = rs_nfa_defs.bool_comb_gen_impl_code [of  rs_lts_dlts_add_choice rm_ops
rs_lts_dlts_succ_label_it rs_lts_dlts_succ_it, folded rs_nfa_defs]
lemmas rs_nfa_bool_comb_gen_impl = rs_nfa_defs.bool_comb_gen_impl_correct
   [unfolded rs_lts_dlts_ops_unfold rs_dlts_ops_unfold rs_ops_unfold,
    OF rmr.StdMap_axioms rs_lts_dlts_add_choice_impl rs_lts_dlts_succ_label_it_impl rs_lts_dlts_succ_it_impl, folded rs_nfa_defs]

lemmas rs_nfa_bool_comb_code [code] = rs_nfa_defs.bool_comb_impl_code [of rs_lts_dlts_add_choice rm_ops
rs_lts_dlts_succ_label_it rs_lts_dlts_succ_it, folded rs_nfa_defs]

lemmas rs_nfa_bool_comb_impl = rs_nfa_defs.bool_comb_impl_correct
   [unfolded rs_lts_dlts_ops_unfold rs_ops_unfold,
    OF rmr.StdMap_axioms rs_lts_dlts_add_choice_impl rs_lts_dlts_succ_label_it_impl rs_lts_dlts_succ_it_impl, folded rs_nfa_defs]
interpretation rs_nfa!: 
 nfa_bool_comb_same rs_nfa_\<alpha> rs_nfa_invar rs_nfa_bool_comb  
   using rs_nfa_bool_comb_impl .

lemmas rs_nfa_right_quotient_lists_code [code] = rs_nfa_defs.right_quotient_lists_impl_code [of rm_ops
rs_lts_dlts_filter_it, folded rs_nfa_defs]
lemmas rs_nfa_right_quotient_lists_impl = rs_nfa_defs.right_quotient_lists_impl_correct
   [unfolded rs_lts_dlts_ops_unfold rs_ops_unfold,
    OF rmr.StdMap_axioms rs_lts_dlts_filter_it_impl, folded rs_nfa_defs]
interpretation rs_nfa!: 
 nfa_right_quotient_lists rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar rs_nfa_right_quotient_lists   
   using rs_nfa_right_quotient_lists_impl .

lemmas rs_nfa_determinise_code [code] = rs_nfa_defs.determinise_impl_code [of rs_lts_dlts_add_choice rm_ops rm_ops
  rs_iteratei rs_iteratei rs_iteratei rs_iteratei rs_lts_dlts_succ_it, 
  folded rs_nfa_defs, unfolded rs_nfa_defs.NFA_construct_reachable_impl_code_def]
lemmas rs_nfa_determinise_impl = rs_nfa_defs.determinise_impl_correct
   [unfolded rs_lts_dlts_ops_unfold rs_dlts_ops_unfold rs_ops_unfold,
    OF rs_iteratei_impl rs_iteratei_impl rs_iteratei_impl rs_iteratei_impl
       rs_lts_dlts_succ_it_impl rs_lts_dlts_add_choice_impl rmr.StdMap_axioms rmr.StdMap_axioms, folded rs_nfa_defs]
interpretation rs_nfa!: 
 nfa_determinise rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar rs_nfa_determinise    
   using rs_nfa_determinise_impl .


lemmas rs_nfa_Brzozowski_code [code] = NFAGA.Brzozowski_impl_def [of rs_nfa_reverse rs_nfa_determinise, folded rs_nfa_defs]
lemmas rs_nfa_Brzozowski_impl = NFAGA.Brzozowski_impl_correct [OF rs_nfa_reverse_impl rs_nfa_determinise_impl, folded rs_nfa_defs]
interpretation rs_nfa_min_Brzozowski!: 
 nfa_minimise rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar rs_nfa_Brzozowski     
   using rs_nfa_Brzozowski_impl .

lemmas rs_nfa_language_is_empty_code [code] = rs_nfa_defs.language_is_empty_impl_code [of rs_nfa_normalise, folded rs_nfa_defs]
lemmas rs_nfa_language_is_empty_impl = rs_nfa_defs.language_is_empty_impl_correct[folded rs_nfa_defs, OF rs_nfa_normalise_impl,
  folded rs_nfa_defs]
interpretation rs_nfa!: nfa_language_is_empty rs_nfa_\<alpha> rs_nfa_invar rs_nfa_language_is_empty 
 using rs_nfa_language_is_empty_impl .

lemmas rs_nfa_language_is_univ_code [code] = NFAGA.NFAGA_language_is_univ_def [of rs_nfa_determinise rs_nfa_complement rs_nfa_language_is_empty, folded rs_nfa_defs]
lemmas rs_nfa_language_is_univ_impl = NFAGA.NFAGA_language_is_univ_correct [folded rs_nfa_defs, 
  OF rs_nfa_complement_impl rs_nfa_determinise_impl rs_nfa_language_is_empty_impl,
  folded rs_nfa_defs]
interpretation rs_nfa!: nfa_language_is_univ rs_nfa_\<alpha> rs_nfa_invar rs_nfa_language_is_univ 
 using rs_nfa_language_is_univ_impl .

lemmas rs_nfa_language_is_subset_code [code] =  NFAGA.NFAGA_language_is_subset_def [of rs_nfa_determinise rs_nfa_complement 
  "rs_nfa_bool_comb op\<and>" rs_nfa_language_is_empty, folded rs_nfa_defs]
lemmas rs_nfa_language_is_subset_impl = NFAGA.NFAGA_language_is_subset_correct [folded rs_nfa_defs, 
  OF rs_nfa_complement_impl rs_nfa_determinise_impl  rs_nfa_bool_comb_impl rs_nfa_language_is_empty_impl,
  folded rs_nfa_defs]
interpretation rs_nfa!: nfa_language_is_subset rs_nfa_\<alpha> rs_nfa_invar rs_nfa_language_is_subset 
 using rs_nfa_language_is_subset_impl .

lemmas rs_nfa_language_is_eq_code [code] = NFAGA.NFAGA_language_is_eq_def [of  
  rs_nfa_language_is_subset, folded rs_nfa_defs]
lemmas rs_nfa_language_is_eq_impl = NFAGA.NFAGA_language_is_eq_correct [folded rs_nfa_defs, 
  OF rs_nfa_language_is_subset_impl, folded rs_nfa_defs]
interpretation rs_nfa!: nfa_language_is_eq rs_nfa_\<alpha> rs_nfa_invar rs_nfa_language_is_eq 
 using rs_nfa_language_is_eq_impl .

lemmas rs_hop_lts_empty_code [code_unfold] = rs_hop_lts_empty_def [unfolded rs_hop_ltsr.hopcroft_lts_empty_def]
lemmas rs_hop_lts_empty_impl = rs_hop_ltsr.hopcroft_lts_empty_correct[folded rs_nfa_defs]

lemmas rs_hop_lts_add_code [code] = rs_hop_lts_add_def [unfolded rs_hop_ltsr.hopcroft_lts_add_alt_def]
lemmas rs_hop_lts_add_impl = rs_hop_ltsr.hopcroft_lts_add_correct[folded rs_nfa_defs]

lemma rs_hop_lts_copy_impl : "lts_copy rs_hop_lts_\<alpha> rs_hop_lts_invar rs_hop_lts_\<alpha>2
 rs_hop_lts_invar2 rs_hop_lts_copy"
unfolding lts_copy_def rs_hop_lts_copy_def rs_hop_no_copy by simp

lemmas rs_hop_lts_get_succs_code [code] = rs_hop_lts_get_succs_def [unfolded rs_hop_ltsr.hopcroft_lts_get_succ_set_def[abs_def]]
lemmas rs_hop_lts_get_succs_impl = rs_hop_ltsr.hopcroft_lts_get_succ_set_correct[folded rs_nfa_defs, unfolded lss_ops_unfold]

lemmas rs_nfa_Hopcroft_impl = rs_hop.Hopcroft_minimise_impl_correct [OF rs_nfa_defs.nfa_by_lts_defs_axioms,
  unfolded rs_ops_unfold rm_ops_unfold rs_lts_dlts_ops_unfold rs_dlts_ops_unfold,
  OF rs_image_impl rs_lts_dlts_image_dlts_impl rs_lts_dlts_it_impl
     rs_hop_lts_empty_impl rs_hop_lts_add_impl rs_hop_lts_get_succs_impl rs_hop_lts_copy_impl, folded rs_nfa_defs]

interpretation rs_nfa_min_Hopcroft!: 
 dfa_minimise rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar rs_nfa_Hopcroft
  using rs_nfa_Hopcroft_impl .

lemmas rs_nfa_sm_update_code [code] = rs_hop.sm_update.simps[folded rs_nfa_sm_update_def]
lemmas rs_nfa_Hopcroft_code [code] = rs_hop.Hopcroft_minimise_impl_code[of rs_hop_lts_empty rs_hop_lts_add rs_hop_lts_get_succs rs_hop_lts_copy rs_image rs_lts_dlts_it
   rs_lts_dlts_image_dlts,
  unfolded rs_hop.Hopcroft_code_def rs_hop.Hopcroft_code_step_def rs_hop.Hopcroft_code_step_compute_iM_swap_check_def rs_hop.class_map_init_pred_code_def,
  folded rs_nfa_defs]

lemmas rs_nfa_Hopcroft_NFA_code [code] = rs_nfa_Hopcroft_NFA_def
lemmas rs_nfa_Hopcroft_NFA_impl = NFAGA_minimisation_with_determinisation [OF rs_nfa_determinise_impl rs_nfa_Hopcroft_impl,
unfolded o_def, folded rs_nfa_defs]
interpretation rs_nfa_min_Hopcroft_NFA!: 
 nfa_minimise rs_nfa_\<alpha> rs_nfa_invar rs_nfa_\<alpha> rs_nfa_invar rs_nfa_Hopcroft_NFA
   using rs_nfa_Hopcroft_NFA_impl .

definition rs_nfa_ops :: "(nat,'a::{linorder},'a rs_nfa) nfa_ops" where
   "rs_nfa_ops \<equiv> \<lparr>
    nfa_op_\<alpha> = rs_nfa_\<alpha>,
    nfa_op_invar = rs_nfa_invar,
    nfa_op_nfa_from_list = rs_nfa_construct,
    nfa_op_dfa_from_list = rs_dfa_construct,
    nfa_op_to_list = rs_nfa_destruct,
    nfa_op_to_list_simple = rs_nfa_destruct_simple,
    nfa_op_states_no = rs_nfa_states_no,
    nfa_op_labels_no = rs_nfa_labels_no,
    nfa_op_trans_no = rs_nfa_trans_no,
    nfa_op_initial_no = rs_nfa_initial_no,
    nfa_op_final_no = rs_nfa_final_no,
    nfa_op_accept = rs_nfa_accept,
    nfa_op_rename_labels = rs_nfa_rename_labels False,
    nfa_op_normalise = rs_nfa_normalise,
    nfa_op_reverse = rs_nfa_reverse,
    nfa_op_complement = rs_nfa_complement,
    nfa_op_bool_comb = rs_nfa_bool_comb,
    nfa_op_determinise = rs_nfa_determinise,
    nfa_op_minimise_Brzozowski = rs_nfa_Brzozowski,
    nfa_op_minimise_Hopcroft = rs_nfa_Hopcroft,
    nfa_op_minimise_Hopcroft_NFA = rs_nfa_Hopcroft_NFA,
    nfa_op_right_quotient_lists = rs_nfa_right_quotient_lists,
    nfa_op_language_is_empty = rs_nfa_language_is_empty,
    nfa_op_language_is_univ = rs_nfa_language_is_univ,
    nfa_op_language_is_subset = rs_nfa_language_is_subset,
    nfa_op_language_is_eq = rs_nfa_language_is_eq \<rparr>"

lemma rs_nfa_ops_unfold[code_unfold] :
   "nfa_op_\<alpha> rs_nfa_ops = rs_nfa_\<alpha>"
   "nfa_op_invar rs_nfa_ops = rs_nfa_invar"
   "nfa_op_nfa_from_list rs_nfa_ops = rs_nfa_construct"
   "nfa_op_dfa_from_list rs_nfa_ops = rs_dfa_construct"
   "nfa_op_to_list rs_nfa_ops = rs_nfa_destruct"
   "nfa_op_to_list_simple rs_nfa_ops = rs_nfa_destruct_simple"
   "nfa_op_states_no rs_nfa_ops = rs_nfa_states_no"
   "nfa_op_labels_no rs_nfa_ops = rs_nfa_labels_no"
   "nfa_op_trans_no rs_nfa_ops = rs_nfa_trans_no"
   "nfa_op_initial_no rs_nfa_ops = rs_nfa_initial_no"
   "nfa_op_final_no rs_nfa_ops = rs_nfa_final_no"
   "nfa_op_accept rs_nfa_ops = rs_nfa_accept"
   "nfa_op_rename_labels rs_nfa_ops = rs_nfa_rename_labels False"
   "nfa_op_normalise rs_nfa_ops = rs_nfa_normalise"
   "nfa_op_reverse rs_nfa_ops = rs_nfa_reverse"
   "nfa_op_complement rs_nfa_ops = rs_nfa_complement"
   "nfa_op_bool_comb rs_nfa_ops = rs_nfa_bool_comb"
   "nfa_op_determinise rs_nfa_ops = rs_nfa_determinise"
   "nfa_op_minimise_Brzozowski rs_nfa_ops = rs_nfa_Brzozowski"
   "nfa_op_minimise_Hopcroft rs_nfa_ops = rs_nfa_Hopcroft"
   "nfa_op_minimise_Hopcroft_NFA rs_nfa_ops = rs_nfa_Hopcroft_NFA"
   "nfa_op_right_quotient_lists rs_nfa_ops = rs_nfa_right_quotient_lists"
   "nfa_op_language_is_empty rs_nfa_ops = rs_nfa_language_is_empty"
   "nfa_op_language_is_univ rs_nfa_ops = rs_nfa_language_is_univ"
   "nfa_op_language_is_subset rs_nfa_ops = rs_nfa_language_is_subset"
   "nfa_op_language_is_eq rs_nfa_ops = rs_nfa_language_is_eq"
  by (simp_all add: rs_nfa_ops_def)

lemmas rs_nfa_impls =
  rs_nfa_impl 
  rs_nfa_construct_impl 
  rs_dfa_construct_impl
  rs_nfa_destruct_impl
  rs_nfa_destruct_simple_impl
  rs_nfa_stats_impl
  rs_nfa_accept_impl
  rs_nfa_rename_labels_impl
  rs_nfa_rename_labels_gen_impl
  rs_nfa_normalise_impl
  rs_nfa_complement_impl
  rs_nfa_bool_comb_gen_impl
  rs_nfa_bool_comb_impl
  rs_nfa_determinise_impl
  rs_nfa_reverse_impl
  rs_nfa_right_quotient_lists_impl
  rs_nfa_Brzozowski_impl
  rs_nfa_Hopcroft_impl
  rs_nfa_Hopcroft_NFA_impl
  rs_nfa_language_is_empty_impl
  rs_nfa_language_is_univ_impl
  rs_nfa_language_is_subset_impl
  rs_nfa_language_is_eq_impl

lemma rs_nfa_StdNFA_impl: "StdNFA rs_nfa_ops"
  apply (rule StdNFA.intro)
  apply (simp_all add: rs_nfa_ops_def rs_nfa_impls nfa_minimise_sublocale)
done

end
