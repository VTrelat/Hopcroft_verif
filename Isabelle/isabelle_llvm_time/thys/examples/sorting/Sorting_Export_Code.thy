theory Sorting_Export_Code
imports (* Sorting_PDQ *) Sorting_Introsort Sorting_Strings
begin
  
text \<open>
  We instantiate Introsort and Pdqsort for unsigned \<open>i64\<close>, and for dynamic arrays of \<open>i8\<close>s \<open>string_assn\<close>.
  We then export code and generate a C header file to interface the code.
\<close>

global_interpretation unat_sort: pure_sort_impl_context "(\<le>)" "(<)" "TYPE(64)" ll_icmp_ult  "cost ''icmp_ult'' 1" unat_assn
  defines unat_sort_is_guarded_insert_impl = unat_sort.is_guarded_insert_impl
      and unat_sort_is_unguarded_insert_impl = unat_sort.is_unguarded_insert_impl
      and unat_sort_unguarded_insertion_sort_impl = unat_sort.unguarded_insertion_sort_impl
      and unat_sort_guarded_insertion_sort_impl = unat_sort.guarded_insertion_sort_impl
      and unat_sort_final_insertion_sort_impl = unat_sort.final_insertion_sort_impl
      and unat_sort_sift_down_impl   = unat_sort.sift_down_impl
      and unat_sort_heapify_btu_impl = unat_sort.heapify_btu_impl
      and unat_sort_heapsort_impl    = unat_sort.heapsort_impl
      and unat_sort_qsp_next_l_impl       = unat_sort.qsp_next_l_impl
      and unat_sort_qsp_next_h_impl       = unat_sort.qsp_next_h_impl
      and unat_sort_qs_partition_impl     = unat_sort.qs_partition_impl
      and unat_sort_partition_pivot_impl  = unat_sort.partition_pivot_impl 
      and unat_sort_introsort_aux_impl = unat_sort.introsort_aux_impl
      and unat_sort_move_median_to_first_impl = unat_sort.move_median_to_first_impl
      and unat_sort_introsort_impl        = unat_sort.introsort_impl      
  apply (rule unat_sort_impl_context)
  by simp

lemmas [llvm_inline] = unat_sort.introsort_aux_impl_def 
                      unat_sort.final_insertion_sort_impl_def
                      unat_sort.guarded_insertion_sort_impl_def
                      unat_sort.unguarded_insertion_sort_impl_def
                      unat_sort.is_guarded_insert_impl_def
                      unat_sort.is_unguarded_insert_impl_def

  
schematic_goal unat_sort_allcost_simp: "project_all (unat_sort.introsort_impl_cost n) = ?x"  
  apply (fold norm_cost_tag_def)
  unfolding unat_sort.projected_introsort_cost_simplified
  apply (simp add: unat_sort.Sum_any_cost) (* TODO: Move this lemma to global context *)
  by (rule norm_cost_tagI)
  
(* Final results for unat_sort: *)  
thm unat_sort.introsort_final_hoare_triple (* Hoare triple *)


(* Cost estimation *)
  
theorem unat_sort_allcost_nlogn: 
  "(\<lambda>n. real (project_all (unat_sort.introsort_impl_cost n))) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  unfolding unat_sort_allcost_simp
  by auto2



global_interpretation string_sort: sort_impl_context "(\<le>)" "(<)" "TYPE(64)" "strcmp_impl'"
              "strcmp_cost' n" "bstring_assn n TYPE(64) TYPE('w::len2)"
  defines string_sort_is_guarded_insert_impl = string_sort.is_guarded_insert_impl
      and string_sort_is_unguarded_insert_impl = string_sort.is_unguarded_insert_impl
      and string_sort_unguarded_insertion_sort_impl = string_sort.unguarded_insertion_sort_impl
      and string_sort_guarded_insertion_sort_impl = string_sort.guarded_insertion_sort_impl
      and string_sort_final_insertion_sort_impl = string_sort.final_insertion_sort_impl
      and string_sort_sift_down_impl   = string_sort.sift_down_impl
      and string_sort_heapify_btu_impl = string_sort.heapify_btu_impl
      and string_sort_heapsort_impl    = string_sort.heapsort_impl
      and string_sort_qsp_next_l_impl       = string_sort.qsp_next_l_impl
      and string_sort_qsp_next_h_impl       = string_sort.qsp_next_h_impl
      and string_sort_qs_partition_impl     = string_sort.qs_partition_impl
      and string_sort_partition_pivot_impl  = string_sort.partition_pivot_impl 
      and string_sort_introsort_aux_impl = string_sort.introsort_aux_impl
      and string_sort_move_median_to_first_impl = string_sort.move_median_to_first_impl
      and string_sort_introsort_impl        = string_sort.introsort_impl  
    
      and string_sort_cmpo_v_idx_impl = string_sort.cmpo_v_idx_impl
      and string_sort_cmpo_idxs_impl = string_sort.cmpo_idxs_impl
      and string_sort_cmp_idxs_impl = string_sort.cmp_idxs_impl
      
  apply (rule strcmp_sort_impl_context)
  by simp


(*lemma cheat[llvm_code,llvm_inline]: "(strcmp_impl :: 'w word ptr \<times> 'size_t word \<times> 'size_t word
   \<Rightarrow> 'w word ptr \<times> 'size_t word \<times> 'size_t word
      \<Rightarrow> 1 word llM) a v = return 1"
  sorry
*)  

print_named_simpset llvm_inline

term "sort_impl_context.cmpo_v_idx_impl"

thm string_sort.cmpo_v_idx_impl_def
(*lemmas [llvm_inline] = strcmp_impl_def (*string_sort.cmpo_v_idx_impl_def*) *)

lemmas [llvm_inline] = string_sort.introsort_aux_impl_def 
                      string_sort.final_insertion_sort_impl_def
                      string_sort.guarded_insertion_sort_impl_def
                      string_sort.unguarded_insertion_sort_impl_def
                      string_sort.is_guarded_insert_impl_def
                      string_sort.is_unguarded_insert_impl_def 

(* TODO: Move and Dup *)
lemma Sum_any_cost: "Sum_any (the_acost (cost n x)) = x"
  unfolding cost_def by (simp add: zero_acost_def)


lemma sum_any_push_costmul: "Sum_any (the_acost (n *m c)) = n * (Sum_any (the_acost c))" for n :: nat 
  apply (cases c) subgoal for x
  apply (auto simp: costmult_def algebra_simps) 
  apply (cases "finite {a. x a \<noteq> 0}"; cases "n=0")
  apply (simp_all add: Sum_any_right_distrib)
  done done

term "\<Theta>\<^sub>2"

term "string_sort.introsort_impl_cost"

schematic_goal string_sort_allcost_simp: "project_all (string_sort.introsort_impl_cost m n) = ?x"  
  apply (fold norm_cost_tag_def)
  unfolding string_sort.projected_introsort_cost_simplified
  unfolding strcmp_cost'_def strcmp_cost_def compare_cost_def compare1_body_cost_def min_cost_def
  apply (simp add: string_sort.Sum_any_cost norm_cost) (* TODO: Move this lemma to global context *)

  apply(simp add: the_acost_propagate add.assoc) 
  
  supply acost_finiteIs = finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero finite_the_acost_mult_nonzeroI
  
  apply (subst Sum_any.distrib, (intro acost_finiteIs;fail), (intro acost_finiteIs;fail))+
  apply (simp only: Sum_any_cost sum_any_push_costmul)
  apply (simp add: add_ac)

  by (rule norm_cost_tagI)

concrete_definition string_sort_allcost is string_sort_allcost_simp 
thm string_sort_allcost_def
thm string_sort_allcost.refine


lemma string_sort_allcost_absch: "(\<lambda>(m::nat,n::nat). real (string_sort_allcost m n)) \<in> \<Theta>\<^sub>2(\<lambda>(m::nat,n::nat). (real m) *  (real n) * ln (real n) )"
  unfolding string_sort_allcost_def
  by auto2

lemmas string_sort_introsort_cost = string_sort_allcost_absch[unfolded string_sort_allcost.refine[symmetric]]

(* *)
term dynamiclist_empty_impl
term dyn_array_push_impl

lemmas [llvm_code] = dynamiclist_empty_impl_def dyn_array_push_impl_def

type_synonym llstring = "(8 word ptr * 64 word * 64 word)"

definition str_init :: "llstring ptr \<Rightarrow> unit llM" where [llvm_code]:
  "str_init sp \<equiv> doM {
    t \<leftarrow> ll_call dynamiclist_empty_impl;
    ll_store t sp
  }"

definition str_append :: "llstring ptr \<Rightarrow> 8 word \<Rightarrow> unit llM" where [llvm_code]:
  "str_append sp x \<equiv> doM {
    s \<leftarrow> ll_load sp;
    s \<leftarrow> ll_call (dyn_array_push_impl s x);
    ll_store s sp
  }"

  
definition llstrcmp :: "llstring ptr \<Rightarrow> _ \<Rightarrow> 8 word llM" where [llvm_code]:
  "llstrcmp ap bp \<equiv> doM {
    a \<leftarrow> ll_load ap;
    b \<leftarrow> ll_load bp;
    r \<leftarrow> strcmp_impl' a b;
    t \<leftarrow> ll_icmp_ne r 0;
    llc_if t (return 1) (return 0)
  }"


context size_t_context begin  
  lemmas [llvm_inline] = 
    has_enough_space_impl_def dyn_list_push_basic_impl_def dyn_list_double_impl_def
    list_copy_impl_def narray_free_def
    

end

(*
export_llvm "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t,int64_t)"
  file "../code/introsort.ll"

export_llvm   "string_sort_introsort_impl :: (8 word ptr \<times> 64 word \<times> 64 word) ptr \<Rightarrow> _" is "llstring* str_introsort(llstring*, int64_t, int64_t)"
*)
export_llvm 
  "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" 
  "string_sort_introsort_impl :: (8 word ptr \<times> 64 word \<times> 64 word) ptr \<Rightarrow> _" is "llstring* str_introsort(llstring*, int64_t, int64_t)"  
  "str_init" is "void str_init(llstring *)"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring*)"

 defines \<open>typedef struct {char *data; struct {int64_t size; int64_t capacity;};} llstring;\<close> 
  file "../code/introsort.ll"



(* Final results for string_sort: *)  
thm string_sort.introsort_final_hoare_triple  (* Hoare triple *)
 string_sort_introsort_cost

end
