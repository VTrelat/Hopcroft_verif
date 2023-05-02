section \<open>LLVM Shallow Embedding --- Reasoning Setup\<close>
theory LLVM_Shallow_RS
imports 
  "../basic/LLVM_Basic_Main"
  LLVM_Memory_RS
begin


subsection \<open>Monadification Setup for VCG\<close>

ML \<open>
  structure LLVM_VCG_Monadify = struct
    structure Monadify = Gen_Monadify_Cong (
    
      fun mk_return x = @{mk_term "return ?x ::_ llM"}
      fun mk_bind m f = @{mk_term "bind ?m ?f ::_ llM"}
    
      fun dest_return @{mpat "return ?x ::_ llM"} = SOME x | dest_return _ = NONE
      fun dest_bind @{mpat "bind ?m ?f ::_ llM"} = SOME (m,f) | dest_bind _ = NONE
      
      fun dest_monadT (Type (@{type_name M},[T,@{typ unit},@{typ cost},@{typ llvm_memory},@{typ err}])) = SOME T | dest_monadT _ = NONE
      val bind_return_thm = @{lemma "bind m return = m" by simp}
      val return_bind_thm = @{lemma "bind (return x) f = f x" by simp}
      val bind_bind_thm = @{lemma "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)" by simp}
      
    )
    
    val _ = Theory.setup
     (Attrib.setup \<^binding>\<open>vcg_const\<close>
      (Args.term >> (fn t => Thm.declaration_attribute (K (Monadify.prepare_add_const_decl t))))
      "declaration of new vcg-constant")

    fun monadify_all_tac ctxt = CONVERSION (Conv.top_sweep_conv (Monadify.monadify_conv) ctxt)
      
  end
\<close>

named_theorems vcg_monadify_xforms

method_setup vcg_monadify_raw = \<open>Scan.succeed (SIMPLE_METHOD' o LLVM_VCG_Monadify.monadify_all_tac)\<close>
method vcg_monadify_xform_raw = (simp only: vcg_monadify_xforms)?


(* xform (monadify xform)+ *)
method vcg_monadify uses simp = 
  vcg_monadify_xform_raw; ((changed \<open>vcg_monadify_raw; vcg_monadify_xform_raw\<close>)+)?


(* TODO: Automatically do monadification when preparing Hoare triple! *)

declare llvm_inline_bind_laws[vcg_monadify_xforms]


subsection \<open>Abbreviations for VCG\<close>


type_synonym ll_astate = "llvm_amemory \<times> ecost"
type_synonym ll_assn = "(ll_astate \<Rightarrow> bool)"

definition "ll_\<alpha> \<equiv> lift_\<alpha>_cost llvm_\<alpha>"
abbreviation llvm_htriple 
  :: "ll_assn \<Rightarrow> 'a llM \<Rightarrow> ('a \<Rightarrow> ll_assn) \<Rightarrow> bool" 
  where "llvm_htriple \<equiv> htriple_gc GC ll_\<alpha>"
(*abbreviation llvm_htripleF 
  :: "ll_assn \<Rightarrow> ll_assn \<Rightarrow> 'a llM \<Rightarrow> ('a \<Rightarrow> ll_assn) \<Rightarrow> bool" 
  where "llvm_htripleF \<equiv> htripleF ll_\<alpha>"*)
abbreviation "llSTATE \<equiv> STATE ll_\<alpha>"
abbreviation "llPOST \<equiv> POSTCOND ll_\<alpha>"

abbreviation (input) ll_cost_assn ("$$") where "ll_cost_assn \<equiv> \<lambda>name n. $lift_acost (cost name n)"  

locale llvm_prim_setup begin
(* Locale to contain primitive VCG setup, without data refinement *)


end

subsection \<open>General VCG Setup\<close>
lemma fri_extract_prod_case[fri_extract_simps]: "(case p of (a,b) \<Rightarrow> (P a b :: ll_assn)) = (EXS a b. \<up>(p=(a,b)) ** P a b)"  
  apply (cases p) apply (rule ext)
  apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
  done
  
lemma norm_prod_case[vcg_normalize_simps]:
  "wp (case p of (a,b) \<Rightarrow> f a b) Q s \<longleftrightarrow> (\<forall>a b. p=(a,b) \<longrightarrow> wp (f a b) Q s)" 
  by (auto split: prod.split) 

lemmas ll_notime_htriple_eq = notime_htriple_eq[of llvm_\<alpha> _ "_::_ llM", folded ll_\<alpha>_def]
  
lemma ll_consume_rule[vcg_rules]: "llvm_htriple ($lift_acost c) (consume c) (\<lambda>_. \<box>)"
  unfolding ll_\<alpha>_def using consume_rule
  by (simp)
  
subsection \<open>Assertions\<close>

(*
xxx: notatiooN!
definition time_credits_assn :: "ecost \<Rightarrow> ll_assn" ("$_" [900] 900) where "($c) \<equiv> SND (EXACT c)"


term "a ** $c"
term "c ** $a"

(* For presentation *)
lemma "($c) (s,c') \<longleftrightarrow> s=0 \<and> c'=c"
  unfolding time_credits_assn_def by (simp add: sep_algebra_simps SND_def) (* TODO: Lemmas for SND! *)
*)

  
typedef ('a,'c) dr_assn = "UNIV :: ('a \<Rightarrow> 'c \<Rightarrow> ll_assn) set" by simp
setup_lifting type_definition_dr_assn
  
lemma dr_assn_inverses[simp]:
  "Abs_dr_assn (Rep_dr_assn A) = A"
  "Rep_dr_assn (Abs_dr_assn B) = B"
  using Rep_dr_assn_inverse Abs_dr_assn_inverse by auto

definition dr_assn_prefix :: "('a, 'b) dr_assn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ll_assn" ("\<upharpoonleft>_" [1000] 1000) where
  "\<upharpoonleft>A a c \<equiv> Rep_dr_assn A a c"
  
definition "is_pure A \<equiv> \<forall>a c. sep_is_pure_assn (\<upharpoonleft>A a c)"

definition dr_assn_pure_prefix ("\<upharpoonleft>\<^sub>p_" [1000] 1000) where  
  "\<upharpoonleft>\<^sub>pA a c \<equiv> \<up>pure_part (\<upharpoonleft>A a c)"
  
definition dr_assn_pure_asm_prefix ("\<flat>\<^sub>p_" [1000] 1000) where  
  "\<flat>\<^sub>pA a c \<equiv> pure_part (\<upharpoonleft>A a c) \<and> is_pure A"
  
lemma pure_fri_rule[fri_rules]: "PRECOND (SOLVE_ASM (\<flat>\<^sub>pA a c)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>\<^sub>pA a c"  
  unfolding vcg_tag_defs entails_def dr_assn_pure_prefix_def dr_assn_pure_asm_prefix_def
    is_pure_def
  apply clarsimp
  apply (subst pure_part_pure_eq[symmetric])  
  apply (auto simp: sep_algebra_simps)
  done

lemma prepare_pure_assn[named_ss fri_prepare_simps]: "\<upharpoonleft>A a c = \<upharpoonleft>\<^sub>pA a c" if "is_pure A"
  using that 
  by (simp add: dr_assn_pure_prefix_def is_pure_def)

lemma extract_pure_assn[fri_extract_simps]: "\<upharpoonleft>A a c = \<up>\<flat>\<^sub>pA a c" if "is_pure A"
  using that
  unfolding vcg_tag_defs entails_def dr_assn_pure_asm_prefix_def is_pure_def
  apply (auto simp: sep_algebra_simps)
  done
  
attribute_setup is_pure_rule = \<open>Attrib.add_del 
    (VCG_Lib.chained_decl_attr @{context} @{attributes [named_ss fri_prepare_simps, fri_extract_simps]})
    (VCG_Lib.chained_decl_attr @{context} @{attributes [named_ss fri_prepare_simps del, fri_extract_simps del]})
  \<close>
  \<open>Rules to introduce pure assertions\<close>


(*lemmas [vcg_prep_ext_start_rules] = 
  rev_mp[of "pure_part _"]
  rev_mp[of "llSTATE _ _"]
  rev_mp[of "\<flat>\<^sub>p _ _ _"]
*)  

text \<open>This rule is to be overloaded by later rules\<close>  
(*lemma thin_pure[vcg_prep_ext_rules]: "pure_part A \<Longrightarrow> True" ..*)
    
lemma pure_part_pureD[vcg_prep_ext_rules]: "pure_part (\<up>\<Phi>) \<Longrightarrow> \<Phi>" by simp

lemma prep_ext_state[vcg_prep_ext_rules]: 
  "llSTATE P s \<Longrightarrow> pure_part P"  
  unfolding STATE_def by (blast intro: pure_partI)
  
lemma prep_ext_pure_part_pure[vcg_prep_ext_rules]: 
  "pure_part (\<upharpoonleft>\<^sub>pA a c) \<Longrightarrow> pure_part (\<upharpoonleft>A a c)"  
  unfolding dr_assn_pure_prefix_def by simp
    
lemma thin_dr_pure_asm[vcg_prep_ext_rules]: "(\<flat>\<^sub>pA a c) \<Longrightarrow> pure_part (\<upharpoonleft>A a c)"
  unfolding dr_assn_pure_asm_prefix_def by simp
  
definition "mk_assn \<equiv> Abs_dr_assn"  
definition "mk_pure_assn A \<equiv> mk_assn (\<lambda>a c. \<up>A a c)"  

lemma is_pure_mk_pure[simp]: "is_pure (mk_pure_assn A)"
  unfolding is_pure_def mk_pure_assn_def mk_assn_def dr_assn_prefix_def
  by (auto)

lemma sel_mk_assn[simp]: "\<upharpoonleft>(mk_assn A) a c = A a c"  
  by (auto simp: mk_assn_def dr_assn_prefix_def)
  
lemma sel_mk_pure_assn[simp]: 
  "\<upharpoonleft>(mk_pure_assn A) a c = \<up>(A a c)"
  "\<upharpoonleft>\<^sub>p(mk_pure_assn A) a c = \<up>(A a c)"
  "\<flat>\<^sub>p(mk_pure_assn A) a c = A a c"
  apply (auto simp: mk_pure_assn_def dr_assn_pure_prefix_def dr_assn_pure_asm_prefix_def)
  apply (auto simp: mk_assn_def is_pure_def dr_assn_prefix_def sep_algebra_simps)
  done
  
lemma mk_pure_assn_extractI:
  assumes "pure_part (\<upharpoonleft>(mk_pure_assn A) a c)"
  assumes "A a c \<Longrightarrow> \<Phi> a c"
  shows "\<Phi> a c"
  using assms
  by auto

lemma mk_assn_extractI:  
  assumes "pure_part (\<upharpoonleft>(mk_assn A) a c)"
  assumes "A a c \<turnstile> \<up>\<Phi> a c ** sep_true"
  shows "\<Phi> a c"
  using assms
  apply (cases "\<Phi> a c"; simp)
  using entails_eqI by fastforce
  
  
lemma mk_assn_extractI':
  assumes "pure_part (\<upharpoonleft>(mk_assn A) a c)"
  assumes "FRAME (A a c) (\<up>\<Phi> a c) F"
  shows "\<Phi> a c"
  apply (rule mk_assn_extractI[OF assms(1)])
  using assms(2) unfolding FRAME_def
  by (metis (no_types, lifting) entails_def entails_mp sep_conj_commute)
  
lemma pure_part_mk_assnD[vcg_prep_ext_rules]: 
  "pure_part (\<upharpoonleft>(mk_assn f) a c) \<Longrightarrow> pure_part (f a c)" 
  by auto
  
  
    
(* Use as [fri_rules] to for 'matching' of abstract values by auto during frame inference *)
lemma fri_abs_cong_rl: "PRECOND (SOLVE_AUTO (a=a')) \<Longrightarrow> \<upharpoonleft>A a c \<turnstile> \<upharpoonleft>A a' c"  
  unfolding vcg_tag_defs by auto

  

subsection \<open>Memory Reasoning\<close>
locale llvm_prim_mem_setup begin
  sublocale llvm_prim_setup .
end  

subsubsection \<open>Pointers\<close>

text \<open>Assertion for pointer to single value\<close>
definition ll_pto :: "('a::llvm_rep, 'a ptr) dr_assn"
  where "ll_pto \<equiv> mk_assn (\<lambda>v p. FST (llvm_pto (to_val v) (the_raw_ptr p)))"

instantiation ptr :: (llvm_rep) addr_algebra begin  
  definition "abase \<equiv> abase o the_raw_ptr"
  definition "acompat a b \<equiv> acompat (the_raw_ptr a) (the_raw_ptr b)"
  definition "adiff a b \<equiv> adiff (the_raw_ptr a) (the_raw_ptr b)"
  definition aidx_ptr :: "'a ptr \<Rightarrow> int \<Rightarrow> 'a ptr" where "aidx a i \<equiv> PTR (aidx (the_raw_ptr a) i)"
  
  instance
    apply standard
    apply (intro part_equivpI sympI transpI)
    unfolding abase_ptr_def acompat_ptr_def adiff_ptr_def aidx_ptr_def
    apply (metis acompat_equiv part_equivp_def ptr.sel)
    apply (auto intro: acompat_sym acompat_trans simp: acompat_dom)
    done

end
  
  
text \<open>Assertion to range of array\<close>  
definition "ll_range I \<equiv> mk_assn (\<lambda>f p. \<up>(abase p) ** (\<Union>*i\<in>I. \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i)))"

lemma ll_range_preep_pure[vcg_prep_ext_rules]: 
  "pure_part (\<upharpoonleft>(ll_range I) f p) \<Longrightarrow> abase p"
  unfolding ll_range_def
  apply (erule mk_assn_extractI')
  by vcg_try_solve
  
lemma ll_range_not_base: "\<not>abase p \<Longrightarrow> \<upharpoonleft>(ll_range I) f p = sep_false"
  unfolding ll_range_def by auto

lemma null_not_base[simp]: "\<not>abase null"  
  apply (auto simp: abase_ptr_def null_def)
  apply (auto simp: abase_llvm_ptr_def llvm_null_def)
  done
  
lemma ll_range_not_null[simp]: "\<upharpoonleft>(ll_range I) f null = sep_false"
  by (simp add: ll_range_not_base)
  
    
lemma ll_pto_not_same: "(\<upharpoonleft>ll_pto x p ** \<upharpoonleft>ll_pto y p) = sep_false"
  apply (rule ext)
  apply (auto simp: ll_pto_def llvm_pto_def ab.ba.pto_def split: rptr.splits addr.splits)
  apply (auto simp: sep_algebra_simps sep_conj_def)
  apply (auto simp: sep_disj_llvm_amemory_def sep_algebra_simps ab.pto_def split: baddr.splits)
  apply (auto simp: vpto_assn_def)
  done


lemma ll_range_merge: "I\<^sub>1\<inter>I\<^sub>2={} \<Longrightarrow> (\<upharpoonleft>(ll_range I\<^sub>1) f p ** \<upharpoonleft>(ll_range I\<^sub>2) f p) = \<upharpoonleft>(ll_range (I\<^sub>1\<union>I\<^sub>2)) f p"
  unfolding ll_range_def
  by (auto simp: sep_algebra_simps)

lemma ll_range_bogus_upd[simp]: "x\<notin>I \<Longrightarrow> \<upharpoonleft>(ll_range I) (f(x:=v)) p = \<upharpoonleft>(ll_range I) f p"  
  unfolding ll_range_def
  apply (cases "abase p"; simp add: sep_algebra_simps)
  by (rule sep_set_img_cong) (auto)
  
  
lemma open_ll_range: "i\<in>I \<Longrightarrow> \<upharpoonleft>(ll_range I) f p = (\<up>abase p ** \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i) ** \<upharpoonleft>(ll_range (I-{i})) f p)"
  unfolding ll_range_def
  apply (cases "abase p"; simp add: sep_algebra_simps)
  by (auto simp:  sep_set_img_remove)

lemma 
  assumes "I\<inter>I'\<noteq>{}"  
  assumes "F \<turnstile> \<upharpoonleft>(ll_range (I'-I)) f p ** F'"
  shows "\<upharpoonleft>(ll_range I) f p ** F \<turnstile> \<upharpoonleft>(ll_range I') f p ** \<upharpoonleft>(ll_range (I-I')) f p ** F'"
proof -
  have "\<upharpoonleft>(ll_range I) f p ** F \<turnstile> \<upharpoonleft>(ll_range I) f p ** \<upharpoonleft>(ll_range (I'-I)) f p ** F'"
    using assms(2) conj_entails_mono by blast
  also have "\<dots> = (\<upharpoonleft>(ll_range (I \<union> (I'-I))) f p ** F')"
    apply (subst ll_range_merge[symmetric])
    by auto
  also have "\<dots> = ((\<upharpoonleft>(ll_range I') f p ** \<upharpoonleft>(ll_range (I-I')) f p) ** F')"
    apply (rewrite in "_=\<hole>" ll_range_merge)
    apply (auto simp: Un_commute)
    done
  finally show ?thesis by simp  
qed    
    
  
(* TODO: Move *)

thm vcg_normalize_simps

lemma FST_pure[sep_algebra_simps, vcg_normalize_simps]: "FST (\<up>\<phi>) = \<up>\<phi>"
  unfolding FST_def by (simp add: fun_eq_iff pred_lift_extract_simps sep_algebra_simps)

lemma FST_extract_pure[sep_algebra_simps, vcg_normalize_simps]: "FST (\<up>\<phi> ** Q) = (\<up>\<phi> ** FST Q)"  
  unfolding FST_def by (simp add: fun_eq_iff pred_lift_extract_simps sep_algebra_simps)

  
(********************)  
text \<open>Frame inference setup to consume excess credits when solving entailments\<close>
(* TODO: Move *)
lemma GC_move_left[named_ss fri_prepare_simps]:
  "NO_MATCH GC P \<Longrightarrow> (P ** GC) = (GC ** P)"
  "NO_MATCH GC Q \<Longrightarrow> (Q ** GC ** P) = (GC ** Q ** P)"
  "(GC ** GC) = GC"
  "(GC ** GC ** P) = (GC ** P)"
  "FRAME_INFER P (GC ** Q) \<box> = FRAME_INFER P Q GC"
  by (simp_all add: sep_algebra_simps sep_conj_c FRAME_INFER_def)
  
lemmas [fri_end_rules] = empty_ent_GC entails_GC

lemma consume_credits_fri_end_rule[fri_end_rules]: "P\<turnstile>GC \<Longrightarrow> $c**P \<turnstile> GC"
  using conj_entails_mono entails_GC by fastforce


print_named_simpset fri_prepare_simps    

(********************)  
  
  
  
subsubsection \<open>Load and Store\<close>
context llvm_prim_mem_setup begin
lemma checked_from_val_rule[vcg_rules]: "llvm_htriple \<box> (checked_from_val (to_val x)) (\<lambda>r. \<up>(r=x))"  
  unfolding checked_from_val_def
  supply [fri_rules] = empty_ent_GC
  by vcg
  
  
lemmas [vcg_rules] = ll_notime_htriple_eq[THEN iffD1, OF llvm_load_rule]
lemmas [vcg_rules] = ll_notime_htriple_eq[THEN iffD1, OF llvm_store_rule]

(*

  $\<^bsub>''load''\<^esub>

  $$ ''load'' 1

  $\<^bsub>load\<^esub>
  
    
*)


text \<open>Standard rules for load and store from pointer\<close>  
lemma ll_load_rule[vcg_rules]: "llvm_htriple ($$ ''load'' 1 ** \<upharpoonleft>ll_pto x p) (ll_load p) (\<lambda>r. \<up>(r=x) ** \<upharpoonleft>ll_pto x p)"
  unfolding ll_load_def ll_pto_def 
  by vcg
  

lemma ll_store_rule[vcg_rules]: "llvm_htriple ($$ ''store'' 1 ** \<upharpoonleft>ll_pto xx p) (ll_store x p) (\<lambda>_. \<upharpoonleft>ll_pto x p)"
  unfolding ll_store_def ll_pto_def
  by vcg
  
text \<open>Rules for load and store from indexed pointer, wrt. range\<close>  

lemmas [fri_extract_simps] = sep_conj_assoc


find_theorems htriple EXTRACT
thm vcg_decomp_rules

lemma ll_load_rule_range[vcg_rules]:
  shows "llvm_htriple ($$ ''load'' 1 ** \<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( p' ~\<^sub>a p \<and> p' -\<^sub>a p \<in> I )) (ll_load p') (\<lambda>r. \<up>(r = a (p' -\<^sub>a p)) ** \<upharpoonleft>(ll_range I) a p)"
  unfolding vcg_tag_defs
  apply (rule htriple_vcgI')
  apply fri_extract_basic
  apply (simp add: open_ll_range)
  apply fri_extract
  apply vcg
  done

lemma ll_store_rule_range[vcg_rules]:
  shows "llvm_htriple ($$ ''store'' 1 ** \<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( p' ~\<^sub>a p \<and> p' -\<^sub>a p \<in> I )) (ll_store x p') (\<lambda>_. \<upharpoonleft>(ll_range I) (a(p' -\<^sub>a p := x)) p)"
  unfolding vcg_tag_defs
  apply (rule htriple_vcgI')
  apply fri_extract_basic
  apply (simp add: open_ll_range)
  apply fri_extract
  by vcg

subsubsection \<open>Offsetting Pointers\<close>

(* TODO: The LLVM semantics also allows pointers one past the end of a range, 
  which is not supported by these rules yet.
*)

lemmas [vcg_rules] = ll_notime_htriple_eq[THEN iffD1, OF llvm_checked_idx_ptr_rule]



text \<open>Rule for indexing pointer. Note, the new target address must exist\<close>
lemma ll_ofs_ptr_rule[vcg_rules]: 
  "llvm_htriple 
    ($$ ''ofs_ptr'' 1 ** \<upharpoonleft>ll_pto v (p +\<^sub>a (sint i)) ** \<up>\<^sub>!(abase p))
    (ll_ofs_ptr p i) 
    (\<lambda>r. \<up>(r= p +\<^sub>a (sint i)) ** \<upharpoonleft>ll_pto v (p +\<^sub>a (sint i)))"
  unfolding ll_ofs_ptr_def ll_pto_def abase_ptr_def aidx_ptr_def
  by vcg

text \<open>Rule for indexing pointer into range. Note, the new target address must exist\<close>
  
lemma ll_ofs_ptr_rule'[vcg_rules]: 
  shows "llvm_htriple 
    ($$ ''ofs_ptr'' 1 ** \<upharpoonleft>(ll_range I) x p ** \<up>\<^sub>!(p ~\<^sub>a p' \<and> (p' +\<^sub>a sint i) -\<^sub>a p \<in> I)) 
    (ll_ofs_ptr p' i) 
    (\<lambda>r. \<up>(r= p' +\<^sub>a sint i) ** \<upharpoonleft>(ll_range I) x p)"
  unfolding vcg_tag_defs
  supply [named_ss fri_prepare_simps] = open_ll_range
  by vcg
  
subsubsection \<open>Allocate and Free\<close>

(* TODO: Move *)
lemma FST_empty[sep_algebra_simps, vcg_normalize_simps]: "FST \<box> = \<box>"
  unfolding FST_def by (auto simp: sep_algebra_simps)

lemmas [vcg_rules] = ll_notime_htriple_eq[THEN iffD1, OF llvm_allocn_rule, unfolded FST_empty]

(* TODO: Move *)
lemma FST_distrib_img[sep_algebra_simps, vcg_normalize_simps, named_ss fri_prepare_simps]:
  "FST (\<Union>*i\<in>I. P i) = (\<Union>*i\<in>I. FST (P i))"
proof (cases "finite I")
  case True
  then show ?thesis by(induct rule: finite_induct) (simp_all add: FST_empty FST_conj_conv[symmetric])
next
  case False
  then show ?thesis by (auto simp add: FST_def)
qed


text \<open>Memory allocation tag, which expresses ownership of an allocated block.\<close>
definition ll_malloc_tag :: "int \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> _" 
  where "ll_malloc_tag n p \<equiv> $$ ''free'' 1 ** \<up>(n\<ge>0) ** FST (llvm_malloc_tag n (the_raw_ptr p))"

(*
(FST ( (\<Union>*i\<in>{0..<int (unat n)}. llvm_pto (to_val init) (r +\<^sub>a i)) \<and>* llvm_malloc_tag (int (unat n)) r) \<and>* $lift_acost (cost ''free'' (Suc 0)) \<and>* F)

*)  
  
text \<open>Allocation returns an array-base pointer to an initialized range, 
  as well as an allocation tag\<close>
lemma ll_malloc_rule[vcg_rules]: 
  "llvm_htriple 
    ($$ ''malloc'' (unat n) ** $$ ''free'' 1 ** \<up>(n\<noteq>0)) 
    (ll_malloc TYPE('a::llvm_rep) n) 
    (\<lambda>r. \<upharpoonleft>(ll_range {0..< uint n}) (\<lambda>_. init) r ** ll_malloc_tag (uint n) r)"
  unfolding ll_malloc_def ll_pto_def ll_malloc_tag_def ll_range_def 
  supply [simp] = list_conj_eq_sep_set_img (*uint_nat*) abase_ptr_def aidx_ptr_def unat_gt_0
  supply [vcg_normalize_simps] = FST_conj_conv[symmetric]
  apply vcg
  done

  
lemmas [vcg_rules] = ll_notime_htriple_eq[THEN iffD1, OF llvm_free_rule]
  
(* TODO: Move *)
lemma FST_EXS_conv[sep_algebra_simps, named_ss fri_prepare_simps, vcg_normalize_simps]: "FST (EXS x. P x) = (EXS x. FST (P x))"
  by (auto simp: FST_def sep_algebra_simps)

  
text \<open>Free takes a range and the matching allocation tag\<close>
lemma ll_free_rule[vcg_rules]:
  "llvm_htriple 
    (\<upharpoonleft>(ll_range {0..<n}) blk p ** ll_malloc_tag n p)
    (ll_free p)
    (\<lambda>_. \<box>)
  "
  unfolding ll_free_def ll_pto_def ll_malloc_tag_def ll_range_def vcg_tag_defs
  supply [simp] = list_conj_eq_sep_set_img abase_ptr_def aidx_ptr_def 
  supply [named_ss fri_prepare_simps] = sep_set_img_pull_EXS FST_conj_conv[symmetric]
  supply [vcg_normalize_simps] = FST_conj_conv[symmetric]
  by vcg
  
  
end  

  
subsection \<open>Arithmetic Instructions\<close>
  
text \<open>Tag for arithmetic bounds check proof obligations\<close>
definition [vcg_tag_defs]: "WBOUNDS \<Phi> \<longleftrightarrow> \<Phi>"  
lemma WBOUNDSI: "\<Phi> \<Longrightarrow> WBOUNDS \<Phi>" by (simp add: WBOUNDS_def)
lemma WBOUNDSD: "WBOUNDS \<Phi> \<Longrightarrow> \<Phi>" by (simp add: WBOUNDS_def)
declaration \<open>K (Basic_VCG.add_solver (@{thms WBOUNDSI},@{binding solve_wbounds},fn ctxt => SELECT_GOAL (auto_tac ctxt)))\<close>
  
  
abbreviation "in_srange op (a::'a::len word) (b::'a word) \<equiv> op (sint a) (sint b) \<in> sints (LENGTH ('a))"
      
lemma udivrem_is_undef_word_conv:
  fixes a b :: "'a::len word"
  shows "udivrem_is_undef (word_to_lint a) (word_to_lint b) \<longleftrightarrow> b=0"  
  by (auto simp: udivrem_is_undef_def word_to_lint_to_uint_0_iff)
  
lemma sdivrem_is_undef_word_conv:
  fixes a b :: "'a::len word"
  shows "sdivrem_is_undef (word_to_lint a) (word_to_lint b) \<longleftrightarrow> b=0 \<or> \<not>in_srange (sdiv) a b"  
  by (auto simp: sdivrem_is_undef_def sdivrem_ovf_def word_to_lint_to_sint_conv)
  
  
subsubsection \<open>VCG Simplifications and Rules\<close>  
text \<open>
  Most of the rules for arithmetic are set up as simplifications.
  For operations with side-conditions, we have both, 
  a conditional simplification rule and a Hoare-rule. 
  Note that the Hoare-rule will only be tried if the simplification rule did not 
  succeed.
\<close>

(* TODO: Move *)  
abbreviation ll_consume :: "cost \<Rightarrow> unit llM" where "ll_consume \<equiv> consume"
  
context llvm_prim_setup begin
  abbreviation "consume1r n v \<equiv> doM {ll_consume (cost n 1); return v}"
  
  lemma cond_llvm_htripleI: "x = consume1r n y \<Longrightarrow> llvm_htriple ($$ n 1) x (\<lambda>r. \<up>(r=y))" by vcg

end

locale llvm_prim_arith_setup begin

sublocale llvm_prim_setup .

context 
  notes [simp] = op_lift_arith2'_def op_lift_arith2_def 
                  op_lift_cmp_def op_lift_ptr_cmp_def op_lift_iconv_def 
  notes [simp] = word_to_lint_convs[symmetric]
  notes [simp] = from_bool_lint_conv udivrem_is_undef_word_conv sdivrem_is_undef_word_conv
  notes [simp] = word_to_lint_to_uint_conv word_to_lint_to_sint_conv
begin

paragraph \<open>Arithmetic\<close>


lemma ll_add_simp[vcg_normalize_simps]: "ll_add a b = consume1r ''add'' (a + b)" by (auto simp: ll_add_def)
lemma ll_sub_simp[vcg_normalize_simps]: "ll_sub a b = consume1r ''sub'' (a - b)" by (auto simp: ll_sub_def)
lemma ll_mul_simp[vcg_normalize_simps]: "ll_mul a b = consume1r ''mul'' (a * b)" by (auto simp: ll_mul_def)
lemma ll_udiv_simp[vcg_normalize_simps]: "b\<noteq>0 \<Longrightarrow> ll_udiv a b = consume1r ''udiv'' (a div b)" by (auto simp: ll_udiv_def)
lemma ll_urem_simp[vcg_normalize_simps]: "b\<noteq>0 \<Longrightarrow> ll_urem a b = consume1r ''urem'' (a mod b)" by (auto simp: ll_urem_def)

lemma ll_sdiv_simp[vcg_normalize_simps]: "\<lbrakk>b\<noteq>0; in_srange (sdiv) a b\<rbrakk> \<Longrightarrow> ll_sdiv a b = consume1r ''sdiv'' (a sdiv b)" 
  by (auto simp: ll_sdiv_def Let_def)
lemma ll_srem_simp[vcg_normalize_simps]: "\<lbrakk>b\<noteq>0; in_srange (sdiv) a b\<rbrakk> \<Longrightarrow> ll_srem a b = consume1r ''srem'' (a smod b)" 
  by (auto simp: ll_srem_def)

lemma ll_udiv_rule[vcg_rules]: "WBOUNDS (b\<noteq>0) \<Longrightarrow> llvm_htriple ($$ ''udiv'' 1) (ll_udiv a b) (\<lambda>r. \<up>(r = a div b))" 
  unfolding vcg_tag_defs by vcg
lemma ll_urem_rule[vcg_rules]: "WBOUNDS (b\<noteq>0) \<Longrightarrow> llvm_htriple ($$ ''urem'' 1) (ll_urem a b) (\<lambda>r. \<up>(r = a mod b))" 
  unfolding vcg_tag_defs by vcg
lemma ll_sdiv_rule[vcg_rules]: "\<lbrakk>WBOUNDS (b\<noteq>0); WBOUNDS (in_srange (sdiv) a b)\<rbrakk> \<Longrightarrow> llvm_htriple ($$ ''sdiv'' 1) (ll_sdiv a b) (\<lambda>r. \<up>(r = a sdiv b))"
  unfolding vcg_tag_defs by vcg
lemma ll_srem_rule[vcg_rules]: "\<lbrakk>WBOUNDS (b\<noteq>0); WBOUNDS (in_srange (sdiv) a b)\<rbrakk> \<Longrightarrow> llvm_htriple ($$ ''srem'' 1) (ll_srem a b) (\<lambda>r. \<up>(r = a smod b))"
  unfolding vcg_tag_defs by vcg

paragraph \<open>Comparison\<close>
lemma ll_icmp_simps[vcg_normalize_simps]: 
  "ll_icmp_eq a b = consume1r ''icmp_eq'' (from_bool (a = b))" 
  "ll_icmp_ne a b = consume1r ''icmp_ne'' (from_bool (a \<noteq> b))" 
  "ll_icmp_sle a b = consume1r ''icmp_sle'' (from_bool (a <=s b))" 
  "ll_icmp_slt a b = consume1r ''icmp_slt'' (from_bool (a <s b))" 
  "ll_icmp_ule a b = consume1r ''icmp_ule'' (from_bool (a \<le> b))" 
  "ll_icmp_ult a b = consume1r ''icmp_ult'' (from_bool (a < b))" 
  unfolding ll_icmp_eq_def ll_icmp_ne_def ll_icmp_sle_def ll_icmp_slt_def ll_icmp_ule_def ll_icmp_ult_def
  by auto

lemma ll_ptrcmp_simps[vcg_normalize_simps]: 
  "ll_ptrcmp_eq a b = consume1r ''ptrcmp_eq'' (from_bool (a = b))" 
  "ll_ptrcmp_ne a b = consume1r ''ptrcmp_ne'' (from_bool (a \<noteq> b))" 
  unfolding ll_ptrcmp_eq_def ll_ptrcmp_ne_def 
  by auto
  
paragraph \<open>Bitwise\<close>

lemma ll_and_simp[vcg_normalize_simps]: "ll_and a b = consume1r ''and'' (a AND b)" by (auto simp: ll_and_def)
lemma ll_or_simp[vcg_normalize_simps]: "ll_or a b = consume1r ''or'' (a OR b)" by (auto simp: ll_or_def)
lemma ll_xor_simp[vcg_normalize_simps]: "ll_xor a b = consume1r ''xor'' (a XOR b)" by (auto simp: ll_xor_def)
  
lemma ll_shl_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_shl (a::'a::len word) b = consume1r ''shl'' (a << unat b)" 
  by (auto simp: ll_shl_def Let_def shift_ovf_def bitSHL'_def)
  
lemma ll_lshr_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_lshr (a::'a::len word) b = consume1r ''lshr'' (a >> unat b)" 
  by (auto simp: ll_lshr_def Let_def shift_ovf_def bitLSHR'_def)

lemma ll_ashr_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_ashr (a::'a::len word) b = consume1r ''ashr'' (a >>> unat b)" 
  by (auto simp: ll_ashr_def Let_def shift_ovf_def bitASHR'_def)
  
lemma [vcg_rules]:
  fixes a b :: "'a::len word" 
  assumes "WBOUNDS (unat b < LENGTH ('a))"  
  shows ll_shl_rule: "llvm_htriple ($$ ''shl'' 1) (ll_shl a b) (\<lambda>r. \<up>(r=a<<unat b))"
    and ll_lshr_rule: "llvm_htriple ($$ ''lshr'' 1) (ll_lshr a b) (\<lambda>r. \<up>(r=a>>unat b))"
    and ll_ashr_rule: "llvm_htriple ($$ ''ashr'' 1) (ll_ashr a b) (\<lambda>r. \<up>(r=a>>>unat b))"
  using assms unfolding vcg_tag_defs
  by vcg  
  
paragraph \<open>Conversion\<close>
    
lemma ll_trunc_simp[vcg_normalize_simps]: "is_down' UCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_trunc (a::'a::len word) TYPE('b::len word) = consume1r ''trunc'' (UCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_trunc_def llb_trunc_def Let_def)
  
lemma ll_zext_simp[vcg_normalize_simps]: "is_up' UCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_zext (a::'a::len word) TYPE('b::len word) = consume1r ''zext'' (UCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_zext_def llb_zext_def Let_def)
  
lemma ll_sext_simp[vcg_normalize_simps]: "is_up' SCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_sext (a::'a::len word) TYPE('b::len word) = consume1r ''sext'' (SCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_sext_def llb_sext_def Let_def)

  
lemmas ll_trunc_rule[vcg_rules] = cond_llvm_htripleI[OF ll_trunc_simp, OF WBOUNDSD]
lemmas ll_zext_rule[vcg_rules] = cond_llvm_htripleI[OF ll_zext_simp, OF WBOUNDSD]
lemmas ll_sext_rule[vcg_rules] = cond_llvm_htripleI[OF ll_sext_simp, OF WBOUNDSD]
    
end
end

subsection \<open>Control Flow\<close>



locale llvm_prim_ctrl_setup begin

sublocale llvm_prim_setup .

text \<open>The if command is handled by a set of normalization rules.
  Note that the VCG will split on the introduced conjunction automatically.
\<close>

lemma llc_if_simps[vcg_normalize_simps]:
  "llc_if 1 t e = doM {consume (cost ''if'' 1); t}"
  "r\<noteq>0 \<Longrightarrow> llc_if r t e = doM {consume (cost ''if'' 1); t}"
  "llc_if 0 t e = doM {consume (cost ''if'' 1); e}"
  by (auto simp: llc_if_def)
  
lemma llc_if_simp[vcg_normalize_simps]: "wp (llc_if b t e) Q s \<longleftrightarrow> wp (ll_consume (cost ''if'' 1)) (\<lambda>_ s. (to_bool b \<longrightarrow> wp t Q s) \<and> (\<not>to_bool b \<longrightarrow> wp e Q s)) s"
  unfolding llc_if_def 
  by (auto simp add: vcg_normalize_simps)
  
(* Probably useless, as we cannot implement that *)
lemma if_simp(*[vcg_normalize_simps]*): "wp (If b t e) Q s \<longleftrightarrow> (b \<longrightarrow> wp t Q s) \<and> (\<not>b \<longrightarrow> wp e Q s)"
  by simp
  
end  
    
text \<open>The while command is handled by a standard invariant/variant rule.\<close>  

lemma llc_while_unfold: "llc_while b f \<sigma> = doM { ll_consume (cost ''call'' 1); ctd \<leftarrow> b \<sigma>; llc_if ctd (doM { \<sigma>\<leftarrow>f \<sigma>; llc_while b f \<sigma>}) (return \<sigma>)}"
  unfolding llc_while_def
  apply (rewrite REC'_unfold[OF reflexive], pf_mono_prover)
  by (simp add: ll_call_def)

definition llc_while_annot :: "('\<sigma>::llvm_rep \<Rightarrow> 't \<Rightarrow> ll_astate \<Rightarrow> bool) \<Rightarrow> ('t\<times>'t) set \<Rightarrow> ('\<sigma>\<Rightarrow>1 word llM) \<Rightarrow> _"
  where [llvm_inline]: "llc_while_annot I R \<equiv> llc_while"

declare [[vcg_const "llc_while_annot I R"]]
  
lemma annotate_llc_while: "llc_while = llc_while_annot I R" by (simp add: llc_while_annot_def) 
  

(* TODO: Move. Some lemmas on how bind and consume commutes if program terminates and throws no exceptions. *)
(* This does not hold: even if everything terminates, m may throw an exception. *)
lemma "mwp (run (doM { r\<leftarrow>m; consume c; return r }) s) N (\<lambda>_. N) E S = mwp (run (doM {consume c; m}) s) N (\<lambda>_. N) E S"
  unfolding mwp_def bind_def consume_def
  apply (auto split: mres.split simp: run_simps)
  oops

lemma "mwp (run (doM { r\<leftarrow>m; consume (c::_::comm_monoid_add); return r }) s) N (\<lambda>_. N) bot S = mwp (run (doM {consume c; m}) s) N (\<lambda>_. N) bot S"
  unfolding mwp_def bind_def consume_def
  by (auto split: mres.split simp: run_simps algebra_simps)
  
lemma "mwp (run (doM { r\<leftarrow>m; consume (c::_::comm_monoid_add); return r }) s) bot bot bot S = mwp (run (doM {consume c; m}) s) bot bot bot S"
  unfolding mwp_def bind_def consume_def
  by (auto split: mres.split simp: run_simps algebra_simps)
  
lemma wp_consume_bind_commute: "wp (doM { r\<leftarrow>m; consume c; f r }) Q = wp (doM {consume c; r\<leftarrow>m; f r}) Q"  
  unfolding wp_def mwp_def bind_def consume_def
  by (auto split: mres.split simp: run_simps algebra_simps fun_eq_iff)
  
lemma wp_consume_bind_commute_simp: "NO_MATCH (consume X) m \<Longrightarrow> wp (doM { r\<leftarrow>m; consume c; f r }) Q = wp (doM {consume c; r\<leftarrow>m; f r}) Q"  
  by (rule wp_consume_bind_commute)
  
  
  
                       

  
context llvm_prim_ctrl_setup begin
  
lemma basic_while_rule:
  assumes "wf R" (* TODO: R = measure (\<pi>_tcredits s)  *)
  assumes "llSTATE (I \<sigma> t) s"
  assumes STEP: "\<And>\<sigma> t s. \<lbrakk> llSTATE (I \<sigma> t) s \<rbrakk> \<Longrightarrow> wp (doM {ll_consume (cost ''call'' 1); ctd \<leftarrow> b \<sigma>; ll_consume (cost ''if'' 1); return ctd}) (\<lambda>ctd s\<^sub>1. 
    (to_bool ctd \<longrightarrow> wp (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. llSTATE (EXS t'. I \<sigma>' t' ** \<up>((t',t)\<in>R)) s\<^sub>2) s\<^sub>1)
  \<and> (\<not>to_bool ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
    ) s"
  shows "wp (llc_while b f \<sigma>) Q s"
  using assms(1,2)
proof (induction t arbitrary: \<sigma> s)
  case (less t)
  
  note STEP = STEP[simplified vcg_normalize_simps]
  
  show ?case 
    apply (subst llc_while_unfold)
    apply (simp only: vcg_normalize_simps)
    apply (rule wp_monoI[OF STEP])
    apply fact
    subgoal for uu s\<^sub>0
      apply (simp add: vcg_normalize_simps)
      apply (erule wp_monoI)
      subgoal for r s\<^sub>1
        apply (cases "to_bool r"; simp add: vcg_normalize_simps)
        subgoal
          apply (erule wp_monoI; clarsimp simp: vcg_normalize_simps)
          apply (erule wp_monoI; clarsimp; fri_extract)
          apply (rule less.IH; assumption)
          done
        subgoal
          apply (erule wp_monoI; clarsimp simp: vcg_normalize_simps)
          done
        done
      done
    done
    
qed          

definition "enat_less_than \<equiv> {(a,b::enat). a<b}"
lemma wf_enat_less_than[simp, intro!]: "wf enat_less_than" unfolding enat_less_than_def by (rule wellorder_class.wf)

(* TODO @Max: This monotonicity property is probably another cost-framework property: 
  Intuitively, (time-like) costs do not decrease, i.e., credits never increase.
*)
lemma wp_weaken_cost:
  assumes "wp c (\<lambda>r s'. (the_acost (snd s') \<le> the_acost (snd s)) \<longrightarrow> Q r s') s"
  shows "wp c Q s"
  using assms unfolding wp_def mwp_def
  apply (auto simp: run_simps split: mres.splits)
  by (smt acost.sel add.commute add_diff_cancel_enat enat.distinct(1) le_cost_ecost_def le_funI le_iff_add minus_ecost_cost_def)

lemma wp_weaken_cost_monoI:
  assumes 1: "wp c Q' s"
  assumes 2: "\<And>r s'. \<lbrakk> the_acost (snd s') \<le> the_acost (snd s); Q' r s' \<rbrakk> \<Longrightarrow> Q r s'"
  shows "wp c Q s"
  using assms 
  by (blast intro: wp_weaken_cost wp_monoI)

lemma wp_weaken_cost_monoI_STATE:
  assumes 1: "wp c Q' s"
  assumes 2: "\<And>r s'. \<lbrakk> the_acost (snd s') \<le> the_acost (snd s); Q' r s' \<rbrakk> \<Longrightarrow> Q r s'"
  shows "wp c Q s"
  using assms 
  by (blast intro: wp_weaken_cost wp_monoI)

    
(*(* TODO: Move *)  
lemma wp_consume': "wp (consume c) Q s = (le_cost_ecost c (snd s) \<and> Q () (fst s, minus_ecost_cost (snd s) c))"
  by (cases s) (simp add: wp_consume)
  *)
(*
lemma basic_while_rule':
  defines "R \<equiv> inv_image enat_less_than (\<lambda>c. the_acost c ''call'')" (* Only works if there are no infinite call credits! *)
  assumes I0: "llSTATE (I \<sigma>) s"
  assumes STEP: "\<And>\<sigma> s. \<lbrakk> llSTATE (I \<sigma>) s \<rbrakk> \<Longrightarrow> wp (doM {ll_consume (cost ''call'' 1); ctd \<leftarrow> b \<sigma>; ll_consume (cost ''if'' 1); return ctd}) (\<lambda>ctd s\<^sub>1. 
    (to_bool ctd \<longrightarrow> wp (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. llSTATE (I \<sigma>') s\<^sub>2) s\<^sub>1)
  \<and> (\<not>to_bool ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
    ) s"
  shows "wp (llc_while b f \<sigma>) Q s"
proof -

  note STEP = STEP[where s="(s,cr)" for s cr, simplified wp_consume vcg_normalize_simps, simplified, zero_var_indexes]
  
  show ?thesis  
    apply (rule basic_while_rule[where R=R and I="\<lambda>\<sigma> t s. I \<sigma> s \<and> t=snd s" and t="snd (ll_\<alpha> s)"])
    subgoal unfolding R_def by blast
    subgoal using I0 unfolding STATE_def by simp
    
    apply (use wp_consume[vcg_normalize_simps] in vcg_normalize)
    apply (rule conjI)
    subgoal using STEP[THEN conjunct1] unfolding STATE_def by auto
    subgoal
      apply (rule wp_weaken_cost_monoI[OF STEP[THEN conjunct2]])
      apply (unfold STATE_def; clarsimp; assumption)
      apply (erule wp_weaken_cost_monoI)
      apply (safe; clarsimp)
      subgoal
        apply (erule wp_weaken_cost_monoI)
        unfolding STATE_def
        apply (simp add: sep_algebra_simps pred_lift_extract_simps R_def enat_less_than_def)
        apply (clarsimp simp: ll_\<alpha>_def lift_\<alpha>_cost_def) apply (drule le_funD[where x="''call''"])+
      
    
    
    find_theorems wp consume
    
    apply vcg_normalize
xxx, ctd here: for the first step, we know that costs actually decrease!    
    apply (rule wp_weaken_cost_monoI[OF STEP])
    apply (unfold STATE_def; clarsimp; assumption)
    apply (erule wp_weaken_cost_monoI)
    apply (safe; clarsimp)
    
    subgoal
      apply (erule wp_weaken_cost_monoI)
      unfolding STATE_def
      apply (simp add: sep_algebra_simps pred_lift_extract_simps R_def enat_less_than_def)
      apply (clarsimp simp: ll_\<alpha>_def lift_\<alpha>_cost_def) apply (drule le_funD[where x="''call''"])+
      
      
    
    
    oops
    apply (safe; clarsimp)
  
*)  






text \<open>
  Standard while rule. 
  Note that the second parameter of the invariant is the termination measure, which must
  decrease wrt. a well-founded relation. It is initialized as a schematic variable, and must be 
  derivable via frame inference. In practice, the invariant will contain a \<open>\<up>(t=\<dots>)\<close> part.
\<close>  
lemma llc_while_annot_rule[vcg_decomp_erules]:  
  assumes "llSTATE P s"
  assumes "FRAME P (I \<sigma> t) F"
  assumes WF: "SOLVE_AUTO_DEFER (wf R)"
  assumes STEP: "\<And>\<sigma> t s. \<lbrakk> llSTATE ((I \<sigma> t ** F)) s \<rbrakk> \<Longrightarrow> EXTRACT (wp (doM {ll_consume (cost ''call'' 1); ctd \<leftarrow> b \<sigma>; ll_consume (cost ''if'' 1); return ctd}) (\<lambda>ctd s\<^sub>1. 
    (to_bool ctd \<longrightarrow> wp (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. llPOST (EXS t'. I \<sigma>' t' ** \<up>((t',t)\<in>R) ** F) s\<^sub>2) s\<^sub>1)
  \<and> (\<not>to_bool ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
    ) s)"
  shows "wp (llc_while_annot I R b f \<sigma>) Q s"
proof -                  
  from \<open>llSTATE P s\<close> \<open>FRAME P (I \<sigma> t) F\<close> have PRE: "llSTATE (I \<sigma> t ** F) s"
    unfolding FRAME_def STATE_def entails_def
    by (simp del: split_paired_All)

  show ?thesis  
    unfolding llc_while_annot_def
    apply (rule basic_while_rule[where I="\<lambda>\<sigma> t. I \<sigma> t ** F" and R=R])
    subgoal using WF unfolding vcg_tag_defs .
    apply (rule PRE)
    using STEP unfolding vcg_tag_defs
    apply (simp add: sep_algebra_simps)
    done
  
qed  
  
end

subsection \<open>LLVM Code Generator Setup\<close>

lemma elim_higher_order_return[llvm_inline]: "doM { x::_\<Rightarrow>_ \<leftarrow> return f; m x } = m f" by simp


text \<open>Useful shortcuts\<close>

subsubsection \<open>Direct Arithmetic\<close>

(* TODO: How would we handle conditional rules, like from return (a div b) to ll_udiv?
  We would have to transform the program to a weaker one, that asserts preconditions, and
  then reason about this!
*)

(*
context begin
  interpretation llvm_prim_arith_setup .

  lemma arith_inlines[llvm_inline, vcg_monadify_xforms]: 
    "return (a+b) = ll_add a b" 
    "return (a-b) = ll_sub a b" 
    "return (a*b) = ll_mul a b" 
  
    "return (a AND b) = ll_and a b" 
    "return (a OR b) = ll_or a b" 
    "return (a XOR b) = ll_xor a b" 
    by vcg
    
end  
*)

(*
subsubsection \<open>Direct Comparison\<close>
abbreviation (input) ll_cmp' :: "bool \<Rightarrow> 1 word" where "ll_cmp' \<equiv> from_bool"
definition [vcg_monadify_xforms,llvm_inline]: "ll_cmp b \<equiv> return (ll_cmp' b)"
  
(* To work with current monadify implementation, 
  we have to replace each operation by a constants
  
  TODO: Can we change monadifier?
*)

definition "ll_cmp'_eq a b \<equiv> ll_cmp' (a=b)"
definition "ll_cmp'_ne a b \<equiv> ll_cmp' (a\<noteq>b)"
definition "ll_cmp'_ule a b \<equiv> ll_cmp' (a\<le>b)"
definition "ll_cmp'_ult a b \<equiv> ll_cmp' (a<b)"
definition "ll_cmp'_sle a b \<equiv> ll_cmp' (a <=s b)"
definition "ll_cmp'_slt a b \<equiv> ll_cmp' (a <s b)"
                                          
lemmas ll_cmp'_defs = ll_cmp'_eq_def ll_cmp'_ne_def ll_cmp'_ule_def ll_cmp'_ult_def ll_cmp'_sle_def ll_cmp'_slt_def

lemmas [llvm_inline, vcg_monadify_xforms] = ll_cmp'_defs[symmetric]

context begin
  interpretation llvm_prim_arith_setup .

  lemma ll_cmp'_xforms[vcg_monadify_xforms,llvm_inline]:
    "return (ll_cmp'_eq  a b) = ll_icmp_eq a b" 
    "return (ll_cmp'_ne  a b) = ll_icmp_ne a b" 
    "return (ll_cmp'_ult a b) = ll_icmp_ult a b" 
    "return (ll_cmp'_ule a b) = ll_icmp_ule a b" 
    "return (ll_cmp'_slt a b) = ll_icmp_slt a b" 
    "return (ll_cmp'_sle a b) = ll_icmp_sle a b" 
    unfolding ll_cmp_def ll_cmp'_defs
    by (all vcg_normalize)

  lemma ll_ptrcmp'_xforms[vcg_monadify_xforms,llvm_inline]:
    "return (ll_cmp'_eq  a b) = ll_ptrcmp_eq a b" 
    "return (ll_cmp'_ne  a b) = ll_ptrcmp_ne a b" 
    unfolding ll_cmp_def ll_cmp'_defs
    by (all vcg_normalize)
    
    
end    
*)


subsubsection \<open>Boolean Operations\<close>
(*
lemma llvm_if_inline[llvm_inline,vcg_monadify_xforms]: "If b t e = llc_if (from_bool b) t e"  
  by (auto simp: llc_if_def)
*)  
  
lemma (in llvm_prim_arith_setup) llvm_from_bool_inline[llvm_inline]: 
  "from_bool (a\<and>b) = (from_bool a AND from_bool b)"  
  "from_bool (a\<or>b) = (from_bool a OR from_bool b)"  
  "(from_bool (\<not>a)::1 word) = (1 - (from_bool a :: 1 word))"  
  subgoal by (metis and.idem and_zero_eq bit.conj_zero_left from_bool_eq_if')
  subgoal by (smt (z3) from_bool_0 or.idem word_bw_comms(2) word_log_esimps(3))
  subgoal by (metis (full_types) cancel_comm_monoid_add_class.diff_cancel diff_zero from_bool_eq_if')
  done

subsubsection \<open>Products\<close>
  
lemma inline_prod_case[llvm_inline]: "(\<lambda>(a,b). f a b) = (\<lambda>x. doM { a\<leftarrow>prod_extract_fst x; b \<leftarrow> prod_extract_snd x; f a b })"  
  by (auto simp: prod_ops_simp)

  
lemma inline_return_prod_case[llvm_inline]: 
  "return (case x of (a,b) \<Rightarrow> f a b) = (case x of (a,b) \<Rightarrow> return (f a b))" by (rule prod.case_distrib)
  

lemma inline_return_prod[llvm_inline]: "return (a,b) = doM { x \<leftarrow> prod_insert_fst init a; x \<leftarrow> prod_insert_snd x b; return x }"  
  by (auto simp: prod_ops_simp)
  
context begin
interpretation llvm_prim_setup .

lemma ll_extract_pair_pair:
  "ll_extract_fst (a,b) = \<^cancel>\<open>consume1r ''extract_fst''\<close> return a" 
  "ll_extract_snd (a,b) = \<^cancel>\<open>consume1r ''extract_snd''\<close> return b" 
  unfolding ll_extract_fst_def ll_extract_snd_def checked_split_pair_def checked_from_val_def
  by auto 

end  
  
subsubsection \<open>Marking of constants\<close>    
definition "ll_const x \<equiv> return x"

lemma ll_const_inline[llvm_inline]: "bind (ll_const x) f = f x" by (auto simp: ll_const_def)
  
declare [[vcg_const "numeral a"]]
declare [[vcg_const "ll_const c"]]

  
section \<open>Data Refinement\<close>  

locale standard_opr_abstraction = 
  fixes \<alpha> :: "'c \<Rightarrow> 'a"
    and I :: "'c \<Rightarrow> bool"
    and dflt_PRE1 :: "('a\<Rightarrow>'a) \<Rightarrow> 'c itself \<Rightarrow> 'a \<Rightarrow> bool"
    and dflt_PRE2 :: "('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'c itself \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and dflt_EPURE :: "'a \<Rightarrow> 'c \<Rightarrow> bool"
    
  assumes dflt_EPURE_correct: "\<And>c. I c \<Longrightarrow> dflt_EPURE (\<alpha> c) c"  
begin

interpretation llvm_prim_setup .

definition "assn \<equiv> mk_pure_assn (\<lambda>a c. I c \<and> a=\<alpha> c)"
                           
lemma assn_pure[is_pure_rule]: "is_pure assn"
  by (auto simp: assn_def)

lemma vcg_prep_delete_assn[vcg_prep_ext_rules]: 
  "pure_part (\<upharpoonleft>assn a c) \<Longrightarrow> dflt_EPURE a c"
  by (auto simp: assn_def dflt_EPURE_correct)
  

definition "is_un_op name PRE cop mop aop \<equiv> 
  (\<forall>a::'c. I a \<and> PRE TYPE('c) (\<alpha> a) \<longrightarrow> I (mop a) \<and> \<alpha> (mop a) = aop (\<alpha> a) \<and> cop a = consume1r name (mop a))"
  
definition "is_bin_op name PRE cop mop aop \<equiv> 
  (\<forall>a b::'c. I a \<and> I b \<and> PRE TYPE('c) (\<alpha> a) (\<alpha> b) \<longrightarrow> I (mop a b) \<and> \<alpha> (mop a b) = aop (\<alpha> a) (\<alpha> b) \<and> cop a b = consume1r name (mop a b))"

abbreviation "is_un_op' name cop mop aop \<equiv> is_un_op name (dflt_PRE1 aop) cop mop aop"
abbreviation "is_bin_op' name cop mop aop \<equiv> is_bin_op name (dflt_PRE2 aop) cop mop aop"

lemma is_un_opI[intro?]:
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> cop a = consume1r name (mop a)"
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> I (mop a)"
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> \<alpha> (mop a) = aop (\<alpha> a)"
  shows "is_un_op name PRE cop mop aop"
  using assms unfolding is_un_op_def by blast

lemma is_bin_opI[intro?]:
  assumes "\<And>a b. \<lbrakk>I a; I b; PRE TYPE('c) (\<alpha> a) (\<alpha> b)\<rbrakk> \<Longrightarrow> cop a b = consume1r name (mop a b)"
  assumes "\<And>a b. \<lbrakk>I a; I b; PRE TYPE('c) (\<alpha> a) (\<alpha> b)\<rbrakk> \<Longrightarrow> I (mop a b)"
  assumes "\<And>a b. \<lbrakk>I a; I b; PRE TYPE('c) (\<alpha> a) (\<alpha> b)\<rbrakk> \<Longrightarrow> \<alpha> (mop a b) = aop (\<alpha> a) (\<alpha> b)"
  shows "is_bin_op name PRE cop mop aop"
  using assms unfolding is_bin_op_def by blast

lemma un_op_tmpl:
  fixes w :: "'c"
  assumes A: "is_un_op name PRE cop mop aop"
  shows "llvm_htriple 
    ($$ name 1 ** \<upharpoonleft>assn i w ** \<up>\<^sub>d(PRE TYPE('c) i)) 
    (cop w) 
    (\<lambda>r. \<upharpoonleft>assn (aop i) r ** \<upharpoonleft>assn i w)
    "
proof -
  interpret llvm_prim_arith_setup .

  show ?thesis
    using A
    unfolding is_un_op_def assn_def apply clarsimp
    by vcg
    
qed
  
  
lemma bin_op_tmpl:
  fixes w\<^sub>1 w\<^sub>2 :: "'c"
  assumes A: "is_bin_op name PRE cop mop aop"
  shows "llvm_htriple 
    ($$name 1 ** \<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2 ** \<up>\<^sub>d(PRE TYPE('c) i\<^sub>1 i\<^sub>2)) 
    (cop w\<^sub>1 w\<^sub>2) 
    (\<lambda>r. \<upharpoonleft>assn (aop i\<^sub>1 i\<^sub>2) r ** \<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2)
    "
proof -
  interpret llvm_prim_arith_setup .

  show ?thesis
    using A
    unfolding is_bin_op_def assn_def apply clarsimp
    by vcg
    
qed

end

interpretation bool: standard_opr_abstraction "to_bool::1 word \<Rightarrow> bool" "\<lambda>_. True" \<open>\<lambda>_ _ _. True\<close> \<open>\<lambda>_ _ _ _. True\<close> "\<lambda>_ _. True" 
  by standard auto

context standard_opr_abstraction begin

  interpretation llvm_prim_setup .

  definition "is_cmp_op name cop mop aop \<equiv> 
    (\<forall>a b. I a \<and> I b \<longrightarrow> (cop a b = consume1r name (from_bool (mop a b)) \<and> (mop a b \<longleftrightarrow> aop (\<alpha> a) (\<alpha> b))))"
  
  lemma is_cmp_opI[intro?]:
    assumes "\<And>a b. \<lbrakk>I a; I b\<rbrakk> \<Longrightarrow> cop a b = consume1r name (from_bool (mop a b))"
    assumes "\<And>a b. \<lbrakk>I a; I b\<rbrakk> \<Longrightarrow> mop a b \<longleftrightarrow> aop (\<alpha> a) (\<alpha> b)"
    shows "is_cmp_op name cop mop aop"
    using assms unfolding is_cmp_op_def by blast
    
  lemma cmp_op_tmpl:
    fixes w\<^sub>1 w\<^sub>2 :: "'c"
    assumes "is_cmp_op name cop mop aop"
    shows "llvm_htriple 
      ($$ name 1 ** \<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2) 
      (cop w\<^sub>1 w\<^sub>2) 
      (\<lambda>r. \<upharpoonleft>bool.assn (aop i\<^sub>1 i\<^sub>2) r ** \<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2)
      "
    using assms unfolding is_cmp_op_def assn_def bool.assn_def apply clarsimp
    by vcg

end
  
subsection \<open>Booleans\<close>

   
lemma to_bool_logics:
  fixes a b :: "1 word"
  shows "to_bool (a&&b) \<longleftrightarrow> to_bool a \<and> to_bool b"  
    and "to_bool (a||b) \<longleftrightarrow> to_bool a \<or> to_bool b"  
    and "to_bool (a XOR b) \<longleftrightarrow> to_bool a \<noteq> to_bool b"  
    and "to_bool (NOT a) \<longleftrightarrow> \<not>to_bool a"  
  apply (cases a; cases b; simp; fail)
  apply (cases a; cases b; simp; fail)
  apply (cases a; cases b; simp; fail)
  apply (cases a; simp; fail)
  done

context begin                                             

interpretation llvm_prim_arith_setup .

abbreviation ll_not1 :: "1 word \<Rightarrow> 1 word llM" where "ll_not1 x \<equiv> ll_add x 1"  
    
(*
lemma ll_not1_inline[llvm_inline]: "return (~~x) \<equiv> ll_not1 x"
  by (auto simp: word1_NOT_eq arith_inlines)
*)  
  
lemma bool_bin_ops:
  "bool.is_bin_op' ''and'' ll_and (AND) (\<and>)" 
  "bool.is_bin_op' ''or'' ll_or (OR) (\<or>)" 
  "bool.is_bin_op' ''xor'' ll_xor (XOR) (\<noteq>)" 
  apply (all \<open>rule\<close>)
  apply (simp_all only: to_bool_logics)
  apply (all \<open>vcg_normalize?\<close>)
  done

lemma bool_un_ops:
  "bool.is_un_op' ''add'' ll_not1 (NOT) Not" 
  apply (all \<open>rule\<close>)
  apply (simp_all only: to_bool_logics)
  apply (all \<open>vcg_normalize?\<close>)
  apply (simp_all add: word1_NOT_eq)
  done
    
lemmas bool_op_rules[vcg_rules] = 
  bool_bin_ops[THEN bool.bin_op_tmpl]
  bool_un_ops[THEN bool.un_op_tmpl]
  
end  
  

subsection \<open>Control Flow\<close>

definition "ABSTRACT c ty P s \<equiv> \<exists>F a. llSTATE (\<upharpoonleft>ty a c ** F) s \<and> P a"  

lemma ABSTRACT_pure: "is_pure A \<Longrightarrow> ABSTRACT c A P h \<longleftrightarrow> (\<exists>a. \<flat>\<^sub>pA a c \<and> P a)"
  unfolding ABSTRACT_def  
  apply (cases h) 
  apply (auto simp only: STATE_def dr_assn_pure_asm_prefix_def sep_conj_def
                          pure_part_def ll_\<alpha>_def lift_\<alpha>_cost_def)
  by (metis disjoint_zero_sym extract_pure_assn pred_lift_extract_simps(1) sep_add_zero_sym) 
  
lemma ABSTRACT_erule[vcg_decomp_erules]:
  assumes "llSTATE P s"
  assumes "FRAME P (\<upharpoonleft>ty a c) F"
  assumes "llSTATE (\<upharpoonleft>ty a c ** F) s \<Longrightarrow> EXTRACT (Q a)"
  shows "ABSTRACT c ty Q s"
  using assms
  by (auto simp: FRAME_def ABSTRACT_def STATE_def entails_def vcg_tag_defs simp del: split_paired_All)


context begin
  interpretation llvm_prim_arith_setup + llvm_prim_ctrl_setup .

  lemma dr_normalize_llc_if[vcg_normalize_simps]: 
    "\<flat>\<^sub>pbool.assn b bi \<Longrightarrow> wp (llc_if bi t e) Q s \<longleftrightarrow> wp (consume1r ''if'' ()) (\<lambda>_ s. (b \<longrightarrow> wp t Q s) \<and> (\<not>b\<longrightarrow>wp e Q s)) s"
    unfolding bool.assn_def by vcg_normalize


  lemma llc_while_annot_dr_rule[vcg_decomp_erules]:  
    assumes "llSTATE P s"
    assumes "FRAME P (I \<sigma> t) F"
    assumes WF: "SOLVE_AUTO_DEFER (wf R)"
    assumes STEP: "\<And>\<sigma> t s. \<lbrakk> llSTATE ((I \<sigma> t ** F)) s \<rbrakk> \<Longrightarrow> EXTRACT (wp (doM {ll_consume (cost ''call'' 1); ctd \<leftarrow> b \<sigma>; ll_consume (cost ''if'' 1); return ctd}) (\<lambda>ctdi s\<^sub>1. 
        ABSTRACT ctdi bool.assn (\<lambda>ctd. 
            (ctd \<longrightarrow> wp (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. llPOST (EXS t'. I \<sigma>' t' ** \<up>\<^sub>d((t',t)\<in>R) ** F) s\<^sub>2) s\<^sub>1)
          \<and> (\<not>ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
        ) s\<^sub>1
      ) s)"
    shows "wp (llc_while_annot I R b f \<sigma>) Q s"
    using assms(1) apply -
    apply vcg_rl
    apply fact
    apply fact
    apply (drule STEP)
    apply (simp add: fri_extract_simps ABSTRACT_pure vcg_tag_defs bool.assn_def)    
    done
    
end
  
  
end
