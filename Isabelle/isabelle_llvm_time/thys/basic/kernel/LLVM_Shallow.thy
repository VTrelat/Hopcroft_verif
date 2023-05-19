section \<open>Shallow Embedding of LLVM Semantics\<close>
theory LLVM_Shallow
imports Main  
  "LLVM_Memory"
  "../../cost/Abstract_Cost"
begin

  text \<open>We define a type synonym for the LLVM monad\<close>
  type_synonym 'a llM = "('a,unit,cost,llvm_memory,err) M"
  translations
    (type) "'a llM" \<leftharpoondown> (type) "('a, unit, (char list, nat) acost, llvm_memory, err) M"
  
  subsection \<open>Shallow Embedding of Values\<close>  

  text \<open>We use a type class to characterize types that can be injected into the value type.
    We will instantiate this type class to obtain injections from types of shape 
    \<open>T = T\<times>T | _ word | _ ptr\<close>
  
    Although, this type class can be instantiated by other types, those will not be accepted 
    by the code generator.
    
    We also define a class \<open>llvm_repv\<close>, which additionally contains \<open>unit\<close>. 
    This is required for void functions, and if-the-else statements that produce no result.
    
    Again, while this class might be instantiated for other types, those will be rejected
    by the code generator.
  \<close>
  
  class llvm_repv  
    
  class llvm_rep = llvm_repv +
    fixes to_val :: "'a \<Rightarrow> llvm_val"
      and from_val :: "llvm_val \<Rightarrow> 'a"
      and struct_of :: "'a itself \<Rightarrow> llvm_vstruct"
      and init :: 'a
    assumes from_to_id[simp]: "from_val o to_val = id"
    assumes to_from_id[simp]: "llvm_vstruct v = struct_of TYPE('a) \<Longrightarrow> to_val (from_val v) = v"
    assumes struct_of_matches[simp]: "llvm_vstruct (to_val x) = (struct_of TYPE('a))"
    assumes init_zero: "to_val init = llvm_zero_initializer (struct_of TYPE('a))"
    
  begin
  
    lemma from_to_id'[simp]: "from_val (to_val x) = x" 
      using pointfree_idE[OF from_to_id] .
  
    lemma "to_val x = to_val y \<longleftrightarrow> x=y"  
      by (metis from_to_id')
      
  end
  
  text \<open>We use a phantom type to attach the type of the pointed to value to a pointer.\<close>
  datatype 'a::llvm_rep ptr = PTR (the_raw_ptr: llvm_ptr)
  definition null :: "'a::llvm_rep ptr" where "null = PTR llvm_null"
  

  text \<open>We instantiate the type classes for the supported types, 
    i.e., unit, word, ptr, and prod.\<close>
  
  instance unit :: llvm_repv by standard
  
  instantiation word :: (len) llvm_rep begin
    definition "to_val w \<equiv> llvm_int (lconst (len_of TYPE('a)) (uint w))"
    definition "from_val v \<equiv> word_of_int (lint_to_uint (llvm_the_int v))"
    definition [simp]: "struct_of_word (_::'a word itself) \<equiv> llvm_s_int (len_of TYPE('a))"
    definition [simp]: "init_word \<equiv> 0::'a word"
    
    
    lemma int_inv_aux: "width i = LENGTH('a) \<Longrightarrow> lconst LENGTH('a) (uint (word_of_int (lint_to_uint i) :: 'a word)) = i"
      by (metis uint_const uint_eq uint_lower_bound uint_upper_bound width_lconst word_of_int_inverse word_ubin.norm_Rep)
    
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_word_def to_val_word_def)
      apply (auto simp: llvm_s_int_def llvm_zero_initializer_def llvm_int_def)
      subgoal for v apply (cases v) 
        apply (auto simp: llvm_int_def llvm_the_int_def llvm_s_ptr_def llvm_s_pair_def)
        using int_inv_aux apply (simp add: llvm_vstruct_def) 
      done
      done
      
  end
  
  instantiation ptr :: (llvm_rep) llvm_rep begin
    definition "to_val \<equiv> llvm_ptr o ptr.the_raw_ptr"
    definition "from_val v \<equiv> PTR (llvm_the_ptr v)"
    definition [simp]: "struct_of_ptr (_::'a ptr itself) \<equiv> llvm_s_ptr"
    definition [simp]: "init_ptr::'a ptr \<equiv> null"
  
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_ptr_def to_val_ptr_def)
      apply (auto simp: llvm_zero_initializer_def llvm_ptr_def llvm_s_ptr_def null_def llvm_null_def)
      subgoal for v apply (cases v)
        by (auto simp: llvm_s_int_def llvm_s_pair_def llvm_ptr_def llvm_the_ptr_def)
      done
      
  end
  
  instantiation prod :: (llvm_rep, llvm_rep) llvm_rep begin
    definition "to_val_prod \<equiv> \<lambda>(a,b). llvm_pair (to_val a) (to_val b)"
    definition "from_val_prod p \<equiv> case llvm_the_pair p of (a,b) \<Rightarrow> (from_val a, from_val b)"
    definition [simp]: "struct_of_prod (_::('a\<times>'b) itself) \<equiv> llvm_s_pair (struct_of TYPE('a)) (struct_of TYPE('b))"
    definition [simp]: "init_prod ::'a\<times>'b \<equiv> (init,init)"
    
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_prod_def to_val_prod_def)
      apply (auto simp: llvm_pair_def llvm_s_pair_def init_zero llvm_zero_initializer_def)
      subgoal for v
        apply (cases v)
        apply (auto simp: llvm_s_int_def llvm_s_ptr_def llvm_pair_def llvm_the_pair_def 
          llvm_val.the_val_def llvm_vstruct_def split: prod.splits llvm_val.splits val.split)
        done
      done
      
  end

  lemma to_val_prod_conv[simp]: "to_val (a,b) = llvm_pair (to_val a) (to_val b)"
    unfolding to_val_prod_def by auto
  
  
  text \<open>Checked conversion from value\<close>  
  definition checked_from_val :: "llvm_val \<Rightarrow> 'a::llvm_rep llM" where
    "checked_from_val v \<equiv> doM {
      fcheck (STATIC_ERROR ''Type mismatch'') (llvm_vstruct v = struct_of TYPE('a));
      return (from_val v)
    }" 

      
  subsection \<open>Instructions\<close>  
  
  text \<open>The instructions are arranged in the order as they are described in the 
    LLVM Language Reference Manual \<^url>\<open>https://llvm.org/docs/LangRef.html\<close>.\<close>
    
  
  subsubsection \<open>Binary Operations\<close>  
  text \<open>We define a generic lifter for binary arithmetic operations.
    It is parameterized by an error condition.
  \<close> (* TODO: Use precondition instead of negated precondition! *)

  definition op_lift_arith2 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word llM"
    where "op_lift_arith2 n ovf f a b \<equiv> doM {
    consume (cost n 1);
    let a = word_to_lint a;
    let b = word_to_lint b;
    fcheck (OVERFLOW_ERROR) (\<not>ovf a b);
    return (lint_to_word (f a b))
  }"
        
  definition "op_lift_arith2' n \<equiv> op_lift_arith2 n (\<lambda>_ _. False)"

  definition udivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" 
    where "udivrem_is_undef a b \<equiv> lint_to_uint b=0"
  definition sdivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" 
    where "sdivrem_is_undef a b \<equiv> lint_to_sint b=0 \<or> sdivrem_ovf a b"
  
  definition "ll_add \<equiv> op_lift_arith2' ''add'' (+)"
  definition "ll_sub \<equiv> op_lift_arith2' ''sub'' (-)"
  definition "ll_mul \<equiv> op_lift_arith2' ''mul'' (*)"
  definition "ll_udiv \<equiv> op_lift_arith2 ''udiv'' udivrem_is_undef (div)"
  definition "ll_urem \<equiv> op_lift_arith2 ''urem'' udivrem_is_undef (mod)"
  definition "ll_sdiv \<equiv> op_lift_arith2 ''sdiv'' sdivrem_is_undef (sdiv)"
  definition "ll_srem \<equiv> op_lift_arith2 ''srem'' sdivrem_is_undef (smod)"
  
  
  subsubsection \<open>Compare Operations\<close>
  definition op_lift_cmp :: "_ \<Rightarrow> _ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 1 word llM"
    where "op_lift_cmp n f a b \<equiv> doM {
    consume (cost n 1);
    let a = word_to_lint a;
    let b = word_to_lint b;
    return (lint_to_word (bool_to_lint (f a b)))
  }"
    
  definition op_lift_ptr_cmp :: "_ \<Rightarrow> _ \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> 'a ptr \<Rightarrow> 1 word llM"
    where "op_lift_ptr_cmp n f a b \<equiv> doM {
    consume (cost n 1);
    return (lint_to_word (bool_to_lint (f a b)))
  }"
  
  definition "ll_icmp_eq \<equiv>  op_lift_cmp ''icmp_eq'' (=)"
  definition "ll_icmp_ne \<equiv>  op_lift_cmp ''icmp_ne'' (\<noteq>)"
  definition "ll_icmp_sle \<equiv> op_lift_cmp ''icmp_sle'' (\<le>\<^sub>s)"
  definition "ll_icmp_slt \<equiv> op_lift_cmp ''icmp_slt'' (<\<^sub>s)"
  definition "ll_icmp_ule \<equiv> op_lift_cmp ''icmp_ule'' (\<le>)"
  definition "ll_icmp_ult \<equiv> op_lift_cmp ''icmp_ult'' (<)"

  
  (* For presentation in paper *)
  lemma "ll_add a b = doM {
      consume (cost ''add'' 1);
      return (a+b)
    }"
    unfolding ll_add_def op_lift_arith2'_def op_lift_arith2_def
    apply simp
    by (metis lint_word_inv word_to_lint_plus)
    
  
  text \<open>Note: There are no pointer compare instructions in LLVM. 
    To compare pointers in LLVM, they have to be casted to integers first.
    However, our abstract memory model cannot assign a bit-width to pointers.
    
    Thus, we model pointer comparison instructions in our semantics, and let the 
    code generator translate them to integer comparisons. 
    
    Up to now, we only model pointer equality. 
    For less-than, suitable preconditions are required, which are consistent with the 
    actual memory layout of LLVM. We could, e.g., adopt the rules from the C standard here.
  \<close>
  definition "ll_ptrcmp_eq \<equiv> op_lift_ptr_cmp ''ptrcmp_eq'' (=)"
  definition "ll_ptrcmp_ne \<equiv> op_lift_ptr_cmp ''ptrcmp_ne'' (\<noteq>)"
  

  
  subsubsection \<open>Bitwise Binary Operations\<close>  
  definition "shift_ovf a n \<equiv> nat (lint_to_uint n) \<ge> width a"
  definition "bitSHL' a n \<equiv> bitSHL a (nat (lint_to_uint n))"
  definition "bitASHR' a n \<equiv> bitASHR a (nat (lint_to_uint n))"
  definition "bitLSHR' a n \<equiv> bitLSHR a (nat (lint_to_uint n))"
  
  definition "ll_shl \<equiv> op_lift_arith2 ''shl'' shift_ovf bitSHL'"  
  definition "ll_lshr \<equiv> op_lift_arith2 ''lshr'' shift_ovf bitLSHR'"  
  definition "ll_ashr \<equiv> op_lift_arith2 ''ashr'' shift_ovf bitASHR'"
  
  definition "ll_and \<equiv> op_lift_arith2' ''and'' (lliAND)"
  definition "ll_or \<equiv> op_lift_arith2' ''or'' (lliOR)"
  definition "ll_xor \<equiv> op_lift_arith2' ''xor'' (lliXOR)"
    

  subsubsection \<open>Aggregate Operations\<close>
  text \<open>In LLVM, there is an \<open>extractvalue\<close> and \<open>insertvalue\<close> operation.
    In our shallow embedding, these get instantiated for \<open>fst\<close> and \<open>snd\<close>.\<close>
    
  
  definition "checked_split_pair v \<equiv> doM {
    fcheck (STATIC_ERROR ''Expected pair'') (llvm_is_pair v);
    return (llvm_the_pair v)
  }"

  (* TODO: reinsert costs for products and push it to the abstract level. *)
  definition ll_extract_fst :: "'t::llvm_rep \<Rightarrow> 't\<^sub>1::llvm_rep llM" where "ll_extract_fst p = doM { \<^cancel>\<open>consume (cost ''extract_fst'' 1);\<close> (a,b) \<leftarrow> checked_split_pair (to_val p); checked_from_val a }"
  definition ll_extract_snd :: "'t::llvm_rep \<Rightarrow> 't\<^sub>2::llvm_rep llM" where "ll_extract_snd p = doM { \<^cancel>\<open>consume (cost ''extract_snd'' 1);\<close> (a,b) \<leftarrow> checked_split_pair (to_val p); checked_from_val b }"
  definition ll_insert_fst :: "'t::llvm_rep \<Rightarrow> 't\<^sub>1::llvm_rep \<Rightarrow> 't llM" where "ll_insert_fst p x = doM { \<^cancel>\<open>consume (cost ''insert_fst'' 1);\<close> (a,b) \<leftarrow> checked_split_pair (to_val p); checked_from_val (llvm_pair (to_val x) b) }" 
  definition ll_insert_snd :: "'t::llvm_rep \<Rightarrow> 't\<^sub>2::llvm_rep \<Rightarrow> 't llM" where "ll_insert_snd p x = doM { \<^cancel>\<open>consume (cost ''insert_snd'' 1);\<close> (a,b) \<leftarrow> checked_split_pair (to_val p); checked_from_val (llvm_pair a (to_val x)) }" 
    
  (*  
  definition ll_extract_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a llM" where "ll_extract_fst ab \<equiv> return (fst ab)"
  definition ll_extract_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b llM" where "ll_extract_snd ab \<equiv> return (snd ab)"
  definition ll_insert_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a \<Rightarrow> ('a\<times>'b) llM" where "ll_insert_fst ab a \<equiv> return (a,snd ab)"
  definition ll_insert_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b \<Rightarrow> ('a\<times>'b) llM" where "ll_insert_snd ab b \<equiv> return (fst ab,b)"
  *)
    
  subsubsection \<open>Memory Access and Addressing Operations\<close>
    
  definition ll_load :: "'a::llvm_rep ptr \<Rightarrow> 'a llM" where
    "ll_load p \<equiv> doM {
      consume (cost ''load'' 1);
      r \<leftarrow> llvm_load (the_raw_ptr p);
      checked_from_val r
    }"
    
  definition ll_store :: "'a::llvm_rep \<Rightarrow> 'a ptr \<Rightarrow> unit llM" where
    "ll_store v p \<equiv> doM {
      consume (cost ''store'' 1);
      llvm_store (to_val v) (the_raw_ptr p)
    }"

  text \<open>Note that LLVM itself does not have malloc and free instructions.
    However, these are primitive instructions in our abstract memory model, 
    such that we have to model them in our semantics.
    
    The code generator will map them to the C standard library 
    functions \<open>calloc\<close> and \<open>free\<close>.
  \<close>
    
  definition ll_malloc :: "'a::llvm_rep itself \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where
    "ll_malloc TYPE('a) n = doM {
      consume (cost ''malloc'' (unat n)); \<comment> \<open>DESIGN CHOICE: malloc consumes n\<close>
      fcheck MEM_ERROR (unat n > 0); \<comment> \<open>Disallow empty malloc\<close>
      r \<leftarrow> llvm_allocn (to_val (init::'a)) (unat n);
      return (PTR r)
    }"
        
  definition ll_free :: "'a::llvm_rep ptr \<Rightarrow> unit llM" 
    where "ll_free p \<equiv> doM {
            consume (cost ''free'' 1); \<comment> \<open>DESIGN CHOICE: consume 1 \<close>
            llvm_free (the_raw_ptr p)
          }"


  text \<open>As for the aggregate operations, the \<open>getelementptr\<close> instruction is instantiated 
    for pointer indexing, fst, and snd. \<close>

  \<comment> \<open>pointer arithmetic, cost 1 each\<close>

  definition ll_ofs_ptr :: "'a::llvm_rep ptr \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where "ll_ofs_ptr p ofs = doM {
    consume (cost ''ofs_ptr'' 1);
    r \<leftarrow> llvm_checked_idx_ptr (the_raw_ptr p) (sint ofs);
    return (PTR r)
  }"  

  definition ll_gep_fst :: "'p::llvm_rep ptr \<Rightarrow> 'a::llvm_rep ptr llM" where "ll_gep_fst p = doM {
    consume (cost ''gep_fst'' 1);
    fcheck (STATIC_ERROR ''gep_fst: Expected pair type'') (llvm_is_s_pair (struct_of TYPE('p)));
    r \<leftarrow> llvm_checked_gep (the_raw_ptr p) PFST;
    return (PTR r)
  }"

  definition ll_gep_snd :: "'p::llvm_rep ptr \<Rightarrow> 'b::llvm_rep ptr llM" where "ll_gep_snd p = doM {
    consume (cost ''gep_snd'' 1);
    fcheck (STATIC_ERROR ''gep_snd: Expected pair type'') (llvm_is_s_pair (struct_of TYPE('p)));
    r \<leftarrow> llvm_checked_gep (the_raw_ptr p) PSND;
    return (PTR r)
  }"

  subsubsection \<open>Conversion Operations\<close>
  definition "llb_trunc i w \<equiv> doM {
    fcheck (STATIC_ERROR ''Trunc must go to smaller type'') (width i > w);
    return (trunc w i)
  }"
  
  definition "llb_sext i w \<equiv> doM {
    fcheck (STATIC_ERROR ''Sext must go to greater type'') (width i < w);
    return (sext w i)
  }"
  
  definition "llb_zext i w \<equiv> doM {
    fcheck (STATIC_ERROR ''Zext must go to greater type'') (width i < w);
    return (zext w i)
  }"
  
  definition op_lift_iconv :: "_ \<Rightarrow> _ \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word itself  \<Rightarrow> 'b word llM"
    where "op_lift_iconv n f a _ \<equiv> doM {
    consume (cost n 1);
    let a = word_to_lint a;
    let w = LENGTH('b);
    r \<leftarrow> f a w;
    return (lint_to_word r)
  }"
  
  definition "ll_trunc \<equiv> op_lift_iconv ''trunc'' llb_trunc"
  definition "ll_sext \<equiv> op_lift_iconv ''sext'' llb_sext"
  definition "ll_zext \<equiv> op_lift_iconv ''zext'' llb_zext"
  
    
        
        
  subsection \<open>Control Flow\<close>  

  text \<open>Our shallow embedding uses a structured control flow, which allows
    only sequential composition, if-then-else, and function calls.
    
    The code generator then maps sequential composition to basic blocks, 
    and if-then-else to a control flow graph with conditional branching.
    Function calls are mapped to LLVM function calls.  
   \<close>
  
  text \<open>We use the to Boolean conversion from word-lib. We re-state its semantics here.\<close>
    
  lemma to_bool_as_lint_to_bool:
    "to_bool (w::1 word) = lint_to_bool (word_to_lint w)"
    unfolding to_bool_def word_to_lint_def
    apply (clarsimp simp: ltrue_def lfalse_def lint_to_bool_def)
    apply transfer
    apply auto
    done
  
  lemma to_bool_eq[simp]: "to_bool (w::1 word) \<longleftrightarrow> w\<noteq>0"
    by (rule to_bool_neq_0)
  
  definition llc_if :: "1 word \<Rightarrow> 'a::llvm_repv llM \<Rightarrow> 'a llM \<Rightarrow> 'a llM" where
    "llc_if b t e \<equiv> doM {
      consume (cost ''if'' 1);
      if to_bool b then t else e
    }"
  
  lemma llc_if_mono[partial_function_mono]:      
    "\<lbrakk>M_mono F; M_mono G\<rbrakk> \<Longrightarrow> M_mono (\<lambda>f. llc_if b (F f) (G f))"
    unfolding llc_if_def 
    by pf_mono_prover  

  subsubsection \<open>Function Call\<close>

  definition ll_call :: "'a llM \<Rightarrow> 'a llM" where 
    "ll_call f \<equiv> doM { consume (cost ''call'' 1) ; f  }"

  lemma ll_call_mono[partial_function_mono]: "M_mono f \<Longrightarrow> M_mono (\<lambda>x. ll_call (f x))"
    unfolding ll_call_def
    by pf_mono_prover
  
  subsubsection \<open>Recursion with Time for Call\<close>  
    
  definition "REC' F x = REC (\<lambda>D x. F (\<lambda>x. ll_call (D x)) x) x"
  
  lemma REC'_unfold:
    assumes DEF: "f \<equiv> REC' F"
    assumes MONO: "\<And>x. M.mono_body (\<lambda>fa. F (\<lambda>x. ll_call (fa x)) x)"
    shows "f = F (\<lambda>x. ll_call (f x))" 
    unfolding DEF REC'_def
    apply (rewrite REC_unfold[OF reflexive MONO])
    by rule
    
  lemma REC'_mono[partial_function_mono]:
    assumes MONO: "\<And>D x. M.mono_body (\<lambda>E. B D (\<lambda>x. ll_call (E x)) x)"
    assumes 1: "\<And>E x. M_mono (\<lambda>D. B D (\<lambda>x. ll_call (E x)) x)"
    shows "M_mono (\<lambda>D. REC' (B D) x)"
    unfolding REC'_def
    using assms
    by pf_mono_prover
    
    
  
  notepad  (* TODO: cleanup *)
  begin
    \<^cancel>\<open>
  
    assume MONO: "\<And>x. M.mono_body (\<lambda>fa. F (\<lambda>x. ll_call (fa x)) x)"
    
      and DEF: "f \<equiv> REC' F"
      and F: " F  \<equiv> \<lambda>D x. (if x>0 then D (x-1) else return 0 )"
    have "P (ll_call (f x))"
      apply(rewrite REC'_unfold[OF DEF MONO])
      apply(rewrite REC'_unfold[OF DEF MONO])
      apply(rewrite REC'_unfold[OF DEF MONO])
      apply(rewrite REC'_unfold[OF DEF MONO])
      unfolding F ll_call_def sorry
  \<close>
  end

  subsubsection \<open>While-Combinator\<close>
  text \<open>
    Note that we also include the while combinator at this point, as we direct translation 
    of while to a control flow graph is the default translation mode of the code generator. 
    
    As an optional feature, while can be translated to 
    a tail recursive function call, which the preprocessor can do automatically.
  \<close>
    
  definition llc_while :: "('a::llvm_repv \<Rightarrow> 1 word llM) \<Rightarrow> ('a \<Rightarrow> 'a llM) \<Rightarrow> 'a \<Rightarrow> 'a llM" where
    "llc_while b f s\<^sub>0 \<equiv> ll_call (REC' (\<lambda>mwhile \<sigma>. doM {
              ctd \<leftarrow> b \<sigma>;
              llc_if ctd (f \<sigma> \<bind> mwhile) (return \<sigma>)
            }) s\<^sub>0)" 

  (*          
  lemma gen_code_thm_llc_while:
    assumes "f \<equiv> llc_while b body"
    shows "f s = ll_call (doM { ctd \<leftarrow> b s; llc_if ctd (doM { s\<leftarrow>body s; f s}) (return s)})"
    unfolding assms
    unfolding llc_while_def llc_if_def
    apply (rewrite REC'_unfold[OF reflexive])
    apply pf_mono_prover
    by simp
  *)

  (* 'Definition' of llc_while for presentation in paper: *)  
  lemma "\<And>c. llc_while b c s \<equiv> ll_call (doM {
     x \<leftarrow> b s;
     llc_if x (doM {s\<leftarrow>c s; llc_while b c s}) (return s)
   })"
    unfolding llc_while_def llc_if_def
    apply (rewrite REC'_unfold[OF reflexive])
    apply pf_mono_prover
    by simp
    
   
  lemma llc_while_mono[partial_function_mono]:      
    assumes "\<And>x. M_mono (\<lambda>f. b f x)"
    assumes "\<And>x. M_mono (\<lambda>f. c f x)"
    shows "M_mono (\<lambda>D. llc_while (b D) (c D) \<sigma>)"
    using assms unfolding llc_while_def by pf_mono_prover
      
    
       
end
