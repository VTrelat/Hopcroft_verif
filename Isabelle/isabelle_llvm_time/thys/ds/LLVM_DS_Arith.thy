section \<open>Fixed-Width Integer Arithmetic\<close>
theory LLVM_DS_Arith
imports "../vcg/LLVM_VCG_Main"
begin

text \<open>Implementing integers and natural numbers
  by fixed-width integers\<close>

(* TODO: Move *)
definition snats :: "nat \<Rightarrow> nat set"
  where "snats n = {i. i < 2 ^ (n-1)}"

definition max_unat :: "nat \<Rightarrow> nat" where "max_unat n \<equiv> 2^n"  
abbreviation (input) "min_uint \<equiv> 0::int"
definition max_uint :: "nat \<Rightarrow> int" where "max_uint n \<equiv> 2^n"  

definition min_sint :: "nat \<Rightarrow> int" where "min_sint n \<equiv> -(2^(n-1))"
definition max_sint :: "nat \<Rightarrow> int" where "max_sint n \<equiv> 2^(n-1)"  

definition "max_snat n \<equiv> (2::nat)^(n-1)"



lemma in_unats_conv[simp]: "x\<in>unats n \<longleftrightarrow> x<max_unat n" by (auto simp: unats_def max_unat_def)
  
lemma in_sints_conv[simp]: "n\<noteq>0 \<Longrightarrow> x\<in>sints n \<longleftrightarrow> min_sint n \<le> x \<and> x<max_sint n"
  by (auto simp: sints_num min_sint_def max_sint_def)


lemma in_uints_conv[simp]: "x\<in>uints n \<longleftrightarrow> min_uint \<le> x \<and> x<max_uint n"
  by (auto simp: uints_num max_uint_def)

lemma in_snats_conv[simp]: "n\<in>snats N \<longleftrightarrow> n<max_snat N"
  by (auto simp: snats_def max_snat_def)
  
  
lemma in_range_uint_conv[simp]: "x\<in>range (uint::'a::len word \<Rightarrow> _) \<longleftrightarrow> min_uint \<le> x \<and> x<max_uint LENGTH('a)"
  by (auto simp: uints_num max_uint_def word_uint.Rep_range) 
  
  
lemma uint_lt_max_uint[simp]: "uint (w::'a::len word) < max_uint LENGTH('a)"  
  using max_uint_def by auto

lemma unat_lt_max_unat[simp]: "unat (w::'a::len word) < max_unat LENGTH('a)"  
  using max_unat_def by auto

lemma sint_cmp_extr_sint[simp]: 
  "min_sint LENGTH('a) \<le> sint (w::'a::len word)"  
  "sint (w::'a::len word) < max_sint LENGTH('a)"  
  unfolding max_sint_def min_sint_def using sint_range' by auto 
  
definition snat :: "_::len2 word \<Rightarrow> nat" where "snat \<equiv> nat o sint"

(* TODO: Move *)       
lemma not_bin_nth_if_less: "\<lbrakk>0\<le>i; i<2^n\<rbrakk> \<Longrightarrow> \<not>(bin_nth i n)"
  apply auto
  using bintrunc_mod2p nth_bintr by force
       
  
lemma snat_zero[simp]: "snat 0 = 0" by (auto simp: snat_def)
lemma snat_one[simp]: "snat (1) = 1" by (auto simp: snat_def)
  
lemma snat_numeral[simp]:
  fixes b
  defines "w::'a::len2 word \<equiv> numeral b"
  defines "n::nat \<equiv> numeral b"
  assumes A: "n<max_snat LENGTH('a)"
  shows "snat w = n"    
proof -  
  have MSB: "\<not>msb w" using A
    apply (simp add: w_def n_def max_snat_def not_bin_nth_if_less)
    apply (rule not_bin_nth_if_less)
    apply simp
    by (metis of_nat_less_iff of_nat_numeral semiring_1_class.of_nat_power)
  
  have "snat w = nat (sint w)" by (simp add: snat_def)
  also have "sint w = uint w" using MSB by (simp add: sint_eq_uint)
  also have "\<dots> = numeral b mod 2^LENGTH('a)" unfolding w_def by (rule uint_numeral)
  also have "\<dots> = numeral b" 
  proof (rule mod_pos_pos_trivial)
    have "int n < int (Suc 1 ^ len_of (TYPE('a)::'a itself))"
      by (metis One_nat_def assms(3) diff_le_self lessI max_snat_def numerals(2) of_nat_less_iff order_less_le_trans power_increasing_iff)
    then show "(numeral b::int) < 2 ^ len_of (TYPE('a)::'a itself)"
      by (simp add: n_def)
  qed simp
  finally show ?thesis unfolding n_def by simp
qed  

abbreviation (input) "word_len \<equiv> \<lambda>_::'a::len0 word. LENGTH('a)"

lemma snat_lt_max_snat[simp]: "snat w < max_snat (word_len w)"
  by (auto simp: snat_def max_snat_def sint_range')
  
  
subsection \<open>Constant Folding\<close>  
(*
   TODO: No idea how complete these are 
*)
lemmas llvm_num_const_simps[llvm_inline] =
  arith_extra_simps
  arith_simps arith_special 
  more_arith_simps
  nat_numeral_diff_1 diff_nat_numeral nat_numeral nat_0 nat_1 minus_nat.diff_0 
  numeral_plus_one one_plus_numeral diff_minus_eq_add add_uminus_conv_diff
  cancel_comm_monoid_add_class.diff_cancel 
  pred_numeral_simps
  Num.pow.simps power_numeral power_0 monoid_mult_class.power_one_right

  word_of_int_numeral word_of_int_neg_numeral word_of_int_0 word_of_int_1  

(* normalize word numerals to be positive and within range. *)    
declaration \<open>fn _ => Named_Simpsets.map_ctxt @{named_simpset llvm_inline} (fn ctxt => 
  ctxt addsimprocs [@{simproc unsigned_norm},@{simproc unsigned_norm_neg0},@{simproc unsigned_norm_neg1}])\<close>
lemmas [llvm_inline] = minus_one_norm_num of_nat_numeral
lemmas [llvm_inline] = len_of_numeral_defs  \<comment> \<open>Computation of LENGTH(_)\<close>
  
  
  
(* Regression test for constant folding *)  
experiment
begin                                                            

  method ss = (simp named_ss llvm_inline: )

  type_synonym w64 = "64 word"
  type_synonym w1 = "1 word"
  
  (* nat + *)
  schematic_goal "(3::nat) + 7 = numeral ?a" by ss
  schematic_goal "(3::nat) + 0 = numeral ?a" by ss
  schematic_goal "(3::nat) + 1 = numeral ?a" by ss
  schematic_goal "(0::nat) + 7 = numeral ?a" by ss
  schematic_goal "(1::nat) + 7 = numeral ?a" by ss
  
  (* int + *)
  schematic_goal "(3::int) + 7 = numeral ?a" by ss
  schematic_goal "(3::int) + 0 = numeral ?a" by ss
  schematic_goal "(3::int) + 1 = numeral ?a" by ss
  schematic_goal "(0::int) + 7 = numeral ?a" by ss
  schematic_goal "(1::int) + 7 = numeral ?a" by ss
  
  schematic_goal "(3::int) + -7 = - numeral ?a" by ss
  schematic_goal "(3::int) + -0 = numeral ?a" by ss
  schematic_goal "(3::int) + -1 = numeral ?a" by ss
  schematic_goal "(0::int) + -7 = - numeral ?a" by ss
  schematic_goal "(1::int) + -7 = - numeral ?a" by ss

  (* word 64 *)
  schematic_goal "(3::w64) + 7 = numeral ?a" by ss
  schematic_goal "(3::w64) + 0 = numeral ?a" by ss
  schematic_goal "(3::w64) + 1 = numeral ?a" by ss
  schematic_goal "(0::w64) + 7 = numeral ?a" by ss
  schematic_goal "(1::w64) + 7 = numeral ?a" by ss
  
  schematic_goal "(-0::w64) = 0" by ss
  schematic_goal "(-1::w64) = numeral ?a" by ss
  schematic_goal "(-3::w64) = numeral ?a" by ss
  
  schematic_goal "(3::w64) + -0 = numeral ?a" by ss
  schematic_goal "(3::w64) + -1 = numeral ?a" by ss
  schematic_goal "(0::w64) + -7 = numeral ?a" by ss
  schematic_goal "(1::w64) + -7 = numeral ?a" by ss
  
  schematic_goal "(3::w1) + 7 = 0" by ss
  schematic_goal "(3::w1) + 0 = 1" by ss
  schematic_goal "(3::w1) + 1 = 0" by ss
  schematic_goal "(0::w1) + 7 = 1" by ss
  schematic_goal "(1::w1) + 7 = 0" by ss
  
  schematic_goal "(-0::w1) = 0" by ss
(*  schematic_goal "(-1::w1) = 1" by ss  
  schematic_goal "(-3::w1) = 0" by ss TODO/FIXME: does not work yet*)
  
  schematic_goal "(3::w1) + -0 = 1" by ss
  schematic_goal "(3::w1) + -1 = 0" by ss
  (*
  schematic_goal "(0::w1) + -7 = 1" by ss
  schematic_goal "(1::w1) + -7 = numeral ?a" by ss TODO/FIXME: does not work yet*)
  
  (* nat - *)
  schematic_goal "(9::nat) - 7 = numeral ?a" by ss
  schematic_goal "(3::nat) - 0 = numeral ?a" by ss
  schematic_goal "(3::nat) - 1 = numeral ?a" by ss
  schematic_goal "(0::nat) - 0 = 0" by ss
  schematic_goal "(1::nat) - 0 = 1" by ss
  schematic_goal "(1::nat) - 1 = 0"  by ss
  
  (* int - *)
  schematic_goal "(3::int) - 7 = -numeral ?a" by ss
  schematic_goal "(3::int) - 0 = numeral ?a" by ss
  schematic_goal "(3::int) - 1 = numeral ?a" by ss
  schematic_goal "(0::int) - 7 = -numeral ?a" by ss
  schematic_goal "(1::int) - 7 = -numeral ?a" by ss
  schematic_goal "(0::int) - 0 = 0" by ss
  schematic_goal "(1::int) - 0 = 1" by ss
  schematic_goal "(1::int) - 1 = 0" by ss
  
  schematic_goal "(3::int) - -7 = numeral ?a" by ss
  schematic_goal "(3::int) - -0 = numeral ?a" by ss
  schematic_goal "(3::int) - -1 = numeral ?a" by ss
  schematic_goal "(0::int) - -7 = numeral ?a" by ss
  schematic_goal "(1::int) - -7 = numeral ?a" by ss
  schematic_goal "(0::int) - -0 = 0" by ss
  schematic_goal "(1::int) - -0 = 1" by ss
  schematic_goal "(1::int) - -1 = numeral ?a" by ss

  (* Powers (of 2) *)
  schematic_goal "(2::nat)^0 = 1" by ss
  schematic_goal "(2::nat)^1 = numeral ?a" by ss
  schematic_goal "(2::nat)^3 = numeral ?a" by ss
  schematic_goal "(2::nat)^4 = numeral ?a" by ss
  schematic_goal "(2::nat)^5 = numeral ?a" by ss
  schematic_goal "(2::nat)^6 = numeral ?a" by ss
  schematic_goal "(2::nat)^7 = numeral ?a" by ss
  schematic_goal "(2::nat)^8 = numeral ?a" by ss
  schematic_goal "(2::nat)^16 = numeral ?a" by ss
  schematic_goal "(2::nat)^32 = numeral ?a" by ss
  schematic_goal "(2::nat)^64 = numeral ?a" by ss
  schematic_goal "(2::nat)^128 = numeral ?a" by ss
  
  
  schematic_goal "(2::int)^0 = 1" by ss
  schematic_goal "(2::int)^1 = numeral ?a" by ss
  schematic_goal "(2::int)^3 = numeral ?a" by ss
  schematic_goal "(2::int)^4 = numeral ?a" by ss
  schematic_goal "(2::int)^5 = numeral ?a" by ss
  schematic_goal "(2::int)^6 = numeral ?a" by ss
  schematic_goal "(2::int)^7 = numeral ?a" by ss
  schematic_goal "(2::int)^8 = numeral ?a" by ss
  schematic_goal "(2::int)^16 = numeral ?a" by ss
  schematic_goal "(2::int)^32 = numeral ?a" by ss
  schematic_goal "(2::int)^64 = numeral ?a" by ss
  schematic_goal "(2::int)^128 = numeral ?a" by ss
    

end


(* 
  = Num.arith_simps power_numeral pred_numeral_simps power_0
    arith_special numeral_One[symmetric]
    len_of_numeral_defs word_of_int_numeral word_of_int_0 word_of_int_1 (* Computing LENGTH(numeral-type) *)
  
    max_uint_def max_sint_def min_sint_def
*)    
    
subsection \<open>Reflection of Maximum Representable Values\<close>  
  
lemmas [llvm_inline] = max_uint_def max_sint_def min_sint_def

find_theorems "word_of_int (-_)"

definition ll_max_uint :: "'l::len word llM" where [llvm_inline]: "ll_max_uint \<equiv> return (word_of_int (max_uint LENGTH('l) - 1))"
definition ll_max_sint :: "'l::len2 word llM" where [llvm_inline]: "ll_max_sint \<equiv> return (word_of_int (max_sint LENGTH('l) - 1))"
definition ll_min_sint :: "'l::len2 word llM" where [llvm_inline]: "ll_min_sint \<equiv> return (word_of_int (min_sint LENGTH('l) + 1))"
  
(* TODO: Tuples will require some more thought. *)
definition mk_pair :: "'a::llvm_rep \<Rightarrow> 'b::llvm_rep llM \<Rightarrow> ('a\<times>'b) llM" where
  [llvm_inline]: "mk_pair a ctd \<equiv> doM { r\<leftarrow>ll_insert_fst init a; b\<leftarrow>ctd; ll_insert_snd r b }"

experiment begin
  (* Regression test to ensure that preprocessor does the computations. export-llvm will complain about non-numeral constants otherwise. *)
  definition [llvm_code]: "test \<equiv> doM {
    a\<leftarrow>(ll_max_uint :: 64 word llM);
    b\<leftarrow>(ll_max_sint :: 64 word llM);
    c\<leftarrow>(ll_min_sint :: 64 word llM);

    d\<leftarrow>(ll_max_uint :: 1 word llM);
    e\<leftarrow>(ll_max_sint :: 2 word llM);
    f\<leftarrow>(ll_min_sint :: 2 word llM);
      
    mk_pair a (mk_pair b (mk_pair c (mk_pair d (mk_pair e (return f)))))
  }"
  
  export_llvm "test"
end


context llvm_prim_arith_setup begin  

lemmas [vcg_normalize_simps] = ll_max_uint_def ll_max_sint_def ll_min_sint_def

lemma len_neq_one_conv: 
  "LENGTH('l::len) \<noteq> Suc 0 \<longleftrightarrow> (\<exists>n. LENGTH('l) = Suc (Suc n))"
  apply auto
  by (metis One_nat_def Suc_pred' len_gt_0 neq0_conv)
  
lemma word_of_int_div2: "0\<le>w \<Longrightarrow> w<2^LENGTH('a) \<Longrightarrow> word_of_int w div (2::'a::len word) = word_of_int (w div 2)"  
  by (force simp add: word_uint_eq_iff uint_word_of_int uint_div bintrunc_mod2p) 
  
lemma word_of_int_shr1: "0\<le>w \<Longrightarrow> w<2^LENGTH('a::len) \<Longrightarrow> (word_of_int w :: 'a word) >> Suc 0 = word_of_int (w div 2)"
  by (auto simp: shiftr1_is_div_2[simplified] word_of_int_div2)

lemma ll_max_sint_aux1: "((4::int) * 2 ^ n - 1) div 2 < 4 * 2 ^ n" 
proof -
  have "((4::int) * 2 ^ n - 1) < (4::int) * 2 ^ n" by auto
  hence "((4::int) * 2 ^ n - 1) div 2 \<le> ((4::int) * 2 ^ n) div 2" by auto
  also have "\<dots> < 4 * 2^n" by auto
  finally show ?thesis .
qed  
 
(*
lemma ll_max_sint_simp[vcg_normalize_simps]: "(ll_max_sint::'l::len2 word llM) = consume1r ''sub'' (word_of_int (max_sint LENGTH('l) - 1))"
  unfolding ll_max_sint_def 
  supply [simp] = Suc_lessI max_sint_def max_uint_def len_neq_one_conv
  apply vcg_normalize
  apply (simp add: word_of_int_shr1)
  apply (rule len2E[where 'a='l]; simp)
  apply (subst word_of_int_inj)
  apply (auto simp: field_simps)
  apply (simp add: nonneg_mod_div)
  apply (simp add: ll_max_sint_aux1)
  apply (smt one_le_power)
  by (simp add: pos_add_strict)
*)    


lemma ll_max_uint_rule[vcg_rules]: "llvm_htriple \<box> (ll_max_uint::'l::len word llM) (\<lambda>r. \<up>(uint r = max_uint (LENGTH('l)) - 1))"
  supply [simp] = max_uint_def zmod_minus1 uint_word_ariths word_of_int_inverse
  by vcg'
  
  
lemma ll_max_sint_simp: "(ll_max_sint::'l::len2 word llM) = return (word_of_int (max_sint LENGTH('l) - 1))"
  unfolding ll_max_sint_def 
  apply vcg_normalize done
  (*by (metis (mono_tags, lifting) One_nat_def arith_simps(1) arith_simps(45) exp_eq_zero_iff mask_eq_decr_exp max_sint_def max_uint_def numeral_code(1) of_int_numeral of_int_power of_nat_numeral semiring_1_class.of_nat_power shiftr_mask2 word_exp_length_eq_0)*)
  
  
lemma ll_max_sint_rule[vcg_rules]: "llvm_htriple (\<box>) (ll_max_sint::'l::len2 word llM) (\<lambda>r. \<up>(uint r = max_sint LENGTH('l) - 1))"
  apply vcg'
  apply (auto simp add: uint_word_of_int max_sint_def)
  by (smt (z3) One_nat_def diff_less len_gt_0 lessI linorder_not_less msb_big msb_uint_big sint_range' uint_arith_simps(4) unsigned_1 word_less_sub_le word_power_less_1)
  
(* TODO: port that
lemma ll_min_sint_rule[vcg_rules]: "llvm_htriple (\<box>) (ll_min_sint::'l::len2 word llM) (\<lambda>r. \<up>(sint r = min_sint LENGTH('l) + 1))"
  apply vcg'
  apply (simp add: min_sint_def max_sint_def power_gt1_lemma word_sint.Abs_inverse)
*)  

end  
  
subsection \<open>Signed Integers\<close>

interpretation sint: standard_opr_abstraction sint 
  "\<lambda>_. True" 
  "\<lambda>op (_::'a::len word itself) a. op a \<in> sints LENGTH('a)" 
  "\<lambda>op (_::'a::len word itself) a b. op a b \<in> sints LENGTH('a)" 
  "\<lambda>a c. a\<in>sints LENGTH('a)"
  by standard auto

  

method prove_sint_op uses simp = (
  rule sint.is_bin_opI sint.is_cmp_opI sint.is_un_opI; 
  (auto simp: min_sint_def max_sint_def vcg_normalize_simps simp)?; 
  (determ uint_arith; fail)?)  

lemma sint_neq_ZD: "sint b \<noteq> 0 \<Longrightarrow> b\<noteq>0" by auto
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma sint_bin_ops:
  "sint.is_bin_op' ''add'' ll_add (+) (+)" 
  "sint.is_bin_op' ''sub'' ll_sub (-) (-)"  
  "sint.is_bin_op' ''mul'' ll_mul (*) (*)"  
  "sint.is_bin_op ''sdiv'' (\<lambda>(_::'a::len word itself) a b. b\<noteq>0 \<and> a sdiv b \<in> sints LENGTH('a)) ll_sdiv (sdiv) (sdiv)"  
  "sint.is_bin_op ''srem'' (\<lambda>(_::'a::len word itself) a b. b\<noteq>0 \<and> a sdiv b \<in> sints LENGTH('a)) ll_srem (smod) (smod)"
  supply [simp del] = in_sints_conv
  apply (all \<open>prove_sint_op simp:  sint_neq_ZD\<close>)
  apply (simp_all add: sbintrunc_eq_if_in_range sint_word_ariths signed_mod_arith signed_div_arith)
  using smod_word_min smod_word_max 
  by (auto simp add: in_sints_conv min_sint_def max_sint_def)
  
lemma sint_cmp_ops: 
  "sint.is_cmp_op ''icmp_eq'' ll_icmp_eq (=) (=)" 
  "sint.is_cmp_op ''icmp_ne'' ll_icmp_ne (\<noteq>) (\<noteq>)"
  "sint.is_cmp_op ''icmp_sle'' ll_icmp_sle (\<lambda>a b. a <=s b) (\<le>)" (* FIXME: Why isn't <=s and <s proper infix operator? *) 
  "sint.is_cmp_op ''icmp_slt'' ll_icmp_slt (\<lambda>a b. a <s b) (<)" 
  by (all \<open>prove_sint_op simp: word_sle_def word_sless_def le_less\<close>)

lemmas sint_rules[vcg_rules] =  
  sint_bin_ops[THEN sint.bin_op_tmpl]
  sint_cmp_ops[THEN sint.cmp_op_tmpl]
  
    
definition signed :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "signed c \<equiv> c"  
  
declare [[vcg_const "signed (numeral a)"]]
declare [[vcg_const "signed (-numeral a)"]]
declare [[vcg_const "signed 0"]]
declare [[vcg_const "signed (-0)"]]
declare [[vcg_const "signed 1"]]
declare [[vcg_const "signed (-1)"]]


lemma monadify_signed[vcg_monadify_xforms]: 
  "return (signed x) = ll_const (signed x)" by (simp add: ll_const_def)

  
lemma ll_const_signed_aux: "\<lbrakk>n\<noteq>0; - (2 ^ (n - Suc 0)) \<le> i; i < 2 ^ (n - Suc 0)\<rbrakk>
         \<Longrightarrow> (i + 2 ^ (n - Suc 0)) mod 2 ^ n - 2 ^ (n - Suc 0) = (i::int)"  
  by (cases n; simp)
  
lemma ll_const_signed_rule[vcg_rules]: 
  "llvm_htriple \<box> (ll_const (signed 0)) (\<lambda>r. \<upharpoonleft>sint.assn 0 r)"
  "llvm_htriple (\<up>\<^sub>d(LENGTH('a::len) \<noteq> 1)) (ll_const (signed (1::'a word))) (\<lambda>r. \<upharpoonleft>sint.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> sints LENGTH('a))) (ll_const (signed (numeral w::'a::len word))) (\<lambda>r. \<upharpoonleft>sint.assn (numeral w) r)"
  unfolding ll_const_def signed_def sint.assn_def
  supply [simp] = sbintrunc_mod2p max_sint_def min_sint_def ll_const_signed_aux
  by vcg

  
(* TODO: Move *)
lemma lt_exp2n_signed_estimate[simp]:
  fixes x::int
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n > n')" "x<2^n'"
  shows "x < max_sint n"
  using A unfolding ASSUMPTION_def max_sint_def
  by (smt One_nat_def Suc_le_mono Suc_pred assms(1) len_gt_0 less_eq_Suc_le power_increasing_iff)
    
end  
  
    
  
  
subsection \<open>Unsigned Integers\<close>

interpretation uint: standard_opr_abstraction uint 
  "\<lambda>_. True" 
  "\<lambda>op (_::'a::len word itself) a. op a \<in> uints LENGTH('a)" 
  "\<lambda>op (_::'a::len word itself) a b. op a b \<in> uints LENGTH('a)" 
  "\<lambda>a c. a\<in>uints LENGTH('a)"
  by standard auto


method prove_uint_op uses simp = (
  rule uint.is_bin_opI uint.is_cmp_opI uint.is_un_opI; 
  (auto simp: max_uint_def vcg_normalize_simps simp)?; 
  (determ uint_arith; fail)?)  

lemma uint_neq_ZD: "uint b \<noteq> 0 \<Longrightarrow> b\<noteq>0" by auto
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma uint_bin_ops_arith:
  "uint.is_bin_op ''add'' (\<lambda>(_::'a::len word itself) a b. a+b < max_uint LENGTH('a)) ll_add (+) (+)" 
  "uint.is_bin_op ''sub'' (\<lambda>_ a b. b\<le>a) ll_sub (-) (-)"  
  "uint.is_bin_op ''mul'' (\<lambda>(_::'a::len word itself) a b. a*b < max_uint LENGTH('a)) ll_mul (*) (*)"  
  "uint.is_bin_op ''udiv'' (\<lambda>_ a b. b\<noteq>0) ll_udiv (div) (div)"  
  "uint.is_bin_op ''urem'' (\<lambda>_ a b. b\<noteq>0) ll_urem (mod) (mod)"
  by (all \<open>prove_uint_op simp: uint_mult_lem uint_neq_ZD uint_div uint_mod\<close>)

(* TODO: Remove preconditions! *)
lemma uint_bin_ops_bitwise:
  "uint.is_bin_op ''and'' (\<lambda>_ _ _. True) ll_and (AND) (AND)" 
  "uint.is_bin_op ''or'' (\<lambda>_ _ _. True) ll_or (OR) (OR)" 
  "uint.is_bin_op ''xor'' (\<lambda>_ _ _. True) ll_xor (XOR) (XOR)" 
  by (all \<open>prove_uint_op simp: uint_and uint_or uint_xor\<close>)

lemmas uint_bin_ops = uint_bin_ops_arith uint_bin_ops_bitwise
  
lemma uint_cmp_ops: 
  "uint.is_cmp_op ''icmp_eq'' ll_icmp_eq (=) (=)" 
  "uint.is_cmp_op ''icmp_ne'' ll_icmp_ne (\<noteq>) (\<noteq>)"
  "uint.is_cmp_op ''icmp_ule'' ll_icmp_ule (\<le>) (\<le>)" 
  "uint.is_cmp_op ''icmp_ult'' ll_icmp_ult (<) (<)" 
  by (all \<open>prove_uint_op\<close>)
  
lemmas uint_rules[vcg_rules] =
  uint_bin_ops[THEN uint.bin_op_tmpl]
  uint_cmp_ops[THEN uint.cmp_op_tmpl]
  
  
definition unsigned :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "unsigned c \<equiv> c"  
  
declare [[vcg_const "unsigned (numeral a)"]]
declare [[vcg_const "unsigned 0"]]
declare [[vcg_const "unsigned 1"]]

lemma monadify_unsigned[vcg_monadify_xforms]: 
  "return (unsigned x) = ll_const (unsigned x)" by (simp add: ll_const_def)

lemma uint_numeral_eq_aux: "numeral w < (2::int) ^ LENGTH('a) \<Longrightarrow> take_bit LENGTH('a::len) (numeral w::nat) = numeral w"  
  by (simp add: nat_int_comparison(2) take_bit_eq_mod)
 
lemma ll_const_unsigned_rule[vcg_rules]: 
  "llvm_htriple \<box> (ll_const (unsigned 0)) (\<lambda>r. \<upharpoonleft>uint.assn 0 r)"
  "llvm_htriple \<box> (ll_const (unsigned 1)) (\<lambda>r. \<upharpoonleft>uint.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> uints LENGTH('a))) (ll_const (unsigned (numeral w::'a::len word))) (\<lambda>r. \<upharpoonleft>uint.assn (numeral w) r)"
  unfolding ll_const_def unsigned_def uint.assn_def
  supply [simp] = bintrunc_mod2p max_uint_def uint_numeral_eq_aux
  by vcg  

  
(* TODO: Move *)
lemma lt_exp2n_estimate[simp]: 
  fixes x::int
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n \<ge> n')" "x<2^n'"
  shows "x < max_uint n"
  using A unfolding ASSUMPTION_def max_uint_def
  by (smt power_increasing_iff)

    
end  

subsubsection \<open>Natural Numbers by unsigned\<close>

find_theorems "uint _ < max_uint _"

interpretation unat: standard_opr_abstraction unat 
  "\<lambda>_. True" 
  "\<lambda>op (_::'a::len word itself) a. op a \<in> unats LENGTH('a)" 
  "\<lambda>op (_::'a::len word itself) a b. op a b \<in> unats LENGTH('a)" 
  "\<lambda>a c. a\<in>unats LENGTH('a)"
  by standard auto


method prove_unat_op uses simp = (
  rule unat.is_bin_opI unat.is_un_opI unat.is_cmp_opI; 
  (auto simp: max_unat_def vcg_normalize_simps simp)?; 
  (determ unat_arith; fail)?)  

lemma unat_neq_ZD: "unat b \<noteq> 0 \<Longrightarrow> b\<noteq>0" by auto
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma unat_bin_ops:
  "unat.is_bin_op ''add'' (\<lambda>(_::'a::len word itself) a b. a+b < max_unat LENGTH('a)) ll_add (+) (+)" 
  "unat.is_bin_op ''sub'' (\<lambda>_ a b. b\<le>a) ll_sub (-) (-)"  
  "unat.is_bin_op ''mul'' (\<lambda>(_::'a::len word itself) a b. a*b < max_unat LENGTH('a)) ll_mul (*) (*)"  
  "unat.is_bin_op ''udiv'' (\<lambda>_ a b. b\<noteq>0) ll_udiv (div) (div)"  
  "unat.is_bin_op ''urem'' (\<lambda>_ a b. b\<noteq>0) ll_urem (mod) (mod)"
  by (all \<open>prove_unat_op simp: unat_mult_lem unat_neq_ZD unat_div unat_mod\<close>)

lemma unat_bin_ops_bitwise:
  "unat.is_bin_op ''and'' (\<lambda>_ _ _. True) ll_and (AND) (AND)" 
  "unat.is_bin_op ''or'' (\<lambda>_ _ _. True) ll_or (OR) (OR)" 
  "unat.is_bin_op ''xor'' (\<lambda>_ _ _. True) ll_xor (XOR) (XOR)" 
  by (all \<open>prove_unat_op simp: unat_and unat_or unat_xor\<close>)
  
lemma unat_un_ops: "unat.is_un_op' ''add'' (\<lambda>x. ll_add x 1) (\<lambda>x. x+1) Suc"
  by (prove_unat_op simp: unat_word_ariths)
  
lemma unat_cmp_ops: 
  "unat.is_cmp_op ''icmp_eq'' ll_icmp_eq (=) (=)" 
  "unat.is_cmp_op ''icmp_ne'' ll_icmp_ne (\<noteq>) (\<noteq>)"
  "unat.is_cmp_op ''icmp_ule'' ll_icmp_ule (\<le>) (\<le>)" 
  "unat.is_cmp_op ''icmp_ult'' ll_icmp_ult (<) (<)" 
  by (all \<open>prove_unat_op\<close>)
  
lemmas unat_rules[vcg_rules] =
  unat_bin_ops[THEN unat.bin_op_tmpl]
  unat_un_ops[THEN unat.un_op_tmpl]
  unat_cmp_ops[THEN unat.cmp_op_tmpl]
  
  
definition unsigned_nat :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "unsigned_nat c \<equiv> c"  
  
declare [[vcg_const "unsigned_nat (numeral a)"]]
declare [[vcg_const "unsigned_nat 0"]]
declare [[vcg_const "unsigned_nat 1"]]

lemma monadify_unsigned_nat[vcg_monadify_xforms]: 
  "return (unsigned_nat x) = ll_const (unsigned_nat x)" 
  by (simp add: ll_const_def)
  
lemma ll_const_unsigned_nat_rule[vcg_rules]: 
  "llvm_htriple \<box> (ll_const (unsigned_nat 0)) (\<lambda>r. \<upharpoonleft>unat.assn 0 r)"
  "llvm_htriple \<box> (ll_const (unsigned_nat 1)) (\<lambda>r. \<upharpoonleft>unat.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> unats LENGTH('a))) (ll_const (unsigned_nat (numeral w::'a::len word))) (\<lambda>r. \<upharpoonleft>unat.assn (numeral w) r)"
  unfolding ll_const_def unsigned_nat_def unat.assn_def 
  supply [simp] = bintrunc_mod2p max_unat_def unat_numeral and [simp del] = unat_bintrunc unsigned_numeral
  by vcg
  
(* TODO: Move *)
lemma lt_exp2n_nat_estimate[simp]: 
  fixes x::nat
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n \<ge> n')" "x<2^n'"
  shows "x < max_unat n"
  using A unfolding ASSUMPTION_def max_unat_def
  by (metis leD leI le_less_trans less_nat_zero_code nat_power_less_imp_less
      nat_zero_less_power_iff pow_mono_leq_imp_lt)

    
end  


subsection \<open>Natural Numbers by signed\<close>


definition "snat_invar (w::'a::len2 word) \<equiv> \<not>msb w"
interpretation snat: standard_opr_abstraction snat "snat_invar" 
  "\<lambda>op (_::'a::len2 word itself) a. op a \<in> snats LENGTH('a)" 
  "\<lambda>op (_::'a::len2 word itself) a b. op a b \<in> snats LENGTH('a)" 
  "\<lambda>a c. a\<in>snats LENGTH('a)" 
  apply standard apply (auto simp: snat_invar_def) done

lemma snat_invar_alt: "snat_invar (w::'a::len2 word) \<longleftrightarrow> (\<exists>n. word_len w = Suc n \<and> unat w < 2^n)"  
  apply (cases "word_len w")
  apply (auto simp: snat_invar_def msb_unat_big)
  done

lemma snat_eq_unat_aux1: "unat w < 2^(word_len w - 1) \<Longrightarrow> snat w = unat w"
  apply (auto simp: snat_invar_alt snat_def) 
  apply transfer
  apply auto
  apply (subst signed_take_bit_eq_if_positive)
  subgoal
    by (metis One_nat_def Suc_pred' bin_nth_take_bit_iff len_gt_0 lessI not_bin_nth_if_less not_le not_take_bit_negative)
  subgoal 
    by (metis bintrunc_bintrunc diff_le_self take_bit_int_eq_self_iff take_bit_tightened) 
  done

lemma snat_eq_unat_aux2: 
  "snat_invar w \<Longrightarrow> snat w = unat w"
  by (auto simp: snat_invar_alt snat_eq_unat_aux1) 

lemmas snat_eq_unat = snat_eq_unat_aux1 snat_eq_unat_aux2


lemma cnv_snat_to_uint:
  assumes "snat_invar w"
  shows "snat w = nat (uint w)" 
    and "sint w = uint w"
    and "unat w = nat (uint w)"
  using assms apply -
  apply (simp add: snat_eq_unat(2)  sint_eq_uint)
  apply (simp add: sint_eq_uint snat_invar_def)
  apply (simp add: )
  done
      


method prove_snat_op uses simp = (
  rule snat.is_bin_opI snat.is_un_opI snat.is_cmp_opI; 
  (auto simp: max_snat_def snat_invar_alt snat_eq_unat vcg_normalize_simps simp)?)  
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma snat_in_bounds_aux: "(a::nat)<2^(x-Suc 0) \<Longrightarrow> a<2^x"
  by (metis diff_le_self leI le_less_trans less_not_refl nat_power_less_imp_less numeral_2_eq_2 zero_less_Suc)

lemma snat_bin_ops:
  "snat.is_bin_op' ''add'' ll_add (+) (+)" 
  "snat.is_bin_op ''sub'' (\<lambda>_ a b. b\<le>a) ll_sub (-) (-)"  
  "snat.is_bin_op' ''mul'' ll_mul (*) (*)"  
  "snat.is_bin_op ''udiv'' (\<lambda>_ a b. b\<noteq>0) ll_udiv (div) (div)"  
  "snat.is_bin_op ''urem'' (\<lambda>_ a b. b\<noteq>0) ll_urem (mod) (mod)"
  
  apply (prove_snat_op simp: unat_word_ariths)
  apply (prove_snat_op simp: unat_word_ariths unat_sub_if')
  apply (prove_snat_op simp: unat_word_ariths)
  subgoal
    apply (prove_snat_op simp: unat_word_ariths)
    apply (subst ll_udiv_simp; auto)
    apply (metis div_le_dividend le_less_trans power_Suc unat_div unat_of_nat word_arith_nat_defs(6))
    apply (subst snat_eq_unat)
    apply (auto simp: unat_div)
    apply (metis div_le_dividend le_less_trans)
    done
  subgoal  
    apply (prove_snat_op simp: unat_word_ariths)
    apply (subst ll_urem_simp; auto)
    apply (meson le_less_trans mod_less_eq_dividend)
    apply (subst snat_eq_unat)
    apply (auto simp: unat_mod)
    apply (meson le_less_trans mod_less_eq_dividend)
    done
  done
  
lemma snat_un_ops: "snat.is_un_op' ''add'' (\<lambda>x. ll_add x 1) (\<lambda>x. x+1) Suc"
  by (prove_snat_op simp: unat_word_ariths)
  
  
lemma snat_cmp_ops:
  "snat.is_cmp_op ''icmp_eq'' ll_icmp_eq (=) (=)" 
  "snat.is_cmp_op ''icmp_ne'' ll_icmp_ne (\<noteq>) (\<noteq>)"
  "snat.is_cmp_op ''icmp_ule'' ll_icmp_ule (\<le>) (\<le>)" 
  "snat.is_cmp_op ''icmp_ult'' ll_icmp_ult (<) (<)" 
  "snat.is_cmp_op ''icmp_sle'' ll_icmp_sle (\<lambda>a b. a <=s b) (\<le>)" 
  "snat.is_cmp_op ''icmp_slt'' ll_icmp_slt (\<lambda>a b. a <s b) (<)" 
  
  apply (prove_snat_op)
  apply (prove_snat_op)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt word_sle_msb_le msb_unat_big)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt word_sle_msb_le word_sless_msb_less msb_unat_big)
  done
  
  
lemmas snat_rules[vcg_rules] =
  snat_bin_ops[THEN snat.bin_op_tmpl]
  snat_un_ops[THEN snat.un_op_tmpl]
  snat_cmp_ops[THEN snat.cmp_op_tmpl]
  
  
  
definition signed_nat :: "'a::len2 word \<Rightarrow> 'a word" where [llvm_inline]: "signed_nat c \<equiv> c"  
  
declare [[vcg_const "signed_nat (numeral a)"]]
declare [[vcg_const "signed_nat 0"]]
declare [[vcg_const "signed_nat 1"]]

lemma monadify_signed_nat[vcg_monadify_xforms]: "return (signed_nat x) = ll_const (signed_nat x)" by (simp add: ll_const_def)

  
lemma ll_const_signed_nat_aux1: "(w::nat) < 2^(n-1) \<Longrightarrow> w mod (2^n) = w"  
  by (simp add: snat_in_bounds_aux)
  
lemma ll_const_signed_nat_aux2: "\<lbrakk>numeral w < (2::nat) ^ (LENGTH('a::len2) - Suc 0)\<rbrakk> \<Longrightarrow> \<not>msb (numeral w::'a word)"  
  apply (auto simp: msb_unat_big snat_in_bounds_aux unat_numeral simp del: unat_bintrunc)
  by (meson le_less_trans linorder_not_less take_bit_nat_less_eq_self)
  
  
lemma ll_const_signed_nat_rule[vcg_rules]: 
  "llvm_htriple (\<box>) (ll_const (signed_nat (0::'a word))) (\<lambda>r. \<upharpoonleft>snat.assn 0 r)"
  "llvm_htriple (\<box>) (ll_const (signed_nat (1::'a word))) (\<lambda>r. \<upharpoonleft>snat.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> snats LENGTH('a))) (ll_const (signed_nat (numeral w::'a::len2 word))) (\<lambda>r. \<upharpoonleft>snat.assn (numeral w) r)"
  unfolding ll_const_def signed_nat_def snat.assn_def 
  apply vcg'
  subgoal by (simp add: not0_implies_Suc snat_invar_alt) 
  subgoal by (simp add: snat_invar_def) 
  subgoal 
    apply (cases "LENGTH('a)"; simp)
    by (metis One_nat_def ll_const_signed_nat_aux2 max_snat_def snat_invar_def)
  done
      
end  

lemma lt_exp2n_snat_estimate[simp]: 
  fixes x::nat
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n > n')" "x<2^n'"
  shows "x < max_snat n"
  using A unfolding ASSUMPTION_def max_snat_def
  by (metis Suc_diff_1 Suc_leI leI le_less_trans nat_power_less_imp_less numeral_2_eq_2 order_less_irrefl zero_less_Suc)




definition [llvm_inline]: "ll_max_snat \<equiv> ll_max_sint"

lemma ll_max_snat_rule[vcg_rules]: "llvm_htriple (\<box>) ll_max_snat (\<lambda>r::'l word. \<upharpoonleft>snat.assn (max_snat LENGTH('l::len2) - 1) r)"
proof -
  interpret llvm_prim_arith_setup .

  note [simp del] = of_int_diff

  have [simp]: "snat_invar (word_of_int (max_sint LENGTH('l) - 1)::'l word)" 
    apply (rule len2E[where 'a='l]; simp)
    apply (auto simp: snat_invar_alt len_neq_one_conv max_sint_def max_snat_def snat_def uint_word_of_int of_int_diff)
    by (metis eq_or_less_helperD lessI power_Suc)
  
  have 1[simp]: "snat_invar ((word_of_int (max_sint LENGTH('l))::'l word) - 1)" 
    apply (rule len2E[where 'a='l]; simp)
    apply (auto simp: snat_invar_alt len_neq_one_conv max_sint_def max_snat_def snat_def uint_word_of_int)
    by (metis eq_or_less_helperD lessI power_Suc)

  show ?thesis
    unfolding ll_max_snat_def snat.assn_def
    apply vcg'
    apply (subst cnv_snat_to_uint, simp)
    apply (simp only: uint_word_of_int)
    apply (clarsimp simp: len_neq_one_conv max_sint_def max_snat_def snat_def snat_invar_alt)
    apply (simp add: nat_mod_distrib nat_mult_distrib nat_diff_distrib' nat_power_eq less_imp_diff_less)
    done
qed  


subsection \<open>Casting\<close>

(* TODO: Add other casts. 

  up/down * su/us/ss/uu

  and su_conv, us_conv
  
  Some casts might be expressable as up/downcast followed by conv!
*)

context begin
  interpretation llvm_prim_arith_setup .

    
  definition [llvm_inline]: "unat_snat_upcast TYPE('a::len2) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "snat_unat_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"
    
  definition [llvm_inline]: "snat_snat_upcast TYPE('a::len2) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "snat_snat_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"
  
  definition [llvm_inline]: "unat_unat_upcast TYPE('a::len) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "unat_unat_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"

  definition unat_snat_conv :: "'l::len2 word \<Rightarrow> 'l word llM" 
    where [llvm_inline]: "unat_snat_conv x \<equiv> return x"  
    
  definition snat_unat_conv :: "'l::len2 word \<Rightarrow> 'l word llM" 
    where [llvm_inline]: "snat_unat_conv x \<equiv> return x"  
  
  lemma unat_snat_upcast_rule[vcg_rules]:
    "llvm_htriple 
      ($$ ''zext'' 1 ** \<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>unat.assn n (ni::'small::len word)) 
      (unat_snat_upcast TYPE('big::len2) ni) 
      (\<lambda>r. \<upharpoonleft>snat.assn n r)"
    unfolding unat.assn_def snat.assn_def unat_snat_upcast_def
    apply vcg'
    apply (auto simp: snat_invar_def snat_eq_unat(2) unat_ucast_upcast)
    done

  lemma snat_unat_downcast_rule[vcg_rules]:
    "llvm_htriple 
      ($$ ''trunc'' 1 ** \<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>snat.assn n (ni::'big::len2 word) ** \<up>(n<max_unat LENGTH('small))) 
      (snat_unat_downcast TYPE('small::len) ni) 
      (\<lambda>r. \<upharpoonleft>unat.assn n r)"
    unfolding unat.assn_def snat.assn_def snat_unat_downcast_def
    apply vcg'
    apply (auto simp: snat_invar_def snat_eq_unat(2) max_unat_def)
    by (metis ucast_nat_def unat_of_nat_eq)

  lemma snat_snat_upcast_rule[vcg_rules]:
    "llvm_htriple 
      ($$ ''zext'' 1 ** \<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>snat.assn n (ni::'small::len2 word)) 
      (snat_snat_upcast TYPE('big::len2) ni) 
      (\<lambda>r. \<upharpoonleft>snat.assn n r)"
    unfolding unat.assn_def snat.assn_def snat_snat_upcast_def
    apply vcg'
    apply (auto simp: snat_invar_def snat_eq_unat(2) unat_ucast_upcast)
    done

  lemma snat_snat_downcast_rule[vcg_rules]:
    "llvm_htriple 
      ($$ ''trunc'' 1 **\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>snat.assn n (ni::'big::len2 word) ** \<up>(n<max_snat LENGTH('small))) 
      (snat_snat_downcast TYPE('small::len2) ni) 
      (\<lambda>r. \<upharpoonleft>snat.assn n r)"
    unfolding snat.assn_def snat_snat_downcast_def
    apply vcg'
    apply (clarsimp simp: snat_invar_def max_snat_def)
    by (metis One_nat_def le_def msb_unat_big snat_eq_unat(1) snat_in_bounds_aux ucast_nat_def unat_of_nat_len)

   lemma unat_unat_upcast_rule[vcg_rules]:
    "llvm_htriple 
      ($$ ''zext'' 1 ** \<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>unat.assn n (ni::'small::len word)) 
      (unat_unat_upcast TYPE('big::len) ni) 
      (\<lambda>r. \<upharpoonleft>unat.assn n r)"
    unfolding unat.assn_def snat.assn_def unat_unat_upcast_def
    apply vcg'
    apply (auto simp: snat_invar_def snat_eq_unat(2) unat_ucast_upcast)
    done

  lemma unat_unat_downcast_rule[vcg_rules]:
    "llvm_htriple 
      ($$ ''trunc'' 1 **\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>unat.assn n (ni::'big::len word) ** \<up>(n<max_unat LENGTH('small))) 
      (unat_unat_downcast TYPE('small::len) ni) 
      (\<lambda>r. \<upharpoonleft>unat.assn n r)"
    unfolding unat.assn_def unat.assn_def unat_unat_downcast_def
    apply vcg'
    apply (auto simp: snat_invar_def snat_eq_unat(2) max_unat_def)
    by (metis ucast_nat_def unat_of_nat_eq)
    
  lemma unat_snat_conv_rule[vcg_rules]: 
    "llvm_htriple (\<upharpoonleft>unat.assn x (xi::'l::len2 word) ** \<up>(x<max_snat LENGTH('l))) (unat_snat_conv xi) (\<lambda>r. \<upharpoonleft>snat.assn x r)"
    unfolding unat_snat_conv_def unat.assn_def snat.assn_def
    apply vcg'
    by (force simp: max_snat_def snat_invar_alt snat_eq_unat(1))
  
  
    
  lemma snat_unat_conv_rule[vcg_rules]: 
    "llvm_htriple (\<upharpoonleft>snat.assn x (xi::'l::len2 word)) (snat_unat_conv xi) (\<lambda>r. \<upharpoonleft>unat.assn x r)"
    unfolding snat_unat_conv_def unat.assn_def snat.assn_def
    apply vcg'
    by (force simp: max_snat_def snat_invar_alt snat_eq_unat(1))
    
    
end

subsection \<open>Pointers\<close>

context begin
  interpretation llvm_prim_arith_setup .
    
  lemma ptrcmp_eq_rule[vcg_rules]: "llvm_htriple ($$''ptrcmp_eq'' 1) (ll_ptrcmp_eq a b) (\<lambda>r. \<upharpoonleft>bool.assn (a=b) r)"
    unfolding bool.assn_def
    by vcg

  lemma ptrcmp_ne_rule[vcg_rules]: "llvm_htriple ($$''ptrcmp_ne'' 1) (ll_ptrcmp_ne a b) (\<lambda>r. \<upharpoonleft>bool.assn (a\<noteq>b) r)"
    unfolding bool.assn_def
    by vcg

end


end
