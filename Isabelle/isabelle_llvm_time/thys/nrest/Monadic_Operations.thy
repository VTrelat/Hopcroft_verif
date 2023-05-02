theory Monadic_Operations
imports NREST_Backwards_Reasoning
begin


definition "mop_swap t = (\<lambda>(a,b). SPECT [ (b,a) \<mapsto> t (a,b)])"

  definition "mop_min t a b =SPECT [min a b \<mapsto> t (a,b)]"

type_synonym 'a mtx = "nat\<times>nat \<Rightarrow> 'a"

  definition "mop_matrix_get t (m::_ mtx) e = SPECT [m e \<mapsto> (t (m,e))]"
  definition "mop_matrix_set t (m::'b mtx) e v = SPECT [m(e:=v) \<mapsto> (t ((m,e),v))]"

definition op_mtx_new :: "'a mtx \<Rightarrow> 'a mtx" where [simp]: "op_mtx_new c \<equiv> c"
  definition [simp]: "op_amtx_new (N::nat) (M::nat) \<equiv> op_mtx_new"
    definition "mop_amtx_new N M t c =  SPECT [op_amtx_new N M c \<mapsto> t N M] "

definition "mop_set_pick_extract t S =
     do { ASSERT (S\<noteq>{});
        SPECT (emb (\<lambda>(x,C). x\<in>S \<and> C=S-{x}) (t S)) }"



  lemma  mop_set_pick_extract: "tt \<le> gwp (SPECT (emb (\<lambda>(x,C). x\<in>S \<and> C=S-{x}) (t S))) Q
        \<Longrightarrow> S \<noteq> {} \<Longrightarrow> tt \<le> gwp  (mop_set_pick_extract t S) Q"
    unfolding mop_set_pick_extract_def 
    apply(cases tt) 
    subgoal by simp
    by simp 


definition "mop_set_isempty t S  = SPECT (emb (\<lambda>b. b \<longleftrightarrow> S={}) (t S))"
lemma mop_set_isempty : "Some tt \<le> T_g Q  (SPECT (emb (\<lambda>b. b \<longleftrightarrow> S={}) (t S)))
           \<Longrightarrow>  Some tt \<le> T_g Q (mop_set_isempty t S)"
  unfolding mop_set_isempty_def by simp
   


definition "mop_map_lookup C m k = do {
        ASSERT (k\<in>dom m);
        SPECT [ the (m k) \<mapsto> C (m, k)]
      }"
definition "mop_append C x xs = SPECT [ xs @ [x] \<mapsto> C (x, xs)]"

definition "mop_empty_list t = SPECT [ [] \<mapsto> t ()]"
definition mop_set_member where "mop_set_member t x S = SPECT [ x \<in> S \<mapsto> t (x,S)]"
definition mop_set_insert where "mop_set_insert t x S = SPECT [ insert x S \<mapsto> t (x,S)]"
definition "mop_push_list t x xs = SPECT [ xs @ [x] \<mapsto> t (x,xs)]"


definition mop_set_empty where "mop_set_empty t = SPECT [ {} \<mapsto> t ()]"

lemma mop_set_empty : "Some t \<le> T_g Q  (SPECT [ {} \<mapsto> tt ()])
           \<Longrightarrow>  Some t \<le> T_g Q (mop_set_empty tt)"
  unfolding mop_set_empty_def by simp


  definition "mop_map_dom_member t m x = SPECT (emb (\<lambda>b. b \<longleftrightarrow> x\<in>dom m) (t (m,x)))"

  definition "mop_map_update t m k v = SPECT [ m(k \<mapsto> v) \<mapsto> t ((m,k),v)]"

end