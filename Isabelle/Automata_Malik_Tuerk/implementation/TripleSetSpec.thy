section "Interface for sets of triples"
theory TripleSetSpec
imports Main   "../../Collections/Refine_Dflt"
  "../../Collections/ICF/CollectionsV1"

begin
  type_synonym ('A,'B,'C,'T) triple_set_\<alpha> = "'T \<Rightarrow> ('A * 'B * 'C) set"
  locale triple_set =
    fixes \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes invar :: "'T \<Rightarrow> bool"

  locale finite_triple_set = triple_set +
    assumes finite[simp, intro!]: "invar t \<Longrightarrow> finite (\<alpha> t)"

  locale triple_set_copy = triple_set \<alpha>1 invar1 + triple_set \<alpha>2 invar2
  for \<alpha>1 :: "'T1 \<Rightarrow> ('A * 'B * 'C) set" and invar1
  and \<alpha>2 :: "'T2 \<Rightarrow> ('A * 'B * 'C) set" and invar2
  +
  fixes copy :: "'T1 \<Rightarrow> 'T2"
  assumes copy_correct: 
    "invar1 t1 \<Longrightarrow> \<alpha>2 (copy t1) = \<alpha>1 t1"
    "invar1 t1 \<Longrightarrow> invar2 (copy t1)"

  type_synonym ('A,'B,'C,'T) triple_set_empty  = "unit \<Rightarrow> 'T"
  locale triple_set_empty = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes empty :: "unit \<Rightarrow> 'T"
    assumes triple_set_empty_correct:
      "\<alpha> (empty ()) = {}"
      "invar (empty ())"

  type_synonym ('A,'B,'C,'T) triple_set_memb = "'T \<Rightarrow> 'A \<Rightarrow> 'B \<Rightarrow> 'C \<Rightarrow> bool"
  locale triple_set_memb = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes memb :: "('A,'B,'C,'T) triple_set_memb"
    assumes triple_set_memb_correct:
      "invar t \<Longrightarrow> (memb t a b c) \<longleftrightarrow> (a, b, c) \<in> (\<alpha> t)"

  type_synonym ('A,'B,'C,'T) triple_set_add = "'A \<Rightarrow>'B \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_add = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes add :: "'A \<Rightarrow> 'B \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_add_correct:
      "invar t \<Longrightarrow> invar (add a b c t)"
      "invar t \<Longrightarrow> \<alpha> (add a b c t) = insert (a, b, c) (\<alpha> t)"

  type_synonym ('A,'B,'C,'T) triple_set_add_Al = "'A list \<Rightarrow> 'B \<Rightarrow>'C \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_add_Al = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes add_Al :: "'A list \<Rightarrow> 'B \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_add_Al_correct:
      "invar t \<Longrightarrow> invar (add_Al as b c t)"
      "invar t \<Longrightarrow> \<alpha> (add_Al as b c t) = {(a, b, c) | a. a \<in> set as} \<union> (\<alpha> t)"

  type_synonym ('A,'B,'C,'T) triple_set_add_Bl = "'A \<Rightarrow>'B list \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_add_Bl = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes add_Bl :: "'A \<Rightarrow> 'B list \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_add_Bl_correct:
      "invar t \<Longrightarrow> invar (add_Bl a bs c t)"
      "invar t \<Longrightarrow> \<alpha> (add_Bl a bs c t) = {(a, b, c) | b. b \<in> set bs} \<union> (\<alpha> t)"

  type_synonym ('A,'B,'C,'T) triple_set_add_Cl = "'A \<Rightarrow>'B \<Rightarrow> 'C list \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_add_Cl = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes add_Cl :: "'A \<Rightarrow> 'B \<Rightarrow> 'C list \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_add_Cl_correct:
      "invar t \<Longrightarrow> invar (add_Cl a b cs t)"
      "invar t \<Longrightarrow> \<alpha> (add_Cl a b cs t) = {(a, b, c) | c. c \<in> set cs} \<union> (\<alpha> t)"

  type_synonym ('A_set,'B,'C,'T) triple_set_add_As = "'A_set \<Rightarrow> 'B \<Rightarrow>'C \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_add_As = triple_set \<alpha> invar + set s_\<alpha> s_invar 
    for s_\<alpha> :: "'A_set \<Rightarrow> 'A set" and \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>" and
        s_invar invar  +
    fixes add_As :: "'A_set \<Rightarrow> 'B \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_add_As_correct:
      "s_invar as \<Longrightarrow> invar t \<Longrightarrow> invar (add_As as b c t)"
      "s_invar as \<Longrightarrow> invar t \<Longrightarrow> 
       \<alpha> (add_As as b c t) = {(a, b, c) | a. a \<in> s_\<alpha> as} \<union> (\<alpha> t)"

  type_synonym ('A,'B_set,'C,'T) triple_set_add_Bs = "'A \<Rightarrow> 'B_set \<Rightarrow>'C \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_add_Bs = triple_set \<alpha> invar + set s_\<alpha> s_invar 
    for s_\<alpha> :: "'B_set \<Rightarrow> 'B set" and \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>" and
        s_invar invar  +
    fixes add_Bs :: "'A \<Rightarrow> 'B_set \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_add_Bs_correct:
      "s_invar bs \<Longrightarrow> invar t \<Longrightarrow> invar (add_Bs a bs c t)"
      "s_invar bs \<Longrightarrow> invar t \<Longrightarrow> 
       \<alpha> (add_Bs a bs c t) = {(a, b, c) | b. b \<in> s_\<alpha> bs} \<union> (\<alpha> t)"

  type_synonym ('A,'B,'C_set,'T) triple_set_add_Cs = "'A \<Rightarrow> 'B \<Rightarrow>'C_set \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_add_Cs = triple_set \<alpha> invar + set s_\<alpha> s_invar 
    for s_\<alpha> :: "'C_set \<Rightarrow> 'C set" and s_invar and \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>" and invar  +
    fixes add_Cs :: "'A \<Rightarrow> 'B \<Rightarrow> 'C_set \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_add_Cs_correct:
      "s_invar cs \<Longrightarrow> invar t \<Longrightarrow> invar (add_Cs a b cs t)"
      "s_invar cs \<Longrightarrow> invar t \<Longrightarrow> 
       \<alpha> (add_Cs a b cs t) = {(a, b, c) | c. c \<in> s_\<alpha> cs} \<union> (\<alpha> t)"

  type_synonym ('A,'B,'C_set,'T) triple_set_set_Cs = "'A \<Rightarrow> 'B \<Rightarrow>'C_set \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_set_Cs = triple_set \<alpha> invar + set s_\<alpha> s_invar 
    for s_\<alpha> :: "'C_set \<Rightarrow> 'C set" and s_invar and \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>" and invar  +
    fixes add_Cs :: "'A \<Rightarrow> 'B \<Rightarrow> 'C_set \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_set_Cs_correct:
      "s_invar cs \<Longrightarrow> invar t \<Longrightarrow> (\<And>c. (a, b, c) \<notin> (\<alpha> t)) \<Longrightarrow> invar (add_Cs a b cs t)"
      "s_invar cs \<Longrightarrow> invar t \<Longrightarrow> (\<And>c. (a, b, c) \<notin> (\<alpha> t)) \<Longrightarrow>
       \<alpha> (add_Cs a b cs t) = {(a, b, c) | c. c \<in> s_\<alpha> cs} \<union> (\<alpha> t)"

  type_synonym ('A,'B,'C,'T) triple_set_delete = "'A \<Rightarrow> 'B \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_delete = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes delete :: "'A \<Rightarrow> 'B \<Rightarrow> 'C \<Rightarrow> 'T \<Rightarrow> 'T"
    assumes triple_set_delete_correct:
      "invar t \<Longrightarrow> invar (delete a b c t)"
      "invar t \<Longrightarrow> \<alpha> (delete a b c t) = (\<alpha> t) - {(a, b, c)}"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_it = "'T \<Rightarrow> (('A\<times>'B\<times>'C),'\<sigma>) set_iterator"
  locale triple_set_iterator = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes it :: "('A,'B,'C,'\<sigma>,'T) triple_set_it"
    assumes triple_set_it_correct:
      "invar t \<Longrightarrow> set_iterator (it t) (\<alpha> t)"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_filter_it = "('A \<Rightarrow> bool) \<Rightarrow> ('B \<Rightarrow> bool) \<Rightarrow> ('C \<Rightarrow> bool) \<Rightarrow>
        (('A \<times> 'B \<times> 'C) \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> (('A\<times>'B\<times>'C),'\<sigma>) set_iterator"
  locale triple_set_filter_it = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes filter_it :: "('A,'B,'C,'\<sigma>,'T) triple_set_filter_it"
    assumes triple_set_filter_it_correct :
      "invar t \<Longrightarrow> set_iterator (filter_it P_a P_b P_c P t)
         {(a, b, c) . (a, b, c) \<in> (\<alpha> t) \<and> P_a a \<and> P_b b \<and> P_c c \<and> P (a, b, c)}"

  type_synonym ('A,'B,'C,'T) triple_set_filter = "('A \<Rightarrow> bool) \<Rightarrow> ('B \<Rightarrow> bool) \<Rightarrow> ('C \<Rightarrow> bool) \<Rightarrow>
        (('A \<times> 'B \<times> 'C) \<Rightarrow> bool) \<Rightarrow> 'T \<Rightarrow> 'T"
  locale triple_set_filter = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>" 
    fixes filter :: "('A,'B,'C,'T) triple_set_filter"
    assumes triple_set_filter_correct :
      "invar t \<Longrightarrow> invar (filter P_a P_b P_c P t)"
      "invar t \<Longrightarrow> \<alpha>(filter P_a P_b P_c P t) =
             {(a, b, c). (a, b, c) \<in> (\<alpha> t) \<and> P_a a \<and> 
               P_b b \<and> P_c c \<and> P (a, b, c)}"

  type_synonym ('A1,'B1,'C1,'T1,'A2,'B2,'C2,'T2) triple_set_image_filter = "
        (('A1 \<times> 'B1 \<times> 'C1) \<Rightarrow> ('A2 \<times> 'B2 \<times> 'C2)) \<Rightarrow>
        ('A1 \<Rightarrow> bool) \<Rightarrow> ('B1 \<Rightarrow> bool) \<Rightarrow> ('C1 \<Rightarrow> bool) \<Rightarrow>
        (('A1 \<times> 'B1 \<times> 'C1) \<Rightarrow> bool) \<Rightarrow> 'T1 \<Rightarrow> 'T2"
  locale triple_set_image_filter = triple_set \<alpha>1 invar1 + triple_set \<alpha>2 invar2 
    for \<alpha>1 :: "('A1,'B1,'C1,'T1) triple_set_\<alpha>" and invar1 and
        \<alpha>2 :: "('A2,'B2,'C2,'T2) triple_set_\<alpha>" and invar2 +
    fixes image_image_filter :: "('A1,'B1,'C1,'T1,'A2,'B2,'C2,'T2) triple_set_image_filter"
    assumes triple_set_image_filter_correct :
      "invar1 t \<Longrightarrow> invar2 (image_image_filter f P_a P_b P_c P t)"
      "invar1 t \<Longrightarrow> \<alpha>2(image_image_filter f P_a P_b P_c P t) =
         f ` {(a, b, c). (a, b, c) \<in> (\<alpha>1 t) \<and> P_a a \<and> 
               P_b b \<and> P_c c \<and> P (a, b, c)}"

  type_synonym ('A1,'B1,'C1,'T1,'A2,'B2,'C2,'T2) triple_set_image = "
        (('A1 \<times> 'B1 \<times> 'C1) \<Rightarrow> ('A2 \<times> 'B2 \<times> 'C2)) \<Rightarrow> 'T1 \<Rightarrow> 'T2"
  locale triple_set_image = triple_set \<alpha>1 invar1 + triple_set \<alpha>2 invar2 
    for \<alpha>1 :: "('A1,'B1,'C1,'T1) triple_set_\<alpha>" and invar1 and
        \<alpha>2 :: "('A2,'B2,'C2,'T2) triple_set_\<alpha>" and invar2 +
    fixes image :: "('A1,'B1,'C1,'T1,'A2,'B2,'C2,'T2) triple_set_image"
    assumes triple_set_image_correct :
      "invar1 t \<Longrightarrow> invar2 (image f t)"
      "invar1 t \<Longrightarrow> \<alpha>2(image f t) = f ` (\<alpha>1 t)"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_BC_it = 
    "'T \<Rightarrow> 'A \<Rightarrow> ('B\<times>'C,'\<sigma>) set_iterator"
  locale triple_set_BC_it = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes BC_it :: "('A,'B,'C,'\<sigma>,'T) triple_set_BC_it"
    assumes triple_set_BC_it_correct:
      "invar t \<Longrightarrow> set_iterator (BC_it t a) {(b, c) . (a, b, c) \<in> (\<alpha> t)}"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_AC_it = 
    "'T \<Rightarrow> 'B \<Rightarrow> ('A\<times>'C,'\<sigma>) set_iterator"
  locale triple_set_AC_it = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes AC_it :: "('A,'B,'C,'\<sigma>,'T) triple_set_AC_it"
    assumes triple_set_AC_it_correct:
      "invar t \<Longrightarrow> set_iterator (AC_it t b) {(a, c) . (a, b, c) \<in> (\<alpha> t)}"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_AB_it = 
    "'T \<Rightarrow> 'C \<Rightarrow> ('A\<times>'B,'\<sigma>) set_iterator"
  locale triple_set_AB_it = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes AB_it :: "('A,'B,'C,'\<sigma>,'T) triple_set_AB_it"
    assumes triple_set_AB_it_correct:
      "invar t \<Longrightarrow> set_iterator (AB_it t c) {(a, b) . (a, b, c) \<in> (\<alpha> t)}"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_A_it = 
    "'T \<Rightarrow> 'B \<Rightarrow> 'C \<Rightarrow> ('A,'\<sigma>) set_iterator"
  locale triple_set_A_it = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes A_it :: "('A,'B,'C,'\<sigma>,'T) triple_set_A_it"
    assumes triple_set_A_it_correct:
      "invar t \<Longrightarrow> set_iterator (A_it t b c) {a . (a, b, c) \<in> (\<alpha> t)}"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_B_it = 
    "'T \<Rightarrow> 'A \<Rightarrow> 'C \<Rightarrow> ('B,'\<sigma>) set_iterator"
  locale triple_set_B_it = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes B_it :: "('A,'B,'C,'\<sigma>,'T) triple_set_B_it"
    assumes triple_set_B_it_correct:
      "invar t \<Longrightarrow> set_iterator (B_it t a c) {b . (a, b, c) \<in> (\<alpha> t)}"

  type_synonym ('A,'B,'C,'\<sigma>,'T) triple_set_C_it = 
    "'T \<Rightarrow> 'A \<Rightarrow> 'B \<Rightarrow> ('C,'\<sigma>) set_iterator"
  locale triple_set_C_it = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes C_it :: "('A,'B,'C,'\<sigma>,'T) triple_set_C_it"
    assumes triple_set_C_it_correct:
      "invar t \<Longrightarrow> set_iterator (C_it t a b) {c . (a, b, c) \<in> (\<alpha> t)}"

  type_synonym ('A,'B,'C,'T) triple_set_from_list = "('A \<times> 'B \<times> 'C) list \<Rightarrow> 'T"
  locale triple_set_from_list = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes from_list :: "('A,'B,'C,'T) triple_set_from_list"
    assumes triple_set_from_list_correct:
      "invar (from_list l)"
      "\<alpha> (from_list l) = set l"
  
  type_synonym ('A,'B,'C,'T) triple_set_to_list = "'T \<Rightarrow> ('A \<times> 'B \<times> 'C) list"
  locale triple_set_to_list = triple_set +
    constrains \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    fixes to_list :: "('A,'B,'C,'T) triple_set_to_list"
    assumes triple_set_to_list_correct:
      "invar l \<Longrightarrow> set (to_list l) = \<alpha> l"
      "invar l \<Longrightarrow> distinct (to_list l)"

  section \<open> Record Based Interface \<close>
  record ('A,'B,'C,'T) triple_set_ops =
    triple_set_op_\<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    triple_set_op_invar :: "'T \<Rightarrow> bool"
    triple_set_op_empty :: "('A,'B,'C,'T) triple_set_empty"
    triple_set_op_memb :: "('A,'B,'C,'T) triple_set_memb"
    triple_set_op_add :: "('A,'B,'C,'T) triple_set_add"
    triple_set_op_add_Al :: "('A,'B,'C,'T) triple_set_add_Al"
    triple_set_op_add_Bl :: "('A,'B,'C,'T) triple_set_add_Bl"
    triple_set_op_add_Cl :: "('A,'B,'C,'T) triple_set_add_Cl"
    triple_set_op_delete :: "('A,'B,'C,'T) triple_set_delete"
    triple_set_op_to_list :: "('A,'B,'C,'T) triple_set_to_list"
    triple_set_op_from_list :: "('A,'B,'C,'T) triple_set_from_list"
    triple_set_op_image_filter :: "('A,'B,'C,'T,'A,'B,'C,'T) triple_set_image_filter"
    triple_set_op_filter :: "('A,'B,'C,'T) triple_set_filter"
    triple_set_op_image :: "('A,'B,'C,'T,'A,'B,'C,'T) triple_set_image"

  locale StdTripleSetDefs =
    fixes ops :: "('A,'B,'C,'T,'m) triple_set_ops_scheme"
  begin
    abbreviation \<alpha> where "\<alpha> \<equiv> triple_set_op_\<alpha> ops"
    abbreviation invar where "invar \<equiv> triple_set_op_invar ops"
    abbreviation empty where "empty \<equiv> triple_set_op_empty ops"
    abbreviation memb where "memb \<equiv> triple_set_op_memb ops"
    abbreviation add where "add \<equiv> triple_set_op_add ops"
    abbreviation add_Al where "add_Al \<equiv> triple_set_op_add_Al ops"
    abbreviation add_Bl where "add_Bl \<equiv> triple_set_op_add_Bl ops"
    abbreviation add_Cl where "add_Cl \<equiv> triple_set_op_add_Cl ops"
    abbreviation delete where "delete \<equiv> triple_set_op_delete ops"
    abbreviation from_list where "from_list \<equiv> triple_set_op_from_list ops"
    abbreviation to_list where "to_list \<equiv> triple_set_op_to_list ops"
    abbreviation image_filter where "image_filter \<equiv> triple_set_op_image_filter ops"
    abbreviation filter where "filter \<equiv> triple_set_op_filter ops"
    abbreviation image where "image \<equiv> triple_set_op_image ops"
  end

  locale StdTripleSet = StdTripleSetDefs +
    finite_triple_set \<alpha> invar +
    triple_set_empty \<alpha> invar empty +
    triple_set_memb \<alpha> invar memb +
    triple_set_to_list \<alpha> invar to_list +
    triple_set_add \<alpha> invar add +
    triple_set_add_Al \<alpha> invar add_Al +
    triple_set_add_Bl \<alpha> invar add_Bl +
    triple_set_add_Cl \<alpha> invar add_Cl +
    triple_set_delete \<alpha> invar delete +
    triple_set_from_list \<alpha> invar from_list +
    triple_set_filter \<alpha> invar filter +
    triple_set_image_filter \<alpha> invar \<alpha> invar image_filter +
    triple_set_image \<alpha> invar \<alpha> invar image
  begin
    lemmas correct = triple_set_empty_correct  
       triple_set_to_list_correct triple_set_add_correct
       triple_set_add_Al_correct triple_set_add_Bl_correct triple_set_add_Cl_correct
       triple_set_delete_correct triple_set_memb_correct 
       triple_set_from_list_correct triple_set_image_filter_correct 
       triple_set_filter_correct triple_set_image_correct
  end

end
