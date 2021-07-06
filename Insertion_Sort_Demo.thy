(*
Author: Wenda Li
University of Cambridge

This example is addapted from Tobias Nipkow's Insertion Sort 
in "HOL-Data_Structures.Sorting".
*)

theory Insertion_Sort_Demo imports
 "HOL-Data_Structures.Sorting"
begin

hide_const (open) insert sort sorted T_isort

section \<open>Implementation\<close>

fun insert :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  insert_base:   "insert x Nil = [x]" |
  insert_induct: "insert x (Cons y ys) =
      (if x \<le> y then Cons x (Cons y ys) 
                else Cons y (insert x ys))"

value "insert 3 Nil"   (*returns [3]*)
value "insert 2 [1,3]" (*returns [1,2,3]*)

fun sort :: "int list \<Rightarrow> int list" where
  sort_base:   "sort Nil = []" |
  sort_induct: "sort (Cons x xs) = insert x (sort xs)"

value "sort []"        (*returns []*)
value "sort [1]"       (*returns [1]*)
value "sort [2,3,1,4]" (*returns [1,2,3,4]*)

fun sorted :: "int list \<Rightarrow> bool" where
  sorted_base: "sorted Nil = True" |
  sorted_induct: "sorted (Cons x ys) 
          = ((\<forall>y \<in> set ys. x \<le> y) \<and> sorted ys)"

section "Functional Correctness"

lemma mset_insort: "mset (insert x xs) = {#x#} + mset xs"
  by (induction xs) auto

lemma mset_isort: "mset (sort xs) = mset xs"
  by (induction xs) (auto simp add: mset_insort)

lemma set_insort: "set (insert x xs) = {x} \<union> set xs"
  by(simp add: mset_insort flip: set_mset_mset)

(* (*More compact proof*)
lemma sorted_insort: "sorted (insert a xs) = sorted xs"
by(induction xs) (auto simp add: set_insort)

lemma sorted_isort: "sorted (sort xs)"
  by(induction xs) (auto simp: sorted_insort)
*)

(*For demonstration purposes, 
  I deleted those simplification rules*)
declare 
  insert.simps[simp del] 
  sort.simps[simp del] 
  sorted.simps[simp del]

lemma sorted_insert: "sorted (insert a xs) = sorted xs"
proof (induction xs)
  have "sorted (insert a []) = sorted [a]"
    using insert_base by simp
  also have "... = ((\<forall>y \<in> set []. a \<le> y) \<and> sorted [])"
    using sorted_induct by simp
  also have "... = (True \<and> sorted [])" by simp
  also have "... = sorted []" by simp
  finally show "sorted (insert a []) = sorted []" . 
next
  fix x xs 
  assume IH:"sorted (insert a xs) = sorted xs"
  let ?thesis = "sorted (insert a (Cons x xs)) 
      = sorted (Cons x xs)"
  have ?thesis if "a\<le>x"
  proof -
    have "sorted (insert a (Cons x xs))
            = sorted (Cons a (Cons x xs))"
      using \<open>a\<le>x\<close> insert_induct by simp
    also have "... = ((\<forall>y \<in> set (Cons x xs). a \<le> y) 
                      \<and> sorted (Cons x xs))"
      using sorted_induct by simp
    also have "... = (True \<and> sorted (Cons x xs))"
      using \<open>a\<le>x\<close> sorted_induct by auto 
    also have "... = sorted (Cons x xs)" by simp
    finally show ?thesis .
  qed
  moreover have ?thesis if "\<not> a\<le>x"
  proof -
    have "sorted (insert a (Cons x xs))
            = sorted (Cons x (insert a xs))"
      using \<open>\<not> a\<le>x\<close> insert_induct by simp
    also have "... = ((\<forall>y \<in> set (Cons a xs). x \<le> y) 
                      \<and> sorted (insert a xs))"
      using sorted_induct set_insort by simp
    also have "... = ((\<forall>y \<in> set (Cons a xs). x \<le> y) 
                      \<and> sorted xs)"
      using IH by simp
    also have "... = ((\<forall>y \<in> set xs. x \<le> y) \<and> sorted xs)"
      using \<open>\<not> a\<le>x\<close> by simp
    also have "... = sorted (Cons x xs)"
      using sorted_induct by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by auto
qed

lemma sorted_sort: "sorted (sort xs)"
proof (induction xs)
  have "sorted (sort Nil) = sorted Nil"
    using sort_base by simp
  also have "... = True" using sorted_base by simp
  finally show "sorted (sort Nil)" by simp
next
  fix x xs assume IH: "sorted (sort xs)"
  have "sorted (sort (Cons x xs)) 
                  = sorted (insert x (sort xs))"
    using sort_induct by simp
  also have "... = sorted (sort xs)" 
    using sorted_insert by simp
  also have "... = True"using IH by simp
  finally show "sorted (sort (Cons x xs))" by simp
qed

section "Time Complexity"

text \<open>We count the number of function calls.\<close>

fun T_insert :: "int \<Rightarrow> int list \<Rightarrow> nat" where
  "T_insert x Nil = 1" |
  "T_insert x (Cons y ys) =
    (if x \<le> y then 0 else T_insert x ys) + 1"

fun T_sort :: "int list \<Rightarrow> nat" where
  "T_sort Nil = 1" |
  "T_sort (Cons x xs) = T_sort xs 
                   + T_insert x (sort xs) + 1"

lemma T_insert_length: "T_insert x xs \<le> length xs + 1"
  by (induction xs)  auto

lemma length_insert: "length (insert x xs) = length xs + 1"
  by (induction xs)  (auto simp:insert.simps)

lemma length_sort: "length (sort xs) = length xs"
  by (induction xs) (auto simp: length_insert sort.simps)

lemma T_sort_length:
  "T_sort xs \<le> (length xs + 1) ^ 2"
proof(induction xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have "T_sort (x#xs) = T_sort xs + T_insert x (sort xs) + 1" by simp
  also have "\<dots> \<le> (length xs + 1) ^ 2 + T_insert x (sort xs) + 1"
    using Cons.IH by simp
  also have "\<dots> \<le> (length xs + 1) ^ 2 + length xs + 1 + 1"
    using T_insert_length[of x "sort xs"] by (simp add: length_sort)
  also have "\<dots> \<le> (length(x#xs) + 1) ^ 2"
    by (simp add: power2_eq_square)
  finally show ?case .
qed

end