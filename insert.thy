theory insert
  imports Main
begin

text \<open>Example. 
apply-style proof of correctness of the functional insertion sorting algorithm.\<close>

text \<open>Algorithm\<close>
fun insert :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "insert a [] = [a]" |
  "insert a (x#xs) =  (if a \<le> x then a#x#xs else x#insert a xs)"
  
fun insertion_sort :: "nat list \<Rightarrow> nat list" where
  "insertion_sort [] = []"  | 
  "insertion_sort (x#xs) = insert x (insertion_sort xs)"

thm insertion_sort.simps

text \<open>Tests: \<close>
value "insert 7 [4,6,78]"
value "insertion_sort [3,7,34,6,0,3,4]"
value "insertion_sort [1, 5, 0, 4, 2, 10, 7]"

text \<open>Specifying the correctness property\<close>

fun le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "le a [] = True"  | 
  "le a (x#xs) = (a\<le>x & le a xs)"

fun ord :: "nat list \<Rightarrow> bool" where
  "ord [] = True" | 
  "ord (x#xs) = (le x xs & ord xs)"

value "ord [1, 5, 0, 4, 2, 10, 7]"
value "ord [1, 7, 8, 19]"
value "ord [20, 1, 7, 8]"

text \<open>Property: \<open>ord (insertion_sort xs)\<close>\<close>

lemma sorted: "ord (insertion_sort xs)"
  apply (induct xs)
   apply simp
  apply (simp add: insertion_sort.cases)
  oops

lemma h1: "x\<le>y \<Longrightarrow> le y xs \<longrightarrow> le x xs"
  apply(induction xs)
  apply auto
  done

lemma h2:
 "le x (insert a xs) = (x \<le> a & le x xs)"
  apply (induction xs)
  apply auto
  done

thm iffD1

lemma in_ord [THEN iffD1, simp]: "ord xs = ord (insert x (xs))"
  apply (induct xs)
   apply simp+
  apply (simp add:h2)
  using h1 by blast

thm in_ord

lemma sorted: "ord (insertion_sort xs)"
  apply (induct xs)
  using [[simp_trace_new]]
  apply auto
  done

text \<open>Exercise. Transform this apply scripts to Isar proof.\<close>

end