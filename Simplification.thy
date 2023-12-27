theory Simplification
  imports Main
begin

text \<open>\<open>Given the simplification rules:
0 + n = n                   (1)
Suc m + n = Suc (m + n)     (2)
(Suc m \<le> Suc n) = (m \<le> n)  (3)
(0 \<le> m) = True             (4)

Then 0 + Suc 0 \<le> Suc 0 + x is simplified to True as follows:

(0 + Suc 0 \<le>  Suc 0 + x)   (1)
(Suc 0 \<le> Suc 0 + x)       (2)
(Suc 0 \<le> Suc (0 + x))     (3)
(0 \<le> 0 + x)               (4)
True\<close>
\<close>

text \<open>Implicit backtracking\<close>
lemma "\<lbrakk>P \<and> Q; R \<and> S\<rbrakk> \<Longrightarrow> S"
  (* doesn't work -- picks the wrong assumption
  apply(erule conjE)
  apply assumption  *)
  apply (erule conjE, assumption)
  done

lemma "\<lbrakk>P \<and> Q; R \<and> S\<rbrakk> \<Longrightarrow> S"
  text \<open>do (n) assumption steps\<close>  
  apply (erule (1) conjE)
  done

lemma "\<lbrakk>P \<and> Q; R \<and> S\<rbrakk> \<Longrightarrow> S"
text \<open>'by' does extra assumption steps implicitly\<close>
  by (erule conjE)

text \<open>More automation\<close>

text \<open>clarsimp: repeated clarify and simp\<close>
lemma "ys = []  \<Longrightarrow> \<forall>xs. xs @ ys = []"
  apply clarsimp
  oops

text \<open>auto: simplification, classical reasoning, more\<close>
text \<open>Method ``auto'' can be modified almost like ``simp'':
  instead of ``add'' use ``simp add''.\<close>
lemma "(\<exists>u::nat. x = y + u) \<longrightarrow> a * (b + c) + y \<le> x + a * b + a * c" 
  thm add_mult_distrib2
  apply (auto simp add: add_mult_distrib2)
  done

text \<open>limit auto (and any other tactic) to first [n] goals\<close>
lemma "(True \<and> True)"
  apply (rule conjI)
   apply (auto)[1]
  apply (rule TrueI)
  done

text \<open>fastforce method\<close>
definition sq :: "nat \<Rightarrow> nat" where
  "sq n = n*n"

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n+n"
  by (fastforce simp add: sq_def)


text \<open>Simplification with assumptions, more control:\<close>

lemma "\<forall>x. f x = g x \<and> g x = f x \<Longrightarrow> f [] = f [] @ []"
  text \<open>would diverge:\<close>
  (*
  apply(simp)
  *)
  apply (simp (no_asm_use))
  done

text \<open>let expressions\<close>
thm Let_def
term "let a = f x in g a"

lemma "let a = f x in g a = x"
  apply (simp)
  oops

text \<open>Splitting if: automatic in conclusion\<close>

lemma "(A \<and> B) = (if A then B else False)"
  by simp

text \<open>Splitting manually\<close>

thm list.split

lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
  by (simp split: list.split)

text \<open>Splitting if: manual in assumptions\<close>
thm if_splits
thm if_split_asm

lemma "\<lbrakk> (if x then A else B) = z; Q \<rbrakk> \<Longrightarrow> P"
   (*apply (simp  split: if_splits)*) 
   apply (simp split: if_split_asm)
  oops

lemma " ((if x then A else B) = z) \<longrightarrow> (z = A \<or> z = B)"
  apply (rule impI)
  apply (simp split:if_splits)
done

text \<open>Congruence rules\<close>
thm conj_cong

lemma "A \<and> (A \<longrightarrow> B)"
  apply (simp cong: conj_cong)
  oops

thm if_cong

lemma "\<lbrakk> (if x then x \<longrightarrow> z else B) = z; Q \<rbrakk> \<Longrightarrow> P"
  apply (simp cong: if_cong)
  oops

thm if_weak_cong

text \<open>Term Rewriting Confluence\<close>

thm add_ac
thm mult_ac

lemmas all_ac = add_ac mult_ac
print_theorems

lemma
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<odot>" 70)
  assumes A: "\<And>x y z. (x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  assumes C: "\<And>x y. x \<odot> y = y \<odot> x"
  assumes AC: "\<And>x y z. x \<odot> (y \<odot> z) = y \<odot> (x \<odot> z)"
  shows "(z \<odot> x) \<odot> (y \<odot> v) = t"
  apply (simp only: C)
  apply (simp only: A C)
  text \<open>No confluence. We want \<open>v \<odot> (x \<odot> (y \<odot> z)) but got v \<odot> (y \<odot> (x \<odot> z))\<close>\<close>
  apply (simp only: AC)
  oops

text \<open>when all else fails: tracing the simplifier

typing
  declare \<open>[[simp_trace]]\<close>        turns tracing on,
  declare \<open>[[simp_trace=false]]\<close>  turns tracing off
(within a proof, write \<open>'using'\<close> rather than \<open>'declare'\<close>)
\<close>

declare [[simp_trace]]
lemma "A \<and> (A \<longrightarrow> B)"
   apply (simp cong: conj_cong)
  oops
declare [[simp_trace=false]]


lemma "A \<and> (A \<longrightarrow> B)"
  using [[simp_trace]] apply (simp cong: conj_cong)
  oops

text \<open>Single stepping: subst\<close>

thm add.commute
thm add.assoc
declare add.assoc [simp]
thm add.assoc [symmetric]

lemma "a + b = x + ((y::nat) + z)"
thm add.assoc[symmetric]
  apply (simp  add: add.assoc [symmetric] del: add.assoc)
thm add.commute
  apply (subst add.commute [where a=a and b = b])
  oops

end