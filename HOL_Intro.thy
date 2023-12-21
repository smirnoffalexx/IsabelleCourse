theory HOL_Intro 
  imports Main 
begin

section \<open>HOL\<close>

subsection Epsilon

text\<open>Epsilon\<close>

lemma "(\<exists>x. P x) = P (SOME x. P x)"
apply (rule iffI)
 apply (erule exE) thm someI
 apply (rule_tac x=x in someI)
   apply assumption thm exI
  thm exI
apply (rule_tac x="SOME x. P x" in exI)
apply assumption
done 

text\<open>Derive the axiom of choice from the SOME operator (using the rule someI), i.e.
using only the rules: allI, allE, exI, exE and someI; with only the
proof methods: rule, erule, rule_tac, erule_tac and assumption, prove:\<close>

lemma choice:
  "\<forall>x. \<exists>y. R x y \<Longrightarrow> \<exists>f. \<forall>x. R x (f x)"
  apply (rule exI)
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply (erule exE)
  thm someI
  apply (erule someI)
  done

subsection HOL

text \<open>You can find definition of HOL at $ISABELLE_HOME/src/HOL/HOL.thy\<close>

text\<open>we want to show "\<lbrakk> P \<longrightarrow> Q; P; Q \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"\<close>
lemma impE:
  assumes PQ: "P \<longrightarrow> Q"
  assumes P: "P"
  assumes QR: "Q \<Longrightarrow> R"
  shows "R"
(*  apply (insert PQ)
  apply (insert P)
apply (insert QR) *)
  apply (rule QR)
  apply (insert PQ) thm mp
  apply (drule mp)
   apply (rule P)
  apply assumption
  done

section \<open>Simplification\<close>

text \<open>
Lists:
  @{term "[]"}       empty list
  @{term "x#xs"}     cons (list with head x and tail xs)
  @{term "xs @ ys"}  append xs and ys

datatype 'a list = Nil | Cons 'a ('a list)
\<close>

print_simpset

lemma "ys @ [] = []"
  apply simp
  oops

definition
  a :: "nat list" where
  "a \<equiv> []"

definition
  b :: "nat list" where
  "b \<equiv> []"

text \<open>simp add, rewriting with definitions\<close>
lemma n[simp]: "xs @ a = xs" 
  (*apply simp *)
  apply (simp add: a_def)
  done

text \<open>simp only\<close>
lemma "xs @ a @ a @ a = xs"
  thm append_Nil2
  apply (simp only: a_def append_Nil2) thm a_def append_Nil2
  done

lemma ab [simp]: "a = b" using [[simp_trace]] by (simp only: a_def b_def)
lemma ba [simp]: "b = a" using [[simp_trace]] by simp

text \<open>simp del, termination\<close>
lemma "a = []"
  (* apply (simp add: a_def) *)
  (*   does not terminate *)
  apply (simp add: a_def del: ab)
  done


text\<open>Simplification in assumption:\<close>
lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
  apply simp
  done

end