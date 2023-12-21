theory Inductive
  imports Main
begin

section Inductive
subsection "Inductive definition of the even numbers"

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

thm ev0 evSS
thm ev.intros
thm ev.intros(1)
thm ev.intros(2)

print_theorems

text \<open>Using the introduction rules:\<close>

lemma "ev (Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)+
apply(rule ev0)
done

thm evSS[OF evSS[OF ev0]]

text \<open>A recursive definition of evenness:\<close>

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text \<open>A simple example of rule induction:\<close>

thm ev.induct
lemma "ev n \<Longrightarrow> evn n"
  apply(induction rule: ev.induct)
  apply(simp)
  apply(simp)
  done

text \<open>An induction on the computation of @{const evn}:\<close>

thm evn.induct
lemma "evn n \<Longrightarrow> ev n"
  apply(induction n  rule: evn.induct)
  apply (simp add: ev0)
  apply simp
  apply(simp add: evSS)
  done

text \<open>No problem with termination
because the premises are always smaller than the conclusion:\<close>

thm ev.intros
declare ev.intros[simp,intro]

text \<open>A shorter proof:\<close>

lemma "evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
  apply(simp_all)
  done

text \<open>The power of "arith":\<close>

lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
  apply(induction rule: ev.induct)
  apply(simp)
  apply arith
  done


subsection "Inductive definition of the reflexive transitive closure"

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

print_theorems
thm star.induct

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply assumption
  apply(rename_tac u x y)
  by (simp add: star.step)

end