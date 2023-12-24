theory UnificationAndRules
  imports Main
begin

section "Types and Terms in Isabelle"

term "True"
term "x"
term "x :: int \<Rightarrow> int"
term "{0} :: nat set"
term "x :: int set"
term "{x} :: 'a set"

datatype my_nat = Z | S my_nat

text \<open>
  Turn on displaying typeclass information
\<close>
thm order.refl
declare [[show_sorts]]
term "x::'a::order"

thm order.refl
declare [[show_sorts=false]]

text \<open>
 Isabelle has free variables (eg @{term x}),bound variables (eg @{term "\<lambda>n. n"}) and constants (eg @{term Suc}).
 Only schematic variables can be instantiated.
 Free converted into schematic after proof is finished.
\<close>

thm conjI
thm conjI [where ?P = "x" and ?Q = "y"]

section "Higher Order Unification"

text  \<open>
  Unify schematic ?t with @{term y}
\<close>

thm refl
lemma "y = y"
  apply(rule refl)
  done

thm add.commute
text \<open>
  Unify schematics ?a and ?b with @{term x} and @{term y} respectively.
\<close>

lemma "(x::nat) + y = y + x"
  apply(rule add.commute)
  done


text \<open>
 \<open>schematic_goal command used to state lemmas that involve schematic variables which may be
  instantiated during their proofs. Used quite rarely.\<close>
\<close>

thm TrueI
text \<open>
  Unify schematic ?P with @{term "(\<lambda>x. True)"}
\<close>


schematic_goal mylemma: "?P x" 
  apply(rule TrueI) (* instantiate ?P to be \<lambda>x. True *)
  (* therefore your statement is ((\<lambda>x. True) x) which reduced to True*)
  done

thm mylemma

lemma "P x"
  oops

text \<open>
  Note that the theorem @{thm mylemma} contains just what was proved (namely the proposition
  @{prop True}) not the more general result as originally stated (which isn't true for all ?P,
  as consider if ?P were instantiated with @{term "\<lambda>x. False"}.
\<close>

section \<open>Propositional logic\<close>

subsection \<open>Basic rules\<close>

text \<open>\<open>\<and>\<close> \<close>
thm conjI 
thm conjE 
thm conjunct1 conjunct2

text \<open>\<open>\<or>\<close> \<close>
thm disjI1 
thm disjI2 
thm disjE
thm disjCI

text \<open>\<open> \<longrightarrow>\<close> \<close>
thm impI impE

subsection\<open>Examples\<close>

text\<open>a simple backward step:\<close>
lemma "A \<and> B" thm conjI
  apply(rule conjI)
  oops

text\<open>a simple backward proof:\<close>
lemma "B \<and> A \<longrightarrow> A \<and> B" 
  apply (rule impI) thm impI
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done


lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply (rule impI) thm disjE
  apply (erule disjE)
   apply (rule disjI2) 
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

lemma "\<lbrakk> B \<longrightarrow> C; A \<longrightarrow> B \<rbrakk> \<Longrightarrow> A \<longrightarrow> C"
  apply (rule impI)
  apply (erule impE) thm impE
   apply (erule impE)
    apply assumption
   apply assumption
  apply assumption
  done

thm notI notE 

lemma "\<not>A \<or> \<not>B \<Longrightarrow> \<not>(A \<and> B)"
  apply (rule notI)
  apply (erule disjE)
   apply (erule conjE) thm notE
   apply (erule notE)
   apply assumption
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done


text \<open>Case distinctions.
Isabelle can do case distinctions on arbitrary terms\<close>

lemma "P \<or> \<not>P"
  apply (case_tac "P")
   apply (rule disjI1)
   apply (assumption)
   apply (rule disjI2)
apply (assumption)
  done

thm FalseE

lemma "(\<not>P \<longrightarrow> False) \<longrightarrow> P"
  apply (rule impI)
  apply (case_tac P)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule FalseE)
  done

text\<open>Explicit backtracking:\<close>

lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
  apply(erule conjE)
  back
  apply(assumption)
  done

text\<open>Implicit backtracking: chaining with ,\<close>

lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
  (* by (erule conjE) *)
  apply (erule conjE, assumption)
  done

text\<open>OR: use \<open>rule_tac or erule_tac\<close> to instantiate the schematic variables of the rule\<close>

lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
  apply (erule_tac ?P=A and ?Q=B in conjE)
  apply assumption
  done

text \<open>= (iff)\<close>
thm iffI
thm iffE
thm iffD1
thm iffD2

lemma "A \<longrightarrow> B = (B \<or> \<not> A)"
  apply (rule impI)
  apply (rule iffI)
   apply (case_tac A)
    apply (rule disjI1)
   apply (assumption)
   apply (rule disjI2)
   apply (assumption)
  apply (erule disjE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

\<comment> \<open>more rules\<close>
text\<open>\<open>\<longrightarrow>\<close>\<close>
thm mp

text \<open>\<open>\<not>\<close>\<close>
thm notI
thm notE

text \<open>True \<open>&\<close> False\<close>
thm TrueI
thm TrueE
thm FalseE

text \<open>Equality\<close>
thm refl
thm sym
thm trans
thm subst

text \<open>classical (contradictions)\<close>
thm classical
thm ccontr
thm excluded_middle

text\<open>classical propositional logic:\<close>
lemma Peirce: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI) thm classical
  apply (rule classical)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
   apply assumption
  apply assumption
  done

text \<open>defer and prefer\<close>
lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)
  prefer 2
  defer
  oops

text \<open>Example\<close>
lemma "A \<longrightarrow> (B \<or> C) \<longrightarrow> (\<not> A \<or> \<not> B) \<longrightarrow> C"
  apply (rule impI)+
  apply (erule disjE)
   defer apply assumption
  apply (erule disjE)
   apply (erule notE)
   apply assumption
   apply (erule notE)
  by assumption

text \<open>Exercises\<close>

lemma "A \<and> B \<longrightarrow> A \<longrightarrow> B"
  oops

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  oops

lemma"((A \<longrightarrow> B) \<and> (B \<longrightarrow> A)) = (A = B)"
  oops 

lemma "(A \<longrightarrow> (B \<and> C)) \<longrightarrow> (A \<longrightarrow> C)"
  oops

end