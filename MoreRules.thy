theory MoreRules
  imports Main 
begin

section \<open>First Order Logic \<close>
text \<open>Quantifier reasoning\<close>

thm allI
thm allE
thm exI
thm exE

text \<open>Successful proofs\<close>

lemma "\<forall>a. \<exists>b. a = b"
  apply (rule allI)
  thm exI
  apply (rule_tac x="a" in exI)
  thm refl
apply (rule refl)
done

lemma "\<forall>a. \<exists>b. a = b"
apply (rule allI)
apply (rule exI)
apply (rule refl)
done


text \<open>An unsuccessful proof\<close>

lemma "\<exists>y. \<forall>x. x = y"
apply(rule exI)
apply(rule allI)
oops

text \<open>Intro and elim reasoning\<close>

lemma "\<exists>b. \<forall>a. P a b \<Longrightarrow> \<forall>a. \<exists>b. P a b"
(* the safe rules first: *)
apply (rule allI)
apply (erule exE)
(* then the unsafe ones: *)
  thm allE
  apply (erule_tac x="a" in allE)
  thm exI
apply (rule_tac x="b" in exI)
apply assumption
done

text \<open>What happens if an unsafe rule is tried too early\<close>

lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply(rule allI) thm exI
apply(rule exI)
apply(erule exE)
apply(erule_tac x="x" in allE)
  oops

text \<open>Instantiating allE and exI\<close>

lemma "\<forall>x. P x \<Longrightarrow> P 37"
  thm allE
apply (erule_tac x = "37" in allE)
apply assumption
done

lemma "\<exists>n. P (f n) \<Longrightarrow> \<exists>m. P m"
  apply(erule exE)
  thm exI
apply(rule_tac x = "f n" in exI)
apply assumption
done

text\<open>Instantiation removes ambiguity\<close>

lemma "\<lbrakk> A \<and> B; C \<and> D \<rbrakk> \<Longrightarrow> D"
  thm conjE
apply(erule_tac P = "C" and Q="D" in conjE)
(* apply (erule conjE) *)
apply assumption
done

text\<open>Renaming parameters\<close>

lemma "\<And>x y z. P x y z"
apply(rename_tac a B)
oops

lemma "\<forall>x. P x \<Longrightarrow> \<forall>x. \<forall>x. P x"
apply(rule allI)
apply(rule allI)
  apply(rename_tac y)
  thm allE
apply(erule_tac x=y in allE)
apply assumption
  done

text\<open>where and of attributes\<close>

thm conjI
thm conjI [of "A"]
thm conjI [of "A"  "B"]
thm conjI [where Q = "f x" and P = "y"]

lemma "\<lbrakk> A \<and> B; C \<and> D \<rbrakk> \<Longrightarrow> D"
  thm conjE
apply(erule conjE[where P = "C" and Q="D"])
(* apply (erule conjE) *)
apply assumption
done

text\<open>Forward reasoning: drule/frule\<close>

lemma "A \<and> B \<Longrightarrow> \<not> \<not> A"
  thm conjunct1
  thm conjunct2
  thm mp
apply (drule conjunct1)
  apply (rule notI)
  thm notE
apply (erule notE)
apply assumption
done


lemma "\<forall>x. P x \<Longrightarrow> P t \<and> P t'"
thm spec
apply (frule_tac x="t" in spec)
apply (drule_tac x="t'" in spec)
apply (rule conjI)
 apply assumption
apply assumption
done

text\<open>OF and THEN attributes\<close>

thm dvd_add dvd_refl
thm dvd_add [OF dvd_refl]
thm dvd_add [OF dvd_refl dvd_refl]

section \<open>Automation\<close>

lemma "\<forall>x y. P x y \<and> Q x y \<and> R x y"
apply (intro allI conjI)
  oops

lemma "\<forall>x y. P x y \<and> Q x y \<and> R x y"
  apply clarify
  apply safe
oops

lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply blast
done

lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply fast
  done

text\<open>More about automation\<close>
definition
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)"

thm xor_def

lemma xorI:
  "A \<or> B \<Longrightarrow> \<not> (A \<and> B) \<Longrightarrow> xor A B"
  apply (unfold xor_def)
  by blast

lemma xorE[elim!]:
  "\<lbrakk> xor A B; \<lbrakk>A; \<not>B\<rbrakk> \<Longrightarrow> R; \<lbrakk>\<not>A; B\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply (unfold xor_def)
  by blast

lemma "xor A A = False"
  apply (blast elim! : xorE)
  done

text \<open>Example\<close>

lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
  apply (rule iffI)
   apply (rule impI)
   apply (erule exE) 
   apply (erule_tac x= x in allE)
   apply (erule impE)
    apply assumption+
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   defer 
   apply assumption
  apply (rule_tac x=x in exI)
  apply assumption
  done

text \<open>Exercises\<close>
text \<open>Prove using the xor definition and 
the proof methods: \<open>rule, erule, rule_tac, erule_tac\<close> and assumption:\<close>
lemma "xor A B = xor B A"
  oops

lemma "((\<forall>x. P x ) \<and> (\<forall>x. Q x)) = (\<forall>x. (P x \<and> Q x))"
  oops
end