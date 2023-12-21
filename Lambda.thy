section \<open>Lambda Сalculus\<close>

theory Lambda
  imports Main 
begin

text "lambda terms"

term "\<lambda>x. x + 3"

term "\<lambda>x a b. x + a + b + 3"

text "alpha-conversion"

thm refl

lemma "(\<lambda>x. x) = (\<lambda>y. y)"
  apply (rule refl)
  done


text "eta-conversion"

term "\<lambda>x. f x"


text "beta-reduction"

term "(\<lambda>x. x y) t"


text \<open>beta with renaming\<close>

term "(\<lambda>z. (\<lambda>x. f x z)) x"

text \<open>example\<close>
text 
\<open>((\<lambda> a. (\<lambda> b. b a) c) b) ((\<lambda> c. (c b)) (\<lambda> a. a)) = ((\<lambda> a. (\<lambda> b. b a) c) b) ((\<lambda> a. a) b) =
((\<lambda> a. (\<lambda> b. b a) c) b) b = 
((\<lambda> a. c a) b) b = c b b\<close>

text \<open>Isabelle performs this automatically:\<close>
term "((\<lambda> a. (\<lambda> b. b a) c) b) ((\<lambda> c. (c b)) (\<lambda> a. a))"

text "basic definitions"

definition
  succ :: "(('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "succ \<equiv> \<lambda>n f x. f (n f x)"

thm succ_def

definition
  add :: "(('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
          ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "add \<equiv> \<lambda>m n f x. m f (n f x)"

definition
  mult :: "(('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>  
          ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "mult \<equiv> \<lambda>m n f x. m (n f) x"


text "unfolding a definition"

definition
  c_0 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_0 \<equiv> \<lambda>f x. x"

definition
  c_1 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_1 \<equiv> \<lambda>f x. f x"

definition
  c_2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_2 \<equiv> \<lambda>f x. f (f x)"

definition
  c_3 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_3 \<equiv> \<lambda>f x. f (f (f x))"

thm c_0_def
lemma "c_0 = (\<lambda>f x. x)"
  apply (unfold c_0_def)
  apply (rule refl)
  done

lemma "succ (succ c_0) = c_2"
  apply (unfold succ_def c_0_def c_2_def)
  apply (rule refl)
  done

lemma "add c_2 c_2 = succ c_3"
  apply (unfold add_def succ_def c_3_def c_2_def)
  apply (rule refl)
  done

lemma "add x c_0 = x"
  apply (unfold add_def c_0_def)
  apply (rule refl)
  done
  
lemma "mult c_1 x = x"
  apply (unfold mult_def c_1_def)
  apply (rule refl)
  done

section "Simply Typed \<lambda>-calculus"

text \<open>Try \texttt{term "\<lambda> a. a a"}\<close>

text \<open>
  An example with a free variable. In this case Isabelle infers the needed type of the
  free variable.
\<close>

term "\<lambda> y f. f (x y)"


end