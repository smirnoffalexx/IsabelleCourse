section \<open>Locales\<close>

theory Locales
  imports "HOL-Library.Countable_Set" 
begin

text\<open>
Locales are based on context . 
A context is a formula scheme  \<open>\<And> x\<^sub>1 . . . x\<^sub>n . [[ A\<^sub>1 ; . . . ;A\<^sub>m ]] \<Longrightarrow> . . .\<close>
\<close>

locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and anti_sym [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

text\<open>
The parameter of this locale is le, which is a binary predicate with infix syntax \<open>\<sqsubseteq>\<close>. 
The parameter syntax is available in the subsequent assumptions,
which are the familiar partial order axioms.
\<close>

print_locales

print_locale! partial_order

text \<open>
The assumptions have turned into conclusions, denoted by the keyword notes. 
Also, there is only one assumption - \<open>partial_order\<close>. 
The locale declaration has introduced the predicate \<open>partial_order\<close> to the theory. 
This predicate is the locale predicate.
\<close>

thm partial_order_def
thm partial_order.trans partial_order.anti_sym partial_order.refl

subsection \<open>Extending Locales\<close>

definition (in partial_order)
less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50) 
  where "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"

text\<open>
The definition generates a foundational constant \<open>partial_order.less:\<close>\<close>

thm partial_order.less_def

text\<open>At the same time, the locale is extended by syntax transformations hiding
this construction in the context of the locale.\<close>

print_locale! partial_order

lemma (in partial_order) less_le_trans [trans]:
  "\<lbrakk> x \<sqsubset> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  unfolding less_def by (blast intro: trans)

subsection \<open>context n begin ... end\<close>

text \<open>Entering locale context:\<close>

context partial_order

begin

definition
  is_inf where "is_inf x y i =
         (i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall> z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i))"

definition
  is_sup where "is_sup x y s =
         (x \<sqsubseteq> s \<and> y \<sqsubseteq> s \<and> (\<forall> z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> s \<sqsubseteq> z))"

theorem is_inf_uniq: "\<lbrakk>is_inf x y i; is_inf x y i'\<rbrakk> \<Longrightarrow> i = i'"
  oops
theorem is_sup_uniq: "\<lbrakk>is_sup x y s; is_sup x y s'\<rbrakk> \<Longrightarrow> s = s'"
  oops

end

print_locale! partial_order

subsection \<open>Import\<close> 

locale total_order = partial_order +
  assumes total: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

locale lattice = partial_order +
  assumes ex_inf: "\<exists> inf. is_inf x y inf"
    and ex_sup: "\<exists> sup. is_sup x y sup"
begin

definition meet (infixl "\<sqinter>" 70) where "x \<sqinter> y = (THE inf. is_inf x y inf)"
definition join (infixl "\<squnion>" 65) where "x \<squnion> y = (THE sup. is_sup x y sup)"

lemma meet_left: "x \<sqinter> y \<sqsubseteq> x" oops

end

subsection \<open>Interpretation\<close>

text \<open>
The declaration sublocale \<open>l1 \<subseteq> l2\<close> causes locale l2 to be interpreted in the context of l1. 
This means that all conclusions of l2 are made available in l1.\<close>

sublocale total_order \<subseteq> lattice
text\<open>The sublocale command generates a goal, which must be discharged by the user:\<close>
proof unfold_locales (*intro_locales*)
  fix x y
  thm is_inf_def
  from total have "is_inf x y (if x \<sqsubseteq> y then x else y)" by (auto simp: is_inf_def)
  thus "\<exists> inf. is_inf x y inf" ..
  from total have "is_sup x y (if x \<sqsubseteq> y then y else x)" by (auto simp: is_sup_def)
  thus "\<exists> sup. is_sup x y sup" ..
qed


text\<open>
The command interpretation is for the interpretation of locale in theories.\<close>

text\<open>In the following example, the parameter of locale \<open>partial_order\<close> is replaced
by \<open>(\<le>)\<close> and the locale instance is interpreted in the current theory.
\<close>

interpretation int: partial_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
  apply unfold_locales 
    apply auto 
  done

thm int.trans
thm int.less_def

text\<open> 
We want to replace int.less by \<open><\<close>. 
\<close>

text\<open> 
In order to allow for the desired replacement,
interpretation accepts equations in addition to the parameter instantiation. 
These follow the locale expression and are indicated with the keyword rewrites.
\<close>

interpretation int: partial_order "(\<le>) :: [int, int] \<Rightarrow> bool"
  rewrites "int.less x y = (x < y)"
  (* apply (simp add: int.partial_order_axioms)
  using int.less_def by fastforce *)
proof-
  show "partial_order ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
    by unfold_locales auto
  show "partial_order.less (\<le>) x y = (x < y)"
    unfolding partial_order.less_def [OF \<open> partial_order (\<le>) \<close>]
    by auto
qed

text\<open>
In the above example, the fact that \<open>\<le>\<close> is a partial order for the integers
was used in the second goal to discharge the premise in the definition of \<open>\<sqsubseteq>\<close>.
In general, proofs of the equations not only may involve definitions from the
interpreted locale but arbitrarily complex arguments in the context of the
locale. Therefore it would be convenient to have the interpreted locale conclusions temporarily available in the proof. 
This can be achieved by a locale interpretation in the proof body. The command for local interpretations is
interpret.
\<close>

interpretation int: partial_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
  rewrites "int.less x y = (x < y)"
proof -
  show "partial_order ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
    by unfold_locales auto
  then interpret int: partial_order "(\<le>) :: [int, int] \<Rightarrow> bool" .
  show "int.less x y = (x < y)"
    unfolding int.less_def by auto
qed

text\<open>
Theorems from the local interpretation disappear after leaving the proof context — that is,
after the succeeding next or qed statement
\<close>

end