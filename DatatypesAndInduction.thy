theory DatatypesAndInduction
  imports Main
begin

section \<open>Types Declaration\<close>
type_synonym string = "char list"

typedecl myType

text \<open>A recursive data type: \<close>

(* datatype nat = Zero | Suc nat *)

datatype ('a,'b) tree = Tip | Node "('a,'b) tree" 'b "('a,'b) tree"

print_theorems

text \<open>Distincteness of constructors automatic: \<close>
lemma "Tip ~= Node l x r" by simp

text\<open>Lists\<close>

text\<open>Large library: HOL/List.thy included in Main. Don’t reinvent, reuse!
Predefined: xs @ ys (append), length, and map\<close>

term "Nil"
term "Cons"

thm list.induct

text\<open>Enumeration\<close>
datatype Status = Inactive | InProgress | Finished

text\<open>Mutual Recursion\<close>
datatype even = EvenZero | EvenSuc odd
  and odd = OddZero | OddSuc even 

thm even.induct odd.induct

text \<open>Case sytax, case distinction manual\<close>
lemma "(1::nat) \<le> (case t of Tip \<Rightarrow> 1 | Node l x r \<Rightarrow> x+1)"
  apply(case_tac t)
  apply auto
  done

text \<open>Partial cases and dummy patterns: \<close>
term "case t of Node _ b _ => b"

text \<open>Partial case maps to 'undefined': \<close>
lemma "(case Tip of Node _ _ _ => 0) = undefined" by simp

text \<open>Nested case and default pattern: \<close>
term "case t of Node (Node _ _ _) x Tip => 0 | _ => 1"

text \<open>Infinitely branching: \<close>
datatype 'a inftree = Tp | Nd 'a "nat \<Rightarrow> 'a inftree"

text \<open>Mutually recursive \<close>
datatype
  ty = Integer | Real | RefT ref
  and
  ref = Class | Array ty


section \<open>Primitive recursion & Functions\<close>

text\<open>Non-recursive functions\<close>
definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n" 

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n" 

thm sq_def

text \<open>but there is no such a thm sq'_def\<close>
(* thm sq'_def *)

primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

primrec
  app :: "'a list => 'a list => 'a list"
where
  "app Nil ys = ys" |
  "app (Cons x xs) ys = Cons x (app xs ys)"

print_theorems

fun rev1 :: "'a list \<Rightarrow> 'a list" where
"rev1 Nil = Nil" |
"rev1 (Cons x xs) = (rev1 xs) @ (Cons x Nil)"
   
value "rev1(Cons True (Cons False Nil))"
value "rev1(Cons a (Cons b Nil))"

text \<open>On trees: \<close>
primrec
  mirror :: "('a,'b) tree => ('a,'b) tree"
where
  "mirror Tip = Tip" |
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"

print_theorems


text \<open>Mutual recursion\<close>
primrec
  has_int :: "ty \<Rightarrow> bool" and
  has_int_ref :: "ref \<Rightarrow> bool"
where
  "has_int Integer       = True" |
  "has_int Real          = False" |
  "has_int (RefT T)      = has_int_ref T" |

  "has_int_ref Class     = False" |
  "has_int_ref (Array T) = has_int T"

\<comment> \<open>------------------------------------------------------------\<close>

section \<open>Structural induction\<close>

text\<open>Basic examples with nats\<close>

lemma add_02: "add m 0 = m"
  apply(induction m)
  apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma nSm_Snm[simp]: "add n (Suc m) = add (Suc n) m"
  apply (induction n)
  apply (auto)
done 

theorem double_add: "add n n = double n"
  apply(induction n)
  apply(auto)
  done

fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = (Suc n) + (sum n)"

lemma sum_is: "sum n = n * (n + 1) div 2"
  apply(induction n)
  apply(auto)
  done

text \<open>Structural induction for lists\<close>
find_theorems "rev (rev _ )"

text \<open>Discovering lemmas needed to prove a theorem \<close>
lemma app_nil[simp]: "xs @ [] = xs"
  apply (induction xs)
   apply (auto)
  done

lemma app_assoc: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  apply (induction xs)
  apply (auto)
  done

thm List.append.append_Cons

lemma rev_app: "rev1 (xs @ ys) = (rev1 ys) @ (rev1 xs)"
  apply (induction xs)
  using [[simp_trace]]
   apply (simp)
  apply (simp add: app_assoc)
  done

theorem rev_rev: "rev1 (rev1 xs) = xs"
  apply (induction xs)
  apply (auto simp add:rev_app)
  done

text\<open>One more example\<close>

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count y [] = 0" |
"count y (x # xs) = (if x = y then Suc(count y xs) else count y xs)"

lemma count_less: "count y xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

text \<open>Induction heuristics\<close>

primrec
  itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma itrev_rev_app: "itrev xs ys = rev xs @ ys"
  apply (induct xs arbitrary: ys)
   apply simp
  using [[simp_trace]]
  apply auto
  done

lemma "itrev xs [] = rev xs"
  apply (induct xs)
   apply simp
  apply (clarsimp simp: itrev_rev_app)
  done

\<comment> \<open>----------------------------------------------------------\<close>

primrec
  lsum :: "nat list \<Rightarrow> nat"
where
  "lsum [] = 0" |
  "lsum (x#xs) = x + lsum xs"

find_theorems "(_ # _) @ _" (* List.append.append_Cons*)

lemma lsum_app: "lsum (xs @ ys) = lsum xs + lsum ys"
  apply (induct xs)
  by auto

lemma
  "2 * lsum [0 ..< Suc n] = n * (n + 1)"
  apply (induct n)
   apply simp
  apply simp
  apply (auto simp: lsum_app)
  done

lemma
  "lsum (replicate n a) = n * a"
  apply (induct n)
   apply simp
  apply simp
  done


text \<open>Tail recursive version: \<close>

primrec
  lsumT :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
where
  "lsumT [] s = s" |
  "lsumT (x#xs) s = lsumT xs (x + s)"

lemma lsumT_gen:
  "lsumT xs s = lsum xs + s"
  by (induct xs arbitrary: s, auto)

lemma lsum_correct:
  "lsumT xs 0 = lsum xs"
  apply (induct xs)
   apply (simp)
  apply (simp add :lsumT_gen)
  done

end
