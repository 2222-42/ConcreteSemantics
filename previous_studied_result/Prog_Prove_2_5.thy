theory Prog_Prove_2_5
  imports Main
begin

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = nodes r + nodes l"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"


lemma "nodes (explode n t) = (2 ^ n) * nodes t "
  apply(induction n arbitrary: t)
  apply(auto)
  done

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const a) x = a" |
"eval (Add a b) x = (eval a x) + (eval b x)" |
"eval (Mult a b) x = (eval a x) * (eval b x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] y = 0" |
"evalp (x#xs) y = x + y * (evalp xs y)"

fun a_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"a_coeffs Nil Nil = Nil" |
"a_coeffs Nil ys = ys" |
"a_coeffs xs Nil = xs" |
"a_coeffs (x#xs) (y#ys) = (x + y) # (a_coeffs xs ys)"

fun multi_dist_list:: "int \<Rightarrow> int list \<Rightarrow> int list" where
"multi_dist_list n Nil = Nil" |
"multi_dist_list n (x#xs) = (n*x)#(multi_dist_list n xs)"

fun m_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"m_coeffs Nil ys = Nil" |
"m_coeffs (x#xs) ys = a_coeffs (multi_dist_list x ys)  (0 # m_coeffs xs ys)"


fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0,1]" |
"coeffs (Const a) = [a]" |
"coeffs (Add a b) = a_coeffs (coeffs(a)) (coeffs(b))" |
"coeffs (Mult a b) = m_coeffs (coeffs(a)) (coeffs(b))"


lemma evalp_coeffs_to_eval_add[simp] :
  "evalp (a_coeffs xs ys) x = evalp xs x + evalp ys x"
  apply(induction xs rule: a_coeffs.induct)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_m_d_l[simp]:" evalp (multi_dist_list a ys) x = a * evalp ys x"
  apply(induction ys)
  apply(auto simp add: algebra_simps)
  done


lemma evalp_coeffs_to_eval_multi[simp]:
  "evalp (m_coeffs xs ys) x = evalp xs x * evalp ys x"
  apply(induction xs)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_coeffs_eval: "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary: x)
  apply(auto)
  done
