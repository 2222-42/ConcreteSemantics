theory Concrete_Semantics_2_5_ex11
imports Main
begin

(* Define arithmetic expressions in one variable over integers *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp => int => int" where
"eval Var x = x" |
"eval (Const m) x = m" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp :: "int list => int => int" where
"evalp [] x = 0" |
"evalp (y # ys) x = y + x * (evalp ys x)"

fun a_coeffs :: "int list => int list => int list" where
"a_coeffs Nil Nil = Nil" |
"a_coeffs Nil ys = ys" |
"a_coeffs xs Nil = xs" |
"a_coeffs (x#xs) (y#ys) = (x + y) # (a_coeffs xs ys)"

fun multi_dist_list:: "int => int list => int list" where
"multi_dist_list n Nil = Nil" |
"multi_dist_list n (x#xs) = (n*x)#(multi_dist_list n xs)"

fun m_coeffs :: "int list => int list => int list" where
"m_coeffs Nil ys = Nil" |
"m_coeffs (x#xs) ys = a_coeffs (multi_dist_list x ys)  (0 # m_coeffs xs ys)"

fun coeffs :: "exp => int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const n) = [n]" |
"coeffs (Add a b) = a_coeffs (coeffs(a)) (coeffs(b))" |
"coeffs (Mult a b) = m_coeffs (coeffs(a)) (coeffs(b))"

lemma evalp_coeffs_to_eval_add : "evalp (a_coeffs xs ys) x = evalp xs x + evalp ys x"
apply(induction xs rule: a_coeffs.induct)
apply(auto simp add: algebra_simps)
(* apply(simp add:algebra_simps) *)
done

lemma evalp_m_d_l: "evalp (multi_dist_list a ys) x = a * evalp ys x"
apply(induction ys )
apply(auto simp add: algebra_simps)
done

lemma evalp_coeffs_to_eval_multi: "evalp (m_coeffs xs ys) x = evalp xs x * evalp ys x"
apply(induction xs )
apply(auto simp add:algebra_simps evalp_m_d_l evalp_coeffs_to_eval_add)
done

(* 
If not proved internal cases, 
2. \<And>e1 e2 x.
       (\<And>x. evalp (coeffs e1) x = eval e1 x) \<Longrightarrow>
       (\<And>x. evalp (coeffs e2) x = eval e2 x) \<Longrightarrow>
       evalp (a_coeffs (coeffs e1) (coeffs e2)) x = eval e1 x + eval e2 x
 3. \<And>e1 e2 x.
       (\<And>x. evalp (coeffs e1) x = eval e1 x) \<Longrightarrow>
       (\<And>x. evalp (coeffs e2) x = eval e2 x) \<Longrightarrow>
       evalp (m_coeffs (coeffs e1) (coeffs e2)) x = eval e1 x * eval e1 x
*)
(*
Find Typo in eval:
 1. \<And>e1 e2 x.
       (\<And>x. evalp (coeffs e1) x = eval e1 x) \<Longrightarrow>
       (\<And>x. evalp (coeffs e2) x = eval e2 x) \<Longrightarrow>
       eval e2 x \<noteq> eval e1 x \<Longrightarrow> eval e1 x = 0
*)
lemma "evalp (coeffs e) x = eval e x"
apply(induction e arbitrary: x)
apply(auto simp add: evalp_coeffs_to_eval_add evalp_m_d_l  evalp_coeffs_to_eval_multi)
done



end