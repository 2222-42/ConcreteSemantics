theory Concrete_Semantics_2_2
  imports Main
begin

fun add:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02: "add m 0 = m"
  apply(induction m) (*
1: add 0 0 = 0 (* saying “for an arbitrary but fixed m” *)
2: \<And>m. add m 0 = m \<Longrightarrow>  add (Suc m) 0 = Suc m (* separates assumptions from the conclusion. *)
.*)
   apply auto
  done


thm add_02
end