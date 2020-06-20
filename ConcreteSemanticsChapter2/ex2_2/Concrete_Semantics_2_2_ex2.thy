theory Concrete_Semantics_2_2_ex2
imports Main
begin
fun add:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_0case[simp]: "n = add n 0"
  apply(induction n)
  apply(auto)
  done

(* Prove that add is associative and commutative *)

lemma add_assoc[simp]: "add (add m n) p = add m (add n p)"
apply(induction m)
apply(auto)
done

lemma succ_add_com[simp]: "Suc (add n m) = add n (Suc m)"
apply(induction n) (* to use `m` needs difficult proof structure *)
apply(auto)
done

lemma add_comm: "add m n = add n m"
apply(induction m)
apply(auto)
done

(* Define a recursive function double *)
fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double m = 2 + double(m - 1)"

(* prove double m = add m m. *)

lemma double_is_add_add: "double m = add m m"
apply(induction m)
apply(auto)
done
  
end