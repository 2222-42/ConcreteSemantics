theory Concrete_Semantics_2_2_ex4
imports Main
begin

(* Define a recursive function that appends an element to the end of a list *)
fun snoc :: "'a list => 'a => 'a list" where
"snoc Nil a = Cons a Nil" |
"snoc (Cons x xs) a = Cons x (snoc xs a)"

(* With the help of snoc define a recursive function reverse *)
fun reverse :: "'a list => 'a list" where
"reverse [] = []" |
"reverse (Cons x xs) = snoc (reverse xs) x"

(* Subgoal: \<And>a xs. reverse (reverse xs) = xs \<Longrightarrow> reverse (snoc (reverse xs) a) = a # xs *)
lemma rev_distributes_over_snoc[simp]: "reverse (snoc xs a) = Cons a (reverse xs)"
apply(induction xs)
apply(auto)
done

(* Prove reverse (reverse xs) = xs *)
lemma "reverse (reverse xs) = xs"
apply(induction xs)
apply(auto)
done

end