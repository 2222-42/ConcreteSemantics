theory MyList
  imports Main
begin

(* datatype requires no quotation marks on the left-hand side, but on the
right-hand side each of the argument types of a constructor needs to be
enclosed in quotation marks, unless it is just an identifier (e.g., nat or 'a).*)
datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"

(* 
To prove that some property P holds for
all lists xs, i.e., P xs, you need to prove
1. the base case P Nil and
2. the inductive case P (Cons x xs) under the assumption P xs, for some
arbitrary but fixed x and xs.
This is often called structural induction
 *)


end