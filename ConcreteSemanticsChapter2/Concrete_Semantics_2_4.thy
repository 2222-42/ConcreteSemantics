theory Concrete_Semantics_2_4
  imports Main
begin

(* generalize the goal before induction. *)

(*
datatype 'a list = Nil | Cons 'a "'a list"
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"
*)
(* A linear time version of rev *)



fun itrev :: "'a list => 'a list => 'a list" where
"itrev [] ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

(* Note that itrev is tail-recursive: it can be
compiled into a loop; no stack is necessary for executing it. *)

(* lemma "itrev xs [] = rev xs" *)
(* The induction hypothesis is too weak, we met the following formula needed to prove:
 \<And> a xs: itrev xs [] = rev xs =) itrev xs [a] = rev xs @ [a] *)
(* heuristic: 
    Generalize goals for induction by replacing constants by variables: 
        e.g., "itrev xs [] = rev xs" -> "itrev xs ys = rev xs @ ys" *)
(* The induction hypothesis is ttile  weak
  \<And>a xs.
       itrev xs ys = rev xs @ ys \<Longrightarrow>
       itrev xs (a # ys) = app (rev xs) [a] @ ys  

we prove the theorem for all ys instead of a fixed one: apply(induction xs ) -> apply(induction xs arbitrary: ys)
*)
lemma "itrev xs ys = rev xs @ ys"
apply(induction xs arbitrary: ys)
apply(auto)
done

(* another heuristic for generalization:
    Generalize induction by generalizing all free variables:
        e.g., apply(induction xs ) -> apply(induction xs arbitrary: ys)
    (except the induction variable itself).
*)

end