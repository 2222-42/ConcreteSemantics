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

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply(induction xs)
  apply(auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
  apply(auto)
  done

(*
lemma app_assoc[simp]: "rev (app xs ys) = app (rev ys) (rev xs) \<Longrightarrow>
       app (app (rev ys) (rev xs)) (Cons x1 Nil) =
       app (rev ys) (app (rev xs) (Cons x1 Nil))"
  apply(induction xs)
   apply(auto)
  done
*)

(*
Insert this lemma, and find more simpler lemma `app_Nil`
lemma " (app (app (rev xs) (Cons x1a Nil)) (Cons x1 Nil)) = Cons x1 (Cons x1a xs)"
*)
(*
 1. \<And>x1 xs.
       MyList.rev (app xs ys) = app (MyList.rev xs) (MyList.rev ys) \<Longrightarrow>
       app (app (MyList.rev xs) (MyList.rev ys)) (MyList.list.Cons x1 MyList.list.Nil) =
       app (app (MyList.rev xs) (MyList.list.Cons x1 MyList.list.Nil)) (MyList.rev ys)
 1. \<And>x1 xs.
       MyList.rev (app xs ys) = app (MyList.rev xs) (MyList.rev ys) \<Longrightarrow>
       app (MyList.rev xs) (app (MyList.rev ys) (MyList.list.Cons x1 MyList.list.Nil)) =
       app (MyList.rev xs) (MyList.list.Cons x1 (MyList.rev ys))
*)

(*lemma rev_app [simp]: "rev (app (rev xs) (Cons x1 Nil)) = Cons x1 xs" *)
lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)" 
  apply(induction xs)
   apply(auto)
  done

(* rev (app (rev xs) (Cons x1 Nil)) = Cons x1 xs is needed to be proved*)

theorem rev_rev [simp]: "rev(rev xs) = xs" (* Via the bracketed attribute simp we also tell *)
                                           (* Isabelle to make the eventual theorem a simplification rule *) 
  apply(induction xs)
  apply(auto) (* subgoal 1 is proved *)
  done

end