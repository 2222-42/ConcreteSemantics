theory Concrete_Semantics_2_3
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree => 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
apply(induction t)
apply(auto)
done

datatype 'a option = None | Some 'a

fun lookup :: "('a * 'b) list => 'a => 'b option" where
"lookup [] x = None" |
"lookup ((a, b) # ps) x = (if a = x then Some b else lookup ps x)"

end