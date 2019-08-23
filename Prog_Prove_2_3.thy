theory Prog_Prove_2_3
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror(mirror t) = t"
  apply(induction t)
   apply(auto)
  done

datatype 'a option = None | Some 'a

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a,b) # ps) x = (if a = x then Some b else lookup ps x)"

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

lemma "div2(n) = n div 2"
  apply(induction n rule: div2.induct)
  apply(auto)
  done

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents (Tip) = []" |
"contents (Node l a r) = 
  (contents l)@(a # (contents r))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = sum_tree(l) + a + sum_tree(r)"

lemma sum_tree_is_sum_list_of_contents :
  "sum_tree t = sum_list (contents t)"
  apply(induction t )
  apply(auto)
  done

datatype 'a tree2 = Tip 'a | Node "'a tree2" "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Tip x) = Tip x" |
"mirror2 (Node l r) = Node (mirror2 r) (mirror2 l)"

fun pre_order2 :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order2 (Tip x) = [x]" |
"pre_order2 (Node l r) = pre_order2 l @ pre_order2 r"

fun post_order2 :: "'a tree2 \<Rightarrow> 'a list" where
"post_order2 (Tip x) = [x]" |
"post_order2 (Node l r) = post_order2 r @ post_order2 l"

lemma "pre_order2 (mirror2 t) = rev (pre_order2 t)"
  apply(induction t)
  apply(auto)
  done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse _ Nil = Nil" |
"intersperse _ [x] = [x]" |
"intersperse x (y # ys) = [y, x] @ intersperse x ys "


lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule:intersperse.induct)
   apply(auto)
  done

