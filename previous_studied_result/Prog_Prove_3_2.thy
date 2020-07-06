theory Prog_Prove_3_2
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a " 'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node xt a yt) = set xt \<union> ({a} \<union> set yt)"

(* make function get int option *)
fun get_max_opt :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
"get_max_opt None None = None" |
"get_max_opt (Some a) None = Some a" |
"get_max_opt None (Some a) = Some a" |
"get_max_opt (Some a) (Some b) = Some(max a b)"

fun get_min_opt :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
"get_min_opt None None = None" |
"get_min_opt (Some a) None = Some a" |
"get_min_opt None (Some a) = Some a" |
"get_min_opt (Some a) (Some b) = Some(min a b)"

(* make function int less than int option *)
fun option_is_less_than_int :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"option_is_less_than_int None b = True" |
"option_is_less_than_int (Some a) b = (a \<le> b)"

fun option_is_greater_than_int :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"option_is_greater_than_int None b = True" |
"option_is_greater_than_int (Some a) b = (a \<ge> b)"

fun get_min_opt_from_tree :: "int tree \<Rightarrow> int option" where
"get_min_opt_from_tree Tip = None" |
"get_min_opt_from_tree (Node xt a yt) = 
    get_min_opt (Some a) (get_min_opt (get_min_opt_from_tree xt) (get_min_opt_from_tree yt))"

fun get_max_opt_from_tree :: "int tree \<Rightarrow> int option" where
"get_max_opt_from_tree Tip = None" |
"get_max_opt_from_tree (Node xt a yt) = 
    get_max_opt (Some a) (get_max_opt (get_max_opt_from_tree xt) (get_max_opt_from_tree yt))  "

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node xt a yt) = ((option_is_less_than_int (get_max_opt_from_tree xt) a) \<and> (option_is_greater_than_int (get_min_opt_from_tree yt) a) \<and> (ord xt) \<and> (ord yt))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins a Tip = Node Tip a Tip" |
"ins a (Node xt b yt) = (if (a = b) then (Node xt b yt) else
                        (if (a < b) then (Node (ins a xt) b yt) else
                        (Node xt b (ins a yt)) ))"

theorem "set (ins x t) = {x} \<union> set t"
  apply(induction t)
   apply(auto)
  done

lemma get_max_opt_com_1 : "get_max_opt (Some a) y = get_max_opt y (Some a)"
  apply(induction y)
   apply(auto)
  done

lemma get_max_opt_com_2 : "get_max_opt (get_max_opt x (Some a)) y = 
  get_max_opt x (get_max_opt y (Some a))"
  apply(induction x; induction y)
     apply(auto)
  done

lemma get_max_opt_com_3 : "get_max_opt (get_max_opt x y) z =
 get_max_opt x (get_max_opt y z)"
  apply(induction x; induction y; induction z)
         apply(auto)
  done

lemma simplify_max_inserted_tree:
"get_max_opt_from_tree (ins i t1) = 
  get_max_opt (Some i) (get_max_opt_from_tree t1)"
  apply(induction t1)
   apply(auto simp add:get_max_opt_com_1)
    apply(auto simp add:get_max_opt_com_2)
   apply(auto simp add:get_max_opt_com_3)
  done

lemma get_min_opt_com_1 : "get_min_opt (Some a) y = get_min_opt y (Some a)"
  apply(induction y)
   apply(auto)
  done

lemma get_min_opt_com_2 : "get_min_opt (get_min_opt x (Some a)) y = 
  get_min_opt x (get_min_opt y (Some a))"
  apply(induction x; induction y)
     apply(auto)
  done

lemma get_min_opt_com_3 : "get_min_opt (get_min_opt x y) z =
 get_min_opt x (get_min_opt y z)"
  apply(induction x; induction y; induction z)
         apply(auto)
  done

lemma simplify_min_inserted_tree:
"get_min_opt_from_tree (ins i t1) = 
  get_min_opt (Some i) (get_min_opt_from_tree t1)"
  apply(induction t1)
   apply(auto simp add:get_min_opt_com_1)
    apply(auto simp add:get_min_opt_com_2)
   apply(auto simp add:get_min_opt_com_3)
  done

lemma less_than_max_opt: 
    "option_is_less_than_int t1 x2 \<Longrightarrow>
       option_is_less_than_int t2 x2 \<Longrightarrow>
          option_is_less_than_int (get_max_opt t1 t2) x2"
  apply(induction t1; induction t2)
   apply(auto)
  done



lemma greater_than_min_opt: 
    "option_is_greater_than_int t1 x2 \<Longrightarrow>
       option_is_greater_than_int t2 x2 \<Longrightarrow>
          option_is_greater_than_int (get_min_opt t1 t2) x2"
  apply(induction t1; induction t2)
   apply(auto)
  done

theorem "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t)

   apply(auto simp add:simplify_max_inserted_tree)
   apply(auto simp add:less_than_max_opt)
   apply(auto simp add:simplify_min_inserted_tree)
   apply(auto simp add:greater_than_min_opt)

  done
end
