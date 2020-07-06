theory Concrete_Semantics_5_1
  imports Main
begin

lemma "\<not> surj (f::'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
(*
from 0 have 1: "8A: 9 a: A = f a" by(simp add: surj_def )
from 1 have 2: "9 a: fx : x =2 f x g = f a" by blast
from 2 show "False" by blast
*)
  hence 1: "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp add: surj_def)
  thus "False" by blast
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists>a. {x. x \<notin> f x} = f a" using s by (auto simp: surj_def)
  thus "False" by blast
qed

lemma "\<not> surj (f::'a \<Rightarrow> 'a set)"
proof
  assume"surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed


lemma 
  fixes a b :: int
  assumes "b dvd (a + b)"
  shows "b dvd a"
proof-
  have "\<exists>k'. a = b * k'" if asm: "a + b = b*k" for k
  proof 
    show "a = b *(k - 1)" using asm by (simp add: algebra_simps)
  qed
  thus ?thesis using assms by(auto simp add: dvd_def)
qed

(* Exercise 5.1. *)
lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" 
  and "A x y"
  shows "T x y"
proof(rule ccontr)
  assume "\<not> T x y"
  hence "T y x" using T by blast
  hence "A y x" using TA by blast
  hence "x = y" using assms by auto
  hence "T x x" using T by auto
  hence "T x y" using `x = y` by auto 
  thus "False" using `\<not> T x y` by auto
qed

(* Exercise 5.2. *)
lemma "\<exists> ys zs. xs = ys @ zs \<and>
        (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
  then obtain a where "length xs = 2 * a" by auto
    let ?ys = "take a xs"
    let ?zs = "drop a xs"
    have "xs = ?ys @ ?zs \<and>length ?ys = length ?zs" by(simp add: `length xs = 2 * a`)
    hence "xs = ?ys @ ?zs \<and>
        (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by (auto)
    thus ?thesis by blast
next
  assume "odd (length xs)"
  then obtain a where "length xs = (2 * a) + 1" 
    using oddE by blast
    let ?ys = "take (a + 1) xs"
    let ?zs = "drop (a + 1) xs"
    have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by (simp add: \<open>length xs = 2 * a + 1\<close>)
    hence "xs = ?ys @ ?zs \<and>
        (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by (auto)
    thus ?thesis  by blast
qed


(* Chap 5.4 *)

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
(*
  assume "xs = []"
*)
  case Nil
  then show ?thesis by simp
next
(*
  fix y ys assume "xs = y#ys"
*)
  case (Cons y ys)
  then show ?thesis 
    by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof(induction n)
  show "?P 0" by simp
next
  fix n assume  "?P n"
  thus  "?P (Suc n)" by simp
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0
  show ?case by simp
(*case ev0 show ?case by simp*)
next
  case evSS
  thus ?case by simp
(* case (evSS m)
have "evn(Suc(Suc m)) = evn m" by simp
thus ?case using hevn mi by blast *)
qed

lemma not_even_1:"\<not> ev(Suc 0)"
proof
  assume "ev(Suc 0)" then show False by cases
qed

(* Exercise 5.4. *)

lemma "\<not> ev(Suc(Suc(Suc 0)))"
proof
  assume "ev(Suc(Suc(Suc 0)))" thus False
  proof cases
    assume "ev(Suc 0)" thus False by cases
  qed
(*  assume "ev(Suc(Suc(Suc 0)))" 
  hence "ev(Suc 0)" 
    using ev.cases by auto
  then show False by (auto simp add: not_even_1)*)
qed

lemma "ev(Suc m) \<Longrightarrow> \<not> ev m"
proof(induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev (Suc n)"
  proof 
    assume "ev (Suc n)"
    thus False
    proof cases
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

(* Exercise 5.3. *)

(*it is not able to use rule: ev.induct, because if n = 0 then it were failed.*)
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
proof -
  show "ev n" 
    using assms ev.cases by blast
qed

(* Exercise 5.5. *) 

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_refl: "iter r n x x" |
iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r n x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof(induction rule:iter.induct)
case (iter_refl n x)
  then show ?case 
    by (simp add: star.refl)
next
  case (iter_step x y n z)
then show ?case 
  by (meson star.step)
qed

(*Exercise 5.6.*)

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x#xs) = {x} \<union> elems xs" 

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case 
  proof cases
    assume "x = a"
    then obtain zs where "x#zs = a#xs" by blast
    let ?ys = "[]"
    have "x \<notin> elems ?ys" 
      by simp
    show ?case 
      using \<open>x = a\<close> \<open>x \<notin> elems []\<close> by blast
  next
    assume "x \<noteq> a"
(* get lists `ys` and `zs`, which were introduced from IH *)
(* it is not possible to use the following:
"by (auto simp add:`x \<in> elems(Cons a xs)`)"
. So I use "from A B have ...".
*)
    from this `x \<in> elems(Cons a xs)` have "x \<in> elems xs" by auto
    then obtain ys zs where "xs = ys @ x # zs \<and> x \<notin> elems ys" 
      using Cons.IH by auto
(*It is not possible to derive ?case from this result.
Because we need the case of "a # xs =..."
*)
    from this `x \<noteq> a` obtain ys' where "a # xs = ys' @ x # zs \<and> x \<notin> elems ys'" by force      
    show ?case 
      using \<open>a # xs = ys' @ x # zs \<and> x \<notin> elems ys'\<close> by auto
  qed
qed

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
s_emp: "S[]" |
s_list: "S xs \<Longrightarrow> S (a # xs @ [b])" |
s_const: "S xs \<Longrightarrow> S ys \<Longrightarrow> S(xs@ys)"

(* Should not use S in def of balanced.
0 abab \<Rightarrow> 1 bab \<Rightarrow> 0 ab \<Rightarrow> 1 b \<Rightarrow> 0 []: True

0 abb \<Rightarrow> 1 bb \<Rightarrow> 0 b \<Rightarrow> -1 b \<Rightarrow> -2 []: False

0 aab \<Rightarrow> 1 ab \<Rightarrow> 2 b \<Rightarrow> 1 [] : False 
*)
fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced 0 [] = True" |
"balanced n (a#xs) = balanced (Suc n) xs" |
"balanced (Suc n) (b#xs) = balanced n xs" |
"balanced _ _ = False"

lemma
  fixes n w
  assumes b: "balanced n w"
  shows "S (replicate n a @ w)"
proof -
  from b show ?thesis
  proof(induction w)
    case Nil
    then show ?case 
    proof (induction n)
      case 0
      then show ?case 
        by (simp add: s_emp)
    next
      case (Suc n)
      then show ?case 
        by simp
    qed
  next
    case (Cons a w)
    then show ?case 
    proof (induction n)
      case 0
      then show ?case sorry
    next
      case (Suc n)
      then show ?case sorry
        
    qed
  qed
qed

lemma 
  fixes n w
  assumes s: "S (replicate n a @ w)"
  shows "balanced n w"
proof (induction w)
  case Nil
  then show ?case sorry
next
  case (Cons a w)
  then show ?case sorry
qed

corollary "balanced n w \<longleftrightarrow> S (replicate n a @ w)"
proof (induction w)
  case Nil
  then have "balanced n [] \<Longrightarrow> S(replicate n a @ [])"
  proof (induction n)
    case 0
    then show ?case 
      by (simp add: s_emp)
  next
    case (Suc n)
    then show ?case sorry
  qed
  then have "S(replicate n a @ []) \<Longrightarrow> balanced n w"
  proof (induction n)
    case 0
    then show ?case sorry
  next
    case (Suc n)
    then show ?case sorry
  qed
  then show ?case sorry
next
  case (Cons a w)
  then have "balanced n w \<Longrightarrow> S(replicate n a @ w)"
  proof(induction n)
    case 0
    then show ?case sorry
  next
    case (Suc n)
    then show ?case sorry
  qed

  then have "S(replicate n a @ w) \<Longrightarrow> balanced n w"
  proof(induction n)
    case 0
    then show ?case sorry
  next
    case (Suc n)
    then show ?case sorry
  qed
  then show ?case sorry
qed



end
