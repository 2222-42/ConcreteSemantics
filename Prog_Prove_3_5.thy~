theory Prog_Prove_3_5
  imports Main
begin

inductive ev:: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev m \<Longrightarrow> evn m"
apply(induction rule: ev.induct)
  by(simp_all)

lemma "ev(Suc(Suc(Suc(Suc 0))))"
  apply(rule evSS)
  apply(rule evSS)
  apply(rule ev0)
  done

lemma "evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
  by(simp_all add: ev0 evSS)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply(assumption)
  apply(metis step)
  done

lemma star_pre: "\<lbrakk>r x y; star r y z\<rbrakk> \<Longrightarrow> star r x z"
  by (rule step)

lemma star_ap: "\<lbrakk>star r x y; r y z\<rbrakk> \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(auto intro: star.intros)
  done


inductive palindrome:: "'a list \<Rightarrow> bool" where
emp: "palindrome []" |
sing: "palindrome [x]" |
list: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  by(simp_all)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star'_ap: "\<lbrakk>star' r y z; r x y\<rbrakk> \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(auto intro: star'.intros)
  done

(*
why this lemma couldn't be shown?
lemma star'_pre: "\<lbrakk>r x y; star' r y z\<rbrakk> \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  done
*)

lemma "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
   apply(rule refl)
    apply(auto intro:  star_ap)
  done


lemma "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(rule refl')
    apply(auto intro: star'_ap)
  done

inductive iter:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_refl: "iter r n x x" |
iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r n x z"


lemma iter_ap: "\<lbrakk> r x y; iter r n y z\<rbrakk> \<Longrightarrow> iter r n x z"
  by (rule iter_step)


lemma "star r x y \<Longrightarrow> iter r n x y"
  apply(induction rule: star.induct)
   apply(rule iter_refl)
  apply(auto intro: iter_ap)
  done

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
s_emp: "S[]" |
s_list: "S xs \<Longrightarrow> S (a # xs @ [b])" |
s_const: "S xs \<Longrightarrow> S ys \<Longrightarrow> S(xs@ys)"

inductive T :: "alpha list \<Rightarrow> bool" where
t_emp: "T[]" |
t_const: "T xs \<Longrightarrow> T ys \<Longrightarrow>  T(a # xs @ b # ys)"


lemma s_formed_for_t: "S xs \<Longrightarrow> S ys \<Longrightarrow> S (a # xs @ b # ys)"
  using s_const s_emp s_list apply force
  done

lemma TS: "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
   apply(rule s_emp)
  apply(auto intro: s_formed_for_t)
  done

lemma t_formed_for_s: " T xs \<Longrightarrow>  T ys \<Longrightarrow> T (xs @ ys)"
  apply(induction rule: T.induct)
   apply simp
  by (simp add: t_const)

lemma ST: "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
  apply(rule t_emp)
   apply(auto intro: t_formed_for_s)
  by (simp add: t_const t_emp)

corollary SeqT: "S w \<longleftrightarrow> T w"
  using ST TS by blast

(*---------------- Exercise 4.6----------------*)

end