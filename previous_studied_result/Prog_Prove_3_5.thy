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

(* Exercise 4.6 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val" 

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus x y) s = aval x s + aval y s" 

inductive aval_rel2 :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
rel_nat: "aval_rel2 (N n) s n" |
rel_var: "s x = n \<Longrightarrow> aval_rel2 (V x) s n" |
rel_plus: "(aval_rel2 x s n1) \<Longrightarrow>  (aval_rel2 y s n2) \<Longrightarrow> aval_rel2 (Plus x y) s (n1 + n2)"

lemma aval_rel_to_aval: "aval_rel2 x s v \<Longrightarrow> (aval x s = v)"
  apply(induction rule: aval_rel2.induct)
  apply(auto)
  done

lemma aval_to_aval_rel: "(aval x s = v) \<Longrightarrow> aval_rel2 x s v"
  apply(induction x arbitrary: v)
(*    apply (simp add: rel_nat)
   apply (simp add: rel_var)
 apply (simp add: rel_plus) *)
  apply(auto intro: rel_nat rel_var rel_plus)
  done

lemma "(aval_rel2 x s v) \<longleftrightarrow> (aval x s = v)"
  apply(auto simp add: aval_rel_to_aval)
  apply(auto simp add: aval_to_aval_rel)
  done

(* Exercise 4.7. *)

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD x) s stk = s(x) # stk" |
"exec1 ADD _ (j # i # stk) = (i + j) # stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

lemma exec_division: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply(induction is1 arbitrary:stk)
   apply(auto)
  done

lemma exec_append: "exec is\<^sub>1 s stk = stk' \<Longrightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = exec is\<^sub>2 s stk'"
apply(induction is\<^sub>1 arbitrary: stk)
apply(auto)
done

fun comp:: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma "exec (comp x) s stk = aval x s # stk"
  apply(induction x arbitrary:stk)
    apply(auto simp add: exec_division )
  done

(* the size of the execution become + 1 when LOADI or LOAD
but when ADD which is compiled and become -1.
*)
inductive  ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where 
ok_emp: "ok n [] n" |
ok_LOADI: "ok n is n'  \<Longrightarrow> ok n (is @ [LOADI _]) (n' + 1)" |
ok_LOAD: "ok n is n'  \<Longrightarrow> ok n (is @ [LOAD _]) (n' + 1)" |
(* when n' = 0 or 1, n' -1 would be not nat*)
ok_ADD: "ok n is (n' + 2)   \<Longrightarrow> ok n (is @ [ADD]) (n' + 1)"

(*
lemma "length (exec is s stk) = Suc (Suc n') \<Longrightarrow>
       length (exec1 ADD s (exec is s stk)) = Suc n'"
  by (smt Nitpick.size_list_simp(2) add_diff_cancel_left' exec1.elims instr.distinct(3) instr.distinct(5) list.sel(3) nat.distinct(1) null_rec(1) null_rec(2) plus_1_eq_Suc)
*)


lemma "\<lbrakk>ok n is n'; length stk = n \<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"
  apply(induction rule: ok.induct)
    apply(auto simp add: exec_division)
  by (smt exec1.elims instr.distinct(3) instr.distinct(5) length_Cons list.size(3) nat.distinct(1) nat.inject)


 (* The followings are timed-out:
  by (smt exec1.elims instr.distinct(3) instr.distinct(5) length_Cons list.size(3) nat.distinct(1) nat.inject)
  by (smt Nitpick.size_list_simp(2) add_left_cancel exec1.elims instr.distinct(3) instr.distinct(5) length_Cons nat.distinct(1) plus_1_eq_Suc)
*)

(* the followings are copied and pasted from following github:
https://github.com/cmr/ConcreteSemantics/blob/master/CS_Ch4.thy

I couldn't understand what have done and how to know this proof.
*)

(* TODO: try again!*)
lemma ok_append: "ok n (e2) n' \<Longrightarrow> ok n'' (e1) n \<Longrightarrow> ok n'' (e1 @ e2) n'"
apply(induction rule: ok.induct)
apply(simp)
apply (metis append_assoc ok.simps)
apply (metis append_assoc ok.simps)
apply (metis append_assoc ok.simps)
done


lemma "ok n (comp x) (Suc n)"
apply(induction x arbitrary: n)

using ok_LOADI ok_emp apply fastforce
using ok_LOAD ok_emp apply fastforce
using ok_ADD ok_append apply fastforce
  done

end