theory Concrete_Semantics_3_3
  imports Main
begin

(* from 3.1 and 3.2 *) 

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val" 

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s" 

(* ----- *)

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

(* we argue about the case of stack, so the following warning is dismissed:
Missing patterns in function definition:
\<And>b. exec1 ADD b [] = undefined
\<And>b v. exec1 ADD b [v] = undefined
*)
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

fun comp:: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma "exec (comp a) s stk = aval a s # stk"
  apply(induction a arbitrary:stk)
    apply(auto simp add: exec_division)
  done

fun mexec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"mexec1 (LOADI n) _ stk = Some (n # stk)" |
"mexec1 (LOAD x) s stk = Some(s(x) # stk)" |
"mexec1 ADD _ (j # i # stk) = Some((i + j) # stk)" |
"mexec1 ADD _ _ = None"

(* case stk is None or Some *)
fun mexec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"mexec [] _ stk = Some(stk)" |
"mexec (i#is) s stk = (case (mexec1 i s stk) of Some stk' \<Rightarrow> mexec is s stk' | 
None \<Rightarrow> None)"

fun mcomp:: "aexp \<Rightarrow> instr list" where
"mcomp (N n) = [LOADI n]" |
"mcomp (V x) = [LOAD x]" |
"mcomp (Plus e1 e2) = mcomp e1 @ mcomp e2 @ [ADD]"

(* add condition to exec_division 
 *)
lemma mexec_division:"mexec a1 s stk = Some stk' \<Longrightarrow> mexec (a1 @ a2) s stk = mexec a2 s stk'"
  apply(induction a1 arbitrary:stk)
  apply(auto)
  by (metis option.case_eq_if option.simps(3))

lemma "mexec (mcomp a) s stk = Some(aval a s # stk)"
  apply(induction a arbitrary:stk)
    apply(auto simp add: mexec_division)
  done

(* ex 3.11 *)

type_synonym reg = nat

datatype r_instr = LDI int reg | LD vname reg | ADD reg reg

fun rexec1 :: "r_instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec1 (LDI i r1) _ f  = f(r1 := i)" |
"rexec1 (LD x r1) s f = f(r1 := s(x))" |
"rexec1 (ADD r1 r2) s f = f(r1:= (f r1) + (f r2))"

fun rexec :: "r_instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec [] _ f = f" |
"rexec (r#rs) s f = rexec rs s (rexec1 r s f)"

(* I don't undestand about register machine enough.
Why (r + 1) is needed? \<rightarrow> the answer might be that each register machines is different?
 *)
fun rcomp:: "aexp \<Rightarrow> reg \<Rightarrow> r_instr list" where
"rcomp (N n) r = [LDI n r]" |
"rcomp (V x) r = [LD x r]" |
"rcomp (Plus e1 e2) r = rcomp e1 r @ rcomp e2 (r + 1) @ [ADD r (r + 1)]"


lemma rexec_division:"rexec (a1 @ a2) s e = rexec a2 s (rexec a1 s e)"
  apply(induction a1 arbitrary: s e)
  apply(auto)
  done

(* 
The following lemma is not needed. And in this proof I found the above lemma.
lemma "rexec (rcomp a1 r @ rcomp a2 (Suc r) @ [ADD r (Suc r)]) s e r 
= aval a1 s + aval a2 s"
  apply(induction a1 arbitrary:s r e)
  done
*)


(* Do not misunderstand to use which of r and q*)
lemma min_number_of_reg_is_prior:"r < q \<Longrightarrow> rexec (rcomp a q) s f r = f r"
  apply(induction a arbitrary: q f)
    apply(auto simp add:rexec_division)
  done

(* NOTE: "The registers > r should be used in a stack-like fashion for intermediate results,
 the ones < r should be left alone."*)
lemma min_number_of_reg_is_aval: "rexec (rcomp a2 (Suc r)) s (rexec (rcomp a1 r) s e) r = aval a1 s"
  apply(induction a1 arbitrary: s e r)
    apply(auto simp add: rexec_division min_number_of_reg_is_prior)
  done

(* counter examples occurs at
- "(rexec (rcomp a r1) s e) r2 = aval a s"
*)
lemma "(rexec (rcomp a r) s e) r = aval a s"
  apply(induction a arbitrary:s r e)
    apply(auto simp add: rexec_division min_number_of_reg_is_aval)
  done


(* Exercise 3.12 *)

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun lexec1 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"lexec1 (LDI0 i) _ f  = f(0 := i)" |
"lexec1 (LD0 x) s f = f(0 := s(x))" |
"lexec1 (MV0 r1) s f = f(r1 := f(0))" |
"lexec1 (ADD0 r1 ) s f = f(0:= (f 0) + (f r1))"

fun lexec :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"lexec [] _ f = f" |
"lexec (r#rs) s f = lexec rs s (lexec1 r s f)"

(* I don't undestand about register machine enough.
Why (r + 1) is needed? \<rightarrow> the answer might be that each register machines is different?
 *)
fun lcomp:: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"lcomp (N n) r = [LDI0 n]" |
"lcomp (V x) r = [LD0 x]" |
"lcomp (Plus e1 e2) r = (lcomp e1 (r + 1)@ [MV0 (r + 1)]  @ lcomp e2 (r + 2) @ [ADD0 (r + 1)])"

lemma lexec_division:"lexec (a1 @ a2) s e = lexec a2 s (lexec a1 s e)"
  apply(induction a1 arbitrary: s e)
  apply(auto)
  done

lemma min_number_of_reg0_is_prior:"0 < r \<Longrightarrow> r < q \<Longrightarrow> lexec (lcomp a q) s f r = f r"
  apply(induction a arbitrary: q f)
    apply(auto simp add:lexec_division)
  done

lemma "lexec (lcomp a r) s rs 0 = aval a s"
  apply(induction a arbitrary: r s rs)
  apply(auto simp add:lexec_division min_number_of_reg0_is_prior)
  done

end