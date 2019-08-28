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

fun mexec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"mexec [] _ stk = Some(stk)" |
"mexec (i#is) s stk = mexec is s (mexec1 i s stk)"


end