section "IMP --- A Simple Imperative Language"

theory Com imports "~~/src/HOL/IMP/BExp" begin

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Throw                (*what is type of exception and its order? -> nothing. cf: http://www21.in.tum.de/~nipkow/Concrete-Semantics/Exercises/exercises.pdf *)
      | Try    com  com         ("(TRY _/ CATCH _)"  [0, 61] 60)

end