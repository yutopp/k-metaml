//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "../k-metaml-syntax.k"

module K-METAML-EXEC-SYNTAX-EXTEND
  imports K-METAML-SYNTAX

  syntax CType ::= "$tag$v" | "$tag$e"
  syntax KItem ::= "$conv" "(" Term "," CType ")"
  syntax KItem ::= "EOE"


  syntax Term ::= Sym(Id) | Real(Term)
  syntax Term ::= "%" "(" Term "," Term ")"     // Symbol, Constant

  syntax Term ::= "$mu" Id "=>" Term

  syntax Term ::= "$builtin_fn" "(" BuiltinFn ")"
  syntax Term ::= "$run_builtin" "(" BuiltinFn "," Term ")"

  syntax KItem ::= isValue(Term, Int)   [function, boolOperation]

  rule isValue(Int,  N) => true
  rule isValue(Bool, N) => true
  rule isValue(Id,   N) => true
  rule isValue(Unit, N) => true
  rule isValue([ (E, Es):ListElems ], N) => isValue([Es], N)
       when isValue(E, N)
  rule isValue([ .ListElems ], N) => true
  rule isValue($builtin_fn(_:BuiltinFn), N) => true

  rule isValue(fn X:Id => E:Term, 0) => true
  rule isValue($mu X:Id => E:Term, 0) => true
  rule isValue(< E:Term >       , 0) => true when isValue(E, 1)

  rule isValue(E1:Term E2:Term, 1) => true when isValue(E1, 1) andBool isValue(E2, 1)
  rule isValue(fn X:Id => E:Term, 1) => true when isValue(E, 1)
  rule isValue($mu X:Id => E:Term, 1) => true when isValue(E, 1)
  rule isValue(< E:Term >, 1) => true when isValue(E, 2)
  rule isValue(run E:Term, 1) => true when isValue(E, 1)

  rule isValue(E1:Term E2:Term, N2) => true when N2 >=Int 2 andBool isValue(E1, N2) andBool isValue(E2, N2)
  rule isValue(fn X:Id => E:Term, N2) => true when N2 >=Int 2 andBool isValue(E, N2)
  rule isValue($mu X:Id => E:Term, N2) => true when N2 >=Int 2 andBool isValue(E, N2)
  rule isValue(< E:Term >, N2) => true when N2 >=Int 2 andBool isValue(E, N2 +Int 1)
  rule isValue(~ E:Term, N2) => true when N2 >=Int 2 andBool isValue(E, N2 -Int 1)
  rule isValue(run E:Term, N2) => true when N2 >=Int 2 andBool isValue(E, N2)

  rule isValue(_, _) => false


  syntax KItem ::= sup(Term)
  rule <k> sup(E) => $conv(E, $tag$v) ... </k>
       <level> N </level>
       when isValue(E, N)
       [structural]

  rule <k> sup(E) => $conv(E, $tag$e) ... </k>
       <level> N </level>
       when notBool isValue(E, N)
       [structural]
endmodule