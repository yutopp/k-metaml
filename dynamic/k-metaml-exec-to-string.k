//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "k-metaml-exec-syntax.k"

module K-METAML-EXEC-TO-STRING
  imports K-METAML-EXEC-SYNTAX-EXTEND

  syntax String ::= "Bool2String" "(" Bool ")"  [function, klabel(Bool2String)]
  rule Bool2String(true) => "true"
  rule Bool2String(false) => "false"

  syntax String ::= "Term2String" "(" Term ")"  [function, klabel(Term2String)]
  rule Term2String(V:Int) => Int2String(V)
  rule Term2String(V:Bool) => Bool2String(V)
  rule Term2String(V:Id) => Id2String(V)
  rule Term2String(V:Unit) => "()"

  //rule Term2String((E:Term)) => "(" +String Term2String(E) +String ")"

  rule Term2String(~ E:Term) => "~(" +String Term2String(E) +String ")"
  rule Term2String(E1:Term E2:Term) => Term2String(E1) +String " " +String Term2String(E2)

  rule Term2String(< E:Term >) => "<" +String Term2String(E) +String ">"

  rule Term2String(E1:Term * E2:Term) =>
        "(" +String Term2String(E1) +String " * " +String Term2String(E2) +String ")"
  rule Term2String(E1:Term / E2:Term) =>
        "(" +String Term2String(E1) +String " / " +String Term2String(E2) +String ")"
  rule Term2String(E1:Term + E2:Term) =>
        "(" +String Term2String(E1) +String " + " +String Term2String(E2) +String ")"
  rule Term2String(E1:Term - E2:Term) =>
        "(" +String Term2String(E1) +String " - " +String Term2String(E2) +String ")"
  rule Term2String(E1:Term = E2:Term) =>
        "(" +String Term2String(E1) +String " = " +String Term2String(E2) +String ")"
  rule Term2String(E1:Term '>' E2:Term) =>
        "(" +String Term2String(E1) +String " '>' " +String Term2String(E2) +String ")"
  rule Term2String(E1:Term '<' E2:Term) =>
        "(" +String Term2String(E1) +String " '<' " +String Term2String(E2) +String ")"

  rule Term2String(if E1:Term then E2:Term else E3:Term) =>
                      "if " +String Term2String(E1) +String " then " +String Term2String(E2) +String " else " +String Term2String(E3)

  rule Term2String(fn P:Id Ps:FnParamRest E:Term) =>
        "fn " +String Id2String(P) +String Params2String(Ps) +String Term2String(E)

  rule Term2String($mu P:Id => E:Term) =>
        "fn " +String Id2String(P) +String " => " +String Term2String(E)

  rule Term2String(run E:Term) => "(run" +String Term2String(E) +String ")"
  rule Term2String(lift E:Term) => "(lift" +String Term2String(E) +String ")"

  rule Term2String(%(X:Term, E:Term)) => "%" +String Term2String(X) // Show symbol

  rule Term2String(hd:BuiltinFn) => "hd"
  rule Term2String(tl:BuiltinFn) => "tl"
  rule Term2String(null:BuiltinFn) => "null"
  rule Term2String(nth:BuiltinFn) => "nth"
  rule Term2String(nthArg1(E):BuiltinFn) => "nth " +String Term2String(E)

  rule Term2String($builtin_fn(Bf:BuiltinFn)) => Term2String(Bf)


  syntax String ::= "Params2String" "(" FnParamRest ")"  [function, klabel(Params2String)]
  rule Params2String(P:Id Ps:FnParamRest) => Id2String(P) +String " " +String Params2String(Ps)
  rule Params2String(=>:FnParamRest) => " => "
endmodule