//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "../k-metaml-syntax.k"

module K-METAML-EXEC
  imports K-METAML-SYNTAX

  syntax Value ::= "<" Term ">"

  syntax Term ::= Sym(Id) | Real(Value)
  syntax Term ::= "%" Value

  syntax Term ::= conv(Term)
  syntax Term ::= "EOE"

  syntax KResult ::= Term

  configuration <k> $PGM:Term ~> EOE </k>
                <level> 0 </level>
                <venv> $VENV:Map </venv>


  // Termination
  rule <k> conv(V:Value) ~> EOE => V ... </k>
       <level> 0 => -1 </level>


// Int
  rule <k> I:Int => conv(I) ... </k>
       <level> N </level>
       when N >=Int 0


  // AExp
  syntax KItem ::= binOP1(String, Term) | binOP2(Term, String)
  rule <k> T1:Term + T2:Term => T1 ~> binOP1("+", T2) ... </k>
       <level> N </level>
       when N >=Int 0

  rule conv(T1) ~> binOP1(Op:String, T2) => T2 ~> binOP2(T1, Op)    [structural]

  rule conv(T2) ~> binOP2(T1, "+") => conv(T1 + T2)                 [structural]
  rule conv(I1:Int + I2:Int) => conv(I1 +Int I2)


  // Abs 0
  syntax KItem ::= abs0End(Id, Map, Int)
  rule <k> lambda X:Id . E:Term => E ~> abs0End(!XX, VEnv, 0) ... </k>
       <level> 0 => 1 </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>

  rule <k> conv(E1) ~> abs0End(XX, VEnv, 0) => conv(lambda XX . E1) ... </k>
       <level> 1 => 0 </level>
       <venv> _ => VEnv </venv>

  // Abs n+1
  rule <k> lambda X:Id . E:Term => E ~> abs0End(!XX, VEnv, N) ... </k>
       <level> N </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>
       when N >=Int 1

  rule <k> conv(E1) ~> abs0End(XX, VEnv, N) => conv(lambda XX . E1) ... </k>
       <level> N </level>
       <venv> _ => VEnv </venv>
       when N >=Int 1


  // App 0
  syntax KItem ::= app0First(Term, Map) | app0Med(Id, Term, Map) | app0End(Map)
  rule <k> E1:Term E2:Term => E1 ~> app0First(E2:Term, VEnv) ... </k>
       <venv> VEnv </venv>
       <level> 0 </level>

  rule <k> conv(lambda X:Id . E:Term) ~> app0First(E2:Term, VEnv) => E2 ~> app0Med(X, E:Term, VEnv) ... </k>
       <level> 0 </level>

  rule <k> conv(V2:Value) ~> app0Med(X, E, VEnv) => E ~> app0End(VEnv) ... </k>
       <level> 0 </level>
       <venv> _ => .Map[X <- Real(V2)] </venv>

  rule <k> conv(V:Value) ~> (app0End(VEnv) => .) ... </k>
       <level> 0 </level>
       <venv> _ => VEnv </venv>

  // App n+1
  syntax KItem ::= appNFirst(Term, Int) | appNEnd(Term, Int)
  rule <k> E1:Term E2:Term => E1 ~> appNFirst(E2, N) ... </k>
       <level> N </level>
       when N >=Int 1

  rule <k> conv(E3:Term) ~> appNFirst(E2, N) => E2 ~> appNEnd(E3, N) ... </k>
       <level> N </level>
       when N >=Int 1

  rule <k> conv(E4:Term) ~> appNEnd(E3, N) => conv(E3 E4) ... </k>
       <level> N </level>
       when N >=Int 1


  // Var 0
  rule <k> X:Id => conv(V) ... </k>
       <venv> ... X |-> Real(V) ... </venv>
       <level> 0 </level>

  // SVar n+1
  rule <k> X:Id => conv(X) ... </k>
       <venv> VEnv </venv>
       <level> N </level>
       when N >=Int 1 andBool notBool(X in keys(VEnv))

  rule <k> X:Id => conv(XX) ... </k>
       <venv> ... X |-> Sym(XX) ... </venv>
       <level> N </level>
       when N >=Int 1

  // RVar n+1
  rule <k> X:Id => conv(%V) ... </k>
       <venv> ... X |-> Real(V) ... </venv>
       <level> N </level>
       when N >=Int 1


  // Bracket 0
  syntax KItem ::= brkEnd(Int)
  rule <k> < E1:Term > => E1 ~> brkEnd(0) ... </k>
       <level> 0 => 1 </level>
  rule <k> conv(E2:Term) ~> brkEnd(0) => conv(< E2 >) ... </k>
       <level> 1 => 0 </level>

  // Bracket n+1
  rule <k> < E1:Term > => E1 ~> brkEnd(N) ... </k>
       <level> N => N +Int 1 </level>
       when N >=Int 1
  rule <k> conv(E2:Term) ~> brkEnd(N) => conv(< E2 >) ... </k>
       <level> BN => N </level>
       when (N >=Int 1) andBool (BN ==Int (N +Int 1))


  // Escape 1
  syntax KItem ::= escEnd(Int)
  rule <k> ~ E1:Term => E1 ~> escEnd(1) ... </k>
       <level> 1 => 0 </level>
  rule <k> conv(< E2:Term >) ~> escEnd(1) => conv(E2) ... </k>
       <level> 0 => 1 </level>

  // Escape n+2
  rule <k> ~ E1:Term => E1 ~> escEnd(N) ... </k>
       <level> N => N -Int 1 </level>
       when N >=Int 2
  rule <k> conv(E2) ~> escEnd(N) => conv(~E2) ... </k>
       <level> BN => N </level>
       when (N >=Int 2) andBool (BN ==Int (N -Int 1))


  // Run 0
  syntax KItem ::= runMid(Int) | runEnd(Int, Map)
  rule <k> run E:Term => E ~> runMid(0) ~> runEnd(0, VEnv) ... </k>
       <level> 0 </level>
       <venv> VEnv </venv>
  rule <k> conv(< E1:Term >) ~> runMid(0) => E1 ... </k>
       <level> 0 </level>
       <venv> _ => .Map </venv>
  rule <k> conv(V:Value) ~> runEnd(0, VEnv) => conv(V) ... </k>
       <level> 0 </level>
       <venv> _ => VEnv </venv>

  // Run n+1
  syntax KItem ::= runEndNP(Int)
  rule <k> run E1:Term => E1 ~> runEndNP(N) ... </k>
       <level> N </level>
       <venv> VEnv </venv>
       when N >=Int 1
  rule <k> conv(E2):Term ~> (runEndNP(N) => .) ... </k>
       <level> N </level>
       when N >=Int 1


  // Constatnt 0
  syntax KItem ::= constEnd(Int)
  rule <k> %V:Value => V ~> constEnd(0) ... </k>
       <level> 0 </level>
  rule <k> conv(V:Value) ~> (constEnd(0) => .) ... </k>
       <level> 0 </level>

  // Constatnt n+1
  rule <k> %V:Value => V ~> constEnd(0) ... </k>
       <level> N </level>
       when N >=Int 1
  rule <k> conv(V:Value) ~> constEnd(0) => conv(%V) ... </k>
       <level> N </level>
       when N >=Int 1
endmodule
