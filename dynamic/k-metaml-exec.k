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

  syntax Term ::= Sym(Id) | Real(Term)
  syntax Term ::= "%" Term

  syntax CType ::= "$tag$v" | "$tag$e"
  syntax KItem ::= conv(Term, CType)
  syntax KItem ::= "EOE"


  syntax KResult ::= Term

  configuration <k> $PGM:Program ~> EOE </k>
                <level> 0 </level>
                <venv> $VENV:Map </venv>


  syntax KItem ::= isValue(Term, Int)   [function, boolOperation]

  rule isValue(Int, N) => true
  rule isValue(Id,  N) => true

  rule isValue(fn X:Id => E:Term, 0) => true
  rule isValue(< E:Term >       , 0) => true when isValue(E, 1)

  rule isValue(E1:Term E2:Term, 1) => true when isValue(E1, 1) andBool isValue(E2, 1)
  rule isValue(fn X:Id => E:Term, 1) => true when isValue(E, 1)
  rule isValue(< E:Term >, 1) => true when isValue(E, 2)
  rule isValue(run E:Term, 1) => true when isValue(E, 1)

  rule isValue(E1:Term E2:Term, N2) => true when N2 >=Int 2 andBool isValue(E1, N2) andBool isValue(E2, N2)
  rule isValue(fn X:Id => E:Term, N2) => true when N2 >=Int 2 andBool isValue(E, N2)
  rule isValue(< E:Term >, N2) => true when N2 >=Int 2 andBool isValue(E, N2 +Int 1)
  rule isValue(~ E:Term, N2) => true when N2 >=Int 2 andBool isValue(E, N2 -Int 1)
  rule isValue(run E:Term, N2) => true when N2 >=Int 2 andBool isValue(E, N2)

  rule isValue(_, _) => false


  syntax KItem ::= sup(Term)
  rule <k> sup(E) => conv(E, $tag$v) ... </k>
       <level> N </level>
       when isValue(E, N)
       [structural]

  rule <k> sup(E) => conv(E, $tag$e) ... </k>
       <level> N </level>
       when notBool isValue(E, N)
       [structural]


  // Top level
  syntax KItem ::= valMid(Id, Program) // Rest
  rule <k> val X:Id = E1:Term ; E2:Program => E1 ~> valMid(X, E2) ... </k>
       <level> 0 </level>

  rule <k> conv(V:Term, $tag$v) ~> valMid(X, E2) => E2 ... </k>
       <level> 0 </level>
       <venv> VEnv => VEnv[X <- Real(V)] </venv>


  // Termination
  rule <k> conv(V, $tag$v) ~> EOE => V ... </k>
       <level> 0 => -1 </level>

  rule <k> _:Empty ~> EOE => ():Unit ... </k>
       <level> 0 => -1 </level>


  // Int
  rule <k> I:Int => conv(I, $tag$v) ... </k>
       <level> N </level>
       when N >=Int 0


  // AExp
  syntax KItem ::= binOP1(String, Term) | binOP2(Term, String)

  rule <k> T1:Term + T2:Term => T1 ~> binOP1("+", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule <k> T1:Term - T2:Term => T1 ~> binOP1("-", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule <k> T1:Term * T2:Term => T1 ~> binOP1("*", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule <k> T1:Term / T2:Term => T1 ~> binOP1("/", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule conv(T1:Term, _) ~> binOP1(Op, T2) => T2 ~> binOP2(T1, Op)   [structural]

  rule conv(T2, _) ~> binOP2(T1, "+") => conv(T1 + T2, $tag$e)     [structural]
  rule conv(I1:Int + I2:Int, _) => conv(I1 +Int I2, $tag$v)

  rule conv(T2, _) ~> binOP2(T1, "-") => conv(T1 - T2, $tag$e)     [structural]
  rule conv(I1:Int - I2:Int, _) => conv(I1 -Int I2, $tag$v)

  rule conv(T2, _) ~> binOP2(T1, "*") => conv(T1 * T2, $tag$e)     [structural]
  rule conv(I1:Int * I2:Int, _) => conv(I1 *Int I2, $tag$v)

  rule conv(T2, _) ~> binOP2(T1, "/") => conv(T1 / T2, $tag$e)     [structural]
  rule conv(I1:Int / I2:Int, _) => conv(I1 /Int I2, $tag$v) when I2 =/=Int 0


  // Abs 0
  rule fn X:Id (N Xs):Rest E:Term => fn X => (fn N Xs E) [macro]

  syntax KItem ::= abs0End(Id, Map, Int)
  rule <k> fn X:Id => E:Term => E ~> abs0End(!XX, VEnv, 0) ... </k>
       <level> 0 => 1 </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>

  rule <k> conv(E1, _) ~> abs0End(XX, VEnv, 0) => sup(fn XX => E1) ... </k>
       <level> 1 => 0 </level>
       <venv> _ => VEnv </venv>

  // Abs n+1
  rule <k> fn X:Id => E:Term => E ~> abs0End(!XX, VEnv, N) ... </k>
       <level> N </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>
       when N >=Int 1

  rule <k> conv(E1, _) ~> abs0End(XX, VEnv, N) => sup(fn XX => E1) ... </k>
       <level> N </level>
       <venv> _ => VEnv </venv>
       when N >=Int 1

  // App 0
  syntax KItem ::= app0First(Term, Map) | app0Med(Id, Term, Map) | app0End(Map)
  rule <k> E1:Term E2:Term => E1 ~> app0First(E2:Term, VEnv) ... </k>
       <venv> VEnv </venv>
       <level> 0 </level>

  rule <k> conv(fn X:Id => E:Term, _) ~> app0First(E2:Term, VEnv) => E2 ~> app0Med(X, E:Term, VEnv) ... </k>
       <level> 0 </level>

  rule <k> conv(V2:Term, $tag$v) ~> app0Med(X, E, VEnv) => E ~> app0End(VEnv) ... </k>
       <level> 0 </level>
       <venv> _ => .Map[X <- Real(V2)] </venv>

  rule <k> conv(V:Term, $tag$v) ~> app0End(VEnv) => conv(V, $tag$v) ... </k>
       <level> 0 </level>
       <venv> _ => VEnv </venv>


  // App n+1
  syntax KItem ::= appNFirst(Term, Int) | appNEnd(Term, Int)
  rule <k> E1:Term E2:Term => E1 ~> appNFirst(E2, N) ... </k>
       <level> N </level>
       when N >=Int 1

  rule <k> conv(E3:Term, _) ~> appNFirst(E2, N) => E2 ~> appNEnd(E3, N) ... </k>
       <level> N </level>
       when N >=Int 1

  rule <k> conv(E4:Term, _) ~> appNEnd(E3, N) => sup(E3 E4) ... </k>
       <level> N </level>
       when N >=Int 1


  // Var 0
  rule <k> X:Id => sup(V) ... </k>
       <venv> ... X |-> Real(V) ... </venv>
       <level> 0 </level>

  // SVar n+1
  rule <k> X:Id => sup(X) ... </k>
       <venv> VEnv </venv>
       <level> N </level>
       when N >=Int 1 andBool notBool(X in keys(VEnv))

  rule <k> X:Id => sup(XX) ... </k>
       <venv> ... X |-> Sym(XX) ... </venv>
       <level> N </level>
       when N >=Int 1

  // RVar n+1
  rule <k> X:Id => sup(%V) ... </k>
       <venv> ... X |-> Real(V) ... </venv>
       <level> N </level>
       when N >=Int 1


  // Bracket 0
  syntax KItem ::= brkEnd0(Int)
  rule <k> < E1:Term > => E1 ~> brkEnd0(0) ... </k>
       <level> 0 => 1 </level>
  rule <k> conv(E2:Term, _) ~> brkEnd0(0) => sup(< E2 >) ... </k>
       <level> 1 => 0 </level>

  // Bracket n+1
  syntax KItem ::= brkEndN(Int)
  rule <k> < E1:Term > => E1 ~> brkEndN(N) ... </k>
       <level> N => N +Int 1 </level>
       when N >=Int 1
  rule <k> conv(E2:Term, _) ~> brkEndN(N) => sup(< E2 >) ... </k>
       <level> BN => N </level>
       when (N >=Int 1) andBool (BN ==Int (N +Int 1))


  // Escape 1
  syntax KItem ::= escEnd(Int)
  rule <k> ~ E1:Term => E1 ~> escEnd(1) ... </k>
       <level> 1 => 0 </level>
  rule <k> conv(< E2:Term >, _) ~> escEnd(1) => sup(E2) ... </k>
       <level> 0 => 1 </level>

  // Escape n+2
  rule <k> ~ E1:Term => E1 ~> escEnd(N) ... </k>
       <level> N => N -Int 1 </level>
       when N >=Int 2
  rule <k> conv(E2, _) ~> escEnd(N) => sup(~ E2) ... </k>
       <level> BN => N </level>
       when (N >=Int 2) andBool (BN ==Int (N -Int 1))


  // Run 0
  syntax KItem ::= runMid(Int) | runEnd(Int, Map)
  rule <k> run E:Term => E ~> runMid(0) ~> runEnd(0, VEnv) ... </k>
       <level> 0 </level>
       <venv> VEnv </venv>
  rule <k> conv(< E1:Term >, _) ~> runMid(0) => E1 ... </k>
       <level> 0 </level>
       <venv> _ => .Map </venv>
  rule <k> conv(V:Term, $tag$v) ~> runEnd(0, VEnv) => conv(V, $tag$v) ... </k>
       <level> 0 </level>
       <venv> _ => VEnv </venv>

  // Run n+1
  syntax KItem ::= runEndNP(Int)
  rule <k> run E1:Term => E1 ~> runEndNP(N) ... </k>
       <level> N </level>
       <venv> VEnv </venv>
       when N >=Int 1
  rule <k> conv(E2, _):Term ~> (runEndNP(N) => .) ... </k>
       <level> N </level>
       when N >=Int 1


  // Constant 0
  syntax KItem ::= constEnd0(Int)
  rule <k> %V => V ~> constEnd0(0) ... </k>
       <level> 0 </level>
  rule <k> conv(V, $tag$v) ~> (constEnd0(0) => .) ... </k>
       <level> 0 </level>

  // Constant n+1
  syntax KItem ::= constEndN(Int)
  rule <k> %V => V ~> constEndN(0) ... </k>
       <level> N </level>
       when N >=Int 1
  rule <k> conv(V, $tag$v) ~> constEndN(0) => sup(%V) ... </k>
       <level> N </level>
       when N >=Int 1

endmodule
