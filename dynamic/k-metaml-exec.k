//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "k-metaml-exec-syntax.k"
require "k-metaml-exec-to-string.k"
require "modules/substitution.k"

module K-METAML-EXEC
  imports K-METAML-EXEC-SYNTAX-EXTEND
  imports K-METAML-EXEC-TO-STRING
  imports SUBSTITUTION

  syntax KResult ::= Term
  syntax Variable ::= Id    // Variable is used in SUBSTITUTION

  configuration <k> $PGM:Program ~> EOE </k>
                <level> 0 </level>
                <venv> $VENV:Map </venv>
                <out color="green" stream="stdout"> .List </out>


  // Top level
  syntax KItem ::= valMid(Id, Program) // Rest
  rule <k> val X:Id = E1:Term ; E2:Program => E1 ~> valMid(X, E2) ... </k>
       <level> 0 </level>

  rule <k> $conv(V:Term, $tag$v) ~> valMid(X, E2) => E2 ... </k>
       <level> 0 </level>
       <venv> VEnv => VEnv[X <- Real(V)] </venv>
       <out> ... .List => ListItem("val " +String Id2String(X) +String " = " +String Term2String(V) +String "\n") </out>


  // Top level : fun
  rule fun X:Id ( P:Id, Px:FunParams ) = E:Term ; E2:Program
           => val X = ($mu X => ($fn_impl (P, Px) = E)) ; E2      [macro]

  syntax Term ::= "$fn_impl" FunParams "=" Term
  rule $fn_impl (X:Id, Xs:FunParams) = E:Term =>
                fn X (=>) ($fn_impl (Xs) = E)       [macro]
  rule $fn_impl (.FunParams) = E:Term => E          [macro]


  // Termination
  rule <k> $conv(V, $tag$v) ~> EOE => V ... </k>
       <level> 0 => -1 </level>

  rule <k> _:Empty ~> EOE => ():Unit ... </k>
       <level> 0 => -1 </level>


  // Int
  rule <k> I:Int => $conv(I, $tag$v) ... </k>
       <level> N </level>
       when N >=Int 0

  // Bool
  rule <k> B:Bool => $conv(B, $tag$v) ... </k>
       <level> N </level>
       when N >=Int 0

  // Unit
  rule <k> U:Unit => $conv(U, $tag$v) ... </k>
       <level> N </level>
       when N >=Int 0

  rule <k> $builtin_fn(F:BuiltinFn) => sup($builtin_fn(F)) ... </k>
       <level> N </level>
       when N >=Int 0


  // List
  syntax KItem ::= "listTerm" Int "|" ListElems "|" List  // Level, Src, Trg
  rule <k> [ (E, Es):ListElems ] => E ~> (listTerm N | Es | .List) ... </k>
       <level> N </level>
       when N >=Int 0
  rule <k> $conv(R:Term, _) ~> (listTerm N | (E, Es):ListElems | Ts:List) =>
             E ~> (listTerm N | (Es:ListElems) | Ts ListItem(R)) ... </k>
       <level> N </level>
       when N >=Int 0
  rule <k> $conv(R, _) ~> (listTerm N | .ListElems | Ts:List) =>
             sup([toMLList(Ts ListItem(R))]) ... </k>
       <level> N </level>
       when N >=Int 0

  syntax KItem ::= toMLList(List) [function]
  rule toMLList(ListItem(X) Xs:List) => (X, toMLList(Xs)):ListElems
  rule toMLList(.List) => .ListElems


  // BinOp
  syntax KItem ::= binOP1(String, Term) | binOP2(Term, String)
  rule $conv(T1:Term, _) ~> binOP1(Op, T2) => T2 ~> binOP2(T1, Op)   [structural]

  rule <k> T1:Term + T2:Term => T1 ~> binOP1("+", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule $conv(T2, _) ~> binOP2(T1, "+") => $conv(T1 + T2, $tag$e)     [structural]
  rule $conv(I1:Int + I2:Int, _) => $conv(I1 +Int I2, $tag$v)

  rule <k> T1:Term - T2:Term => T1 ~> binOP1("-", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule $conv(T2, _) ~> binOP2(T1, "-") => $conv(T1 - T2, $tag$e)     [structural]
  rule $conv(I1:Int - I2:Int, _) => $conv(I1 -Int I2, $tag$v)

  rule <k> T1:Term * T2:Term => T1 ~> binOP1("*", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule $conv(T2, _) ~> binOP2(T1, "*") => $conv(T1 * T2, $tag$e)     [structural]
  rule $conv(I1:Int * I2:Int, _) => $conv(I1 *Int I2, $tag$v)

  rule <k> T1:Term / T2:Term => T1 ~> binOP1("/", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule $conv(T2, _) ~> binOP2(T1, "/") => $conv(T1 / T2, $tag$e)     [structural]
  rule $conv(I1:Int / I2:Int, _) => $conv(I1 /Int I2, $tag$v) when I2 =/=Int 0

  rule <k> T1:Term = T2:Term => T1 ~> binOP1("=", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule $conv(T2, _) ~> binOP2(T1, "=") => $conv(T1 = T2, $tag$e)     [structural]
  rule $conv(I1:Int = I2:Int, _) => $conv(I1 =Int I2, $tag$v)

  rule <k> T1:Term '>' T2:Term => T1 ~> binOP1(">", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule $conv(T2, _) ~> binOP2(T1, ">") => $conv(T1 '>' T2, $tag$e)     [structural]
  rule $conv(I1:Int '>' I2:Int, _) => $conv(I1 >Int I2, $tag$v)

  rule <k> T1:Term '<' T2:Term => T1 ~> binOP1("<", T2) ... </k>
       <level> N </level>
       when N >=Int 0
  rule $conv(T2, _) ~> binOP2(T1, "<") => $conv(T1 '<' T2, $tag$e)     [structural]
  rule $conv(I1:Int '<' I2:Int, _) => $conv(I1 <Int I2, $tag$v)


  // if
  syntax KItem ::= ifCond(Term, Term)
  rule if C:Term then E1:Term else E2:Term => C ~> ifCond(E1, E2)   [structural]
  rule <k> $conv(true, $tag$v)  ~> ifCond(E1, E2) => E1 ... </k>
       <level> 0 </level>   [structural]
  rule <k> $conv(false, $tag$v) ~> ifCond(E1, E2) => E2 ... </k>
       <level> 0 </level>   [structural]

  syntax KItem ::= ifThenN(Term, Term, Int) | ifElseN(Term, Term, Int)
  rule <k> $conv(C, _) ~> ifCond(E1, E2) => E1 ~> ifThenN(C, E2, N) ... </k>
       <level> N </level>
       when N >=Int 1   [structural]

  rule <k> $conv(E1, _) ~> ifThenN(C, E2, N) => E2 ~> ifElseN(C, E1, N) ... </k>
       <level> N </level>
       when N >=Int 1   [structural]

  rule <k> $conv(E2, _) ~> ifElseN(C, E1, N) => sup(if C then E1 else E2) ... </k>
       <level> N </level>
       when N >=Int 1   [structural]


  // Abs 0
  rule fn X:Id (N Xs):FnParamRest E:Term => fn X => (fn N Xs E) [macro]

  syntax KItem ::= abs0End(Id, Map, Int)
  rule <k> fn X:Id => E:Term => E ~> abs0End(!XX, VEnv, 0) ... </k>
       <level> 0 => 1 </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>

  rule <k> $conv(E1, _) ~> abs0End(XX, VEnv, 0) => sup(fn XX => E1) ... </k>
       <level> 1 => 0 </level>
       <venv> _ => VEnv </venv>

  syntax KItem ::= abs0EndMu(Id, Map, Int)
  rule <k> $mu X:Id => E:Term => E ~> abs0EndMu(!XX, VEnv, 0) ... </k>
       <level> 0 => 1 </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>

  rule <k> $conv(E1, _) ~> abs0EndMu(XX, VEnv, 0) =>
                    sup($mu XX => E1) ... </k>
       <level> 1 => 0 </level>
       <venv> _ => VEnv </venv>

  // Abs n+1
  syntax KItem ::= absNEnd(Id, Map, Int)
  rule <k> fn X:Id => E:Term => E ~> absNEnd(!XX, VEnv, N) ... </k>
       <level> N </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>
       when N >=Int 1

  rule <k> $conv(E1, _) ~> absNEnd(XX, VEnv, N) => sup(fn XX => E1) ... </k>
       <level> N </level>
       <venv> _ => VEnv </venv>
       when N >=Int 1

  syntax KItem ::= absNEndMu(Id, Map, Int)
  rule <k> $mu X:Id => E:Term => E ~> absNEndMu(!XX, VEnv, N) ... </k>
       <level> N </level>
       <venv> VEnv => VEnv[X <- Sym(!XX)] </venv>
       when N >=Int 1

  rule <k> $conv(E1, _) ~> absNEndMu(XX, VEnv, N) =>
                    sup($mu XX => E1) ... </k>
       <level> N </level>
       <venv> _ => VEnv </venv>
       when N >=Int 1


  // App 0
  syntax KItem ::= app0First(Term, Map) | app0Med(Id, Term, Map) | app0End(Map)
  rule <k> E1:Term E2:Term => E1 ~> app0First(E2:Term, VEnv) ... </k>
       <venv> VEnv </venv>
       <level> 0 </level>

  rule <k> $conv(fn X:Id => E:Term, _) ~> app0First(E2:Term, VEnv) => E2 ~> app0Med(X, E:Term, VEnv) ... </k>
       <level> 0 </level>
  rule <k> $conv(V2:Term, $tag$v) ~> app0Med(X, E, VEnv) => E ~> app0End(VEnv) ... </k>
       <level> 0 </level>
       <venv> _ => .Map[X <- Real(V2)] </venv>
  rule <k> $conv(V:Term, $tag$v) ~> app0End(VEnv) => $conv(V, $tag$v) ... </k>
       <level> 0 </level>
       <venv> _ => VEnv </venv>

  syntax KItem ::= app0MedMu(Id, Term, Map)  // Param, Body, VEnv
  rule <k> $conv($mu X:Id => E:Term, _) ~> app0First(E2:Term, VEnv) =>
                       sup(E[X |-> ($mu X => E)]) ~> app0First(E2:Term, VEnv) ... </k>
       <level> 0 </level>

  syntax KItem ::= app0MedBuiltin(BuiltinFn, Map)  // Name, VEnv
  rule <k> $conv($builtin_fn(BFn:BuiltinFn), _) ~> app0First(E2:Term, VEnv) =>
                 E2 ~> app0MedBuiltin(BFn, VEnv) ... </k>
       <level> 0 </level>
  rule <k> $conv(V2:Term, $tag$v) ~> app0MedBuiltin(BFn, VEnv) => $run_builtin(BFn, V2) ~> app0End(VEnv) ... </k>
       <level> 0 </level>
       <venv> _ => .Map </venv>

  // App n+1
  syntax KItem ::= appNFirst(Term, Int) | appNEnd(Term, Int)
  rule <k> E1:Term E2:Term => E1 ~> appNFirst(E2, N) ... </k>
       <level> N </level>
       when N >=Int 1

  rule <k> $conv(E3:Term, _) ~> appNFirst(E2, N) => E2 ~> appNEnd(E3, N) ... </k>
       <level> N </level>
       when N >=Int 1

  rule <k> $conv(E4:Term, _) ~> appNEnd(E3, N) => sup(E3 E4) ... </k>
       <level> N </level>
       when N >=Int 1


  // Var 0
  rule <k> X:Id => sup(V) ... </k>
       <venv> ... X |-> Real(V) ... </venv>
       <level> 0 </level>
  rule <k> X:BuiltinFn => sup($builtin_fn(X)) ... </k>
       <venv> VEnv </venv>
       <level> 0 </level>
       when notBool(X in keys(VEnv))

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
  rule <k> X:BuiltinFn => sup(%$builtin_fn(X)) ... </k>
       <venv> VEnv </venv>
       <level> N </level>
       when N >=Int 1 andBool notBool(X in keys(VEnv))


  // Bracket 0
  syntax KItem ::= "brkEnd0"
  rule <k> < E1:Term > => E1 ~> brkEnd0 ... </k>
       <level> 0 => 1 </level>
  rule <k> $conv(E2:Term, _) ~> brkEnd0 => sup(< E2 >) ... </k>
       <level> 1 => 0 </level>

  // Bracket n+1
  syntax KItem ::= brkEndN(Int)
  rule <k> < E1:Term > => E1 ~> brkEndN(N) ... </k>
       <level> N => N +Int 1 </level>
       when N >=Int 1
  rule <k> $conv(E2:Term, _) ~> brkEndN(N) => sup(< E2 >) ... </k>
       <level> BN => N </level>
       when (N >=Int 1) andBool (BN ==Int (N +Int 1))


  // Lift 0
  syntax KItem ::= "liftEnd0"
  rule <k> lift E1:Term => E1 ~> liftEnd0 ... </k>
       <level> 0 </level>
  rule <k> $conv(E2:Term, _) ~> liftEnd0 => sup(< E2 >) ... </k>
       <level> 0 </level>

  // Lift n+1
  syntax KItem ::= liftEndN(Int)
  rule <k> lift E1:Term => E1 ~> liftEndN(N) ... </k>
       <level> N </level>
       when N >=Int 1
  rule <k> $conv(E2:Term, _) ~> liftEndN(N) => sup(lift E2) ... </k>
       <level> N </level>
       when (N >=Int 1)


  // Escape 1
  syntax KItem ::= "escEnd0"
  rule <k> ~ E1:Term => E1 ~> escEnd0 ... </k>
       <level> 1 => 0 </level>
  rule <k> $conv(< E2:Term >, _) ~> escEnd0 => sup(E2) ... </k>
       <level> 0 => 1 </level>

  // Escape n+2
  syntax KItem ::= escEndN(Int)
  rule <k> ~ E1:Term => E1 ~> escEndN(N) ... </k>
       <level> N => N -Int 1 </level>
       when N >=Int 2
  // Escape n+2 (Optimized)
  rule <k> $conv(< E2:Term >, _) ~> escEndN(N) => sup(E2) ... </k>
       <level> BN => N </level>
       when (N >=Int 2) andBool (BN ==Int (N -Int 1))
  rule <k> $conv(E2:Term, _) ~> escEndN(N) => sup(~ E2) ... </k>
       <level> BN => N </level>
       when (N >=Int 2) andBool (BN ==Int (N -Int 1))


  // Run 0
  syntax KItem ::= runMid(Int) | runEnd(Int, Map)
  rule <k> run E:Term => E ~> runMid(0) ~> runEnd(0, VEnv) ... </k>
       <level> 0 </level>
       <venv> VEnv </venv>
  rule <k> $conv(< E1:Term >, _) ~> runMid(0) => E1 ... </k>
       <level> 0 </level>
       <venv> _ => .Map </venv>
  rule <k> $conv(V:Term, $tag$v) ~> runEnd(0, VEnv) => $conv(V, $tag$v) ... </k>
       <level> 0 </level>
       <venv> _ => VEnv </venv>

  // Run n+1
  syntax KItem ::= runEndNP(Int)
  rule <k> run E1:Term => E1 ~> runEndNP(N) ... </k>
       <level> N </level>
       <venv> VEnv </venv>
       when N >=Int 1
  rule <k> $conv(E2, _):Term ~> (runEndNP(N) => .) ... </k>
       <level> N </level>
       when N >=Int 1


  // Constant 0
  syntax KItem ::= constEnd0(Int)
  rule <k> %V => V ~> constEnd0(0) ... </k>
       <level> 0 </level>
  rule <k> $conv(V, $tag$v) ~> (constEnd0(0) => .) ... </k>
       <level> 0 </level>

  // Constant n+1
  syntax KItem ::= constEndN(Int)
  rule <k> %V => V ~> constEndN(0) ... </k>
       <level> N </level>
       when N >=Int 1
  rule <k> $conv(V, $tag$v) ~> constEndN(0) => sup(%V) ... </k>
       <level> N </level>
       when N >=Int 1


  // --- Builtins ---

  // head
  rule $run_builtin(hd, [(X, Xs):ListElems]) => sup(X)

  // tail
  rule $run_builtin(tl, [(X, Xs):ListElems]) => sup([Xs])

  // null
  rule $run_builtin(null, [(X, Xs):ListElems]) => sup(false)
  rule $run_builtin(null, [.ListElems])        => sup(true)

  // nth V N
  rule $run_builtin(nth, V:Term)                       => sup($builtin_fn(nthArg1(V)))
  rule $run_builtin(nthArg1([X, Xs:ListElems]), 0)     => sup(X)
  rule $run_builtin(nthArg1([X, Xs:ListElems]), N:Int) => $run_builtin(nthArg1([Xs]), N -Int 1)
endmodule
