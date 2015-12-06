//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "../k-metaml-syntax.k"

module K-METAML-TYPING
  imports K-METAML-SYNTAX

  syntax Type ::= "int" | "bool" | "unit"
                | Type "->" Type
                > "#<#" Type "#>#"          // code
                > "(" Type ")"              [bracket]

  syntax TypeTRI ::= typeTriple(Type, Int, Int)   // Type, R, N

  syntax Term ::= Type
  syntax KResult ::= Type

  configuration <k> $PGM:Program </k>
                <level> 0 </level>
                <run> 0 </run>
                <tenv> .Map </tenv>

  // Top level
  syntax KItem ::= valMid(Int, Int, Type, Term, Map) // Run, H, T, Term, VEnv
  rule <k> val X:Id = E1:Term ; E2:Program => E2 ~> valMid(R, 99999, ?T1, E1, VEnv) ... </k>
       <level> 0 </level>
       <run> R </run>
       <tenv> VEnv => VEnv[X <- typeTriple(?T1, R +Int 99999, 0)] </tenv>

  syntax KItem ::= valEnd(Int, Int, Type, Type, Map) // Run, H, T, T1
  rule <k> T:Type ~> valMid(R, H, T1, E1, VEnv) => E1 ~> valEnd(R, H, T, T1, VEnv) ... </k>
       <level> 0 </level>
       <run> R => R +Int H </run>
       <tenv> _ => VEnv </tenv>

  rule <k> _:Empty ~> valMid(R, H, T1, E1, VEnv) => E1 ~> valEnd(R, H, unit, T1, VEnv) ... </k>
       <level> 0 </level>
       <run> R => R +Int H </run>
       <tenv> _ => VEnv </tenv>

  rule <k> T1:Type ~> valEnd(R, H, T, T1, VEnv) => T ... </k>
       <level> 0 </level>
       <run> BR => R </run>
       <tenv> _ => VEnv </tenv>
       when BR ==Int (R +Int H)


  // Int n
  rule _:Int => int:Type        [structural]

  // Bool n
  rule _:Bool => bool:Type      [structural]

  // Unit n
  rule _:Unit => unit:Type      [structural]


  // AExp
  rule T1:Type + T2:Type => T1 =?= int ~> T2 =?= int ~> int
  rule T1:Type - T2:Type => T1 =?= int ~> T2 =?= int ~> int
  rule T1:Type * T2:Type => T1 =?= int ~> T2 =?= int ~> int
  rule T1:Type / T2:Type => T1 =?= int ~> T2 =?= int ~> int

  rule T1:Type = T2:Type => T1 =?= T2 ~> bool

  // if
  syntax KItem ::= ifThen(Term) | ifElse(Type)
  rule if bool:Type then E1:Term else E2:Term => E1 ~> ifThen(E2)
  rule T1:Type ~> ifThen(E2) => E2 ~> ifElse(T1)
  rule T2:Type ~> ifElse(T1) => T1 =?= T2 ~> T1     // or T2

  // Br n
  syntax KItem ::= brEnd(Int) // Ndepth
  rule <k> < E:Term > => E ~> brEnd(N) ... </k>
       <level> N => N +Int 1 </level>

  rule <k> T:Type ~> brEnd(N) => #<# T #># ... </k>
       <level> BN => N </level>
       when BN ==Int (N +Int 1)


  rule fn X:Id (N Xs):FnParamRest E:Term => fn X (=>) (fn N Xs E) [macro]

  // Abs n
  syntax KItem ::= absEnd(Type, Int, Int, Map) // TypeEnv
  rule <k> fn X:Id (=>) E:Term => E ~> absEnd(?T1, N, R, Rho) ... </k>
       <tenv> Rho => Rho[X <- typeTriple(?T1, R, N)] </tenv>
       <level> N </level>
       <run> R </run>

  rule <k> T2:Type ~> absEnd(T1, N, R, Rho) => T1 -> T2 ... </k>
       <level> N </level>
       <run> R </run>
       <tenv> _ => Rho </tenv>


  // Var N
  rule <k> X:Id => XType ... </k>
       <tenv> ... X |-> typeTriple(XType, XR, XN) ... </tenv>
       <level> N </level>
       <run> R </run>
       when (XN +Int R) <=Int (N +Int XR)

  // Esc n+1
  syntax KItem ::= escEnd(Int) // Level
  rule <k> ~E:Term => E ~> escEnd(N) ... </k>
       <level> N => N -Int 1 </level>
       when N >=Int 1

  rule <k> #<# T:Type #># ~> escEnd(N) => T ... </k>
       <level> BN => N </level>
       when BN ==Int (N -Int 1)


  // App n
  syntax KItem ::= appMid(Int, Int, Term) | appEnd(Int, Int, Type, Type)
  rule <k> E1:Term E2:Term => E1 ~> appMid(N, R, E2) ... </k>
       <level> N </level>
       <run> R </run>

  rule <k> LT:Type ~> appMid(N, R, E2) => LT =?= (?T1 -> ?T) ~> E2 ~> appEnd(N, R, ?T1, ?T) ... </k>
       <level> N </level>
       <run> R </run>

  rule <k> RT:Type ~> appEnd(N, R, T1, T) => T1 =?= RT ~> T ... </k>
       <level> N </level>
       <run> R </run>

  // run n
  syntax KItem ::= runEnd(Int) // Level, Run
  rule <k> run E:Term => E ~> runEnd(R) ...</k>
       <run> R => R +Int 1 </run>

  rule <k> (#<# T #>#):Type ~> runEnd(R) => T ... </k>
       <run> R +Int 1 => R </run>


  // unification...
  syntax KItem ::= Type "=?=" Type
  rule T =?= T => .K

endmodule
