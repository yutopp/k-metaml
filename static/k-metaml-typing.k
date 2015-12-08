//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "k-metaml-typing-syntax.k"
require "k-metaml-typing-to-string.k"
require "modules/unification.k"

module K-METAML-TYPING
  imports K-METAML-TYPING-SYNTAX-EXTEND
  imports K-METAML-TYPING-TO-STRING
  imports UNIFICATION

  syntax KResult ::= Type

  configuration <k> $PGM:Program </k>
                <level> 0 </level>
                <run> 0 </run>
                <tenv> .Map </tenv>

                <out color="green" stream="stdout"> .List </out>
                <typeVarNameMap> .Map </typeVarNameMap>

  syntax TypeSchema ::= "(" "forall" Set ")" TypeTRI

  // Top level
  syntax KItem ::= valMid(Id, Int, Int, Program, Map) // Id, Run, H
  rule <k> val X:Id = E1:Term ; E2:Program => E1 ~> valMid(X, R, 99999, E2, TEnv) ... </k>
       <level> 0 </level>
       <run> R => R +Int 99999 </run>
       <tenv> TEnv </tenv>

  syntax KItem ::= valEnd(Int, Map) //
  rule <k> T1:Type ~> valMid(X, R, H, E2, TEnv) => E2 ~> valEnd(R, TEnv) ... </k>
       <level> 0 </level>
       <run> BR => R </run>
       <tenv> _ => TEnv[X <- (forall #metaVariables(T1) -Set #metaVariables(TEnv)) typeTriple(T1, R +Int H, 0)] </tenv>
       <out> ... .List => ListItem("val " +String Id2String(X) +String " : " +String Type2String(T1, TVM) +String "\n") </out>
       <typeVarNameMap> TVM </typeVarNameMap>
       when BR =Int (R +Int H)

  rule <k> T:Type ~> valEnd(R, TEnv) => T ... </k>
       <level> 0 </level>
       <run> R </run>
       <tenv> _ => TEnv </tenv>

  rule <k> _:Empty ~> valEnd(R, TEnv) => unit ... </k>
       <level> 0 </level>
       <run> R </run>
       <tenv> _ => TEnv </tenv>


  // Top level : val rec
  syntax Term ::= "$valrec" Id "=" Term ";" Program
  rule <k> $valrec X:Id = E1:Term ; E2:Program => E1 ~> valMid(X, R, 99999, E2, TEnv) ... </k>
       <level> 0 </level>
       <run> R => R +Int 99999 </run>
       <tenv> TEnv => TEnv[X <- (forall #metaVariables(?T1) -Set #metaVariables(TEnv)) typeTriple(?T1, R +Int 99999, 0)] </tenv>
       <typeVarNameMap> TVM => TVM[?T1 <- !T1N:Int] </typeVarNameMap>


  // Top level : fun
  rule fun X:Id ( P:Id, Ps:FunParams) = E:Term ; E2:Program
           => $valrec X:Id = ($fn_impl (P, Ps) = E):Term ; E2    [macro]

  syntax Term ::= "$fn_impl" FunParams "=" Term
  rule $fn_impl (X:Id, Xs:FunParams) = E:Term => fn X (=>) ($fn_impl (Xs) = E)  [macro]
  rule $fn_impl (.FunParams)         = E:Term => E                              [macro]


  // Int n
  rule _:Int => int:Type        [structural]

  // Bool n
  rule _:Bool => bool:Type      [structural]

  // Unit n
  rule _:Unit => unit:Type      [structural]

  // List
  syntax KItem ::= listTerm(Int, Int, Type, ListElems)
  rule <k> [ (E, Es):ListElems ] => E ~> listTerm(N, R, ?T, Es) ... </k>
       <level> N </level>
       <run> R </run>
       <typeVarNameMap> TVM => TVM[?T <- !T1N:Int] </typeVarNameMap>

  rule <k> T:Type ~> listTerm(N, R, T, (E, Es):ListElems) => E ~> listTerm(N, R, T, Es) ... </k>
       <level> N </level>
       <run> R </run>

  rule <k> T:Type ~> listTerm(N, R, T, .ListElems) => (T list):Type ... </k>
       <level> N </level>
       <run> R </run>


  // Bin Op
  rule T1:Type + T2:Type => T1 =!= int ~> T2 =!= int ~> int
  rule T1:Type - T2:Type => T1 =!= int ~> T2 =!= int ~> int
  rule T1:Type * T2:Type => T1 =!= int ~> T2 =!= int ~> int
  rule T1:Type / T2:Type => T1 =!= int ~> T2 =!= int ~> int

  rule T1:Type = T2:Type => T1 =!= T2 ~> bool
  rule T1:Type '>' T2:Type => T1 =!= T2 ~> bool
  rule T1:Type '<' T2:Type => T1 =!= T2 ~> bool

  rule <k> hd => (?T list) -> ?T ... </k>
       <level> N </level>
       <run> R </run>
       <typeVarNameMap> TVM => TVM[?T <- !T1N:Int] </typeVarNameMap>

  rule <k> tl => (?T list) -> (?T list) ... </k>
       <level> N </level>
       <run> R </run>
       <typeVarNameMap> TVM => TVM[?T <- !T1N:Int] </typeVarNameMap>

  rule <k> null => (?T list) -> bool ... </k>
       <level> N </level>
       <run> R </run>
       <typeVarNameMap> TVM => TVM[?T <- !T1N:Int] </typeVarNameMap>


  // if
  syntax KItem ::= ifThen(Term) | ifElse(Type)
  rule if bool:Type then E1:Term else E2:Term => E1 ~> ifThen(E2)
  rule T1:Type ~> ifThen(E2) => E2 ~> ifElse(T1)
  rule T2:Type ~> ifElse(T1) => T1 =!= T2 ~> T1     // or T2


  // Br n
  syntax KItem ::= brEnd(Int) // Ndepth
  rule <k> < E:Term > => E ~> brEnd(N) ... </k>
       <level> N => N +Int 1 </level>

  rule <k> T:Type ~> brEnd(N) => #<# T #># ... </k>
       <level> BN => N </level>
       when BN ==Int (N +Int 1)


  // Lift n
  rule <k> lift E:Term => E ~> brEnd(N) ... </k>
       <level> N => N +Int 1 </level>


  rule fn X:Id (N Xs):FnParamRest E:Term => fn X (=>) (fn N Xs E) [macro]

  // Abs n
  syntax KItem ::= absEnd(Type, Int, Int, Map) // TypeEnv
  rule <k> fn X:Id (=>) E:Term => E ~> absEnd(?T1, N, R, Rho) ... </k>
       <tenv> Rho => Rho[X <- typeTriple(?T1, R, N)] </tenv>
       <level> N </level>
       <run> R </run>
       <typeVarNameMap> TVM => TVM[?T1 <- !T1N:Int] </typeVarNameMap>

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
  rule <k> X:Id => #rename(XType, Tvs) ... </k>
       <tenv>... X |-> (forall Tvs) typeTriple(XType, XR, XN) ... </tenv>
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

  rule <k> LT:Type ~> appMid(N, R, E2) => LT =!= (?T1 -> ?T) ~> E2 ~> appEnd(N, R, ?T1, ?T) ... </k>
       <level> N </level>
       <run> R </run>
       <typeVarNameMap> TVM => TVM[?T1 <- !T1N:Int][?T <- !TN:Int] </typeVarNameMap>

  rule <k> RT:Type ~> appEnd(N, R, T1, T) => T1 =!= RT ~> T ... </k>
       <level> N </level>
       <run> R </run>


  // run n
  syntax KItem ::= runEnd(Int) // Level, Run
  rule <k> run E:Term => E ~> runEnd(R) ...</k>
       <run> R => R +Int 1 </run>

  rule <k> (#<# T #>#):Type ~> runEnd(R) => T ... </k>
       <run> R +Int 1 => R </run>


  // unification...
  syntax KItem ::= Type "=!=" Type
  rule T =!= T => .K
endmodule
