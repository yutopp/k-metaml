//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "k-metaml-typing-syntax.k"

module K-METAML-TYPING-TO-STRING
  imports K-METAML-TYPING-SYNTAX-EXTEND

  configuration <zoi> .Map </zoi>

  syntax String ::= Type2String(Type, Map)  [function, klabel(Type2String)]
  rule Type2String(int:Type, _)  => "int"
  rule Type2String(bool:Type, _) => "bool"
  rule Type2String(unit:Type, _) => "unit"
  rule Type2String(T1:Type -> T2:Type, M) =>
                           Type2String(T1, M) +String " -> " +String Type2String(T2, M)
  rule Type2String(#<# T:Type #>#, M) => "#<# " +String Type2String(T, M) +String " #>#"

  rule Type2String(T:Type, M) => "t." +String Int2String(M[T])
       when T in keys(M)
endmodule