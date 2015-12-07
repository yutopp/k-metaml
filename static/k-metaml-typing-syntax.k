//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "../k-metaml-syntax.k"

module K-METAML-TYPING-SYNTAX-EXTEND
  imports K-METAML-SYNTAX

  syntax Type ::= "int" | "bool" | "unit"
                | Type "->" Type
                > "#<#" Type "#>#"          // code
                > "(" Type ")"              [bracket]

  syntax TypeTRI ::= typeTriple(Type, Int, Int)   // Type, R, N

  syntax Term ::= Type
endmodule