//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

module K-METAML-SYNTAX
  syntax Program ::= Term
                   | "val" Id "=" Term ";" Program
                   | Empty

  syntax Empty ::= ""   [klabel('Empty), notInRules, notInGround]

  syntax Unit ::= "(" ")"

  syntax Term ::= Int | Bool | Id | Unit
                | "(" Term ")"              [bracket]

                > "~" Term

                > Term Term                 [left]

                | "<" Term ">"

                > Term "*" Term             [seqstrict, left]
                | Term "/" Term             [seqstrict, left]

                > Term "+" Term             [seqstrict, left]
                | Term "-" Term             [seqstrict, left]

                > "fn" Id Rest Term

                > "run" Term

  syntax Dot ::= "=>"
  syntax Rest  ::= Id Rest | Dot
endmodule
