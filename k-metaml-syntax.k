//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

module K-METAML-SYNTAX
  syntax Value ::= Int | Bool | Id

  syntax Term ::= Value
                | "(" Term ")"              [bracket]
                | Term Term                 [strict, left]
                > Term "+" Term             [seqstrict, left]
                > "<" Term ">"
                > "~" Term
                > "run" Term
                | "lambda" Id "." Term      [binder]
endmodule
