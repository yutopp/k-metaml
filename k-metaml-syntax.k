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
                   | "fun" Id "(" FunParams ")" "=" Term ";" Program
                   | Empty

  syntax Empty ::= ""   [klabel('Empty), notInRules, notInGround]

  syntax Unit ::= "(" ")"

  syntax Term ::= Int | Bool | Id | Unit
                | BuiltinFn
                | "[" ListElems "]"
                | "(" Term ")"              [bracket]
                | "<" Term ">"

                > "~" Term

                > Term Term                 [left]

                > Term "*" Term             [seqstrict, left]
                | Term "/" Term             [seqstrict, left]

                > Term "+" Term             [seqstrict, left]
                | Term "-" Term             [seqstrict, left]

                > Term "=" Term             [seqstrict, left]
                > Term "'>'" Term           [seqstrict, left]
                > Term "'<'" Term           [seqstrict, left]

                > "if" Term "then" Term "else" Term     [strict(1)]

                > "fn" Id FnParamRest Term

                > "run" Term
                | "lift" Term


  syntax BuiltinFn ::= "hd"
                     | "tl"
                     | "null"
                     | "nth"
                     | nthArg1(Term)

  syntax ListElems ::= List{Term, ","}

  syntax FnSep ::= "=>"
  syntax FnParamRest ::= FnSep | Id FnParamRest

  syntax FunParams ::= List{Id, ","}
endmodule
