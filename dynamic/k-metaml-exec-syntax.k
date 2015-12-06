//
// Copyright yutopp 2015 - .
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

require "../k-metaml-syntax.k"

module K-METAML-EXEC-SYNTAX-EXTEND
  imports K-METAML-SYNTAX

  syntax Term ::= Sym(Id) | Real(Term) | RealRef(Term, Id)
  syntax Term ::= "%" Term

  syntax Term ::= "$fn_rec" Id Id FnParamRest Term
endmodule