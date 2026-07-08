-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILTests.LanguageFile
Layer: Tests
Purpose: Machine-checked examples for the external MeTTaIL dialect file format. These examples cover
  the product-facing path: parse a user-editable file, elaborate it to a presentation, and run a term
  through the generic verified runtime. String parsing executes through `#eval`, matching the other
  runtime demos; the shell regression asserts the shipped CLI output.
Imports: MeTTaIL.Runtime.LanguageFile
Trusted boundary: none
Main exports: (examples only)
Open obligations: none
-/
import MeTTaIL.Runtime.LanguageFile

namespace MeTTaILTests
open MeTTaIL

private def boolFile : String := "
# A small editable dialect file.
sort Tm
term tt : Tm
term ff : Tm
term notOp : Tm -> Tm
rewrite notTt : (notOp tt) => ff
rewrite notFf : (notOp ff) => tt
"

#eval LanguageFile.runSource boolFile 100 "(notOp tt)"   -- Except.ok (some "ff")
#eval LanguageFile.runSource boolFile 100 "(notOp ff)"   -- Except.ok (some "tt")

end MeTTaILTests
