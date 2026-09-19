import ConstitutiveSearch.SAT.ComposedLocalPrimitivePathSearch

namespace ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression

open ConstitutiveSearch
open SAT

theorem chain3_length :
    (composedPrimitiveStateChain 3).length = 2 :=
  composedPrimitiveStateChain_length 3

theorem local3_found :
    (composedLocalPrimitiveCodeRun 3).path? ≠ none :=
  composedLocalPrimitiveCodeRun_found 3

theorem local3_primitiveQueries :
    (composedLocalPrimitiveCodeRun 3).stats.primitiveQueries = 2 :=
  composedLocalPrimitiveCodeRun_primitiveQueries 3

theorem local3_compositionCandidates :
    (composedLocalPrimitiveCodeRun 3).stats.compositionCandidates = 0 :=
  composedLocalPrimitiveCodeRun_compositionCandidates 3

theorem local3_codeSize :
    match (composedLocalPrimitiveCodeRun 3).path? with
    | none => False
    | some code => code.size = 2 :=
  composedLocalPrimitiveCodeRun_codeSize 3

theorem local3_primitiveStrict :
    (composedLocalPrimitiveCodeRun 3).stats.primitiveQueries <
      (composedClosureFuelTwo 3).stats.primitiveQueries :=
  composedLocalPrimitiveCodeRun_primitiveQueries_lt_global 3

theorem local3_compositionStrict :
    (composedLocalPrimitiveCodeRun 3).stats.compositionCandidates <
      (composedClosureFuelTwo 3).stats.compositionCandidates :=
  composedLocalPrimitiveCodeRun_compositionCandidates_lt_global 3

end ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression.chain3_length
#print axioms ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression.local3_found
#print axioms ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression.local3_primitiveQueries
#print axioms ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression.local3_compositionCandidates
#print axioms ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression.local3_codeSize
#print axioms ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression.local3_primitiveStrict
#print axioms ConstitutiveSearch.Tests.SATComposedLocalPrimitivePathSearchRegression.local3_compositionStrict
/- AXIOM_AUDIT_END -/
