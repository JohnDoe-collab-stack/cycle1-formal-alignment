import StrongPerimetralTurning.HistoryDerivedIntrinsicAlignment
import Examples.ConcreteContinuation.LoggedAlgebra

namespace StrongPerimetralTurning.Tests.HistoryDerivedIntrinsicAlignmentRegression

open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open StrongPerimetralTurning.IteratedConstitutivePersistence
open StrongPerimetralTurning.HistoryDerivedIntrinsicAlignment
open StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra

/--
At arbitrary finite depth, the fully history-derived intrinsic alignment agrees
with the transport already used by the circular persistence layer.
-/
theorem depth_three_intrinsic_agrees_with_existing
    (occurrence :
      (iteratedRealization
        examplePresentation exampleConcreteAlgebra 3).Concrete) :
    (iteratedConcreteConstitutiveAlignment
        examplePresentation
        exampleConcreteAlgebra
        loggedConcreteAlgebra
        3).initial.transport.forward occurrence =
      ((iteratedRealization
          examplePresentation exampleConcreteAlgebra 3).transport
        (iteratedRealization
          examplePresentation loggedConcreteAlgebra 3)).forward occurrence :=
  iteratedConcreteAlignment_forward_eq_realizationTransport
    examplePresentation
    exampleConcreteAlgebra
    loggedConcreteAlgebra
    3
    occurrence

/--
Any other compatible intrinsic alignment at the same depth is forced to be the
same established circular transport.
-/
theorem depth_three_any_intrinsic_alignment_is_existing
    (candidate :
      Alignment.GenesisReconstruction.HistoryDerivedAlignment.ConstitutiveAlignment
        (exampleConcreteAlgebra.realizeHistory
          (iteratedHistory examplePresentation 3).history)
        (loggedConcreteAlgebra.realizeHistory
          (iteratedHistory examplePresentation 3).history))
    (occurrence :
      (iteratedRealization
        examplePresentation exampleConcreteAlgebra 3).Concrete) :
    candidate.initial.transport.forward occurrence =
      ((iteratedRealization
          examplePresentation exampleConcreteAlgebra 3).transport
        (iteratedRealization
          examplePresentation loggedConcreteAlgebra 3)).forward occurrence :=
  iteratedConcreteAlignment_canonical
    examplePresentation
    exampleConcreteAlgebra
    loggedConcreteAlgebra
    3
    candidate
    occurrence

end StrongPerimetralTurning.Tests.HistoryDerivedIntrinsicAlignmentRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Tests.HistoryDerivedIntrinsicAlignmentRegression.depth_three_intrinsic_agrees_with_existing
#print axioms StrongPerimetralTurning.Tests.HistoryDerivedIntrinsicAlignmentRegression.depth_three_any_intrinsic_alignment_is_existing
/- AXIOM_AUDIT_END -/
