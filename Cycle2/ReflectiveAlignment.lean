import StrongPerimetralTurning
import Cycle2.DiagonalizationKernel

namespace Cycle2
namespace ReflectiveAlignment

open Cycle2.DiagonalizationKernel
open StrongPerimetralTurning

universe uCarrier uLeft uRight uCode

/- Reflection observes only whether a type-valued status has a witness.  The
   proof-relevant status itself remains unchanged. -/
abbrev HasStatus
    {Carrier : Type uCarrier}
    (Status : Carrier → Type uLeft)
    (carrier : Carrier) : Prop :=
  Nonempty (Status carrier)

theorem hasStatus_iff_of_maps
    {Carrier : Type uCarrier}
    {Left : Carrier → Type uLeft}
    {Right : Carrier → Type uRight}
    {carrier : Carrier}
    (forward : Left carrier → Right carrier)
    (backward : Right carrier → Left carrier) :
    HasStatus Left carrier ↔ HasStatus Right carrier := by
  constructor
  · intro inhabited
    obtain ⟨witness⟩ := inhabited
    exact ⟨forward witness⟩
  · intro inhabited
    obtain ⟨witness⟩ := inhabited
    exact ⟨backward witness⟩

abbrev CircularRegimeStatus
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Prop :=
  Nonempty (CircularRefinement P history)

abbrev CircularSpecificationStatus
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Prop :=
  Nonempty (CircularSpecificationSatisfaction P history)

theorem circularStatusAdequacy
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) :
    CircularRegimeStatus P history ↔
      CircularSpecificationStatus P history := by
  apply hasStatus_iff_of_maps
  · exact circularRefinement_soundSpecification
  · exact circularSpecification_complete

def PullbackStatus
    {Code : Type uCode}
    {Carrier : Type uCarrier}
    (decode : Code → Carrier)
    (Status : Carrier → Prop) : Code → Prop :=
  fun code => Status (decode code)

abbrev CodedCircularRegimeStatus
    (P : CircularPresentation)
    {Code : Type uCode}
    (decode : Code → RootedGeneratedHistory P) : Code → Prop :=
  PullbackStatus decode (CircularRegimeStatus P)

abbrev CodedCircularSpecificationStatus
    (P : CircularPresentation)
    {Code : Type uCode}
    (decode : Code → RootedGeneratedHistory P) : Code → Prop :=
  PullbackStatus decode (CircularSpecificationStatus P)

theorem codedCircularStatusAdequacy
    (P : CircularPresentation)
    {Code : Type uCode}
    (decode : Code → RootedGeneratedHistory P)
    (code : Code) :
    CodedCircularRegimeStatus P decode code ↔
      CodedCircularSpecificationStatus P decode code :=
  circularStatusAdequacy P (decode code)

theorem transportRepresentation
    {Code : Type uCode}
    {eval : Code → Code → Prop}
    {program : Code}
    {left right : Code → Prop}
    (represented : Represents eval program left)
    (equivalent : ∀ code, left code ↔ right code) :
    Represents eval program right :=
  fun code => (represented code).trans (equivalent code)

theorem representCircularRegime_toSpecification
    {P : CircularPresentation}
    {Code : Type uCode}
    {eval : Code → Code → Prop}
    {program : Code}
    {decode : Code → RootedGeneratedHistory P}
    (represented :
      Represents eval program (CodedCircularRegimeStatus P decode)) :
    Represents eval program
      (CodedCircularSpecificationStatus P decode) :=
  transportRepresentation represented
    (codedCircularStatusAdequacy P decode)

theorem representCircularSpecification_toRegime
    {P : CircularPresentation}
    {Code : Type uCode}
    {eval : Code → Code → Prop}
    {program : Code}
    {decode : Code → RootedGeneratedHistory P}
    (represented :
      Represents eval program
        (CodedCircularSpecificationStatus P decode)) :
    Represents eval program (CodedCircularRegimeStatus P decode) :=
  transportRepresentation represented
    (fun code => (codedCircularStatusAdequacy P decode code).symm)

/- A view assumes exact internal representation of one operational status.  It
   does not assume diagonal closure or representation of every status. -/
structure ReflectiveCircularStatusView
    (P : CircularPresentation)
    (Code : Type uCode) where
  decode : Code → RootedGeneratedHistory P
  eval : Code → Code → Prop
  program : Code
  representsRegime :
    Represents eval program (CodedCircularRegimeStatus P decode)

namespace ReflectiveCircularStatusView

theorem representsSpecification
    {P : CircularPresentation}
    {Code : Type uCode}
    (view : ReflectiveCircularStatusView P Code) :
    Represents view.eval view.program
      (CodedCircularSpecificationStatus P view.decode) :=
  representCircularRegime_toSpecification view.representsRegime

end ReflectiveCircularStatusView

/- Exact representation of the particular circular regime and norm coexists
   with a constructively produced status outside the same representability
   regime.  Local exactness therefore does not entail global closure. -/
theorem exactCircularStatusRepresentation_hasDiagonalOutside
    {P : CircularPresentation}
    {Code : Type uCode}
    (view : ReflectiveCircularStatusView P Code) :
    Represents view.eval view.program
        (CodedCircularRegimeStatus P view.decode) ∧
      Represents view.eval view.program
        (CodedCircularSpecificationStatus P view.decode) ∧
      ¬ InternallyRepresentable view.eval (diagonalStatus view.eval) :=
  ⟨view.representsRegime,
    view.representsSpecification,
    diagonalStatus_notRepresentable view.eval⟩

theorem exactCircularStatusRepresentation_notGloballyClosed
    {P : CircularPresentation}
    {Code : Type uCode}
    (view : ReflectiveCircularStatusView P Code) :
    ¬ GlobalReflectiveClosure view.eval :=
  noGlobalReflectiveClosure view.eval

def circularDiagonalStatusExit
    {P : CircularPresentation}
    {Code : Type uCode}
    (view : ReflectiveCircularStatusView P Code) :
    StatusRepresentationExit view.eval :=
  diagonalStatusExit view.eval

/- Separator model: a particular circular status can be represented exactly
   without making the evaluator globally closed. -/
def canonicalUnitCircularStatusView
    (P : CircularPresentation) :
    ReflectiveCircularStatusView P Unit where
  decode := fun _ => perimeterDeployment P
  eval := fun _ _ => True
  program := ()
  representsRegime := by
    intro input
    constructor
    · intro _holds
      exact ⟨identityCircularRefinement P⟩
    · intro _inhabited
      exact True.intro

theorem canonicalUnitCircularStatusView_hasDiagonalOutside
    (P : CircularPresentation) :
    ¬ InternallyRepresentable
      (canonicalUnitCircularStatusView P).eval
      (diagonalStatus (canonicalUnitCircularStatusView P).eval) :=
  diagonalStatus_notRepresentable _

end ReflectiveAlignment
end Cycle2

/- AXIOM_AUDIT_BEGIN -/
#print axioms Cycle2.ReflectiveAlignment.HasStatus
#print axioms Cycle2.ReflectiveAlignment.hasStatus_iff_of_maps
#print axioms Cycle2.ReflectiveAlignment.CircularRegimeStatus
#print axioms Cycle2.ReflectiveAlignment.CircularSpecificationStatus
#print axioms Cycle2.ReflectiveAlignment.circularStatusAdequacy
#print axioms Cycle2.ReflectiveAlignment.PullbackStatus
#print axioms Cycle2.ReflectiveAlignment.CodedCircularRegimeStatus
#print axioms Cycle2.ReflectiveAlignment.CodedCircularSpecificationStatus
#print axioms Cycle2.ReflectiveAlignment.codedCircularStatusAdequacy
#print axioms Cycle2.ReflectiveAlignment.transportRepresentation
#print axioms Cycle2.ReflectiveAlignment.representCircularRegime_toSpecification
#print axioms Cycle2.ReflectiveAlignment.representCircularSpecification_toRegime
#print axioms Cycle2.ReflectiveAlignment.ReflectiveCircularStatusView
#print axioms Cycle2.ReflectiveAlignment.ReflectiveCircularStatusView.representsSpecification
#print axioms Cycle2.ReflectiveAlignment.exactCircularStatusRepresentation_hasDiagonalOutside
#print axioms Cycle2.ReflectiveAlignment.exactCircularStatusRepresentation_notGloballyClosed
#print axioms Cycle2.ReflectiveAlignment.circularDiagonalStatusExit
#print axioms Cycle2.ReflectiveAlignment.canonicalUnitCircularStatusView
#print axioms Cycle2.ReflectiveAlignment.canonicalUnitCircularStatusView_hasDiagonalOutside
/- AXIOM_AUDIT_END -/
