import StrongPerimetralTurning
import RepresentationBoundary.DiagonalizationKernel

namespace RepresentationBoundary
namespace CircularStatusRepresentation

open RepresentationBoundary.DiagonalizationKernel
open StrongPerimetralTurning

universe uCarrier uLeft uRight uCode

/- This observation records only whether a type-valued status has a witness.
   The proof-relevant status itself remains unchanged. -/
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

/- This structure assumes exact internal representation of one determined
   circular status. It does not assume diagonal closure or representation of
   every predicate on the code space. -/
structure ExactCircularStatusRepresentation
    (P : CircularPresentation)
    (Code : Type uCode) where
  decode : Code → RootedGeneratedHistory P
  eval : Code → Code → Prop
  program : Code
  representsRegime :
    Represents eval program (CodedCircularRegimeStatus P decode)

namespace ExactCircularStatusRepresentation

theorem representsSpecification
    {P : CircularPresentation}
    {Code : Type uCode}
    (representation : ExactCircularStatusRepresentation P Code) :
    Represents representation.eval representation.program
      (CodedCircularSpecificationStatus P representation.decode) :=
  representCircularRegime_toSpecification representation.representsRegime

end ExactCircularStatusRepresentation

/- Exact representation of the selected circular regime and norm coexists with
   a constructively produced predicate outside the same representation regime.
   Local exactness therefore does not entail global representation closure. -/
theorem localExactRepresentation_hasDiagonalExit
    {P : CircularPresentation}
    {Code : Type uCode}
    (representation : ExactCircularStatusRepresentation P Code) :
    Represents representation.eval representation.program
        (CodedCircularRegimeStatus P representation.decode) ∧
      Represents representation.eval representation.program
        (CodedCircularSpecificationStatus P representation.decode) ∧
      ¬ InternallyRepresentable representation.eval
        (diagonalStatus representation.eval) :=
  ⟨representation.representsRegime,
    representation.representsSpecification,
    diagonalStatus_notRepresentable representation.eval⟩

theorem localExactRepresentation_notGloballyClosed
    {P : CircularPresentation}
    {Code : Type uCode}
    (representation : ExactCircularStatusRepresentation P Code) :
    ¬ GlobalRepresentationClosure representation.eval :=
  noGlobalRepresentationClosure representation.eval

def diagonalRepresentationExit
    {P : CircularPresentation}
    {Code : Type uCode}
    (representation : ExactCircularStatusRepresentation P Code) :
    StatusRepresentationExit representation.eval :=
  diagonalStatusExit representation.eval

/- Separator model: a particular circular status can be represented exactly
   without making the evaluator globally representation-complete. -/
def canonicalUnitCircularStatusRepresentation
    (P : CircularPresentation) :
    ExactCircularStatusRepresentation P Unit where
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

theorem canonicalUnitCircularStatusRepresentation_hasDiagonalExit
    (P : CircularPresentation) :
    ¬ InternallyRepresentable
      (canonicalUnitCircularStatusRepresentation P).eval
      (diagonalStatus
        (canonicalUnitCircularStatusRepresentation P).eval) :=
  diagonalStatus_notRepresentable _

end CircularStatusRepresentation
end RepresentationBoundary

/- AXIOM_AUDIT_BEGIN -/
#print axioms RepresentationBoundary.CircularStatusRepresentation.HasStatus
#print axioms RepresentationBoundary.CircularStatusRepresentation.hasStatus_iff_of_maps
#print axioms RepresentationBoundary.CircularStatusRepresentation.CircularRegimeStatus
#print axioms RepresentationBoundary.CircularStatusRepresentation.CircularSpecificationStatus
#print axioms RepresentationBoundary.CircularStatusRepresentation.circularStatusAdequacy
#print axioms RepresentationBoundary.CircularStatusRepresentation.PullbackStatus
#print axioms RepresentationBoundary.CircularStatusRepresentation.CodedCircularRegimeStatus
#print axioms RepresentationBoundary.CircularStatusRepresentation.CodedCircularSpecificationStatus
#print axioms RepresentationBoundary.CircularStatusRepresentation.codedCircularStatusAdequacy
#print axioms RepresentationBoundary.CircularStatusRepresentation.transportRepresentation
#print axioms RepresentationBoundary.CircularStatusRepresentation.representCircularRegime_toSpecification
#print axioms RepresentationBoundary.CircularStatusRepresentation.representCircularSpecification_toRegime
#print axioms RepresentationBoundary.CircularStatusRepresentation.ExactCircularStatusRepresentation
#print axioms RepresentationBoundary.CircularStatusRepresentation.ExactCircularStatusRepresentation.representsSpecification
#print axioms RepresentationBoundary.CircularStatusRepresentation.localExactRepresentation_hasDiagonalExit
#print axioms RepresentationBoundary.CircularStatusRepresentation.localExactRepresentation_notGloballyClosed
#print axioms RepresentationBoundary.CircularStatusRepresentation.diagonalRepresentationExit
#print axioms RepresentationBoundary.CircularStatusRepresentation.canonicalUnitCircularStatusRepresentation
#print axioms RepresentationBoundary.CircularStatusRepresentation.canonicalUnitCircularStatusRepresentation_hasDiagonalExit
/- AXIOM_AUDIT_END -/
