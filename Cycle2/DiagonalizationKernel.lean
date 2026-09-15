import Init

namespace Cycle2
namespace DiagonalizationKernel

universe uCode

/- A program represents a predicate when its evaluation agrees pointwise with
   that predicate.  No syntax, arithmetic, or normative reading is assumed. -/
def Represents {Code : Type uCode}
    (eval : Code → Code → Prop)
    (program : Code)
    (predicate : Code → Prop) : Prop :=
  ∀ input, eval program input ↔ predicate input

def InternallyRepresentable {Code : Type uCode}
    (eval : Code → Code → Prop)
    (predicate : Code → Prop) : Prop :=
  ∃ program, Represents eval program predicate

/- The diagonal candidate is constructed from the evaluator itself. -/
def diagonalStatus {Code : Type uCode}
    (eval : Code → Code → Prop) : Code → Prop :=
  fun code => ¬ eval code code

def GlobalReflectiveClosure {Code : Type uCode}
    (eval : Code → Code → Prop) : Prop :=
  ∀ predicate, InternallyRepresentable eval predicate

theorem diagonalStatus_notRepresentable
    {Code : Type uCode}
    (eval : Code → Code → Prop) :
    ¬ InternallyRepresentable eval (diagonalStatus eval) := by
  intro represented
  obtain ⟨program, represents⟩ := represented
  have self := represents program
  have notSelf : ¬ eval program program := by
    intro holds
    exact (self.mp holds) holds
  exact notSelf (self.mpr notSelf)

theorem noGlobalReflectiveClosure
    {Code : Type uCode}
    (eval : Code → Code → Prop) :
    ¬ GlobalReflectiveClosure eval := by
  intro closure
  exact diagonalStatus_notRepresentable eval (closure (diagonalStatus eval))

/- Local representability of the operator-transformed diagonal predicate
   yields a fixed point for that operator.  The fixed point is derived from
   the representing program; no global reflective closure is assumed. -/
theorem diagonalFixedPoint_ofRepresentable
    {Code : Type uCode}
    {eval : Code → Code → Prop}
    (operator : Prop → Prop)
    (represented :
      InternallyRepresentable eval
        (fun input => operator (eval input input))) :
    ∃ proposition : Prop, proposition ↔ operator proposition := by
  obtain ⟨program, represents⟩ := represented
  exact ⟨eval program program, represents program⟩

/- The local premise is inhabited by a concrete evaluator/operator pair. -/
theorem diagonalFixedPoint_ofRepresentable_unit_example :
    ∃ proposition : Prop, proposition ↔ True := by
  let eval : Unit → Unit → Prop := fun _ _ => True
  let operator : Prop → Prop := fun _ => True
  have represented :
      InternallyRepresentable eval
        (fun input => operator (eval input input)) := by
    refine ⟨(), ?_⟩
    intro input
    rfl
  exact diagonalFixedPoint_ofRepresentable operator represented

structure StatusRepresentationExit
    {Code : Type uCode}
    (eval : Code → Code → Prop) where
  candidate : Code → Prop
  outside : ¬ InternallyRepresentable eval candidate

def diagonalStatusExit
    {Code : Type uCode}
    (eval : Code → Code → Prop) :
    StatusRepresentationExit eval :=
  { candidate := diagonalStatus eval
    outside := diagonalStatus_notRepresentable eval }

end DiagonalizationKernel
end Cycle2

/- AXIOM_AUDIT_BEGIN -/
#print axioms Cycle2.DiagonalizationKernel.Represents
#print axioms Cycle2.DiagonalizationKernel.InternallyRepresentable
#print axioms Cycle2.DiagonalizationKernel.diagonalStatus
#print axioms Cycle2.DiagonalizationKernel.GlobalReflectiveClosure
#print axioms Cycle2.DiagonalizationKernel.diagonalStatus_notRepresentable
#print axioms Cycle2.DiagonalizationKernel.noGlobalReflectiveClosure
#print axioms Cycle2.DiagonalizationKernel.diagonalFixedPoint_ofRepresentable
#print axioms Cycle2.DiagonalizationKernel.diagonalFixedPoint_ofRepresentable_unit_example
#print axioms Cycle2.DiagonalizationKernel.StatusRepresentationExit
#print axioms Cycle2.DiagonalizationKernel.diagonalStatusExit
/- AXIOM_AUDIT_END -/
