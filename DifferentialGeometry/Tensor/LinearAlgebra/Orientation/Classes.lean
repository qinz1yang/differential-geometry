import Mathlib.LinearAlgebra.Orientation
import Mathlib.Basic.Real.Basic



noncomputable section
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem orientation_has_basis [NeZero n] (hdim : Module.finrank ℝ V = n)
    (o : Orientation ℝ V (Fin n)) : ∃ b : Module.Basis (Fin n) ℝ V, b.orientation = o :=
  ⟨o.someBasis (by simpa using hdim.symm), o.someBasis_orientation (by simpa using hdim.symm)⟩

omit [FiniteDimensional ℝ V] in
theorem orientation_two_classes (b : Module.Basis (Fin n) ℝ V) :
    b.orientation ≠ -b.orientation ∧
      ∀ o : Orientation ℝ V (Fin n), o = b.orientation ∨ o = -b.orientation :=
  ⟨Module.Ray.ne_neg_self _, b.orientation_eq_or_eq_neg⟩


omit [FiniteDimensional ℝ V] in
def orientationEquivBool (b : Module.Basis (Fin n) ℝ V) : Orientation ℝ V (Fin n) ≃ Bool := by
  classical
  apply Equiv.symm
  apply Equiv.ofBijective (fun q : Bool => if q then b.orientation else -b.orientation)
  constructor
  · intro q r h
    cases q <;> cases r
    · rfl
    · exact False.elim (Module.Ray.ne_neg_self b.orientation (by simpa using h.symm))
    · exact False.elim (Module.Ray.ne_neg_self b.orientation (by simpa using h))
    · rfl
  · intro o
    rcases b.orientation_eq_or_eq_neg o with h | h
    · exact ⟨true, by simpa using h.symm⟩
    · exact ⟨false, by simpa using h.symm⟩

end DifferentialGeometry.VectorBundle
