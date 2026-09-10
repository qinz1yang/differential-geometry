import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Real.Basic



noncomputable section
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem basis_orientation_eq_iff (b c : Module.Basis (Fin n) ℝ V) :
    b.orientation = c.orientation ↔ 0 < b.det c := b.orientation_eq_iff_det_pos c

theorem orientation_has_basis [NeZero n] (hdim : Module.finrank ℝ V = n)
    (o : Orientation ℝ V (Fin n)) : ∃ b : Module.Basis (Fin n) ℝ V, b.orientation = o :=
  ⟨o.someBasis (by simpa using hdim.symm), o.someBasis_orientation (by simpa using hdim.symm)⟩

omit [FiniteDimensional ℝ V] in
theorem orientation_two_classes (b : Module.Basis (Fin n) ℝ V) :
    b.orientation ≠ -b.orientation ∧
      ∀ o : Orientation ℝ V (Fin n), o = b.orientation ∨ o = -b.orientation :=
  ⟨Module.Ray.ne_neg_self _, b.orientation_eq_or_eq_neg⟩


theorem map_orientation_eq_iff (hdim : Module.finrank ℝ V = n)
    (o : Orientation ℝ V (Fin n)) (A : V ≃ₗ[ℝ] V) :
    Orientation.map (Fin n) A o = o ↔ 0 < LinearMap.det (A : V →ₗ[ℝ] V) :=
  o.map_eq_iff_det_pos A (by simpa using hdim.symm)

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
