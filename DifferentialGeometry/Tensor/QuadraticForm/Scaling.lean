import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

namespace QuadraticForm

theorem equivalent_sq_smul {R E : Type*} [CommSemiring R] [AddCommMonoid E] [Module R E]
    (Q : QuadraticForm R E) {c : R} (hc : IsUnit c) :
    QuadraticMap.Equivalent (c ^ 2 • Q) Q := by
  refine ⟨{ LinearEquiv.smulOfUnit hc.unit with map_app' := ?_ }⟩
  intro x
  change Q ((hc.unit : R) • x) = c ^ 2 * Q x
  rw [hc.unit_spec, Q.map_smul]
  simp only [smul_eq_mul, pow_two]

theorem equivalent_smul_of_pos {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (Q : QuadraticForm ℝ E) {c : ℝ} (hc : 0 < c) :
    QuadraticMap.Equivalent (c • Q) Q := by
  simpa only [Real.sq_sqrt hc.le] using
    Q.equivalent_sq_smul (isUnit_iff_ne_zero.2 (ne_of_gt (Real.sqrt_pos.2 hc)))

end QuadraticForm
