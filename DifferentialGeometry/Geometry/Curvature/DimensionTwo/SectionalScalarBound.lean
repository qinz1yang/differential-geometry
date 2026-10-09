import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalCurvature
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# Sectional lower bounds on surfaces are scalar lower bounds

On a surface the curvature tensor is `Rm = (R / 2) g ∧ g`
(`metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two`), so the sectional lower bound
`SectionalBoundedBelow g K` says exactly `2 K ≤ R`. This turns the scalar maximum principles for
the scalar curvature along a Ricci flow into statements about sectional curvature.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

/-- On a surface, `Rm(v, w, w, v)` is half the scalar curvature times the Gram determinant. -/
theorem metricRm04StandardAt_sectional_eq_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2) (x : M)
    (v w : TangentSpace I x) :
    metricRm04StandardAt (I := I) (M := M) g x v w w v =
      metricScalarAt (I := I) g x / 2 * sectionalCurvatureDenominator (I := I) g x v w := by
  rw [metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hdim x v w w v,
    sectionalCurvatureDenominator_def, g.symm x w v, ← pow_two]

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- A tangent plane of a surface contains a linearly independent pair. -/
theorem exists_linearIndependent_pair_of_finrank_eq_two
    (hdim : Module.finrank Real E = 2) (x : M) :
    ∃ v w : TangentSpace I x, LinearIndependent Real ![v, w] := by
  have hdimT : Module.finrank Real (TangentSpace I x) = 2 := hdim
  let b := Module.finBasisOfFinrankEq Real (TangentSpace I x) hdimT
  refine ⟨b 0, b 1, ?_⟩
  convert b.linearIndependent using 1
  funext i
  fin_cases i <;> rfl

/-- **Pointwise bridge.** On a surface, `sec ≥ K` at `x` iff `K ≤ R(x) / 2`. -/
theorem sectionalBoundedBelowAt_iff_le_half_scalar_of_finrank_eq_two
    (hdim : Module.finrank Real E = 2) {g : SmoothRiemannianMetric I M} {x : M} {K : Real} :
    SectionalBoundedBelowAt g x K ↔ K ≤ metricScalarAt (I := I) g x / 2 := by
  constructor
  · intro h
    obtain ⟨v, w, hvw⟩ := exists_linearIndependent_pair_of_finrank_eq_two (I := I) hdim x
    have hden := sectionalCurvatureDenominator_pos_of_linearIndependent g x v w hvw
    have hvw' := h v w
    rw [metricRm04StandardAt_sectional_eq_of_finrank_eq_two g hdim x v w] at hvw'
    rw [sectionalCurvatureDenominator_def] at hden
    rw [sectionalCurvatureDenominator_def] at hvw'
    exact le_of_mul_le_mul_right hvw' hden
  · intro hK v w
    rw [metricRm04StandardAt_sectional_eq_of_finrank_eq_two g hdim x v w]
    have hden := sectionalCurvatureDenominator_nonneg g x v w
    rw [sectionalCurvatureDenominator_def] at hden ⊢
    exact mul_le_mul_of_nonneg_right hK hden

/-- **Global bridge.** On a surface, `sec ≥ K` everywhere iff `2 K ≤ R` everywhere. -/
theorem sectionalBoundedBelow_iff_two_mul_le_scalar_of_finrank_eq_two
    (hdim : Module.finrank Real E = 2) {g : SmoothRiemannianMetric I M} {K : Real} :
    SectionalBoundedBelow g K ↔ ∀ x, 2 * K ≤ metricScalarAt (I := I) g x := by
  refine forall_congr' fun x => ?_
  rw [sectionalBoundedBelowAt_iff_le_half_scalar_of_finrank_eq_two hdim]
  constructor <;> intro h <;> linarith

/-- On a surface with vanishing scalar curvature the whole curvature tensor vanishes. -/
theorem metricRm04StandardAt_eq_zero_of_scalar_eq_zero_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2) {x : M}
    (hR : metricScalarAt (I := I) g x = 0) (v w z u : TangentSpace I x) :
    metricRm04StandardAt (I := I) (M := M) g x v w z u = 0 := by
  rw [metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hdim x v w z u, hR, zero_div,
    zero_mul]

end DifferentialGeometry.Geometry.Riemannian
