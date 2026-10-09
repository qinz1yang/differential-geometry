import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientField

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis

def coefficientSectional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x v u : E) : ℝ :=
  coefficientRm04 b x v u u v / (b x v v * b x u u - (b x v u) ^ 2)

theorem coefficientSectional_def {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x v u : E) :
    coefficientSectional b x v u =
      coefficientRm04 b x v u u v / (b x v v * b x u u - (b x v u) ^ 2) :=
  rfl

private theorem bilin_smul_add_smul_self {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ u v : E, B u v = B v u)
    (v u : E) (s t : ℝ) :
    B (s • v + t • u) (s • v + t • u) =
      s * s * B v v + 2 * s * t * B v u + t * t * B u u := by
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  linear_combination (s * t) * hsymm u v

theorem bilin_gram_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ u v : E, B u v = B v u)
    (hpos : ∀ w : E, 0 ≤ B w w) (v u : E) :
    0 ≤ B v v * B u u - (B v u) ^ 2 := by
  have h1 := hpos (-B v u • v + B v v • u)
  have h2 := hpos (-(B u u + 1) • v + B v u • u)
  rw [bilin_smul_add_smul_self hsymm] at h1 h2
  rcases (hpos v).lt_or_eq with ha | ha
  · have h3 : 0 ≤ B v v * (B v v * B u u - B v u ^ 2) := by linarith
    exact nonneg_of_mul_nonneg_right h3 ha
  · rw [← ha] at h2 ⊢
    linarith [mul_nonneg (sq_nonneg (B v u)) (hpos u)]

theorem bilin_gram_pos_of_linearIndependent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ u v : E, B u v = B v u)
    (hco : IsCoercive B) {v u : E} (hvu : LinearIndependent ℝ ![v, u]) :
    0 < B v v * B u u - (B v u) ^ 2 := by
  obtain ⟨C, hC, hCu⟩ := hco
  have hind := LinearIndependent.pair_iff.mp hvu
  have hposw : ∀ w : E, w ≠ 0 → 0 < B w w := fun w hw =>
    lt_of_lt_of_le (mul_pos (mul_pos hC (norm_pos_iff.mpr hw)) (norm_pos_iff.mpr hw)) (hCu w)
  have hv : v ≠ 0 := by
    intro h
    exact one_ne_zero (hind 1 0 (by rw [h, smul_zero, zero_smul, add_zero])).1
  have ha := hposw v hv
  have hw : -B v u • v + B v v • u ≠ 0 := fun h => ha.ne' (hind _ _ h).2
  have h1 := hposw _ hw
  rw [bilin_smul_add_smul_self hsymm] at h1
  have h2 : 0 < B v v * (B v v * B u u - B v u ^ 2) := by linarith
  exact pos_of_mul_pos_right h2 ha.le

end DifferentialGeometry.Analysis
