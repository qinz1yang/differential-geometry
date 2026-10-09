import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientSectional
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientPullback
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientTransition

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Analysis

theorem coefficientSectional_transition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hc : ContDiffOn ℝ 2 c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 3 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    {x : E} (hx : x ∈ U) (v u : E) :
    coefficientSectional b x v u =
      coefficientSectional c (Φ x) (fderiv ℝ Φ x v) (fderiv ℝ Φ x u) := by
  rw [coefficientSectional_def, coefficientSectional_def,
    coefficientRm04_transition hU hV hc hcsymm hcco hΦ hΦUV hΦinv hpull hx v u u v,
    hpull x hx v v, hpull x hx u u, hpull x hx v u]

theorem coefficientRm04_lower_bound_of_pullback {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hc : ContDiffOn ℝ 2 c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 3 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    (κ : ℝ)
    (hκ : ∀ z ∈ V, ∀ v u : E,
      κ * (c z v v * c z u u - (c z v u) ^ 2) ≤ coefficientRm04 c z v u u v) :
    ∀ y ∈ U, ∀ v u : E,
      κ * (b y v v * b y u u - (b y v u) ^ 2) ≤ coefficientRm04 b y v u u v := by
  intro y hy v u
  rw [coefficientRm04_transition hU hV hc hcsymm hcco hΦ hΦUV hΦinv hpull hy v u u v,
    hpull y hy v v, hpull y hy u u, hpull y hy v u]
  exact hκ (Φ y) (hΦUV hy) (fderiv ℝ Φ y v) (fderiv ℝ Φ y u)

theorem coefficientSectional_nonneg_of_pullback {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hc : ContDiffOn ℝ 2 c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 3 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    (hsign : ∀ z ∈ V, ∀ v u : E, 0 ≤ coefficientRm04 c z v u u v) :
    ∀ y ∈ U, ∀ v u : E,
      0 ≤ coefficientRm04 b y v u u v ∧ 0 ≤ coefficientSectional b y v u := by
  intro y hy v u
  have h1 : 0 ≤ coefficientRm04 b y v u u v := by
    rw [coefficientRm04_transition hU hV hc hcsymm hcco hΦ hΦUV hΦinv hpull hy v u u v]
    exact hsign (Φ y) (hΦUV hy) (fderiv ℝ Φ y v) (fderiv ℝ Φ y u)
  obtain ⟨C, hC, hCu⟩ := isCoercive_of_pullback hcco hΦUV hΦinv hpull y hy
  refine ⟨h1, ?_⟩
  rw [coefficientSectional_def]
  exact div_nonneg h1 (bilin_gram_nonneg (symm_of_pullback hcsymm hΦUV hpull y hy)
    (fun w => (mul_nonneg (mul_nonneg hC.le (norm_nonneg w)) (norm_nonneg w)).trans (hCu w)) v u)

end DifferentialGeometry.Analysis
