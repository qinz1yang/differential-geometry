import DifferentialGeometry.Geometry.Metric.Comparison.DerivativeDistance
import DifferentialGeometry.Geometry.Metric.ConvexChartDistance
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Metric

section
variable {E F H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsRiemannianManifold I M]

theorem edist_bounds_of_radial_partial_homeomorph
    (Φ : OpenPartialHomeomorph E M)
    (hΦ : ContMDiffOn 𝓘(ℝ, E) I 1 Φ Φ.source)
    (hΦinv : ContMDiffOn I 𝓘(ℝ, E) 1 Φ.symm Φ.target)
    {R : ℝ} (hR : 0 < R)
    (hsource : Metric.ball (0 : E) R ⊆ Φ.source)
    (himage : (Φ : E → M) '' Metric.ball 0 R = Metric.ball (Φ 0) R)
    (hrad : ∀ z ∈ Metric.ball 0 R, dist (Φ z) (Φ 0) = ‖z‖)
    (C D : ℝ≥0)
    (hforward : ∀ z ∈ Metric.ball 0 R, ∀ v : E,
      ‖mfderiv 𝓘(ℝ, E) I Φ z v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ)
    (hinverse : ∀ z ∈ Metric.ball (Φ 0) R, ∀ w : TangentSpace I z,
      ‖mfderiv I 𝓘(ℝ, E) Φ.symm z w‖ₑ ≤ (D : ℝ≥0∞) * ‖w‖ₑ)
    {x y : E} (hx : ‖x‖ ≤ R / 8) (hy : ‖y‖ ≤ R / 8) :
    edist x y ≤ (D : ℝ≥0∞) * edist (Φ x) (Φ y) ∧
      edist (Φ x) (Φ y) ≤ (C : ℝ≥0∞) * edist x y := by
  have hxR : x ∈ Metric.ball (0 : E) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hyR : y ∈ Metric.ball (0 : E) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hbuffer : Metric.closedEBall (Φ x) (ENNReal.ofReal (R / 2)) ⊆
      Metric.ball (Φ 0) R := by
    rw [Metric.closedEBall_ofReal (by positivity)]
    intro z hz
    have hz' : dist z (Φ x) ≤ R / 2 := hz
    have htri := dist_triangle z (Φ x) (Φ 0)
    rw [hrad x hxR] at htri
    change dist z (Φ 0) < R
    linarith
  have htarget : Metric.ball (Φ 0) R ⊆ Φ.target := by
    rw [← himage]
    rintro z ⟨w, hw, rfl⟩
    exact Φ.map_source (hsource hw)
  have hsep : edist (Φ x) (Φ y) < ENNReal.ofReal (R / 2) := by
    rw [edist_lt_ofReal]
    have htri := dist_triangle (Φ x) (Φ 0) (Φ y)
    rw [hrad x hxR, dist_comm (Φ 0) (Φ y), hrad y hyR] at htri
    linarith
  constructor
  · have h := Manifold.edist_map_le_mul_of_enorm_mfderiv_le_on_closedEBall
      Φ.open_target hΦinv (hbuffer.trans htarget)
      (fun z hz w => hinverse z (hbuffer hz) w) hsep
    simpa only [Φ.left_inv (hsource hxR), Φ.left_inv (hsource hyR)] using h
  · rw [IsRiemannianManifold.out (I := I)]
    exact Manifold.riemannianEDist_le_mul_edist_of_convex
      Φ.open_source hΦ hsource (convex_ball (0 : E) R) hforward hxR hyR
end

section
variable {E F H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem edist_bounds_of_normalized_radial_chart
    (g : SmoothRiemannianMetric I M)
    (hg : letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; IsRiemannianManifold I M)
    (Φ : OpenPartialHomeomorph E M)
    (hΦ : ContMDiffOn 𝓘(ℝ, E) I 1 Φ Φ.source)
    (hΦinv : ContMDiffOn I 𝓘(ℝ, E) 1 Φ.symm Φ.target)
    {R : ℝ} (hR : 0 < R)
    (hsource : Metric.ball (0 : E) R ⊆ Φ.source)
    (himage : (Φ : E → M) '' Metric.ball 0 R = Metric.ball (Φ 0) R)
    (hrad : ∀ z ∈ Metric.ball 0 R, dist (Φ z) (Φ 0) = ‖z‖)
    (hforms : ∀ z ∈ Metric.ball 0 R, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients g Φ z v v ∧
      pullbackMetricCoefficients g Φ z v v ≤ 2 * ‖v‖ ^ 2)
    {x y : E} (hx : ‖x‖ ≤ R / 8) (hy : ‖y‖ ≤ R / 8) :
    edist x y ≤ 2 * edist (Φ x) (Φ y) ∧
      edist (Φ x) (Φ y) ≤ 2 * edist x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsRiemannianManifold I M := hg
  have hnorm (z : E) (v : E) :
      ‖mfderiv 𝓘(ℝ, E) I Φ z v‖ ^ 2 = pullbackMetricCoefficients g Φ z v v := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  have hd : Φ.MDifferentiable 𝓘(ℝ, E) I :=
    ⟨hΦ.mdifferentiableOn one_ne_zero, hΦinv.mdifferentiableOn one_ne_zero⟩
  apply edist_bounds_of_radial_partial_homeomorph Φ hΦ hΦinv hR hsource himage hrad
    (2 : ℝ≥0) (2 : ℝ≥0) ?_ ?_ hx hy
  · intro z hz v
    have hq := (hforms z hz v).2
    rw [← hnorm] at hq
    have hn : ‖mfderiv 𝓘(ℝ, E) I Φ z v‖ ≤ 2 * ‖v‖ := by
      nlinarith [norm_nonneg (mfderiv 𝓘(ℝ, E) I Φ z v), norm_nonneg v,
        sq_nonneg (‖mfderiv 𝓘(ℝ, E) I Φ z v‖ - 2 * ‖v‖)]
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_norm,
      ENNReal.ofReal_ofNat, ENNReal.coe_ofNat] using ENNReal.ofReal_le_ofReal hn
  · intro z hz w
    have hpre : Φ.symm z ∈ Metric.ball (0 : E) R := by
      rw [← himage] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      simpa only [Φ.left_inv (hsource hv)] using hv
    have hzt : z ∈ Φ.target := by
      rw [← himage] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      exact Φ.map_source (hsource hv)
    have hcomp := DFunLike.congr_fun (hd.comp_symm_deriv hzt) w
    change mfderiv 𝓘(ℝ, E) I Φ (Φ.symm z) (mfderiv I 𝓘(ℝ, E) Φ.symm z w) = w at hcomp
    have hq := (hforms (Φ.symm z) hpre (mfderiv I 𝓘(ℝ, E) Φ.symm z w)).1
    have hn0 := hnorm (Φ.symm z) (mfderiv I 𝓘(ℝ, E) Φ.symm z w)
    change ‖mfderiv 𝓘(ℝ, E) I Φ (Φ.symm z) (mfderiv I 𝓘(ℝ, E) Φ.symm z w)‖ ^ 2 = _ at hn0
    rw [hcomp] at hn0
    erw [Φ.right_inv hzt] at hn0
    have hsq := hq.trans hn0.symm.le
    have key : ∀ a b : ℝ, (1 / 2 : ℝ) * a ^ 2 ≤ b ^ 2 → 0 ≤ b → a ≤ 2 * b := by
      intro a b hab hb
      have hab' : a ^ 2 ≤ (2 * b) ^ 2 := by
        nlinarith [sq_nonneg b, hab]
      exact le_of_sq_le_sq hab' (by linarith [hb])
    have hn := key _ _ hsq (norm_nonneg w)
    have hn' : ‖NormedSpace.fromTangentSpace (𝕜 := ℝ) (Φ.symm z)
        (mfderiv I 𝓘(ℝ, E) Φ.symm z w)‖ ≤ 2 * ‖w‖ := hn
    have h2 := ENNReal.ofReal_le_ofReal hn'
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_norm,
      ENNReal.ofReal_ofNat] at h2
    rw [enorm_tangentSpace_vectorSpace, ENNReal.coe_ofNat]
    exact h2
end

end DifferentialGeometry.Geometry.Metric
