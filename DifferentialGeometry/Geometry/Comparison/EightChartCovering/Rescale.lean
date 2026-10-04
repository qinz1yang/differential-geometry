import DifferentialGeometry.Geometry.Comparison.EightChartCovering
import DifferentialGeometry.Geometry.Comparison.RescaleComparison
import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleLength

set_option autoImplicit false

noncomputable section
open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_closedBall_net_of_positive_curvature_scale_and_chart
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {κ R L δ ε : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    [LocallyCompactSpace (ball o (8 * R))]
    (hlocal : ∀ z ∈ ball o (8 * R),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball o (R / 2)) {n : ℕ} (hn : 0 < n)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hε : 0 < ε)
    (φ : ball q δ → EuclideanSpace ℝ (Fin n))
    (hφ0 : φ ⟨q, mem_ball_self hδ⟩ = 0)
    (hφlower : ∀ u v, L⁻¹ * dist u v ≤ dist (φ u) (φ v))
    (hφupper : ∀ u v, dist (φ u) (φ v) ≤ L * dist u v) :
    ∃ T : Finset X,
      T.card ≤ (1 + ⌈4 * L ^ 2 * sqrt n * sinh (2 * (sqrt κ * R)) /
        (sqrt κ * ε)⌉₊) ^ n ∧
      (T : Set X) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  let c := sqrt κ
  have hc : 0 < c := sqrt_pos.mpr hκ
  let m' := m.rescale c hc
  let _ : MetricSpace X := m
  have hcomplete : @CompleteSpace X m'.toUniformSpace :=
    (m.rescale_completeSpace_iff c hc).mpr inferInstance
  have hcurves' := @MetricSpace.rescale_arbitrarily_short_curves X m hcurves c hc
  have hball : @ball X m'.toPseudoMetricSpace o (8 * (c * R)) = ball o (8 * R) := by
    rw [show 8 * (c * R) = c * (8 * R) by ring]
    exact m.rescale_ball c hc o (8 * R)
  have hcompact : LocallyCompactSpace (@ball X m'.toPseudoMetricSpace o (8 * (c * R))) := by
    rw [hball]
    infer_instance
  have hlocal' : ∀ z ∈ @ball X m'.toPseudoMetricSpace o (8 * (c * R)),
      ∃ Ω : Set X, @IsOpen X m'.toUniformSpace.toTopologicalSpace Ω ∧
        @fourPointComparison X m' 1 Ω ∧ z ∈ Ω := by
    rw [hball]
    intro z hz
    exact (@local_fourPointComparison_rescale_sqrt_iff X m κ hκ z).mpr (hlocal z hz)
  let d : @ball X m'.toPseudoMetricSpace q (c * δ) → ball q δ :=
    fun x => ⟨x.1, (mul_lt_mul_iff_right₀ hc).mp x.2⟩
  let ψ : @ball X m'.toPseudoMetricSpace q (c * δ) → EuclideanSpace ℝ (Fin n) :=
    fun x => c • φ (d x)
  have hψdist (x y : @ball X m'.toPseudoMetricSpace q (c * δ)) :
      dist (ψ x) (ψ y) = c * dist (φ (d x)) (φ (d y)) := by
    simp only [ψ, dist_smul₀, Real.norm_eq_abs, abs_of_pos hc]
  have hq' : q ∈ @ball X m'.toPseudoMetricSpace o (c * R / 2) := by
    change c * dist q o < c * R / 2
    have h := mul_lt_mul_of_pos_left hq hc
    linarith
  obtain ⟨T, hcard, hT, hnet⟩ :=
    @exists_closedBall_net_of_intrinsic_8_comparison_and_chart X m' hcomplete
      (fun a b ε hε => hcurves' a b hε) o (c * R) L (c * δ) (c * ε)
      (mul_pos hc hR) hcompact (fun z =>
        (@exists_local_fourPointComparison_intrinsicBall_iff X m'
          (fun a b ε hε => hcurves' a b hε) o (8 * (c * R)) 1
          (by positivity) z).mpr (hlocal' z z.property))
      q hq' n hn hL (mul_pos hc hδ) (mul_pos hc hε) ψ
      (by change c • φ ⟨q, _⟩ = 0; rw [hφ0, smul_zero])
      (by
        intro x y
        change L⁻¹ * (c * dist (d x) (d y)) ≤ dist (ψ x) (ψ y)
        rw [hψdist]
        nlinarith [mul_le_mul_of_nonneg_left (hφlower (d x) (d y)) hc.le])
      (by
        intro x y
        change dist (ψ x) (ψ y) ≤ L * (c * dist (d x) (d y))
        rw [hψdist]
        nlinarith [mul_le_mul_of_nonneg_left (hφupper (d x) (d y)) hc.le])
  refine ⟨T, hcard, ?_, ?_⟩
  · rwa [m.rescale_closedBall c hc o R] at hT
  · intro x hx
    have hx' : x ∈ @closedBall X m'.toPseudoMetricSpace o (c * R) := by
      rwa [m.rescale_closedBall c hc o R]
    obtain ⟨y, hy, hxy⟩ := hnet x hx'
    exact ⟨y, hy, (mul_lt_mul_iff_right₀ hc).mp hxy⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
