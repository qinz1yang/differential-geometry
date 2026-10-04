import DifferentialGeometry.Geometry.Collapse.EdgeModelDirectionTransfer

/-!
# LFR26 consumer: pulled-back nearest-set directions are pairwise close

Consumer of `eventually_inverse_nearest_directions_close_radial`: on the collar, any two pulled-back
source nearest-set directions at the same point are within `2c` of each other for every
`c > 40 √(h + τ)` (a radial inward direction of the model exists by CM3.a and serves as the common
comparison vector). This is the model-side form of LFR25.4's diameter bound.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **LFR26, pairwise form.** Under the hypotheses of LFR26, for every `c > 40 √(h + τ)`,
eventually any two pulled-back source nearest-set directions at a collar point are within `2c`
in the `G`-norm. -/
theorem eventually_inverse_nearest_directions_pairwise_close [∀ i, CompleteSpace (M i)]
    [CompleteSpace N] {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hGsec : ∀ (y : N) (w₁ w₂ : TangentSpace I y), 0 ≤ G.sectionalCurvature y w₁ w₂)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ k h : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hk : 0 < k) (hkΔ : k * Δ ≤ 1 / 100)
    (hh : 0 < h) (hh1 : h < 1 / 100)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i))
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hQcover : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball (j i q) (200 * Δ), dist (Q i x) z ≤ τ * Δ)
    (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hsec : ∀ i, letI : RiemannianBundle (fun x : M i => TangentSpace I x) :=
        ⟨(g i).toRiemannianMetric⟩
      ∀ z ∈ ball (j i q) (1000 * Δ), DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt
        (g i) z (-k ^ 2))
    (hhgt : ∀ h' : ℝ, h < h' → ∀ᶠ i in atTop, ∀ x ∈ ball q (100 * Δ),
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ) :
    ∀ c : ℝ, 40 * Real.sqrt (h + τ) < c → ∀ᶠ i in atTop, ∀ x : N,
      |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ → dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ vi ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) (j i x),
      ∀ vi' ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) (j i x),
        let u : TangentSpace I x := mfderiv I I ((j i).symm : M i → N) (j i x) vi
        let u' : TangentSpace I x := mfderiv I I ((j i).symm : M i → N) (j i x) vi'
        G.inner x (u - u') (u - u') ≤ (2 * c) ^ 2 := by
  intro c hc
  filter_upwards [eventually_inverse_nearest_directions_close_radial hr G hGnorm hGsec g hmetric hK q
    j hexh hconv hdist hcover Φ hΦq hΔ hτ hτ1 hk hkΔ hh hh1 Q A hQp hQdist hheight hQcover hpA
    hborder hbordercover hsec hhgt c hc] with i hi
  intro x ht hr1 hr2 vi hvi vi' hvi'
  have hSne : (Φ ⁻¹' {z | z.snd = z₀}).Nonempty := ⟨q, by
    simp only [mem_preimage, mem_ofPred_eq, hΦq, WithLp.toLp_snd]⟩
  obtain ⟨v, hv⟩ := (ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo_nonempty_isCompact G hr
    hGnorm (isClosed_axis Φ z₀) hSne x).1
  intro u u'
  have h1 : G.inner x (u - v) (u - v) ≤ c ^ 2 := hi x ht hr1 hr2 vi hvi v hv
  have h2 : G.inner x (u' - v) (u' - v) ≤ c ^ 2 := hi x ht hr1 hr2 vi' hvi' v hv
  have hnorm : ∀ a : TangentSpace I x, ‖a‖ = Real.sqrt (G.inner x a a) := fun a => by
    have h := hGnorm x a
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.sqrt_nonneg _)).mp h
  have hc0 : 0 ≤ c := le_trans (by positivity) hc.le
  have hb1 : ‖u - v‖ ≤ c := by
    rw [hnorm]
    exact Real.sqrt_le_iff.mpr ⟨hc0, h1⟩
  have hb2 : ‖u' - v‖ ≤ c := by
    rw [hnorm]
    exact Real.sqrt_le_iff.mpr ⟨hc0, h2⟩
  have htri : ‖u - u'‖ ≤ 2 * c := by
    calc ‖u - u'‖ = ‖(u - v) - (u' - v)‖ := by congr 1; abel
      _ ≤ ‖u - v‖ + ‖u' - v‖ := norm_sub_le _ _
      _ ≤ 2 * c := by linarith
  rw [hnorm] at htri
  have hnn := DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg G x (u - u')
  calc G.inner x (u - u') (u - u') = Real.sqrt (G.inner x (u - u') (u - u')) ^ 2 :=
        (Real.sq_sqrt hnn).symm
    _ ≤ (2 * c) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) htri 2

end DifferentialGeometry.Geometry.Riemannian.Geodesic
