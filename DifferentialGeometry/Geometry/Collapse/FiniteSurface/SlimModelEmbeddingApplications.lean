import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelEmbedding

/-!
# Consumer: the interpolation inverse images lie in one compact `Q`

`eventually_interpolation_preimage_subset_compact` (LFR20 item 3): the compact
`Q = {|t| ≤ a + 3e}` lies in the open cylinder `{|t| < b}`, and eventually every inverse image of
`[-a, a]` under every straight interpolation `(1 - u) t + u (η_i ∘ j_i)` on the cylinder lies in `Q`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle WithLp
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)] [∀ i, IsRiemannianManifold I (M i)]
  [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]
  {W : Type*} [MetricSpace W]

/-- **Consumer (LFR20 item 3).** One compact `Q` inside the open cylinder encloses all
interpolation inverse images of `[-a, a]`, eventually. -/
theorem eventually_interpolation_preimage_subset_compact [CompactSpace W]
    {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) (hEnorm : ∀ i, IsMetricNorm (g i))
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
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100)
    (hD : ∀ a b : W, dist a b ≤ 10 ^ 3 * Δ)
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] {p : ∀ i, M i} {y₀ : ∀ i, Y i} {β : ℕ → ℝ}
    (α : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : ℝ), y₀ i)) (β i))
    (c : ∀ i, SlimChart (g i) (hEnorm i) Δ σ (α i)) (hpt : ∀ i, j i q = p i)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => ((α i).toFun (j i x)).fst) (fun x => (Φ x).fst) atTop C') :
    IsCompact {x : N | |(Φ x).fst| ≤ 9 / 10 * (10 ^ 6 * Δ) + 3 * (Δ / 100)} ∧
      {x : N | |(Φ x).fst| ≤ 9 / 10 * (10 ^ 6 * Δ) + 3 * (Δ / 100)} ⊆
        {x : N | |(Φ x).fst| < 95 / 100 * (10 ^ 6 * Δ)} ∧
      ∀ᶠ i in atTop, ∀ u ∈ Icc (0 : ℝ) 1, ∀ x, |(Φ x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) →
        |(1 - u) * (Φ x).fst + u * (c i).coord (j i x)| ≤ 9 / 10 * (10 ^ 6 * Δ) →
        x ∈ {x : N | |(Φ x).fst| ≤ 9 / 10 * (10 ^ 6 * Δ) + 3 * (Δ / 100)} := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨V, -, -, hev⟩ := eventually_slimChart_model_embedding hr G hGnorm g hEnorm hmetric hK q j
    hexh hconv hdist hcover Φ hΔ hσ hσ1 hD α c hpt hU
  refine ⟨isCompact_splitting_cylinder Φ _, fun x hx => ?_, ?_⟩
  · change |(Φ x).fst| ≤ _ at hx
    change |(Φ x).fst| < _
    linarith
  · filter_upwards [hev] with i hi u hu x hx hFa
    have h := ((hi.1 x hx).2.2.2 u hu).2 hFa
    change |(Φ x).fst| ≤ _
    linarith

end DifferentialGeometry.Geometry.Collapse
