import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalDerivativeBridge

/-!
# Consumers of the LFR18 → LFR20 / LFR28 bridge

* `eventually_three_quarters_lt_mvfderiv_vertical`: (LFR20.1) `∂_t f_i > 3/4` eventually on `C`, for
  `σ ≤ 1/100` (LFR20's quality range).
* `eventually_abs_mvfderiv_sub_inner_vertical_le_thousandth`: (LFR28.3)
  `‖d(f_i j_i) − dt‖ ≤ 10⁻³` (so `‖d(f_i j_i) − dt‖² ≤ 10⁻⁶`) eventually on `C`, for
  `σ ≤ 10⁻¹⁰` (LFR28's `σ₀`).
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **(LFR20.1).** For `σ ≤ 1/100`: `D f_i(V) > 3/4` eventually, uniformly on `C`. -/
theorem eventually_three_quarters_lt_mvfderiv_vertical [∀ i, CompleteSpace (M i)]
    {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
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
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσ : 0 < σ) {C : Set N} (hC : IsCompact C) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    (hVcont : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I N)))
    (η U : ∀ i, M i → ℝ) (hηlip : ∀ i, LipschitzWith (Real.toNNReal (1 + σ)) (η i))
    (hηsmooth : ∀ᶠ i in atTop, ∀ x ∈ C, MDifferentiableAt I 𝓘(ℝ, ℝ) (η i) (j i x))
    (h19 : ∀ᶠ i in atTop, ∀ x ∈ C,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
        {j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))} (j i x),
        |mvfderiv I (η i) (j i x) w -
          (U i (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))) - U i (j i x)) /
            dist (j i x) (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))))| < σ)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => U i (j i x)) (fun x => (Φ x).fst) atTop C')
    (hσ1 : σ ≤ 1 / 100) :
    ∀ᶠ i in atTop, ∀ x ∈ C, 3 / 4 < mvfderiv I (fun y => η i (j i y)) x (V x) := by
  filter_upwards [eventually_one_sub_lt_mvfderiv_vertical hr G hGnorm g hmetric hK q j hexh hconv
    hdist hcover Φ hℓ hσ hC V hVdir hVcont η U hηlip hηsmooth h19 hU (1 / 8) (by norm_num)]
    with i hi x hx
  linarith [hi x hx]

/-- **(LFR28.3), numerical form.** For `σ ≤ 10⁻¹⁰`: `|d f_i(X) − G(V, X)| ≤ 10⁻³ |X|_G` eventually,
uniformly on `C`. -/
theorem eventually_abs_mvfderiv_sub_inner_vertical_le_thousandth [∀ i, CompleteSpace (M i)]
    {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
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
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσ : 0 < σ) {C : Set N} (hC : IsCompact C) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    (hVcont : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I N)))
    (η U : ∀ i, M i → ℝ) (hηlip : ∀ i, LipschitzWith (Real.toNNReal (1 + σ)) (η i))
    (hηsmooth : ∀ᶠ i in atTop, ∀ x ∈ C, MDifferentiableAt I 𝓘(ℝ, ℝ) (η i) (j i x))
    (h19 : ∀ᶠ i in atTop, ∀ x ∈ C,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
        {j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))} (j i x),
        |mvfderiv I (η i) (j i x) w -
          (U i (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))) - U i (j i x)) /
            dist (j i x) (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))))| < σ)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => U i (j i x)) (fun x => (Φ x).fst) atTop C')
    (hσ1 : σ ≤ 1 / 10 ^ 10) :
    ∀ᶠ i in atTop, ∀ x ∈ C, ∀ X : TangentSpace I x,
      |mvfderiv I (fun y => η i (j i y)) x X - G.inner x (V x) X| ≤
        1 / 1000 * Real.sqrt (G.inner x X X) := by
  filter_upwards [eventually_abs_mvfderiv_sub_inner_vertical_le hr G hGnorm g hmetric hK q j hexh
    hconv hdist hcover Φ hℓ hσ hC V hVdir hVcont η U hηlip hηsmooth h19 hU (1 / 10 ^ 4)
    (by norm_num)]
    with i hi x hx X
  refine (hi x hx X).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have h1 : Real.sqrt (4 * σ + σ ^ 2) ≤ 1 / 10 ^ 4 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    nlinarith
  linarith

end DifferentialGeometry.Geometry.Riemannian.Geodesic
