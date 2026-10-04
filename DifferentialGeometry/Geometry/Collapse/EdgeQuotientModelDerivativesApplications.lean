import DifferentialGeometry.Geometry.Collapse.EdgeQuotientModelDerivatives

/-!
# Consumer: the numeric form `< 10⁻³` of (LFR28.4) for the edge quotient

Blueprint LFR28 proof step 2 fixes `ε, μ, λ ≤ 10⁻⁸` and `40√(h + τ) < 10⁻⁵`, and the model
smoothing has gradient error `10⁻⁸`; then `‖d(η_i ∘ j_i) - dG_N‖ < 10⁻³` on the collar (LFR28.4).
`eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le_thousandth` is that conclusion, from the
binding with `c = ε' = 10⁻⁵` (bound `3·10⁻⁸ + 2·10⁻⁵ ≤ 10⁻³`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

/-- **(LFR28.4), numeric form.** Under the binding's hypotheses with LFR28's constants
(`ε ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`, model gradient error `ε_N ≤ 10⁻⁸`, `40√(h+τ) < 10⁻⁵`), eventually on the
collar `|d(η_i ∘ j_i)(X) - dG_N(X)| ≤ 10⁻³ |X|_G`. -/
theorem eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le_thousandth [∀ i, CompleteSpace (M i)]
    [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
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
    {Δ τ k h : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτ4 : τ ≤ 1 / 4) (hk : 0 < k)
    (hkΔ : k * Δ ≤ 1 / 100) (hh : 0 < h) (hh1 : h < 1 / 100)
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
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ)
    (hAc : ∀ i, IsClosed (A i))
    (F ρ : ∀ i, M i → ℝ) {Λ : ℝ≥0} {ε : ℝ} (hε : 0 ≤ ε)
    (hρ : ∀ i, LipschitzWith Λ (ρ i)) (hρp : ∀ i, ρ i (j i q) = 1)
    (hlam : 100 * Δ * Λ < 1 / 100)
    (hρs : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ρ i) (ball (j i q) (100 * Δ)))
    (O : ∀ i, Set (M i)) (hO : ∀ i, IsOpen (O i))
    (hCO : ∀ i, closedBall (j i q) (20 * Δ) ∩
      {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ} ⊆ O i)
    (hFs : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (F i) (O i))
    (hFgrad : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      ∀ v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) y,
        Real.sqrt ((g i).inner y (gradFun (g i) (F i) y + v) (gradFun (g i) (F i) y + v)) < ε)
    (hquot : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      Real.sqrt ((g i).inner y (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)
        (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)) ≤ 100 * Δ * Λ)
    (GN : N → ℝ) {εN : ℝ}
    (hGgrad : ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ G.finiteMinimizingDirectionsTo (Φ ⁻¹' {z | z.snd = z₀}) x, ∀ X : TangentSpace I x,
        |mvfderiv I GN x X + G.inner x v X| ≤ εN * Real.sqrt (G.inner x X X))
    (hε8 : ε ≤ 1 / 10 ^ 8) (hlam8 : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hεN8 : εN ≤ 1 / 10 ^ 8)
    (hhτ : 40 * Real.sqrt (h + τ) < 1 / 10 ^ 5) :
    ∀ᶠ i in atTop, ∀ x : N,
      |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ → dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ X : TangentSpace I x,
        |mvfderiv I (fun y => F i (j i y) / ρ i (j i y)) x X - mvfderiv I GN x X| ≤
          1 / 1000 * Real.sqrt (G.inner x X X) := by
  filter_upwards [eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le hr G hGnorm hGsec g
    hmetric hK q j hexh hconv hdist hcover Φ hΦq hΔ hτ hτ4 hk hkΔ hh hh1 Q A hQp hQdist hheight
    hQcover hpA hborder hbordercover hsec hhgt hAc F ρ hε hρ hρp hlam hρs O hO hCO hFs hFgrad
    hquot GN hGgrad (1 / 10 ^ 5) hhτ (1 / 10 ^ 5) (by norm_num)] with i hi
  intro x ht hr1 hr2 X
  refine (hi x ht hr1 hr2 X).trans ?_
  have hs : 0 ≤ Real.sqrt (G.inner x X X) := Real.sqrt_nonneg _
  have hc : ε + 100 * Δ * Λ + εN + 1 / 10 ^ 5 + 1 / 10 ^ 5 ≤ 1 / 1000 := by linarith
  exact mul_le_mul_of_nonneg_right hc hs

end DifferentialGeometry.Geometry.Collapse
