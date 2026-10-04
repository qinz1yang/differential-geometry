import DifferentialGeometry.Geometry.Collapse.EdgeSourceDerivatives

/-!
# (LFR28.4), numerical form

Consumer of `eventually_abs_mvfderiv_comp_sub_model_le`: when the gradient errors and LFR26's
angular tolerance satisfy `ε_S + ε_N + 40 √(h + τ) < 10⁻³` (LFR28's parameter choice:
`40 √(h + τ) < 10⁻⁵`, LFR27's `ε + 150ΔΛ` and LFR02's `10⁻⁸`), eventually on the collar
`‖d(F_i ∘ j_i) − dG_N‖_G ≤ 10⁻³`, the form (LFR28.4) consumed by the transversality step.
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

/-- **(LFR28.4), numerical form.** If `ε_S + ε_N + 40 √(h + τ) < 10⁻³`, then eventually on the
collar `|d(F_i ∘ j_i)(X) − dG_N(X)| ≤ 10⁻³ |X|_G`. -/
theorem eventually_abs_mvfderiv_comp_sub_model_le_thousandth [∀ i, CompleteSpace (M i)]
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
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ)
    (hAc : ∀ i, IsClosed (A i)) (F : ∀ i, M i → ℝ) {εS εN : ℝ} (hεS : 0 ≤ εS)
    (hFd : ∀ᶠ i in atTop, ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ → MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) (j i x))
    (hFgrad : ∀ᶠ i in atTop, ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) (j i x),
      ∀ w : TangentSpace I (j i x),
        |mvfderiv I (F i) (j i x) w + (g i).inner (j i x) v w| ≤
          εS * Real.sqrt ((g i).inner (j i x) w w))
    (GN : N → ℝ)
    (hGgrad : ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ G.finiteMinimizingDirectionsTo (Φ ⁻¹' {z | z.snd = z₀}) x, ∀ X : TangentSpace I x,
        |mvfderiv I GN x X + G.inner x v X| ≤ εN * Real.sqrt (G.inner x X X))
    (hsmall : εS + εN + 40 * Real.sqrt (h + τ) < 1 / 1000) :
    ∀ᶠ i in atTop, ∀ x : N,
      |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ → dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ X : TangentSpace I x,
        |mvfderiv I (fun y => F i (j i y)) x X - mvfderiv I GN x X| ≤
          1 / 1000 * Real.sqrt (G.inner x X X) := by
  set δ : ℝ := (1 / 1000 - (εS + εN + 40 * Real.sqrt (h + τ))) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hk' := eventually_abs_mvfderiv_comp_sub_model_le hr G hGnorm hGsec g hmetric hK q j hexh
    hconv hdist hcover Φ hΦq hΔ hτ hτ1 hk hkΔ hh hh1 Q A hQp hQdist hheight hQcover hpA hborder
    hbordercover hsec hhgt hAc F hεS hFd hFgrad GN hGgrad (40 * Real.sqrt (h + τ) + δ)
    (by linarith) δ hδ0
  filter_upwards [hk'] with i hi x ht hr1 hr2 X
  refine (hi x ht hr1 hr2 X).trans (le_of_eq ?_)
  congr 1
  rw [hδ]
  ring

end DifferentialGeometry.Geometry.Riemannian.Geodesic
