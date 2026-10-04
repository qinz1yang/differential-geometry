import DifferentialGeometry.Geometry.Collapse.EdgeSourceHeights
import DifferentialGeometry.Geometry.Collapse.EdgeModelDirectionTransferApplications

/-!
# LFR28 step 2, angular part: (LFR28.2) feeds LFR26

Consumer of `eventually_abs_height_sub_axisDist_le` (LFR28.2) and
`eventually_inverse_nearest_directions_close_radial` (LFR26): when the coarse-border charts' first
coordinates converge to `t` uniformly on `B̄(q, 100Δ)`, LFR26 applies with `h = 20 √τ` (the blueprint
uses `40 √τ`, A:27305), giving the comparison of EVERY pulled-back source nearest-set direction with
EVERY radial inward model direction on the collar, `‖d j⁻¹ v_i − v‖ ≤ c` for
`c > 40 √(20 √τ + τ)`. This is the angular input of (LFR28.4).
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

/-- **LFR28.2 ⇒ LFR26.** Under LFR26's hypotheses with the height bound (LFR26.1) replaced by the
uniform convergence `u_i ∘ j_i → t` on `B̄(q, 100Δ)` and `0 < τ`, `20 √τ < 1/100`: for every
`c > 40 √(20 √τ + τ)`, eventually on the collar every pulled-back source nearest-set direction is
within `c` of every radial inward model direction. -/
theorem eventually_inverse_nearest_directions_close_radial_of_coarseBorder_height [∀ i, CompleteSpace (M i)]
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
    {Δ τ k : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hk : 0 < k) (hkΔ : k * Δ ≤ 1 / 100)
    (hτ0 : 0 < τ) (hτs : 20 * Real.sqrt τ < 1 / 100)
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
    (hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst) (fun x => (Φ x).fst) atTop
      (closedBall q (100 * Δ))) :
    ∀ c : ℝ, 40 * Real.sqrt (20 * Real.sqrt τ + τ) < c → ∀ᶠ i in atTop, ∀ x : N,
      |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ → dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ vi ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) (j i x),
      ∀ v ∈ G.finiteMinimizingDirectionsTo (Φ ⁻¹' {z | z.snd = z₀}) x,
        let u : TangentSpace I x := mfderiv I I ((j i).symm : M i → N) (j i x) vi
        G.inner x (u - v) (u - v) ≤ c ^ 2 := by
  have hh : 0 < 20 * Real.sqrt τ := by positivity
  exact eventually_inverse_nearest_directions_close_radial hr G hGnorm hGsec g hmetric hK q j hexh
    hconv hdist hcover Φ hΦq hΔ hτ hτ1 hk hkΔ hh hτs Q A hQp hQdist hheight hQcover hpA hborder
    hbordercover hsec (eventually_abs_height_sub_axisDist_le (fun i => (j i : N → M i)) q hdist Φ
      hΦq hΔ hτ hτ1 Q hQp hQdist hheight hcoord)

end DifferentialGeometry.Geometry.Riemannian.Geodesic
