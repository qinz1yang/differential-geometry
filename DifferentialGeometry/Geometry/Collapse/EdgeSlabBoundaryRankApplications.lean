import DifferentialGeometry.Geometry.Collapse.EdgeSlabBoundaryRank

/-!
# Consumer: the source slab boundary is a regular level of `η`

`exists_edge_slab_boundary_rankTwo` at `γ = 1/1000`, `β₂ = 10⁻⁷`: under LFR38's ordered
parameters, every point of the source slab boundary `{|f| < 4Δ, F/ρ = 4Δ} ∩ B(p, 100Δ)` is a
regular point of `η = F/ρ` (and of `f`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open scoped Manifold ContDiff Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM uY

/-- The level `η = 4Δ` of the source slab is regular for `η`. -/
theorem edge_slab_boundary_regular_level :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 ≤ ε → ε < 1 / 100 →
        μ ≤ 1 / 1000000 → τ ≤ τ₀ → 0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < 1 / 1000000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type uY) [MetricSpace Y] (p : M) (y₀ : Y)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b)
        (Q : M → WithLp 2 (ℝ × ℝ)) (A : Set M) (ρ F f : M → ℝ) (O : Set M),
      (∀ z ∈ ball p (10000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2)) →
      (∀ z ∈ ball p b⁻¹, SectionalBoundedBelowAt g z (-b ^ 2)) →
      IsClosed A → Q p = 0 →
      (∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
        |dist (Q y) (Q z) - dist y z| ≤ τ * Δ) →
      (∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd) →
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ) →
      p ∈ A → (∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
        dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
      (∀ z ∈ ball p (200 * Δ), (Q z).fst = (α.toFun z).fst) →
      LipschitzWith Λ ρ → ρ p = 1 → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      IsOpen O →
      closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ O →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O → LipschitzWith (Real.toNNReal (1 + ε)) F →
      (∀ y, |F y - infDist y A| ≤ μ * Δ) →
      (∀ y ∈ closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
        ∀ v ∈ minimizingDirectionsTo g hEnorm A y,
          Real.sqrt (g.inner y (gradFun g F y + v) (gradFun g F y + v)) < ε) →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
      LipschitzWith (Real.toNNReal (1 + σ)) f →
      (∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ) →
      (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
        ∀ w : TangentSpace I x, g.inner x w w = 1 →
        intrinsicGeodesic g hEnorm x w (dist x x') = x' →
        |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
      ∀ x ∈ ball p (100 * Δ), |f x| < 4 * Δ → F x / ρ x = 4 * Δ →
        mvfderiv (I := I) (fun z => F z / ρ z) x ≠ 0 := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hrank⟩ := exists_edge_slab_boundary_rankTwo.{uE, uH, uM, uY}
    (β := 1 / 10000000) (γ := 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔrank⟩ := hrank Δ hΔ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α Q A ρ F f O
    hsecκ hsecb hA hQp hdist hheight hcover hpA hborder hbordercover hQα hρ hρp hρs
    hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx hη
  exact (hΔrank σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam (by linarith)
    E H I M g hEnorm Y p y₀ α Q A ρ F f O hsecκ hsecb hA hQp hdist hheight hcover hpA hborder
    hbordercover hQα hρ hρp hρs hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx hη).2.2

end DifferentialGeometry.Geometry.Collapse
