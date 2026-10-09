import DifferentialGeometry.Geometry.Collapse.EdgePrescribedGradientPinning
import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing

/-!
# Consumer: LFR34's smoothing is pinned to the anchor directions (LFR36 with the smoothing chosen)

The LFR34 producer `exists_edge_low_collar_smoothing` composed with the LFR36 row
`exists_edge_prescribed_gradient_pinning` at `ι = 1/1000`: ONE nonnegative `(1+ε)`-Lipschitz `F`,
`μΔ`-close to `d_A`, such that for EVERY LFR19-type coordinate `f`, at every band point `x`, anchors of
LFR35's shape exist and, for all of them and all minimizing unit directions, both gradients are pinned
in the point's own scale (`edgeLowCollarSmoothing_gradient_pinning`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open scoped Manifold ContDiff Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM uY

/-- **Concrete consumer.** LFR34's smoothing, chosen once, satisfies LFR36 on the whole band. -/
theorem edgeLowCollarSmoothing_gradient_pinning :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < 1 / 1000 →
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
        (Q : M → WithLp 2 (ℝ × ℝ)) (A : Set M) (ρ : M → ℝ),
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
      ∃ F : M → ℝ, (∀ y, 0 ≤ F y) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        (∀ y, |F y - infDist y A| < μ * Δ) ∧
        ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace I x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x x') = x' →
          |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ → Δ / 10 ≤ F x / ρ x → F x / ρ x ≤ 10 * Δ →
        (∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) ≤ τ * Δ) ∧
        (∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ) ∧
        (∀ a ∈ ball p (20 * Δ),
          dist (Q a) (Q x + WithLp.toLp 2 (Δ / 40, (0 : ℝ))) ≤ τ * Δ →
          ∀ y ∈ ball x (300 * ρ x), ∀ v ∈ minimizingDirectionsTo g hEnorm {a} y,
            ∀ X : TangentSpace I y,
              |ρ x * mvfderiv (I := I) f y X - g.inner y v X| ≤
                1 / 1000 / 2 * Real.sqrt (g.inner y X X)) ∧
        ∀ a ∈ ball p (20 * Δ),
          dist (Q a) (Q x + WithLp.toLp 2 ((0 : ℝ), Δ / 40)) ≤ τ * Δ →
          ∀ y ∈ ball x (300 * ρ x), ∀ w ∈ minimizingDirectionsTo g hEnorm {a} y,
            Real.sqrt (g.inner y (ρ x • gradFun g (fun z => F z / ρ z) y - w)
              (ρ x • gradFun g (fun z => F z / ρ z) y - w)) < 1 / 1000 := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hcollar⟩ := exists_edge_prescribed_gradient_pinning.{uE, uH, uM, uY}
    (ι := 1 / 1000) (by norm_num)
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  have hΔpos : 0 < Δ := hΔ₀.trans_le hΔ
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔcollar⟩ := hcollar Δ hΔ
  refine ⟨min τ₀ (1 / 20000), lt_min hτ₀ (by norm_num), min κ₀ (1 / (100 * Δ)),
    lt_min hκ₀ (by positivity), b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α Q A ρ hsecκ hsecb hA hQp hdist
    hheight hcover hpA hborder hbordercover hQα hρ hρp hρs
  have hκΔ : κ * Δ ≤ 1 / 100 := by
    have h : κ ≤ 1 / (100 * Δ) := hκκ₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hτsmall : τ < 1 / 10000 :=
    (hττ₀.trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨F, O, hO, hCO, hFO, hF0, hFL, hval, -, -, hgrad, -⟩ :=
    exists_edge_low_collar_smoothing g hEnorm hA hΔpos hτ hτsmall hQp hdist hheight hcover hpA
      hborder hbordercover hκ hκΔ (fun z hz => hsecκ z (ball_subset_ball (by linarith) hz))
      hε hε1 hμ (by linarith) hθ hρ hρp hρs.contMDiffOn (by linarith)
  refine ⟨F, hF0, hFL, hval, fun f hfs hfL hfval htest x hx hfx hη hη' => ?_⟩
  obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := hΔcollar σ ε μ τ κ b Λ hσ hσσ₀ hε.le hε1 hμ1
    (hττ₀.trans (min_le_left _ _)) hκ (hκκ₀.trans (min_le_left _ _)) hb hbb₀ hlam
    (by linarith) E H I M g hEnorm Y p y₀ α Q A ρ F f O hsecκ hsecb hA hQp hdist hheight hcover
    hpA hborder hbordercover hQα hρ hρp hρs hO hCO hFO hFL (fun y => (hval y).le) hgrad hfs
    hfL hfval htest x hx hfx hη hη'
  exact ⟨h1, h2, h3, h4⟩

end DifferentialGeometry.Geometry.Collapse
