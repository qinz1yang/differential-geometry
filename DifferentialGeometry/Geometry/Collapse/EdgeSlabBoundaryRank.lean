import DifferentialGeometry.Geometry.Collapse.EdgeFullCollar

/-!
# LFR28: on the source slab boundary `η = 4Δ` the original pair has rank two

Blueprint 207A, LFR28 (A:27223), statement: "Its boundary is exactly `η = 4Δ`, where `df, dη`
have rank two." The rank-two clause is obtained here from LFR38 (`exists_edge_full_collar_parameters`),
not from the finite model: the level `η = 4Δ` lies inside LFR38's band `Δ/10 ≤ η ≤ 10Δ`, and every
band point is the centre of its own adapted ball. Under LFR38's ordered parameters, at every point
of `B(p, 100Δ)` with `|f| < 4Δ` and `F/ρ = 4Δ`, the differential of `J = (f, F/ρ)` is onto `ℝ²`; in
particular `df ≠ 0` and `dη ≠ 0` there. The bundle/boundary identification of LFR28 itself (steps
1–4) remains blocked (LFR14 data, LFR23/LFR24/LFR26).
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

/-- **LFR28, boundary rank two (via LFR38).** -/
theorem exists_edge_slab_boundary_rankTwo {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 ≤ ε → ε < 1 / 100 →
        μ ≤ 1 / 1000000 → τ ≤ τ₀ → 0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
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
      Function.Surjective
          (mvfderiv (I := I) (edgeReferenceCoordinates ![f, fun z => F z / ρ z]) x) ∧
        mvfderiv (I := I) f x ≠ 0 ∧ mvfderiv (I := I) (fun z => F z / ρ z) x ≠ 0 := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hcollar⟩ := exists_edge_full_collar_parameters.{uE, uH, uM, uY}
    hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  have hΔpos : 0 < Δ := hΔ₀.trans_le hΔ
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔcollar⟩ := hcollar Δ hΔ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α Q A ρ F f O
    hsecκ hsecb hA hQp hdist hheight hcover hpA hborder hbordercover hQα hρ hρp hρs
    hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx hfx hη
  obtain ⟨⟨hq1, -⟩, -, hJ⟩ := hΔcollar σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hττ₀ hκ hκκ₀ hb hbb₀ hlam
    hbudget E H I M g hEnorm Y p y₀ α Q A ρ F f O hsecκ hsecb hA hQp hdist hheight hcover hpA
    hborder hbordercover hQα hρ hρp hρs hO hCO hFO hFL hval hFgrad hfs hfL hfval htest x hx
    (by linarith) (by rw [hη]; linarith) (by rw [hη]; linarith)
  obtain ⟨hJs, hsurj, -⟩ := hJ
  have hqpos : 0 < ρ x := by linarith
  have hxx : x ∈ ball x (100 * ρ x) := mem_ball_self (by positivity)
  have hxx3 : x ∈ ball x (300 * ρ x) := mem_ball_self (by positivity)
  have hJx := (hJs.contMDiffAt (isOpen_ball.mem_nhds hxx3)).mdifferentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hs := hsurj x hxx
  refine ⟨hs, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ := hs (EuclideanSpace.single 0 1)
    have hc := mvfderiv_component_apply _ hJx w 0
    have he : (fun z => edgeReferenceCoordinates ![f, fun z => F z / ρ z] z 0) = f := rfl
    rw [he, hw, h0] at hc
    simp at hc
  · intro h0
    obtain ⟨w, hw⟩ := hs (EuclideanSpace.single 1 1)
    have hc := mvfderiv_component_apply _ hJx w 1
    have he : (fun z => edgeReferenceCoordinates ![f, fun z => F z / ρ z] z 1) =
        fun z => F z / ρ z := rfl
    rw [he, hw, h0] at hc
    simp at hc

end DifferentialGeometry.Geometry.Collapse
