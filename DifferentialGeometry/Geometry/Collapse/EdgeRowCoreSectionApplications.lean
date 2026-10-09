import DifferentialGeometry.Geometry.Collapse.EdgeRowCoreSectionThreshold

/-!
# Consumer: the CGP03 section over `[-23Δ/4, 23Δ/4]`

`edgeSourceSlab_core_section_Icc_threshold`: CGP03's edge-case section (blueprint 207B B:4029–4053)
over the closed interval `[-23Δ/4, 23Δ/4]`, the restriction of the EGP05 section of
`edgeSourceSlab_core_section_threshold` (`23/4 < 17/2`), same threshold.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold WithLp
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance nezero_finrank_euclidean_three_secapp_LFR28ROW2 :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **Concrete consumer (CGP03).** -/
theorem edgeSourceSlab_core_section_Icc_threshold {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 8) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30)
    (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      ∀ (M : Type) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ManifoldOrientation (𝓡 3) M 3 → ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p b⁻¹, SectionalBoundedBelowAt g y (-b ^ 2)) →
        ∀ (Y : Type) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b)
          (Q : M → WithLp 2 (ℝ × ℝ)) (E : Set M) (F f ρ : M → ℝ) (OF Of : Set M),
        (∀ z, (Q z).fst = (α.toFun z).fst) → Q p = 0 →
        (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
          |dist (Q x) (Q y) - dist x y| ≤ τ * Δ) →
        (∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd) →
        (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
          ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ) →
        IsClosed E → p ∈ E →
        (∀ a ∈ E ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
        (∀ t : ℝ, |t| ≤ 100 * Δ →
          ∃ a ∈ E ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
        (∀ x, |F x - infDist x E| < μ * Δ) →
        IsOpen OF →
        closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ} ⊆ OF →
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F OF →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g E y,
            Real.sqrt (g.inner y (gradFun g F y + u) (gradFun g F y + u)) < ε) →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          Real.sqrt (g.inner y (gradFun g (fun z => F z / ρ z) y - gradFun g F y)
            (gradFun g (fun z => F z / ρ z) y - gradFun g F y)) ≤ 100 * Δ * Λ) →
        (∀ x ∈ ball p (20 * Δ), infDist x E < 41 / 4 * Δ →
          ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ F ρ) x) →
        LipschitzWith Λ ρ → ρ p = 1 → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ)) →
        IsOpen Of → closedBall p (100 * Δ) ⊆ Of → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f Of →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (α.toFun x).fst| < μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x x') = x' →
          |mvfderiv 𝓘(ℝ, E3) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∃ sec : Icc (-(23 / 4 * Δ)) (23 / 4 * Δ) → M, Continuous sec ∧
          ∀ a : Icc (-(23 / 4 * Δ)) (23 / 4 * Δ),
            f (sec a) = a ∧ F (sec a) / ρ (sec a) < Δ / 100 ∧ dist (sec a) p < 10 * Δ := by
  obtain ⟨b₀, hb₀, hmain⟩ := edgeSourceSlab_core_section_threshold hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1
    hΛ K hK hr hv A
  refine ⟨b₀, hb₀, fun b hb hbb₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec Y _ y₀ α Q E F
    f ρ OF Of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
    h24 h25 => ?_⟩
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨sec, hsc, hsec'⟩ := hmain b hb hbb₀ M g hEnorm o p hvol hcurv hsec Y y₀ α Q E F f ρ
    OF Of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
    h25
  let ι : Icc (-(23 / 4 * Δ)) (23 / 4 * Δ) → Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) := fun a =>
    ⟨a, by linarith [a.2.1], by linarith [a.2.2]⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  exact ⟨sec ∘ ι, hsc.comp hι, fun a => hsec' (ι a)⟩

end DifferentialGeometry.Geometry.Collapse
