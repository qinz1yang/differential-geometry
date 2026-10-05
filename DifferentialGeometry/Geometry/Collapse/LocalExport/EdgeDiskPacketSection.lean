import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket
import DifferentialGeometry.Geometry.Collapse.EdgeRowCoreSectionThreshold

/-!
# EGP05 / CGP03 at the chart level: the edge disk packet together with its core section

Blueprint 207B, EGP05 (`lem:fibration-edge-cloud-section`, B:5042–5053): "At the initial
construction the common local packets may also be required to have a continuous section
`s_i : (-8.5Δ, 8.5Δ) → U_i`, `η_i s_i(a) = a`, `0 ≤ t s_i(a) < Δ/100`. Its image lies in
`B_g(p_i, 10ΔR_i)`. The threshold for this augmented conclusion has the same permitted dependencies
as LFR28." CGP03's edge case (B:4024–4053) is the restriction to `[-23Δ/4, 23Δ/4]`.

`exists_edgeDiskPacket_section_threshold`: the binders and hypotheses of LC84's producer
`exists_edgeDiskPacket_threshold`; ONE threshold (the minimum of the packet threshold and of the
augmented LFR28 threshold `edgeSourceSlab_core_section_threshold`); for every edge chart `c` with
LFR28's data, an `EdgeDiskPacket P` over `c` AND a continuous section of the chart's own tangential
coordinate `c.coord` over `(-8.5Δ, 8.5Δ)` with `F/ρ < Δ/100` and `d(sec a, center) < 10Δ`.
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

local instance nezero_finrank_euclidean_three_section_KC : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **EGP05 at the chart level (augmented LC84 producer).** For `b` below ONE threshold, every
edge chart with LFR28's data extends to an edge disk packet and carries a continuous section of
its tangential coordinate over `(-8.5Δ, 8.5Δ)` inside `B(center, 10Δ)` with `F/ρ < Δ/100`. -/
theorem exists_edgeDiskPacket_section_threshold {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
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
        ∀ (γ β : ℝ) (E : Set M) (ρ F : M → ℝ) (c : EdgeChart g hEnorm Δ σ μ b γ β E ρ F)
          (OF : Set M), c.center = p → c.Qn p = 0 →
        (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
          |dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ) →
        (∀ x ∈ ball p (200 * Δ), 0 ≤ (c.Qn x).snd) →
        (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
          ∃ x ∈ ball p (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) →
        IsClosed E →
        (∀ a ∈ E ∩ ball p (190 * Δ), (c.Qn a).snd ≤ τ * Δ) →
        (∀ t : ℝ, |t| ≤ 100 * Δ →
          ∃ a ∈ E ∩ ball p (190 * Δ), dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
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
        LipschitzWith Λ ρ → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ)) →
        ∃ P : EdgeDiskPacket g hEnorm Δ σ μ b γ β E ρ F, P.toEdgeChart = c ∧
          ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → M, Continuous sec ∧
            ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
              F (sec a) / ρ (sec a) < Δ / 100 ∧ dist (sec a) c.center < 10 * Δ := by
  obtain ⟨b₁, hb₁, hpk⟩ := exists_edgeDiskPacket_threshold hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1 hΛ K hK
    hr hv A
  obtain ⟨b₂, hb₂, hsc⟩ := edgeSourceSlab_core_section_threshold hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1
    hΛ K hK hr hv A
  refine ⟨min b₁ b₂, lt_min hb₁ hb₂, fun b hb hbb₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv
    hsec γ β E ρ F c OF hcp hQp hQdist hheight hQcover hEc hborder hbordercover hF hOF hCO hFs
    hFgrad hquot hHs hρL hρs => ?_⟩
  obtain ⟨P, hP⟩ := hpk b hb (hbb₀.trans_le (min_le_left _ _)) M g hEnorm o p hvol hcurv hsec γ β
    E ρ F c OF hcp hQp hQdist hheight hQcover hEc hborder hbordercover hF hOF hCO hFs hFgrad hquot
    hHs hρL hρs
  refine ⟨P, hP, ?_⟩
  subst hcp
  let _ := c.instY
  exact hsc b hb (hbb₀.trans_le (min_le_right _ _)) M g hEnorm o c.center hvol hcurv hsec c.Y c.q
    c.split c.Qn E F c.coord ρ OF c.domain c.Qn_fst hQp hQdist hheight hQcover hEc c.center_mem
    hborder hbordercover hF hOF hCO hFs hFgrad hquot hHs hρL c.rho_center hρs c.isOpen_domain
    c.closedBall_subset_domain c.contMDiffOn_coord c.lipschitz c.value c.test

end DifferentialGeometry.Geometry.Collapse
