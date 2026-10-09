import DifferentialGeometry.Geometry.Fibration.ActualStageChainFinalBases

/-!
# Consumers of the final bases `W_st`

* `Gaf02Chain.finalBase_circle_point_chart_BAS`: every point of `W₁` lies in the image of some
  circle chart `ψ_j` (cover + chart).
* `Gaf02Chain.rf_circle_stage_point_BAS`: (RF) at the stage image of a point of the carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- Every point of `W₁` is `ψ_j(b)` for some circle chart `j` and some `b ∈ B(0, 5.5)`, with
`b = R_j⁻¹u_j(y)`. -/
theorem finalBase_circle_point_chart_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hy : y ∈ C.finalBase_BAS 0) :
    ∃ (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
      (ψ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * 1)) ∧ ∃ b ∈ ball (0 : ℝ²) (11 / 2 * 1),
        ψ b = y ∧ ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) y = b := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp (C.finalBase_circle_cover_BAS hy)
  obtain ⟨ψ, hψ, -, hout⟩ := C.finalBase_circle_chart_BAS R j
  exact ⟨j, ψ, hψ, _, (hout y ⟨hy, hj⟩).1, (hout y ⟨hy, hj⟩).2, rfl⟩

/-- (RF) at a carrier point: the final fibre of `π₁E` through `p ∈ D₁` is the stage fibre of `f₁`
through `p`, inside `D₁`. -/
theorem rf_circle_stage_point_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) {p : X} (hp : p ∈ C.carrier_BAS 0) :
    {q | q ∈ C.carrier_BAS 0 ∧ (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E q) =
        C.Θ_BAS 0 (C.stageMap_BAS 0 p)} =
      {q | q ∈ C.carrier_BAS 0 ∧ C.stageMap_BAS 0 q = C.stageMap_BAS 0 p} :=
  C.rf_BAS R 0 hp.2

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
