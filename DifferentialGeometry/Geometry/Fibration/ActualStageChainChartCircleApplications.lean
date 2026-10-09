import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartCircle

/-!
# Consumers of CGP07 on the chain, circle charts

* `Gaf02Chain.circlePatch_existsUnique_BAS`: over every target `a ∈ B(0, 5.5)` there is exactly
  one point of the circle patch `V_j⁰` with retained coordinate `a` (one sheet + full ball).
* `Gaf02Chain.circlePatch_compact_core_BAS`: the part of `V_j⁰` over the closed `4`-ball (GAF07's
  base piece) is compact.
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

/-- **One sheet over every target**: each `a ∈ B(0, 5.5)` is the retained coordinate of exactly one
point of the circle patch `V_j⁰`. -/
theorem circlePatch_existsUnique_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) {a : ℝ²}
    (ha : a ∈ ball (0 : ℝ²) (11 / 2 * 1)) :
    ∃! w, w ∈ C.circlePatch_BAS j ∧ ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) w = a := by
  obtain ⟨hbij, -⟩ := C.cgp07_circle_BAS R j
  obtain ⟨w, hw, hwa⟩ := hbij.surjOn ha
  exact ⟨w, ⟨hw, hwa⟩, fun w' hw' => hbij.injOn hw'.1 hw (hw'.2.trans hwa.symm)⟩

/-- **The compact core of the patch**: `V_j⁰ ∩ {‖R_j⁻¹u_j‖ ≤ 4}` is compact. -/
theorem circlePatch_compact_core_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    IsCompact (C.circlePatch_BAS j ∩
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) ⁻¹' closedBall 0 4) := by
  obtain ⟨-, -, -, -, -, -, hK⟩ := C.cgp07_circle_BAS R j
  exact hK _ (closedBall_subset_ball (by norm_num)) (isCompact_closedBall 0 4)

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
