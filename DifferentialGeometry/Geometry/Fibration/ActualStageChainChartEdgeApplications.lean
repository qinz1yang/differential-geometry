import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartEdge

/-!
# Consumers of CGP07 on the chain, edge charts

* `Gaf02Chain.edgePatch_existsUnique_BAS`: over every target `a ∈ (-5.5Δ, 5.5Δ)` there is exactly
  one point of the edge patch `V_j⁰` with axis coordinate `a`.
* `Gaf02Chain.edgePatch_compact_core_BAS`: the part of `V_j⁰` over `[-4Δ, 4Δ]` is compact.
* `exists_bounded_preimage_line_fst_BAS`: the one-dimensional adapter on `ℝ × ℝ → ℝ × {0}`.
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

/-- **The one-dimensional adapter, concretely**: `P_m (s, t) = (s, 0)` onto the line `ℝ × {0}`,
`D = P_m`, `N (s, t) = |s| + |t|`, unit witness `(1, 0)`. -/
theorem exists_bounded_preimage_line_fst_BAS :
    ∀ v ∈ LinearMap.range (LinearMap.inl ℝ ℝ ℝ), ∃ w : ℝ × ℝ,
      (LinearMap.inl ℝ ℝ ℝ ∘ₗ LinearMap.fst ℝ ℝ ℝ) w = v ∧ |w.1| + |w.2| ≤ 2 * ‖v‖ ∧
      ‖(LinearMap.inl ℝ ℝ ℝ ∘ₗ LinearMap.fst ℝ ℝ ℝ) w -
        (LinearMap.inl ℝ ℝ ℝ ∘ₗ LinearMap.fst ℝ ℝ ℝ) w‖ ≤ 0 * (|w.1| + |w.2|) := by
  have hL : Module.finrank ℝ (LinearMap.range (LinearMap.inl ℝ ℝ ℝ)) = 1 := by
    rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_self]
  refine exists_bounded_preimage_line_BAS (e := 0) _ hL
    (LinearMap.inl ℝ ℝ ℝ ∘ₗ LinearMap.fst ℝ ℝ ℝ) (LinearMap.inl ℝ ℝ ℝ ∘ₗ LinearMap.fst ℝ ℝ ℝ)
    (fun w => ⟨w.1, rfl⟩) (fun w => |w.1| + |w.2|) (fun t w => ?_) ((1 : ℝ), (0 : ℝ)) (by simp) ?_
    (by simp)
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
    ring
  · norm_num [Prod.norm_def]

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **One sheet over every target**: each `a ∈ (-5.5Δ, 5.5Δ)` is the axis coordinate of exactly
one point of the edge patch `V_j⁰`. -/
theorem edgePatch_existsUnique_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) {a : ℝ}
    (ha : a ∈ ball (0 : ℝ) (11 / 2 * Δ)) :
    ∃! w, w ∈ C.edgePatch_BAS j ∧
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) w = a := by
  have hbij := (C.cgp07_edge_BAS R j).1
  obtain ⟨w, hw, hwa⟩ := hbij.surjOn ha
  exact ⟨w, ⟨hw, hwa⟩, fun w' hw' => hbij.injOn hw'.1 hw (hw'.2.trans hwa.symm)⟩

/-- **The compact core of the edge patch**: `V_j⁰ ∩ {|R_j⁻¹u_j| ≤ 4Δ}` is compact. -/
theorem edgePatch_compact_core_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) :
    IsCompact (C.edgePatch_BAS j ∩
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) ⁻¹'
        closedBall 0 (4 * Δ)) := by
  have hΔ : 0 < Δ := by linarith [C.std.2.1]
  exact (C.cgp07_edge_BAS R j).2.2.choose_spec.2.2.2 _
    (closedBall_subset_ball (by linarith)) (isCompact_closedBall 0 _)

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
