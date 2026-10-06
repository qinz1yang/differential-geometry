import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusPacketsC14Z
import DifferentialGeometry.Geometry.Fibration.ActualStageClouds

/-!
# The stage-0 cloud of the flat torus is non-empty (S-FIXTURE-C1b, R1 start)

For any local chart family, a circle centre `j` with `‖η_j(j)‖ ≤ 7` gives a point of the first
stage core `A₁ = fc04Set 7` and hence a point of the stage-0 cloud `S₁ = π 𝓔⁰ (A₁)`
(`gafCloud_zero_nonempty_FXC1`, stated for a VARIABLE family). On the flat torus the centre
`π(0, 0, 0)` has `η_j(j) = 0`: the stage-0 cloud of the torus packet is non-empty, so every clause
of the chain quantified over it has content.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Cloud

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **The first stage core contains the centre** of a circle chart whose coordinate is `≤ 7` there:
the stage-0 core `fc04Set 7` and the stage-0 cloud are non-empty. -/
theorem gafCloud_zero_nonempty_FXC1
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {j : X}
    (hj : j ∈ L.circle.centres) (h0 : ‖cgpCircleCoord L j hj j‖ ≤ 7) :
    j ∈ gafStageCore L Z 0 ∧ (gafCloud L Z 0).Nonempty := by
  have hmem : j ∈ gafStageCore L Z 0 :=
    ⟨⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩, mem_ball_self (mul_pos (by norm_num) (hρ j)), h0⟩
  exact ⟨hmem, ⟨_, j, hmem, rfl⟩⟩

end Cloud

end DifferentialGeometry.Geometry.Collapse
