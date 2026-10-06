import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusStageCloud
import DifferentialGeometry.Geometry.Fibration.ActualStageChain

/-!
# The stage-0 slot of a chain over a non-empty circle family is active (S-FIXTURE-C1b, R1 start)

`Gaf02StageSlot.inactive` requires the stage family to be EMPTY. Hence on any packet with a circle
centre every `Gaf02Chain` has an ACTIVE stage-0 slot (`slot_zero_active_FXC1`, for a VARIABLE
packet), and its smoothing slot is a `Cfs15StageOutput` on the non-empty stage-0 cloud. Applied to
a chain over the flat torus packet (the chain itself is the open R1 step: see the state file) this
gives the first chain object of the tree whose first stage actually runs.
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

section Slot

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **A chain over a packet with a circle centre has an active stage-0 slot.** -/
theorem slot_zero_active_FXC1
    {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
    {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {j : X}
    (hj : j ∈ P.circle.centres) :
    ∃ O, C.slot 0 = Gaf02StageSlot.active O := by
  rcases h : C.slot 0 with O | hempty
  · exact ⟨O, rfl⟩
  · exfalso
    have : j ∈ gafStageCentres P 0 := hj
    rw [hempty] at this
    exact this

end Slot

end DifferentialGeometry.Geometry.Collapse
