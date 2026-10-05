import DifferentialGeometry.Geometry.Fibration.ActualCfs27RowCFSB

/-!
# Consumer of CFS27: the pruned planes are the chain's planes and kill every deleted block

* `Gaf02ChainE.cfs27_deleted_CFSB`: at every stage, a retained block with `R_i ≤ R_{a(x)}/2` is
  zero at `x ∈ S_st` and on the chain's plane `L_x` (the input CFS28 / CFS24 use).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

namespace Gaf02ChainE

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X]
  [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- CFS27's deleted blocks at stage `1`: zero at `x` and on the edge plane `L_x`. -/
theorem cfs27_deleted_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1) (i : CGPMarkerIndex P.toLocalChartFamily)
    (hi : ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤ ρ (C.planes₁.ref ⟨x, hx⟩).1 / 2) :
    x (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
      ∀ w ∈ C.toChain.plane 1 x, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 :=
  (C.cfs27_row_CFSB.2.2.2.2.1 x hx).2 i hi

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
