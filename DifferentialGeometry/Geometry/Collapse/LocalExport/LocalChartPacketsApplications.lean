import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsFinal
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBallApplications

/-!
# Consumers of the final combined LC87 family

* `LocalChartPackets.exhaustion_four_kinds`: every point lies in the tenth-radius ball of a zero-model
  ball of `zero` or in the plateau of a circle, slim or edge cutoff of `toLocalChartFamily` — the two
  projections speak about the same scale and the same manifold (LPA06).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace LocalChartPackets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of the zero kind, as a local instance. -/
local instance instMetricN_packets_LC87
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (L.N a) :=
  L.instMetricN a

/-- The model charts of the zero kind, as a local instance. -/
local instance instChartedN_packets_LC87
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (L.N a) :=
  L.instChartedN a

/-- The cone metrics of the zero kind, as a local instance. -/
local instance instMetricC_packets_LC87
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (L.C a) :=
  L.instMetricC a

/-- **LPA06's exhaustion by the four kinds on the final family.** -/
theorem exhaustion_four_kinds
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 0 < Δ) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (x : X) :
    (∃ i, ∃ hi : i ∈ L.zero.centres, x ∈ ball i ((L.zero.zero i hi).radius / 10)) ∨
      (∃ j ∈ L.circle.centres, L.circle.cutoff j x = 1) ∨
      (∃ j ∈ L.slim.centres, L.slim.cutoff j x = 1) ∨
      ∃ j ∈ L.edge.centres, L.edge.cutoff j x = 1 := by
  rcases L.exists_cutoff_eq_one hΔ hσs hσs1 x with h0 | h
  · exact Or.inl (L.zero.exists_mem_tenth_ball h0)
  · exact Or.inr h

end LocalChartPackets

end DifferentialGeometry.Geometry.Collapse
