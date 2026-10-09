import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceZeroDomainsV2

/-!
# Boundary route interfaces v2: consumer of the P0 group (lane BIFACEc, G1)

Consumer of `LE/BoundaryInterface{BasesV2,FibresV2,ZeroDomainsV2}.lean` on the empty-family chain of
BIFACE's inhabitants (empty stage and zero centres, `F_∂` continuous): the v2 BASES exit, its
whole-fibre layer and the actual zero domains exist, and project to v1's objects (`toV1_BIFc`
with `Θ = id`, the whole-fibre projection, the saturated cores `toSat_BIFc`) — the migration path
of the v1 consumers on this regime.

* `emptyInterfaceV2_BIFc`: the three v2 objects on the empty-family chain.
* `emptyInterfaceV2_toV1_BIFc`: their v1 projections (v1 BASES, v1 whole fibres, v1 saturated cores).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {D : BoundaryAugmentedData S S.emptySlots_BIF} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **The v2 interface objects on the empty-family chain**: a v2 BASES exit, its v2 whole-fibre
layer and the actual zero domains of `C.E`. -/
theorem emptyInterfaceV2_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) :
    ∃ Bs : BoundaryGaf02BasesV2 C, BoundaryWholeFiberSpecV2 C Bs ∧
      Nonempty (BoundaryActualZeroDomains_BIFc C Bs) :=
  ⟨C.emptyBasesV2_BIFc hc hF, C.emptyWholeFiberSpecV2_BIFc hc hF,
    ⟨C.emptyActualZeroDomains_BIFc hc hF hz0⟩⟩

/-- **The v1 projections on the empty-family chain** (the migration path): the v2 BASES exit
projects to v1's (`Θ = id`), the v2 whole fibres to v1's (no slim base point), the actual zero
domains to v1's saturated cores on that v1 object. -/
theorem emptyInterfaceV2_toV1_BIFc (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) :
    ∃ Bs₁ : BoundaryGaf02Bases C, BoundaryWholeFiberSpec C Bs₁ ∧
      Nonempty (BoundaryInitialCoresSpecSat C Bs₁) := by
  let Bs := C.emptyBasesV2_BIFc hc hF
  let Bs₁ : BoundaryGaf02Bases C :=
    Bs.toV1_BIFc (Bs.base_subset_zeroSet_of_later_id_BIFc fun _ => rfl)
  refine ⟨Bs₁, (C.emptyWholeFiberSpecV2_BIFc hc hF).toV1_BIFc Bs₁ rfl rfl
    fun y hy => (notMem_empty y hy).elim, ⟨?_⟩⟩
  exact (C.emptyActualZeroDomains_BIFc hc hF hz0).toSat_BIFc Bs₁ fun _ _ => rfl

end DifferentialGeometry.Geometry.Collapse
