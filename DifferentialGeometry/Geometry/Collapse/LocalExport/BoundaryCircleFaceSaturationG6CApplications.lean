import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleFaceSaturationG6C

/-!
# Consumer of the face saturation (lane O-G6C, G2d)

`BoundaryGaf02ChainE.mem_circleLabelsAt_of_mem_G6C`: at a point `y` of the actual circle base, ONE
point of the whole fibre on a face puts the face's label into `circleLabelsAt_G6C Kc y`.
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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **One fibre point on a face gives the label.** -/
theorem mem_circleLabelsAt_of_mem_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {p : W.Carrier} (hp : p ∈ Bs.fibre 0 y)
    {f : CircleFaceLabel74 Kc} (hpf : p ∈ circleFaceSet74 Kc f) :
    f ∈ circleLabelsAt_G6C Kc y :=
  mem_circleLabelsAt_G6C.mpr
    (C.fibre_subset_circleFace_of_mem_G6C (circleFibre_subset_M₂_G6C hsat hy) f hp hpf)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
