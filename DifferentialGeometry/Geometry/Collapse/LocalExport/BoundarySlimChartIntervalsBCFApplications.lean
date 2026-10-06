import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChartIntervalsBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimAtlasBCF

/-!
# Consumers of BCF01 G1a: the composed producer G1 and the face identities (lane S-BCF134c)

* `exists_boundaryCompactSlimChoiceV2_BCF01` (v3.1 §G G1, composed): G1a at the graph atlas of `B₃`
  from `WF` (`slimBase_graphAtlas_BCF`), then G1b (`exists_compactSlimChoiceV2_of_intervals_BCF01`):
  a compact slim choice on every enhanced chain with whole-fibre layer and actual zero domains;
* `exists_boundaryCompactSlimChoiceV2_faces_BCF01`: the same choice together with G3's three face
  identities for ITS slim piece and `M₂` (`bcf01_faces_BCF01`, on the arc form's `K₃`).
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

/-- **G1 BCF01 producer, composed** (v3.1 §G; numerical premises of F4c / F5 / F5z, named revision
v3.2): a compact slim choice, from G1a over `B₃`'s own graph atlas and G1b. -/
theorem exists_boundaryCompactSlimChoiceV2_BCF01 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Nonempty (BoundaryCompactSlimChoiceV2 Bs) := by
  obtain ⟨At⟩ := WF.slimBase_graphAtlas_BCF
  obtain ⟨Ki⟩ := C.exists_slimChartIntervals_BCF01 WF Z hrd hrd4 hrdc hprem hθ At
  obtain ⟨Kc, -, -⟩ := exists_compactSlimChoiceV2_of_intervals_BCF01 WF Ki
  exact ⟨Kc⟩

/-- **G1 and G3 together**: a compact slim choice whose slim piece and `M₂` satisfy BCF01's three
face identities (`S ∩ M₂ = ∂S \ ∂M₁`, `∂M₂ = (∂M₁ \ S) ∪ (∂S \ ∂M₁)`, and their disjointness). -/
theorem exists_boundaryCompactSlimChoiceV2_faces_BCF01 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ Kc : BoundaryCompactSlimChoiceV2 Bs, Kc.piece ∩ Kc.M₂ = frontier Kc.piece \ frontier
        C.toChain.M₁_BIFc ∧
      frontier Kc.M₂ = (frontier C.toChain.M₁_BIFc \ Kc.piece) ∪
        (frontier Kc.piece \ frontier C.toChain.M₁_BIFc) ∧
      Disjoint (frontier C.toChain.M₁_BIFc \ Kc.piece)
        (frontier Kc.piece \ frontier C.toChain.M₁_BIFc) := by
  obtain ⟨Kc⟩ := C.exists_boundaryCompactSlimChoiceV2_BCF01 WF Z hrd hrd4 hrdc hprem hθ
  exact ⟨Kc, bcf01_faces_BCF01 Z Kc.slimCut_BIFc⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
