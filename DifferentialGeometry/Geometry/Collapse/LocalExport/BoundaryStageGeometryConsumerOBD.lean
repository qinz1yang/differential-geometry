import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometryOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsHeadV2bOBD

/-!
# Consumer of the stage geometry (lane S-BD2, suffix `_OBD`), group G7b

**`BoundaryGaf02ChainE.exists_zeroCuspExit_stageGeometry74b_OBD`**: the zero / cusp exit produced
by `exists_zeroCuspExit74b_OBD` (BD2 head, zero and cusp halves) together with the stage geometry
`BoundaryStageGeometry74b` over it (G7b): the whole of `BoundaryLandingExits74b` except the eight
cut-fact structures `H` (`slim`, `edgeFacts`, `edgeModels`, `circleFacts`, `cover`, `faces`,
`rims`, `corners`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}


namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
theorem exists_zeroCuspExit_stageGeometry74b_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ zc : BoundaryZeroCuspExit74b C.toChain dec, Nonempty (BoundaryStageGeometry74b zc) := by
  obtain ⟨zc⟩ := C.exists_zeroCuspExit74b_OBD dec Q hrd hrd4 hrdc hprem hθ
  exact ⟨zc, C.exists_stageGeometry74b_OBD dec geom hint zc⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
