import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleTrivOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometrySmoothOBD

/-!
# Consumer of the circle trivializations (lane S-BD2d, suffix `_OBDd`), group G9

**`BoundaryGaf02ChainE.exists_stageGeometry_circleFacts_OBDd`**: for every zero / cusp exit `zc`
the stage geometry of G7e exists with the WHOLE `CircleCutFacts74` of its cut (trivializations G9,
properness and compact remaining base G7c, saturation G7d). The premises are those of the
producers (`geom`, and `hint` of the edge stage); G9 itself uses neither `hint` nor the smoothness
of the base inclusions.
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
theorem exists_stageGeometry_circleFacts_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) :
    ∃ P : BoundaryStageGeometry74b zc, Nonempty (CircleCutFacts74 P.stageGeometry P.cut) := by
  obtain ⟨P, -⟩ := C.exists_stageGeometry74b_smooth_OBD dec geom hint zc
  exact ⟨P, C.exists_circleCutFacts_OBDd P geom⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
