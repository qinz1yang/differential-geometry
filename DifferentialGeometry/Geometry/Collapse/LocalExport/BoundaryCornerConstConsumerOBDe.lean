import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCornerConstOBDe

/-!
# Consumer of the corner fibre constancy (lane S-BD2e, suffix `_OBDe`), group G11d

The corner descents of ALL endpoints of rows over the produced stages, when no endpoint is attached
to a new slim end (the new ends need the end-coordinate clause of the slim exit): the family
`∀ e, CornerDescent74 F G e` of `CornerCutFacts74.descent`, and the fibre constancy of `T`.
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

section CornerConstConsumer

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **The corner descents of all endpoints, when no endpoint label is a new slim end.** -/
theorem corner_descent_family_nonNew_OBDe (F : JunctionFaceFacts74 P.stageGeometry P.cut R)
    (G : JunctionRimFacts74 P.stageGeometry P.cut R)
    (hlab : ∀ (e : R.edge.EdgeEnd) (en : R.slimPieces.NewEnd), F.horizontal e ≠ .inr en) :
    ∀ e : R.edge.EdgeEnd, Nonempty (CornerDescent74 F G e) := fun e =>
  C.exists_cornerDescent_nonNew_OBDe P R F G e (hlab e)

end BoundaryGaf02ChainE

end CornerConstConsumer

end DifferentialGeometry.Geometry.Collapse
