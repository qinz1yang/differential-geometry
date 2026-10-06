import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageZeroOBD

/-!
# Consumer of the circle stage map being `E` (lane S-BD2c, suffix `_OBD`), group G11c

`T = A/s` is constant on every circle fibre of the restricted circle bundle of the produced stages
(`heightRatio_fibreConst_OBD` and `circleFibre_set_OBD`).
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}


section Stage0Consumer

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc)

/-- **`T` is constant on the circle fibres of the restricted circle bundle.** -/
theorem heightRatio_eq_of_mem_fibre_OBD (G : CircleCutFacts74 P.stageGeometry P.cut)
    (b' : P.cut.circleBaseOpen) {x y : W.Carrier}
    (hx : x ∈ (circleBundle74 P.stageGeometry P.cut G).fibre b')
    (hy : y ∈ (circleBundle74 P.stageGeometry P.cut G).fibre b') :
    C.toChain.heightRatio x = C.toChain.heightRatio y := by
  rw [C.circleFibre_set_OBD P G b'] at hx hy
  exact C.heightRatio_fibreConst_OBD (hx.trans hy.symm)

end BoundaryGaf02ChainE

end Stage0Consumer

end DifferentialGeometry.Geometry.Collapse
