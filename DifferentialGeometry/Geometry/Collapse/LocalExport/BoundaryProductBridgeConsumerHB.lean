import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductBridgeHB
import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyWithChoiceBSTD2

/-!
# Consumer of the product-label bridge: the member's OWN supply (lane S-HBRIDGE, group G1)

`labelledCertificate_of_product_at_member_supply_HB`: for the stored-choice early package `EW`,
a standing sequence `Sq`, the register `R` and the member output `hm` at index `m`, if the member's
own supply `(hm.supply_BSTD2 oM).some` (the supply that H1 instantiates its `Sup` at) is in the
labelled whole-product branch, then the member has the labelled certificate of H2 on `Sq.B m`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
open GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The product-label bridge at the member's own supply.** -/
theorem labelledCertificate_of_product_at_member_supply_HB {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    {V : ℝ} (R : BoundaryRegisterOverXBA_BSTD2 EW.early V) {m : ℕ}
    (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3)
    (h : (hm.supply_BSTD2 oM).some.LabelledWholeProduct_BIF) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i :=
  labelledCertificate_of_product_member_HB Sq m oM _ h

end DifferentialGeometry.Geometry.Collapse
