import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMemberLabelledCertificateHB

/-!
# Consumer of `member_output_to_labelled_certificate_HB` at the member's OWN supply

(lane S-HBRIDGE, G2)

`member_output_to_labelled_certificate_own_supply_HB`: the statement of
`member_output_to_labelled_certificate_HB` at `Sup := (hm.supply_BSTD2 oM).some`, the supply that
H1 instantiates its `Sup` at (`bbr02_geometricOutputE_of_member_BBR` in text v3.3). It shows that
the supply type of the member output unifies with the bridge, for both branches.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The member output gives the labelled certificate at the member's own supply.** -/
theorem member_output_to_labelled_certificate_own_supply_HB {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    {V : ℝ} (R : BoundaryRegisterOverXBA_BSTD2 EW.early V) {m : ℕ}
    (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3)
    {Γ Sg eg Ξ c cw : Fin 3 → ℝ} {Kj : ℕ} {bcut bder κ cadj : ℝ}
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    (Q : ∀ k : (hm.supply_BSTD2 oM).some.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0}
        {q : (Sq.W m).pieceInterior ⊤ | (hm.supply_BSTD2 oM).some.zeroRadial_BIFc k q ≤ 2 / 5})
    (hlift : ∀ (DP : BoundaryAugmentedDataPV3 (hm.supply_BSTD2 oM).some
        (actualSlotsV2_BAUGD (hm.supply_BSTD2 oM).some) Γ Sg eg)
      (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
      (dec : BoundaryActualDecompositionV2b C.toChain) (zc : BoundaryZeroCuspExit74b C.toChain dec),
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc)
    (O : (hm.supply_BSTD2 oM).some.LabelledWholeProduct_BIF ∨
      ∃ (DP : BoundaryAugmentedDataPV3 (hm.supply_BSTD2 oM).some
          (actualSlotsV2_BAUGD (hm.supply_BSTD2 oM).some) Γ Sg eg)
        (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
        (dec : BoundaryActualDecompositionV2b C.toChain),
        BoundaryGeometricExports74V32 C.toChain dec) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i :=
  member_output_to_labelled_certificate_HB EW Sq R hm _ rr Q hlift O

end DifferentialGeometry.Geometry.Collapse
