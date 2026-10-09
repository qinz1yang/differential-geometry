import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductBridgeHB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsV32ProducerOBD
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterRowReadyRNUM
import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyWithChoiceBSTD2

/-!
# `member_output_to_labelled_certificate` (lane S-HBRIDGE, suffix `_HB`), group G2

Disposition D80-11 (h): from the geometric output of a tail member — the product branch OR the
separated branch — the labelled certificate of H2 on the member's own boundary `Sq.B m`.

* `labelledCertificate_of_packetLabels_HB`: the label transport `S.cusp_eq : S.packet.cusp = B`
  in the `Nonempty` shape of H2;
* **`member_separated_to_labelled_certificate_HB`**: the separated branch `(DP, C, dec, geom)`
  through the V2b / V32 head `boundary_graphPresentation_of_actual_decomposition_V32_BCF04_OBD`;
  every numerical premise of that head (`r_∂`, `θ`, N76-3) is read off the records
  (`R`, `rr : RegisterRowReady_RNUM`, `EW.θ_lt`, `hm.1.1.2`); the ONLY inputs besides the output are
  the two inputs that every separated head of the tree already carries: the selected solid cores
  `Q` (Z1 data) and the stage lift `hlift` (no new premise, no new named proposition);
* **`member_output_to_labelled_certificate_HB`**: both branches in one statement; the product
  branch is unconditional (G1), the separated branch needs `Q` and `hlift`.

The text-only inductive `BoundaryGeometricOutputE` is represented by its Prop-level content
`LabelledWholeProduct_BIF ∨ ∃ DP C dec, BoundaryGeometricExports74V32 C.toChain dec`
(`Nonempty (BoundaryGeometricOutputE S ch)` is equivalent to it), with the chain numbers
`Ξ Γ Sg eg c cw` explicit as in the tree's `exists_boundaryChainE_register_stored_ready_RNUM`.
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **Label transport** (`Nonempty` shape): a certificate with the rim-product clause on tori
labelled by the supply's packet components is one on the supplied boundary `B`
(`S.cusp_eq : S.packet.cusp = B`). -/
theorem labelledCertificate_of_packetLabels_HB (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i) :
    ∃ Et : BoundaryTori W B.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = B.component i := by
  rw [← S.cusp_eq]
  exact h

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The separated branch of the member output gives the labelled certificate** (D80-11 (h)):
the chain `C` with its V2b decomposition `dec` and the V32 exports `geom` at the member's supply
`Sup`; the numerical premises of the head are the register / member records, the other inputs are
the selected cores `Q` and the stage lift `hlift` of `dec`. -/
theorem member_separated_to_labelled_certificate_HB {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    {V : ℝ} (R : BoundaryRegisterOverXBA_BSTD2 EW.early V) {m : ℕ}
    (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
    {oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3}
    (Sup : BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ EW.early.σs
      EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s' EW.early.ε
      EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal EW.early.εr EW.early.e
      EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz EW.θ (Sq.W m) (Sq.g m)
      (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM)
    {Γ Sg eg Ξ c cw : Fin 3 → ℝ} {Kj : ℕ} {bcut bder κ cadj : ℝ}
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    {DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg}
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74V32 C.toChain dec)
    (Q : ∀ k : Sup.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : (Sq.W m).pieceInterior ⊤ | Sup.zeroRadial_BIFc k q ≤ 2 / 5})
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i :=
  labelledCertificate_of_packetLabels_HB Sup
    (C.boundary_graphPresentation_of_actual_decomposition_V32_BCF04_OBD dec geom Q R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM rr.rd_mul
      (memberPremise_RNUM hm) EW.θ_lt hlift)

/-- **`member_output_to_labelled_certificate`** (D80-11 (h)): the geometric output of the member
(the product branch of the labelled whole product, or the separated branch with a chain, its V2b
decomposition and the V32 exports) gives the labelled certificate of H2 on `Sq.B m`. The product
branch is unconditional (`labelledCertificate_of_product_HB`); the separated branch uses `Q` and
the stage lift `hlift` (for every chain and decomposition of the output). -/
theorem member_output_to_labelled_certificate_HB {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    {V : ℝ} (R : BoundaryRegisterOverXBA_BSTD2 EW.early V) {m : ℕ}
    (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
    {oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3}
    (Sup : BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ EW.early.σs
      EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s' EW.early.ε
      EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal EW.early.εr EW.early.e
      EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz EW.θ (Sq.W m) (Sq.g m)
      (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM)
    {Γ Sg eg Ξ c cw : Fin 3 → ℝ} {Kj : ℕ} {bcut bder κ cadj : ℝ}
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    (Q : ∀ k : Sup.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : (Sq.W m).pieceInterior ⊤ | Sup.zeroRadial_BIFc k q ≤ 2 / 5})
    (hlift : ∀ (DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg)
      (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
      (dec : BoundaryActualDecompositionV2b C.toChain) (zc : BoundaryZeroCuspExit74b C.toChain dec),
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc)
    (O : Sup.LabelledWholeProduct_BIF ∨
      ∃ (DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg)
        (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
        (dec : BoundaryActualDecompositionV2b C.toChain),
        BoundaryGeometricExports74V32 C.toChain dec) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i := by
  rcases O with h | ⟨DP, C, dec, geom⟩
  · exact labelledCertificate_of_product_HB Sup h
  · exact member_separated_to_labelled_certificate_HB EW Sq R hm Sup rr C dec geom Q
      (hlift DP C dec)

end DifferentialGeometry.Geometry.Collapse
