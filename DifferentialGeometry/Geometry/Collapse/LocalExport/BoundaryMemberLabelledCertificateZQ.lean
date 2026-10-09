import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMemberLabelledCertificateHB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroSelectedCoresConsumerZQ

/-!
# The labelled certificate from the separated member output, Z1 cores produced (lane S-ZQ, `_ZQ`)

`member_separated_to_labelled_certificate_HB` (S-HBRIDGE G2) without its input `Q`: the selected
solid cores of the member's supply are produced (`BoundarySupply.zeroSelectedCores_ZQ`), so the
separated branch `(DP, C, dec, geom)` gives the labelled certificate of H2 on `Sq.B m` from the
records and the stage lift `hlift` alone: `member_separated_to_labelled_certificate_ZQ`, and, for
both branches of the member output, `member_output_to_labelled_certificate_ZQ`.
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

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The separated branch of the member output gives the labelled certificate, Z1 cores
produced** (`member_separated_to_labelled_certificate_HB` without `Q`): the numerical premises of
the head are read off the records as there, the selected cores are
`Sup.zeroSelectedCores_ZQ`, and the only input besides the output `(DP, C, dec, geom)` is the stage
lift `hlift` of `dec`. -/
theorem member_separated_to_labelled_certificate_ZQ {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
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
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i :=
  labelledCertificate_of_packetLabels_HB Sup
    (C.boundary_graphPresentation_of_actual_decomposition_V32_BCF04_ZQ dec geom R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM rr.rd_mul
      (memberPremise_RNUM hm) EW.θ_lt hlift)


/-- **`member_output_to_labelled_certificate`, Z1 cores produced** (`_HB` without `Q`): the
product branch is unconditional, the separated branch needs only the stage lift `hlift` (for every
chain and decomposition of the output). -/
theorem member_output_to_labelled_certificate_ZQ {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
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
  · exact member_separated_to_labelled_certificate_ZQ EW Sq R hm Sup rr C dec geom (hlift DP C dec)

end DifferentialGeometry.Geometry.Collapse
