import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStrongCertificateHeadOBDf
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMemberLabelledCertificateHB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductBridgeConsumerHB

/-!
# The member's labelled certificate from the OBDf head (lane S-A01BMAP, `_A01B`), group G1a

`member_separated_to_labelled_certificate_HP` (S-HEADPLUG) took the stage lift `hlift` and seven
register-level numerics `hT hσL hbη h3b hbH hLΛ hμΔ`. After S-BD2f's `_OBDf` heads the stage lift
is a theorem (with the explicit input `hint`, obstruction O1), and the seven numerics are the
7th and 13th to 18th components of `R.bcf02_premises_BSTD2`, i.e. of `hm.premises_BSTD2`.

* `member_separated_to_labelled_certificate_A01B`: the labelled certificate on `Sq.B m` from the
  chain `C` of the separated branch alone; the ONLY non-record inputs are `hrim` and `hint`;
* `member_output_to_labelled_certificate_A01B`: both branches of `geometric_cases_BIF` in one
  statement; the product branch is unconditional (`labelledCertificate_of_product_HB`), the
  separated branch uses the chain and `hrim`, `hint` for every chain of the supply.

No new named `Prop`, no new premise: `hrim` and `hint` are verbatim the binders of
`boundary_graphPresentation_V32_A4_OBDf`.
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

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The separated branch of the member output gives the labelled certificate, from the chain
`C` alone, with the stage lift PRODUCED** (`member_separated_to_labelled_certificate_HP` with
`hlift` replaced by `hint` and the seven register numerics read off the member output): the
non-record inputs are `hrim` and `hint`. -/
theorem member_separated_to_labelled_certificate_A01B {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
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
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0)))
    (mr : MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m)
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    {DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg}
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
    (hrim : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder)
    (hint : ∀ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec →
        dec.bases.edgeParent ⊆ (Sq.W m).interior) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i := by
  obtain ⟨hβ2, hγ, hd, hμ, hτ, hσc, hbA, hε0, hε, hγc, hγc1, hβc1⟩ := ea.a4_premises_RNUM
  obtain ⟨h3βc, -, hγ0, -, hC⟩ := ea.f1_premises_RNUM
  obtain ⟨hεr, he⟩ := ea.f3_premises_RNUM
  obtain ⟨hΔ, -, -, -, -, -, hT, -, -, hb, hs, -, hσL, hbη, h3b, hbH, hLΛ, hμΔ⟩ :=
    hm.premises_BSTD2.1
  exact labelledCertificate_of_packetLabels_HB Sup
    (C.boundary_graphPresentation_V32_A4_OBDf hβ2 hγ hd (by omega) mr.index hμ hτ hσc hbA hC hε0 hε
      hγc hγc1 hβc1 hεr he R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
      rr.rd_mul (memberPremise_RNUM hm) EW.θ_lt hΔ EW.early.Λ_pos.le hT EW.early.σs_pos.le
      EW.early.σs_le hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0 hrim hint)

/-- **Both branches of the member output give the labelled certificate of H2** (the product
branch with no input, the separated branch with the chain and `hrim`, `hint` for every chain of the
supply). -/
theorem member_output_to_labelled_certificate_A01B {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
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
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0)))
    (mr : MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m)
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    (hch : Sup.SeparatedCollarZero_BIF →
      ∃ DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg,
        Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj))
    (hrim : ∀ (DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg)
      (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj),
      ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder)
    (hint : ∀ (DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg)
      (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
      (dec : BoundaryActualDecompositionV2b C.toChain),
      BoundaryGeometricExports74V32 C.toChain dec →
        dec.bases.edgeParent ⊆ (Sq.W m).interior) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i := by
  rcases Sup.geometric_cases_BIF with h | hsep
  · exact labelledCertificate_of_product_HB Sup h
  · obtain ⟨DP, ⟨C⟩⟩ := hch hsep
    exact member_separated_to_labelled_certificate_A01B EW Sq R hm Sup ea mr rr C (hrim DP C)
      (hint DP C)

end DifferentialGeometry.Geometry.Collapse
