import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStrongCertificateHeadHP
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMemberLabelledCertificateZQ

/-!
# The labelled certificate from the member's chain alone, rows plugged in (lane S-HEADPLUG, `_HP`)

`member_separated_to_labelled_certificate_ZQ` (S-ZQ) takes the member output's decomposition
`dec` and exports `geom` as given. Here only the chain `C` of the separated branch is given, and
the decomposition with its V32 exports is PRODUCED by
`exists_boundaryGeometricExports74V32_A4_rim3_BG4` (module BoundaryStrongCertificateHeadHP):
`member_separated_to_labelled_certificate_HP` has, besides the records, ONLY the two inputs
`hrim` (`hV ∧ hF ∧ hsat` over every v2b decomposition of `C`) and the stage lift `hlift`.

The numerical premises of the head are read off the records as far as the tree has them
(`EarlyRowReady_RNUM`, `MemberRowReady_RNUM`, `RegisterRowReady_RNUM`, the early choice's own
fields); the seven that no record carries remain explicit register-level hypotheses (`hT`, `hσL`,
`hbη`, `h3b`, `hbH`, `hLΛ`, `hμΔ`).
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

/-- **The separated branch of the member output gives the labelled certificate, from the chain
`C` alone** (`member_separated_to_labelled_certificate_ZQ` with `dec` and `geom` produced): the
non-register inputs are `hrim` and the stage lift `hlift`. -/
theorem member_separated_to_labelled_certificate_HP {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
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
    (hT : 1000 * EW.early.Δ ≤ EW.early.T)
    (hσL : (bcf02Sigma_BCF2K EW.early.Δ)⁻¹ ≤ R.Lmax)
    (hbη : EW.early.b ≤ bcf02Eta_BCF2K EW.early.Δ)
    (h3b : 3 * EW.early.b ≤ bcf02Sigma_BCF2K EW.early.Δ)
    (hbH : EW.early.b * (2 * (20 * EW.early.Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * EW.early.Δ * EW.early.Λ < 1 / 100000)
    (hμΔ : EW.early.μ * EW.early.Δ < 1 / 10000)
    {DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg}
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
    (hrim : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder)
    (hlift : ∀ (dec : BoundaryActualDecompositionV2b C.toChain)
      (zc : BoundaryZeroCuspExit74b C.toChain dec),
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i := by
  obtain ⟨hβ2, hγ, hd, hμ, hτ, hσc, hbA, hε0, hε, hγc, hγc1, hβc1⟩ := ea.a4_premises_RNUM
  obtain ⟨h3βc, -, hγ0, -, hC⟩ := ea.f1_premises_RNUM
  obtain ⟨hεr, he⟩ := ea.f3_premises_RNUM
  have hΔ : 2 ≤ EW.early.Δ := by
    have h1 : (100 : ℝ) / (1 / 100) < 100 / EW.early.β₂ :=
      div_lt_div_of_pos_left (by norm_num) EW.early.β₂_pos EW.early.β₂_lt
    have h2 := EW.early.Δ_gt
    norm_num at h1
    linarith
  have hb' : EW.early.b' < 1 / 1000000 := by
    refine lt_of_lt_of_le EW.early.b'_lt ?_
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  exact labelledCertificate_of_packetLabels_HB Sup
    (C.boundary_graphPresentation_V32_A4_HP hβ2 hγ hd (by omega) mr.index hμ hτ hσc hbA hC hε0 hε
      hγc hγc1 hβc1 hεr he R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
      rr.rd_mul (memberPremise_RNUM hm) EW.θ_lt hΔ EW.early.Λ_pos.le hT EW.early.σs_pos.le
      EW.early.σs_le (by linarith [EW.early.b_lt_s, EW.early.s_lt])
      (by linarith [EW.early.s_lt_b']) hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0 hrim hlift)

end DifferentialGeometry.Geometry.Collapse
