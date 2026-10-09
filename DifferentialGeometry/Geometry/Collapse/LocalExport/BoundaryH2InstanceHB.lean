import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMemberLabelledCertificateHB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorOrientation
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductBridgeConsumerHB

/-!
# H2 as an instance at the tail index `n₀` (lane S-HBRIDGE, suffix `_HB`), group G3

D80-11 (h): "`member_output_to_labelled_certificate` (per member, both branches) so that H2 is the
case `n₀` of it; `hn₀ = 32 · 10⁶ Δ ≤ n₀` fine".

* `memberRowReady_of_tailIndex_HB` (unconditional; the tree form of the text's
  `memberRowReady_of_tailIndex_BIFc`): the index clause of `MemberRowReady_RNUM` for every
  `m ≥ n₀` from the single bound `32 · 10⁶ Δ ≤ n₀`;
* `exists_member_orientation_HB` (unconditional): the member's interior carries an orientation
  (`W.orientation`, `nonempty_interiorOrientation_BDRY5`), so H2 needs no orientation input;
* the CONSUMER `example` (end of file): the conclusion of H2 on the SAME `EW`, `ea`-free tree form
  (`ea` is used only inside H1), the SAME register `R` with `rr`, the tail `htail` and `hn₀`, as the
  instance `m = n₀` of `member_output_to_labelled_certificate_HB`, from the member's output
  (H1 at the member's own supply, `bbr02_geometricOutputE_of_member_BBR`) and, for the separated
  branch only, the two inputs `Q` and `hlift` of G2.

H1 itself is OPEN (text `sorry`) and the text-only types of H1 / H2 are not tree declarations, so
no `h1_HB` / `h2_HB` theorem is stated: the example takes H1 at the member's own supply as its
hypothesis `h1`, which is a consumer shape, not a new premise of any tree theorem. The second
example is the PRODUCT branch of H2 at `n₀` with no `Q`, no `hlift` and no index bound (a
strengthening: the product branch uses no numerical record).
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

/-- **Member index from the tail index**: the index clause of `MemberRowReady_RNUM` for every
`m ≥ n₀` is the single bound `32 · 10⁶ Δ ≤ n₀`. -/
theorem memberRowReady_of_tailIndex_HB {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) {n₀ m : ℕ} (hn₀ : 32 * (1000000 * E.Δ) ≤ (n₀ : ℝ))
    (hm : n₀ ≤ m) : MemberRowReady_RNUM E m := by
  refine ⟨hn₀.trans ?_⟩
  have h1 : (n₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact h1.trans h2

/-- **Every member has an orientation of its interior** (from the carrier's orientation). -/
theorem exists_member_orientation_HB (W : CompactCarrier.{0}) :
    Nonempty (ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) :=
  nonempty_interiorOrientation_BDRY5 W

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **H2 as the instance `m = n₀` of `member_output_to_labelled_certificate_HB`** (consumer shape;
`h1` is H1 at the member's own supply in its Prop-level form, `Q` and `hlift` serve the separated
branch only). -/
example {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    {V : ℝ} (R : BoundaryRegisterOverXBA_BSTD2 EW.early V)
    {Γ Sg eg Ξ c cw : Fin 3 → ℝ} {Kj : ℕ} {bcut bder κ cadj : ℝ}
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2)) (n₀ : ℕ)
    (hn₀ : 32 * (1000000 * EW.early.Δ) ≤ (n₀ : ℝ))
    (htail : ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R)
    (h1 : ∀ {m : ℕ} (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
      (_ : MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m)
      (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3),
      (hm.supply_BSTD2 oM).some.LabelledWholeProduct_BIF ∨
        ∃ (DP : BoundaryAugmentedDataPV3 (hm.supply_BSTD2 oM).some
            (actualSlotsV2_BAUGD (hm.supply_BSTD2 oM).some) Γ Sg eg)
          (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
          (dec : BoundaryActualDecompositionV2b C.toChain),
          BoundaryGeometricExports74V32 C.toChain dec)
    (Q : ∀ {m : ℕ} (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
      (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3)
      (k : (hm.supply_BSTD2 oM).some.ZeroIdx_BAUGC),
      SelectedSmoothCore74.{0, 0}
        {q : (Sq.W m).pieceInterior ⊤ | (hm.supply_BSTD2 oM).some.zeroRadial_BIFc k q ≤ 2 / 5})
    (hlift : ∀ {m : ℕ} (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
      (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3)
      (DP : BoundaryAugmentedDataPV3 (hm.supply_BSTD2 oM).some
        (actualSlotsV2_BAUGD (hm.supply_BSTD2 oM).some) Γ Sg eg)
      (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
      (dec : BoundaryActualDecompositionV2b C.toChain) (zc : BoundaryZeroCuspExit74b C.toChain dec),
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ m, n₀ ≤ m ∧ letI := Sq.conn m
      ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
        Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
          ∀ i, range (Et.torusMap i) = (Sq.B m).component i := by
  obtain ⟨oM⟩ := exists_member_orientation_HB (Sq.W n₀)
  have hm := htail n₀ le_rfl
  have mr := memberRowReady_of_tailIndex_HB EW.early.toBoundaryEarlyOver_BSTD1 hn₀ (le_refl n₀)
  exact ⟨n₀, le_rfl, member_output_to_labelled_certificate_HB EW Sq R hm _ rr (Q hm oM)
    (hlift hm oM) (h1 hm mr oM)⟩

/-- **H2 in the product branch** (consumer shape, a strengthening: no `hn₀`, no `Q`, no `hlift`):
if the member `n₀` is in the labelled whole-product branch at its own supply, the labelled
certificate of H2 holds at `m = n₀`. -/
example {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    {V : ℝ} (R : BoundaryRegisterOverXBA_BSTD2 EW.early V) (n₀ : ℕ)
    (htail : ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R)
    (h1 : ∀ {m : ℕ} (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
      (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3),
      (hm.supply_BSTD2 oM).some.LabelledWholeProduct_BIF) :
    ∃ m, n₀ ≤ m ∧ letI := Sq.conn m
      ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
        Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
          ∀ i, range (Et.torusMap i) = (Sq.B m).component i := by
  obtain ⟨oM⟩ := exists_member_orientation_HB (Sq.W n₀)
  have hm := htail n₀ le_rfl
  exact ⟨n₀, le_rfl, labelledCertificate_of_product_at_member_supply_HB EW Sq R hm oM
    (h1 hm oM)⟩

end DifferentialGeometry.Geometry.Collapse
