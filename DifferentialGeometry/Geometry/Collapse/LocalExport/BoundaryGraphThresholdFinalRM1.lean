import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdOBDgA01B
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimActualRM1

/-!
# The boundary endpoint input A01 at universe 0 with NO non-register input (lane S-RIM81, G6)

`exists_boundary_graph_threshold_of_rim_A01B` (S-A01BMAP) proves the admitted
`exists_boundary_graph_threshold` at `CompactCarrier.{0}` from ONE non-register input `hrims` (the
rim conjunction `hV ∧ hF ∧ hsat` for every chain of the ready theorem's data). Review 81 B⁺ makes
the rim conjunction a theorem (`rim3_actual_RM1`), with the register numerics read off the member
output and the three row-readiness records exactly as in the S-A01BMAP member heads:

* `rim3_of_member_records_RM1`: the rim conjunction from the member records
  (`hm`, `ea`, `mr`, `rr`) and `hm.premises_BSTD2`;
* **`exists_boundary_graph_threshold_final_RM1`**: A01 at universe 0, no hypothesis beyond the
  statement's own `K`, `A`, `hA`.
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

/-- **The rim conjunction for a chain of the member output, from the records alone**: the register
numerics of `rim3_actual_RM1` are read off `ea`, `rr`, `hm` as in
`member_separated_to_labelled_certificate_OBDg_A01B`. -/
theorem rim3_of_member_records_RM1 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    {V : ℝ} (R : BoundaryRegisterOverXBA_BSTD2 EW.early V) {m : ℕ}
    (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R)
    {oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3}
    {Sup : BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ EW.early.σs
      EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s' EW.early.ε
      EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal EW.early.εr EW.early.e
      EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz EW.θ (Sq.W m) (Sq.g m)
      (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM}
    {Γ Sg eg Ξ c cw : Fin 3 → ℝ} {Kj : ℕ} {bcut bder κ cadj : ℝ}
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0)))
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    {DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg}
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj) :
    ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder := by
  obtain ⟨-, hγ, -, hμ, -, hσc, -, -, -, -, -, -⟩ := ea.a4_premises_RNUM
  obtain ⟨hΔ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLΛ, -⟩ := hm.premises_BSTD2.1
  exact C.rim3_actual_RM1 R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
    rr.rd_mul (memberPremise_RNUM hm) EW.θ_lt (by linarith) EW.early.Λ_pos.le hμ hσc
    EW.early.σs_pos.le EW.early.σs_le (by linarith) hLΛ

/-- **A01 at universe 0 with NO non-register input**: the statement of the admitted
`exists_boundary_graph_threshold` at `CompactCarrier.{0}`
(`exists_boundary_graph_threshold_of_rim_A01B` with `hrims := rim3_of_member_records_RM1`). -/
theorem exists_boundary_graph_threshold_final_RM1 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = B.component i :=
  exists_boundary_graph_threshold_of_rim_A01B K hK A hA
    fun _ _ _ _ _ _ EW Sq _ R _ hm _ _ ea _ rr _ C =>
      rim3_of_member_records_RM1 EW Sq R hm ea rr C

end DifferentialGeometry.Geometry.Collapse
