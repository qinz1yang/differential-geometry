import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMemberLabelledCertificateA01B
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryH2InstanceHB
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterChainEReadyRNUM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42SequenceBindings

/-!
# The boundary endpoint input A01 at universe 0 from `hrim` and `hint` (lane S-A01BMAP, `_A01B`)

Group G1c. The X132 ledger's A01 is `exists_boundary_graph_threshold`
(`Geometry/Collapse/GraphManifold.lean:116`): a static threshold `w₀` below which every connected
carrier with nearly cuspidal boundary data and the two collapse hypotheses has a raw graph
presentation whose external tori are the boundary components.

`exists_boundary_graph_threshold_of_rim_hint_A01B` proves exactly that statement, at
`CompactCarrier.{0}`, from

* `boundary_graph_threshold_of_sequence_binding_rimProduct_BQ` (BBR03: by contradiction with the
  boundary counterexample sequence at the ratios `δ_{n+1}`; FC42's form-(b) consumer),
* `exists_boundaryChainE_register_stored_ready_RNUM` (the stored choice, the register of every
  standing sequence, the member output and the chain of every separated supply on a tail),
* `member_output_to_labelled_certificate_A01B` (G1a: product bridge, the V32 / A4 head with the
  stage lift produced, label transport),

with exactly TWO non-register inputs, verbatim the binders `hrim` and `hint` of
`boundary_strongCertificate_V32_A4_OBDf`, quantified over every chain of the ready theorem's data
(`hrimint`). The standing sequence is the one of the contradiction argument: no standing-sequence
production (F77-1S) is used. The universe is `0` (the boundary supply is on `CompactCarrier.{0}`).
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

/-- **A01 at universe 0, modulo `hrim` and `hint`**: the statement of the admitted
`exists_boundary_graph_threshold` at `CompactCarrier.{0}`. The hypothesis `hrimint` is the pair
`hrim ∧ hint` of `boundary_strongCertificate_V32_A4_OBDf` for every chain of the stored choice's
register data (jet order `0`, `c_adj = 1`), given the member output and the three row-readiness
records of the ready theorem. -/
theorem exists_boundary_graph_threshold_of_rim_hint_A01B (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w)
    (hrimint : ∀ (Ξ Γ Sg eg c cw : Fin 3 → ℝ)
      (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => fun j => e j / 2))
      (Sq : BoundaryStandingSequence_BSTD1 K A
        (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
      (V : ℝ) (R : BoundaryRegisterOverXBA_BSTD2 EW.early V) (m : ℕ),
      BoundaryMemberOutputXBA_BSTD2 Sq m R →
      ∀ (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3)
      (Sup : BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ
        EW.early.σs EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s'
        EW.early.ε EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal EW.early.εr
        EW.early.e EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz EW.θ (Sq.W m) (Sq.g m)
        (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM),
      EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
        (100 * (boundaryDerivBound_BDFB + 1) *
          (1 + boundaryChainCutoffConst_BAUGD + cw 0 / Sg 0)) →
      MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m →
      RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2) →
      ∀ (DP : BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg)
      (C : BoundaryGaf02ChainE DP 0 Ξ c cw boundaryChainCutoffConst_BAUGD boundaryDerivBound_BDFB
        cutoffKappa_BAUGP2 1),
      (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
        BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
        Kc.verticalFace ⊆ Kc.remainder ∧
          Kc.remainder ∩ frontier Kc.M₂ ⊆
            frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
          Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
            Kc.remainder) ∧
      (∀ dec : BoundaryActualDecompositionV2b C.toChain,
        BoundaryGeometricExports74V32 C.toChain dec →
          dec.bases.edgeParent ⊆ ((Sq.W m).interior : Set (Sq.W m).Carrier))) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W, ∃ e : Fin B.count ≃ Fin G.externalCount,
          ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, -, EW, -, hea, hmain⟩ :=
    exists_boundaryChainE_register_stored_ready_RNUM K hK A hA 0 (cadj := 1) one_pos
  have hδ := (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar_pos
  refine boundary_graph_threshold_of_sequence_binding_rimProduct_BQ.{0} K A hδ ?_
    fun W _ _ _ D hp =>
      exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct W D hp
  intro W hW g B hcoll
  let Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar :=
    ⟨_, hδ, le_rfl, W, hW, g, B, fun n => (hcoll n).1, fun n => (hcoll n).2⟩
  obtain ⟨V, R, rr, n₀, hR⟩ := hmain Sq
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hm, mr, hsupp⟩ := hR n hn
  obtain ⟨oM⟩ := exists_member_orientation_HB (Sq.W n)
  obtain ⟨Et, ⟨Dc, hDc⟩, hEt⟩ := member_output_to_labelled_certificate_A01B EW Sq R hm
    (hm.supply_BSTD2 oM).some hea mr rr
    (fun hsep => by
      obtain ⟨DP, C, -⟩ := hsupp oM _ hsep
      exact ⟨DP, ⟨C⟩⟩)
    (fun DP C => (hrimint Ξ Γ Sg eg c cw EW Sq V R n hm oM _ hea mr rr DP C).1)
    (fun DP C => (hrimint Ξ Γ Sg eg c cw EW Sq V R n hm oM _ hea mr rr DP C).2)
  exact ⟨Et, ⟨Dc, hDc⟩, hEt⟩

end DifferentialGeometry.Geometry.Collapse
