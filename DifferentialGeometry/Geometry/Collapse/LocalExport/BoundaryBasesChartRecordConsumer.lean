import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesChartRecord
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCoreConsumer

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3c (part 2): inhabitant and consumer of the record

* `BoundaryGaf02ChainE.chartSpec_of_isEmpty_BBP`: over empty chart families the record is
  inhabited (all sets are empty);
* `BoundaryGaf02ChainE.exists_basesV2_of_chartSpec_BBP`: the record, the core's register premises
  and G12's numeric premises assemble `BoundaryGaf02BasesV2 C.toChain` (core `basesCore_BBP`,
  split `laterSplit_basesCore_BBP`, parent `edgeParent_of_basesCore_BBP`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **Inhabitant of the record**: over empty chart families (hence empty bases) it holds. -/
theorem chartSpec_of_isEmpty_BBP [IsEmpty S.CircleIdx_BAUGD] [IsEmpty S.EdgeIdx_BAUGD]
    [IsEmpty S.SlimIdx_BAUGD] :
    ∃ (σc : S.CircleIdx_BAUGD → ℝ² →
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (σe : S.EdgeIdx_BAUGD → ℝ →
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (σs : S.SlimIdx_BAUGD → ℝ →
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      BoundaryBaseChartsSpec_BBP C σc σe σs := by
  have hsrc : ∀ st, C.baseSource_BBP st = ∅ := fun st => C.baseSet_eq_empty_of_isEmpty_BBP st
  have hset : ∀ st, C.baseSet_BBP st = ∅ := fun st => by
    unfold baseSet_BBP
    rw [hsrc st, Set.image_empty]
  have hO : ∀ st, S.ratioSet_BBP st = ∅ := fun st => by
    fin_cases st
    · exact Set.iUnion_of_empty _
    · exact Set.iUnion_of_empty _
    · exact Set.iUnion_of_empty _
  have hnat : ∀ st, C.nativePatch_BBP st = ∅ := fun st => by
    fin_cases st
    · exact Set.iUnion_of_empty _
    · exact Set.iUnion_of_empty _
    · exact Set.iUnion_of_empty _
  have hbig : ∀ st, C.bigBase_BBP st = ∅ := fun st => by
    unfold bigBase_BBP
    rw [hnat st, Set.image_empty]
  have hU : C.edgeParentSet_BBP = ∅ := by
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hp
    have h1 : C.toChain.stageMap 1 p ∈ S.ratioSet_BBP 1 := hp.1
    rw [hO 1] at h1
    exact h1
  refine ⟨fun i _ => isEmptyElim i, fun i _ => isEmptyElim i, fun i _ => isEmptyElim i, ?_⟩
  refine
    { base_eq := fun st => by rw [hset st, hO st, Set.inter_empty]
      circle_smooth := fun i => isEmptyElim i
      circle_mem := fun i => isEmptyElim i
      circle_inv := fun i => isEmptyElim i
      circle_cover := by rw [hbig 0]; exact Set.empty_subset _
      edge_smooth := fun i => isEmptyElim i
      edge_mem := fun i => isEmptyElim i
      edge_inv := fun i => isEmptyElim i
      edge_cover := by rw [hbig 1]; exact Set.empty_subset _
      slim_smooth := fun i => isEmptyElim i
      slim_mem := fun i => isEmptyElim i
      slim_inv := fun i => isEmptyElim i
      slim_cover := by rw [hbig 2]; exact Set.empty_subset _
      later_isEmbedding := fun st => ?_
      edgeParent_sub := by rw [hU]; exact Set.empty_subset _ }
  have hE : IsEmpty ↥(C.toChain.nativeStageMap_BIFc st '' C.baseSource_BBP st) := by
    rw [hsrc st, Set.image_empty]
    exact inferInstance
  exact Topology.IsEmbedding.of_subsingleton _

include C in
/-- **Consumer (the A4 assembly of the BASES exit)**: the record, the core's register premises and
G12's numeric premises give `BoundaryGaf02BasesV2 C.toChain`. -/
theorem exists_basesV2_of_chartSpec_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    {σc' : S.CircleIdx_BAUGD → ℝ² →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    {σe : S.EdgeIdx_BAUGD → ℝ →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    {σs' : S.SlimIdx_BAUGD → ℝ →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hspec : BoundaryBaseChartsSpec_BBP C σc' σe σs') :
    Nonempty (BoundaryGaf02BasesV2 C.toChain) := by
  obtain ⟨sp⟩ := C.laterSplit_basesCore_BBP hspec.later_isEmbedding
  obtain ⟨par⟩ := C.edgeParent_of_basesCore_BBP hβ2 hγ hσ hb hc hC hε0 hε hγc hγc1 hβc1
    hspec.edgeParent_sub
  exact ⟨{ toBoundaryGaf02BasesCore_BIFc := C.basesCore_BBP hβ2 hγ hσ hb
           split := sp
           parent := par }⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
