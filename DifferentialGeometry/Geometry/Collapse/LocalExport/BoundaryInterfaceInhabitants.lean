import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecomposition

/-!
# Boundary route interfaces, part 5: inhabitants and consumer (lane BIFACE)

Compiled inhabitants of every structure of `BoundaryInterface{Augmented,Chain,Bases,Decomposition}`
(the rule "interface structures need inhabitants"), on the ACTUAL supply object `S` (inhabited on
the double-cusp standing sequence by BAUG-A's `lc88_boundarySupply_doubleCusp_BAUGA`).

* `BoundarySupply.emptySlots_BIF S`: the slot with no interior stage tags, empty stage cores and
  zero cutoffs; every stage adjustment is the identity (`emptySlots_adjust_BIF`).
* `BoundarySupply.emptyStageReferences_BIF`: a stage table on the empty clouds whose boundary model
  slots are EXACTLY the (BM) formula `R_a⁻¹ 𝓑(h_{a,b})` on the listed `b ∈ J_∂(a)` and `0`
  elsewhere, for EVERY centre of the stored family (the centres are not assumed empty here).
* `BoundarySupply.emptyAugmentedData_BIF`: `BoundaryAugmentedData S (emptySlots)` on the separated
  branch, for every `S`; `BoundarySupply.product_or_augmentedData_BIF`: every supply is the
  labelled whole product or carries augmented data.
* The empty-family regime (draft 61 §3.3, D61-7: `ψ_j = 0`, `Ψ_j = id`, empty marked bases): for a
  supply whose three stage-centre sets are empty, the chain `emptyChain_BIF` (inactive slots, the
  explicit CHOICE numbers `Ξ = 1/10`, `Σ = c = (10⁻⁸, 10⁻⁷, 10⁻⁶)`, `e = c_w = b_cut = b_der = 0`,
  `κ = 1`; the stage-one scale positivity is `ℓ_ρ(F_∂) = ρ > 0`), the empty bases / whole fibres /
  zero cores / `K₃` / edge restriction and the decomposition `emptyDecomposition_BIF`.
* Consumer: `nonempty_boundaryGeometricOutput_BIF` — on that regime (also no zero centre, and
  BAUG-A's smoothness inequalities so that `F_∂` is continuous) every supply has a
  `BoundaryGeometricOutput` (product branch, or separated with `D`, `C`, `dec`).

The ACTIVE inhabitants (active slots with native CFS15 outputs, nonempty bases) are the producers
`exists_boundaryGaf02Chain` / `buildBases` of lanes BAUG-C/D (frozen targets in
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

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

/-- The empty slots have empty slim slabs when the slim centres are empty. -/
theorem BoundarySupplyCore.slimSlabs_eq_empty_BIF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ
    b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W g δn n B oM)
    (h : S.stageCentres_BIF 2 = ∅) : S.slimSlabs_BIF = ∅ := by
  ext q
  simp only [BoundarySupplyCore.slimSlabs_BIF, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨j, hj, -⟩
  rw [h] at hj
  exact notMem_empty j hj

/-- The height coordinate `u_{E'}` of `H^∂` is continuous (a coordinate of a block projection). -/
theorem BoundarySupplyCore.continuous_heightCoord_BIF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs
    σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W g δn n B oM) :
    Continuous S.heightCoord_BIF :=
  (EuclideanSpace.proj (0 : Fin 2)).continuous.comp
    (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl S.edgeTag_BAUGA)).continuous

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **The empty slot**: no interior stage tags, empty stage cores and enlargements, zero
cutoffs. -/
def emptySlots_BIF : BoundaryInteriorSlots_BIF S where
  stageTags := fun _ => ∅
  stageCore := fun _ => ∅
  stageEnlargement := fun _ => ∅
  cutoff := fun _ _ => 0

/-- On the empty slot every stage adjustment is the identity (`ψ_j = 0`). -/
theorem emptySlots_adjust_BIF (st : Fin 3)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.emptySlots_BIF.adjust st a = id := by
  funext x
  simp [BoundaryInteriorSlots_BIF.adjust, adjustmentMap, emptySlots_BIF]

/-- The stage clouds of the empty slot are empty. -/
theorem isEmpty_emptySlots_stageCloud_BIF (st : Fin 3) :
    IsEmpty (S.emptySlots_BIF.stageCloud st) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, hp, -⟩ := x.2
  exact notMem_empty p hp

/-- The enlarged stage clouds of the empty slot are empty. -/
theorem isEmpty_emptySlots_stageCloudEnlarged_BIF (st : Fin 3) :
    IsEmpty (S.emptySlots_BIF.stageCloudEnlarged st) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, hp, -⟩ := x.2
  exact notMem_empty p hp

open Classical in
/-- **A stage table on the empty clouds** whose boundary model slots are exactly (BM) on the listed
components of EVERY centre and `0` on the unlisted ones; pruning `id`, coordinates `eta`. -/
def emptyStageReferences_BIF (st : Fin 3) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ) :
    BoundaryStageReferences_BIF S.emptySlots_BIF st E eta row where
  planes :=
    { rpre := fun x => (S.isEmpty_emptySlots_stageCloudEnlarged_BIF st).elim x
      pre := fun x => (S.isEmpty_emptySlots_stageCloud_BIF st).elim x
      ref := fun x => (S.isEmpty_emptySlots_stageCloud_BIF st).elim x
      model := fun a z => WithLp.toLp 2 (Sum.elim (fun _ => 0) fun i =>
        if i ∈ S.boundaryList_BIF st a then
          planeBlockEmbed_BAUGA (boundaryModel_BCG8b (S.packet.height i a) (S.rho a) (row a i)
            (eta a a) z)
        else 0)
      prune := fun _ => ContinuousLinearMap.id ℝ _
      coord := eta }
  ref_mem := fun x => (S.isEmpty_emptySlots_stageCloud_BIF st).elim x
  coord_eq := fun _ _ => rfl
  rpre_spec := fun x => (S.isEmpty_emptySlots_stageCloudEnlarged_BIF st).elim x
  pre_spec := fun x => (S.isEmpty_emptySlots_stageCloud_BIF st).elim x
  model_listed := fun a _ i hi z => by simp [hi]
  model_unlisted := fun a _ i hi z => by simp [hi]
  prune_boundary := fun _ _ _ => rfl

/-- **`BoundaryAugmentedData` on the separated branch** of any supply (empty slot, the three
stage tables of `emptyStageReferences_BIF` with the stored coordinates and rows). -/
def emptyAugmentedData_BIF (hsep : S.SeparatedCollarZero_BIF) :
    BoundaryAugmentedData S S.emptySlots_BIF where
  separated := hsep
  circle := S.emptyStageReferences_BIF 0 ℝ² S.circleEta_BIF S.circleRow_BIF
  edge := S.emptyStageReferences_BIF 1 ℝ S.edgeEta_BIF S.edgeRow_BIF
  slim := S.emptyStageReferences_BIF 2 ℝ S.slimEta_BIF S.slimRow_BIF

/-- Every supply is T3B's labelled whole product or carries augmented data. -/
theorem product_or_augmentedData_BIF :
    S.LabelledWholeProduct_BIF ∨ Nonempty (BoundaryAugmentedData S S.emptySlots_BIF) := by
  rcases S.geometric_cases_BIF with h | h
  · exact Or.inl h
  · exact Or.inr ⟨S.emptyAugmentedData_BIF h⟩

end BoundarySupply

/-- The accuracies `Ξ_j = 1/10` of the empty-family chain. -/
def emptyChainXi_BIF : Fin 3 → ℝ :=
  fun _ => 1 / 10

/-- The scale factors `Σ_j` and the CHOICE constants `c_j` of the empty-family chain:
`(10⁻⁸, 10⁻⁷, 10⁻⁶)`. -/
def emptyChainSg_BIF : Fin 3 → ℝ :=
  ![1 / 100000000, 1 / 10000000, 1 / 1000000]

/-- GAF01's CHOICE inequalities hold for the explicit numbers of the empty-family chain. -/
theorem emptyChain_numbers_BIF :
    (∀ j, 0 < emptyChainXi_BIF j ∧ 0 < emptyChainSg_BIF j ∧
      128 * (emptyChainXi_BIF j)⁻¹ * emptyChainSg_BIF j ≤ 1 / 5 ∧ 0 ≤ (fun _ : Fin 3 => (0 : ℝ)) j ∧
      emptyChainSg_BIF j ≤ emptyChainXi_BIF j / 10000 ∧ 0 ≤ (fun _ : Fin 3 => (0 : ℝ)) j) ∧
    5 / 3 * emptyChainXi_BIF 0 * emptyChainSg_BIF 0 < emptyChainSg_BIF 0 ∧
    emptyChainSg_BIF 0 ≤ 1 / 512 ∧
    (5 / 3 * emptyChainXi_BIF 0 * emptyChainSg_BIF 0 * 0 * 0 + emptyChainXi_BIF 0 * 0 +
        (fun _ : Fin 3 => (0 : ℝ)) 0) < emptyChainSg_BIF 0 ∧
    emptyChainSg_BIF 0 ≤ 4 * 1 / 5 ∧ emptyChainSg_BIF 0 ≤ 3 * emptyChainSg_BIF 1 / 10 ∧
    (emptyChainSg_BIF 0 + (5 / 3 * emptyChainXi_BIF 1 * emptyChainSg_BIF 1 +
        (1 + emptyChainXi_BIF 1) * emptyChainSg_BIF 0)) < emptyChainSg_BIF 1 ∧
    emptyChainSg_BIF 1 ≤ 1 / 512 ∧
    ((5 / 3 * emptyChainXi_BIF 1 * emptyChainSg_BIF 1 +
          (1 + emptyChainXi_BIF 1) * emptyChainSg_BIF 0) * 0 * (0 + emptyChainSg_BIF 0) +
        emptyChainXi_BIF 1 * (0 + emptyChainSg_BIF 0) + (fun _ : Fin 3 => (0 : ℝ)) 1 +
        2 * emptyChainSg_BIF 0) < emptyChainSg_BIF 1 ∧
    emptyChainSg_BIF 1 ≤ 4 * 1 / 5 ∧ emptyChainSg_BIF 1 ≤ 3 * emptyChainSg_BIF 2 / 10 ∧
    (emptyChainSg_BIF 1 + (5 / 3 * emptyChainXi_BIF 2 * emptyChainSg_BIF 2 +
        (1 + emptyChainXi_BIF 2) * emptyChainSg_BIF 1)) < emptyChainSg_BIF 2 ∧
    emptyChainSg_BIF 2 ≤ 1 / 512 ∧
    ((5 / 3 * emptyChainXi_BIF 2 * emptyChainSg_BIF 2 +
          (1 + emptyChainXi_BIF 2) * emptyChainSg_BIF 1) * 0 * (0 + emptyChainSg_BIF 1) +
        emptyChainXi_BIF 2 * (0 + emptyChainSg_BIF 1) + (fun _ : Fin 3 => (0 : ℝ)) 2 +
        2 * emptyChainSg_BIF 1) < emptyChainSg_BIF 2 := by
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> norm_num [emptyChainXi_BIF, emptyChainSg_BIF]
  · norm_num [emptyChainXi_BIF, emptyChainSg_BIF]

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM}

namespace BoundaryAugmentedData

/-- **The empty-family chain** (D61-7's empty case): inactive slots, zero cutoffs, the explicit
CHOICE numbers; requires the three stage-centre sets of the stored family to be empty (the cutoff
plateaus are then vacuous). -/
def emptyChain_BIF (D : BoundaryAugmentedData S S.emptySlots_BIF)
    (hc : ∀ st, S.stageCentres_BIF st = ∅) (Kj : ℕ) :
    BoundaryGaf02Chain D Kj emptyChainXi_BIF emptyChainSg_BIF (fun _ => 0) emptyChainSg_BIF
      (fun _ => 0) 0 0 1 where
  numbers := emptyChain_numbers_BIF
  slot := fun _ => .inactive rfl rfl
  cutoff_bindings := by
    have hnot : ∀ st (j : W.pieceInterior ⊤), j ∉ S.stageCentres_BIF st := fun st j hj => by
      rw [hc st] at hj
      exact notMem_empty j hj
    have hts : tsupport (fun _ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
        (0 : ℝ)) = ∅ := tsupport_zero
    have hseg : ∀ (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (t : ℝ),
        (1 - t) • x + t • x = x := fun x t => by
      rw [← add_smul, sub_add_cancel, one_smul]
    simp only [BoundarySupply.emptySlots_adjust_BIF, id, hseg]
    refine ⟨⟨contDiff_const, fun _ => ⟨le_rfl, zero_le_one⟩, fun p ⟨j, hj, _⟩ => (hnot 0 j hj).elim,
      fun p hp => ?_, fun p => ?_⟩, ⟨contDiffOn_const, fun _ => ⟨le_rfl, zero_le_one⟩,
      fun p ⟨j, hj, _⟩ => (hnot 1 j hj).elim, fun p hp => ?_, fun p t _ => ⟨?_, ?_⟩⟩,
      ⟨contDiff_const, fun _ => ⟨le_rfl, zero_le_one⟩, fun p ⟨j, hj, _⟩ => (hnot 2 j hj).elim,
      fun p hp => ?_, fun p t _ => ?_⟩⟩
    · exact absurd (hts ▸ hp : _ ∈ (∅ : Set _)) (notMem_empty _)
    · simp [BoundarySupply.emptySlots_BIF]
    · exact absurd (hts ▸ hp : _ ∈ (∅ : Set _)) (notMem_empty _)
    · rw [S.scaleMarker_boundaryOriginalMap_BIF p]
      exact S.rho_pos p
    · simp [BoundarySupply.emptySlots_BIF]
    · exact absurd (hts ▸ hp : _ ∈ (∅ : Set _)) (notMem_empty _)
    · simp [BoundarySupply.emptySlots_BIF]

end BoundaryAugmentedData

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ}
  {bcut bder κ : ℝ} (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)
  (hz0 : letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.family.zero.centres = ∅)

/-- Over the empty slot every chain is the original map: `E = F_∂`. -/
theorem E_eq_of_emptySlots_BIF : C.E = S.boundaryOriginalMap := by
  rw [C.E_eq]
  simp [BoundaryGaf02Chain.Ψ, BoundarySupply.emptySlots_adjust_BIF]

/-- Over the empty slot `T = u_{E'}(F_∂)/ρ` is continuous when `F_∂` is. -/
theorem continuous_heightRatio_of_emptySlots_BIF (hF : Continuous S.boundaryOriginalMap) :
    Continuous C.heightRatio := by
  have hE := C.E_eq_of_emptySlots_BIF
  have h : C.heightRatio = fun p => S.heightCoord_BIF (S.boundaryOriginalMap p) /
      S.scaleMarker_BIF (S.boundaryOriginalMap p) := by
    funext p
    simp only [BoundaryGaf02Chain.heightRatio, BoundaryGaf02Chain.height,
      BoundaryGaf02Chain.scale, hE]
  rw [h]
  exact (S.continuous_heightCoord_BIF.comp hF).div (S.scaleMarker_BIF.continuous.comp hF)
    fun p => by
      rw [S.scaleMarker_boundaryOriginalMap_BIF p]
      exact (S.rho_pos p).ne'

/-- **Empty bases** (no stage has a source or a base point) on a chain over the empty slot of a
supply with empty stage centres. -/
def emptyBases_BIF (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap) :
    BoundaryGaf02Bases C where
  source := fun _ => ∅
  isOpen_source := fun _ _ => isOpen_empty
  base := fun _ => ∅
  image_eq := fun _ => image_empty _
  circle_source_eq := by simp
  edge_source_eq := by simp
  slim_source_eq := by simp
  circle_original_subset := fun _ j hj => by
    rw [hc 0] at hj
    exact (notMem_empty j hj).elim
  edge_original_subset := fun _ j hj => by
    rw [hc 1] at hj
    exact (notMem_empty j hj).elim
  slim_original_subset := fun _ j hj => by
    rw [hc 2] at hj
    exact (notMem_empty j hj).elim
  edge_entry := fun _ j hj => by
    rw [hc 1] at hj
    exact (notMem_empty j hj).elim
  heightRatio_continuous := C.continuous_heightRatio_of_emptySlots_BIF hF
  circle_localization := fun p hp => (notMem_empty p hp).elim
  edge_localization := fun p hp => (notMem_empty p hp).elim
  slim_localization := fun p hp => (notMem_empty p hp).elim
  proper := fun _ _ _ _ => by simp
  rank_eq := fun _ p hp => (notMem_empty p hp).elim
  base_subset_zeroSet := fun _ _ _ => empty_subset _
  inactive_empty := fun _ _ _ _ => ⟨rfl, rfl⟩

/-- The whole-fibre layer of the empty bases (vacuous: no base point). -/
theorem emptyWholeFiberSpec_BIF : BoundaryWholeFiberSpec C (C.emptyBases_BIF hc hF) where
  circle_fibre := fun y hy => (notMem_empty y hy).elim
  slim_fibre := fun y hy => (notMem_empty y hy).elim
  edge_fibre := fun y hy => (notMem_empty y hy).elim
  source_buffered := fun _ => empty_subset _

/-- No zero cores. -/
def emptyInitialCores_BIF (hz0 : letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.family.zero.centres = ∅) : BoundaryInitialCoresSpec C where
  count := 0
  core := fun k => k.elim0
  centre := fun k => k.elim0
  centre_mem := fun k => k.elim0
  core_subset_ball := fun k => k.elim0
  zero_cover := fun z hz => by
    rw [hz0] at hz
    exact (notMem_empty z hz).elim
  isCompact_core := fun k => k.elim0
  pairwise_disjoint := fun k => k.elim0
  face_type := fun k => k.elim0

/-- `K₃ = ∅` (no arc) on the empty bases; (K) holds since there are no slabs and no slim source. -/
def emptySlimChoice_BIF :
    BoundaryCompactSlimChoice (C.emptyBases_BIF hc hF) (C.emptyInitialCores_BIF hz0) where
  arcCount := 0
  arc := fun k => k.elim0
  arc_isEmbedding := fun k => k.elim0
  arc_disjoint := fun k => k.elim0
  arc_subset_base := fun k => k.elim0
  slabs_subset := by
    rw [S.slimSlabs_eq_empty_BIF (hc 2)]
    simp
  faces_subset := by
    change C.stageMap 2 '' (frontier _ ∩ ∅) ⊆ _
    simp

/-- The relative edge restriction with no face function on the empty bases. -/
def emptyEdgeRestriction_BIF :
    BoundaryRelativeEdgeRestriction (C.emptyBases_BIF hc hF) (C.emptyInitialCores_BIF hz0)
      (C.emptySlimChoice_BIF hc hF hz0) where
  faceCount := 0
  faceFun := fun k => k.elim0
  saturated := by
    change _ ∩ (∅ : Set W.Carrier) = (∅ : Set W.Carrier) ∩ _
    simp
  base_eq := by
    change C.stageMap 1 '' (_ ∩ (∅ : Set W.Carrier)) = {y | y ∈ (∅ : Set _) ∧ _}
    simp
  face_continuousOn := fun k => k.elim0
  face_smooth := fun k => k.elim0
  regular := fun k => k.elim0
  transverse := fun k => k.elim0

/-- **The empty decomposition** of a chain over the empty slot (empty stage centres). -/
def emptyDecomposition_BIF : BoundaryActualDecomposition C where
  bases := C.emptyBases_BIF hc hF
  fibres := C.emptyWholeFiberSpec_BIF hc hF
  zero := C.emptyInitialCores_BIF hz0
  slim := C.emptySlimChoice_BIF hc hF hz0
  edge := C.emptyEdgeRestriction_BIF hc hF hz0

end BoundaryGaf02Chain

/-- **Consumer**: for a supply whose three stage-centre sets and whose zero-centre set are empty,
with BAUG-A's smoothness inequalities, the boundary route has a geometric output — T3B's labelled
whole product, or the separated branch with the augmented data, the empty-family chain and its
decomposition. -/
theorem nonempty_boundaryGeometricOutput_BIF (hc : ∀ st, S.stageCentres_BIF st = ∅)
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (Kj : ℕ) :
    Nonempty (BoundaryGeometricOutput S S.emptySlots_BIF Kj emptyChainXi_BIF emptyChainSg_BIF
      (fun _ => 0) emptyChainSg_BIF (fun _ => 0) 0 0 1) := by
  have hF : Continuous S.boundaryOriginalMap :=
    (S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he).continuous
  rcases S.geometric_cases_BIF with h | h
  · exact ⟨.product h⟩
  · exact ⟨.separated (S.emptyAugmentedData_BIF h)
      ((S.emptyAugmentedData_BIF h).emptyChain_BIF hc Kj)
      (((S.emptyAugmentedData_BIF h).emptyChain_BIF hc Kj).emptyDecomposition_BIF hc hF hz0)⟩

end DifferentialGeometry.Geometry.Collapse
