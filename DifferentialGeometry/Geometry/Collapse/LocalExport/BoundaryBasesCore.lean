import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCoreData

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a (part 7): the BASES core `exists_basesCore_BBP`

`BoundaryGaf02ChainE.basesCore_BBP` (the producer, a def: sources `baseSource_BBP`, bases
`baseSet_BBP`) and `exists_basesCore_noEmb_BBP`: a `BoundaryGaf02BasesCore_BIFc C.toChain` with the
plateau clause `ψ_st = 1` on the sources and `B_st = Θ_st(f_st⁰(X_st))`. The only clause of the
frozen G11 target that is NOT here is the embedding of `Θ_st` on `f_st⁰(X_st)`, which needs CGP07's
one-sheet property of the native zero set (no boundary port yet).

Register premises (not in `C.std`, as for the stage submersions of G1/G2): `β₂ ≤ 10⁻⁷`,
`γ ≤ 1/2` (circle), `σ_c ≤ 1/4`, `b ≤ 1/(1000Δ)` (edge).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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
/-- **`rank Df_st = k_st` on every source point** (localization and G2). -/
theorem rank_eq_src_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hσ : σc ≤ 1 / 4)
    (hb : b ≤ 1 / (1000 * Δ)) (st : Fin 3) {p : W.Carrier} (hp : p ∈ C.baseSource_BBP st) :
    C.toChain.stageRank_BIFc st p = gafStageDim st := by
  obtain ⟨-, hΔ, -⟩ := C.std
  fin_cases st
  · obtain ⟨j, q, rfl, hd, hη⟩ := C.circle_source_loc_BBP hp
    exact C.stage_rank_eq_circle_BBP hβ2 hγ j hd (by linarith)
  · obtain ⟨j, q, rfl, hd, hη, ht⟩ := C.edge_source_loc_BBP hp
    exact C.stage_rank_eq_edge_BBP hσ hb j hd (by linarith) (by linarith)
  · obtain ⟨j, q, rfl, hd, hη⟩ := C.slim_source_loc_BBP hp
    exact C.stage_rank_eq_slim_BBP j hd (by linarith)

include C in
/-- **The BASES core** of the boundary chain (G11, without the later-embedding clause): sources
`X_st = f_st⁻¹(O_st)` (`∩ {T ≤ 4Δ}` for the edge), bases `B_st = f_st(X_st)`; every field of v1's
core is discharged by the open ratio sets, the marker route of localization and G1/G2. -/
def basesCore_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hσ : σc ≤ 1 / 4)
    (hb : b ≤ 1 / (1000 * Δ)) : BoundaryGaf02BasesCore_BIFc C.toChain where
  source := C.baseSource_BBP
  isOpen_source := fun st hst => by
    fin_cases st
    · change IsOpen (C.baseSource_BBP 0)
      rw [C.baseSource_zero_eq_BBP]
      exact (S.isOpen_ratioSet_BBP 0).preimage (C.continuous_stageMap_V2_BAUGD 0)
    · exact absurd rfl hst
    · change IsOpen (C.baseSource_BBP 2)
      rw [C.baseSource_two_eq_BBP]
      exact (S.isOpen_ratioSet_BBP 2).preimage (C.continuous_stageMap_V2_BAUGD 2)
  base := C.baseSet_BBP
  image_eq := fun _ => rfl
  circle_source_eq := C.baseSource_eq_preimage_BBP (by decide)
  edge_source_eq := C.baseSource_one_eq_preimage_BBP
  slim_source_eq := C.baseSource_eq_preimage_BBP (by decide)
  circle_original_subset := by
    intro q j hj hd hη
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    have hj' : j ∈ S.family.circle.centres := hj
    let jj : S.CircleIdx_BAUGD := ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩
    exact ⟨Set.mem_iUnion.mpr ⟨jj, C.circle_orig_piece_BBP jj hd hη⟩, fun h => absurd h (by decide)⟩
  edge_original_subset := by
    intro q j hj hd hη hh
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    obtain ⟨-, hΔ, -⟩ := C.std
    have hj' : j ∈ S.family.edgeB.centres := hj
    let jj : S.EdgeIdx_BAUGD := ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩
    have hpc := C.edge_orig_piece_BBP jj hd hη (by linarith)
    have hT := C.edge_orig_height_BBP hh
    refine mem_interior.mpr ⟨{p | C.toChain.stageMap 1 p ∈ S.ratioSet_BBP 1} ∩
      {p | C.toChain.heightRatio p < 4 * Δ}, ?_, ?_, ⟨Set.mem_iUnion.mpr ⟨jj, hpc⟩, hT⟩⟩
    · exact fun p hp => ⟨hp.1, fun _ => hp.2.le⟩
    · exact ((S.isOpen_ratioSet_BBP 1).preimage (C.continuous_stageMap_V2_BAUGD 1)).inter
        (isOpen_lt C.continuous_heightRatio_BAUGD continuous_const)
  slim_original_subset := by
    intro q j hj hd hη
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    have hj' : j ∈ S.family.slim.centres := hj
    let jj : S.SlimIdx_BAUGD := ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩
    have hη' : |S.slimEta_BIF j q| ≤ 7 / 2 * (10 ^ 5 * Δ) := by linarith
    exact ⟨Set.mem_iUnion.mpr ⟨jj, C.slim_orig_piece_BBP jj hd hη'⟩, fun h => absurd h (by decide)⟩
  edge_entry := by
    intro q j hj hd hη hh hT
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    obtain ⟨-, hΔ, -⟩ := C.std
    have hj' : j ∈ S.family.edgeB.centres := hj
    let jj : S.EdgeIdx_BAUGD := ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩
    exact ⟨Set.mem_iUnion.mpr ⟨jj, C.edge_orig_piece_BBP jj hd hη (by linarith)⟩, fun _ => hT⟩
  heightRatio_continuous := C.continuous_heightRatio_BAUGD
  circle_localization := by
    intro p hp
    obtain ⟨j, q, hq, hd, hη⟩ := C.circle_source_loc_BBP hp
    exact ⟨q, hq, j.1, (Set.Finite.mem_toFinset _).mp j.2, hd, hη⟩
  edge_localization := by
    intro p hp
    obtain ⟨j, q, hq, hd, hη, ht⟩ := C.edge_source_loc_BBP hp
    exact ⟨q, hq, j.1, (Set.Finite.mem_toFinset _).mp j.2, hd, hη, ht⟩
  slim_localization := by
    intro p hp
    obtain ⟨j, q, hq, hd, hη⟩ := C.slim_source_loc_BBP hp
    exact ⟨q, hq, j.1, (Set.Finite.mem_toFinset _).mp j.2, hd, hη⟩
  proper := C.proper_of_source_eq_V2_BAUGD C.baseSource_BBP C.baseSet_BBP
    (C.baseSource_eq_preimage_BBP (by decide)) C.baseSource_one_eq_preimage_BBP
    (C.baseSource_eq_preimage_BBP (by decide))
  rank_eq := fun st p hp => C.rank_eq_src_BBP hβ2 hγ hσ hb st hp
  inactive_empty := by
    intro st hc he hslot
    obtain ⟨-, hΔ, -⟩ := C.std
    have hempty : C.baseSource_BBP st = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      fin_cases st
      · obtain ⟨j, q, rfl, hd, hη⟩ := C.circle_source_loc_BBP hp
        have hmem : q ∈ (actualSlotsV2_BAUGD S).stageCore 0 :=
          Set.mem_iUnion₂.mpr ⟨Sum.inl j, rfl, hd, by linarith⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hc) q hmem
      · obtain ⟨j, q, rfl, hd, hη, ht⟩ := C.edge_source_loc_BBP hp
        have hmem : q ∈ (actualSlotsV2_BAUGD S).stageCore 1 :=
          Set.mem_iUnion₂.mpr ⟨Sum.inr (Sum.inr j), rfl, hd, by linarith, by linarith⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hc) q hmem
      · obtain ⟨j, q, rfl, hd, hη⟩ := C.slim_source_loc_BBP hp
        have hmem : q ∈ (actualSlotsV2_BAUGD S).stageCore 2 :=
          Set.mem_iUnion₂.mpr ⟨Sum.inr (Sum.inl j), rfl, hd, by linarith⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hc) q hmem
    refine ⟨hempty, ?_⟩
    change C.toChain.stageMap st '' C.baseSource_BBP st = ∅
    rw [hempty, Set.image_empty]

include C in
/-- **G11 target without the later-embedding clause**: a BASES core of the boundary chain with
the plateau clause and `B_st = Θ_st(f_st⁰(X_st))`. -/
theorem exists_basesCore_noEmb_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ)) :
    ∃ Bc : BoundaryGaf02BasesCore_BIFc C.toChain,
      (∀ st, ∀ p ∈ Bc.source st,
        (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc p) = 1) ∧
      (∀ st, Bc.base st = C.toChain.laterV2_BAUGD st ''
        (C.toChain.nativeStageMap_BIFc st '' Bc.source st)) :=
  ⟨C.basesCore_BBP hβ2 hγ hσ hb, fun st _ hp => C.baseSource_plateau_BBP st hp,
    fun st => C.baseSet_eq_later_native_BBP st⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
