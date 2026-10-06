import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesLocalizationEdgeB

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a (part 6): the sources and bases of the BASES core

* the open ratio sets `O_st = ⋃_i piece_i` of `H^∂` (`circleRatioSet_BBP`, `edgeRatioSet_BBP`,
  `slimRatioSet_BBP`, `ratioSet_BBP`, `isOpen_ratioSet_BBP`);
* the sources `X_st = {p | f_st(p) ∈ O_st ∧ (st = 1 → T(p) ≤ 4Δ)}`
  (`BoundaryGaf02ChainE.baseSource_BBP`) and the bases `B_st = f_st(X_st)` (`baseSet_BBP`);
* the whole-preimage localization of a source point in the chart of its piece:
  `circle_source_loc_BBP`, `edge_source_loc_BBP`, `slim_source_loc_BBP`;
* the plateau and the original-subset facts used by the core fields.
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

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The open ratio set of the circle stage: `⋃_j {v_j > .9R_j, R_j‖κ_j‖ < 3.9 v_j}`. -/
def circleRatioSet_BBP : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ⋃ j : S.CircleIdx_BAUGD,
    ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1

/-- The open ratio set of the edge stage: `⋃_j {v_j > .9R_j, R_j|κ_j| < 3.9Δ v_j}`. -/
def edgeRatioSet_BBP : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ⋃ j : S.EdgeIdx_BAUGD,
    ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ

/-- The open ratio set of the slim stage: `⋃_j {v_j > .9R_j, R_j|κ_j| < 3.9·10⁵Δ v_j}`. -/
def slimRatioSet_BBP : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ⋃ j : S.SlimIdx_BAUGD,
    ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ)

/-- The open ratio sets `O_0, O_1, O_2`. -/
def ratioSet_BBP : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  ![S.circleRatioSet_BBP, S.edgeRatioSet_BBP, S.slimRatioSet_BBP]

theorem isOpen_ratioSet_BBP (st : Fin 3) : IsOpen (S.ratioSet_BBP st) := by
  fin_cases st
  · exact isOpen_iUnion fun j => isOpen_ratioPiece_BBP _ _ _ _
  · exact isOpen_iUnion fun j => isOpen_ratioPiece_BBP _ _ _ _
  · exact isOpen_iUnion fun j => isOpen_ratioPiece_BBP _ _ _ _

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The sources** `X_st = {p | f_st(p) ∈ O_st ∧ (st = 1 → T(p) ≤ 4Δ)}` of the BASES core. -/
def baseSource_BBP (st : Fin 3) : Set W.Carrier :=
  {p | C.toChain.stageMap st p ∈ S.ratioSet_BBP st ∧
    (st = 1 → C.toChain.heightRatio p ≤ 4 * Δ)}

/-- **The bases** `B_st = f_st(X_st)` of the BASES core. -/
def baseSet_BBP (st : Fin 3) :
    Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :=
  C.toChain.stageMap st '' C.baseSource_BBP st

include C in
/-- Circle sources are whole preimages of `O_0`. -/
theorem baseSource_zero_eq_BBP : C.baseSource_BBP 0 = C.toChain.stageMap 0 ⁻¹' S.ratioSet_BBP 0 := by
  ext p
  simp [baseSource_BBP]

include C in
/-- Slim sources are whole preimages of `O_2`. -/
theorem baseSource_two_eq_BBP : C.baseSource_BBP 2 = C.toChain.stageMap 2 ⁻¹' S.ratioSet_BBP 2 := by
  ext p
  simp [baseSource_BBP]

include C in
/-- Edge sources: `f₁⁻¹(O_1) ∩ {T ≤ 4Δ}`. -/
theorem baseSource_one_eq_BBP : C.baseSource_BBP 1 =
    C.toChain.stageMap 1 ⁻¹' S.ratioSet_BBP 1 ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} := by
  ext p
  simp [baseSource_BBP]

include C in
/-- `X_st = f_st⁻¹(B_st)` for the circle and the slim stage. -/
theorem baseSource_eq_preimage_BBP {st : Fin 3} (hst : st ≠ 1) :
    C.baseSource_BBP st = C.toChain.stageMap st ⁻¹' C.baseSet_BBP st := by
  ext p
  constructor
  · intro hp
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p', hp', hfp⟩
    refine ⟨?_, fun h => absurd h hst⟩
    rw [← hfp]
    exact hp'.1

include C in
/-- Edge: `X_1 = f₁⁻¹(B_1) ∩ {T ≤ 4Δ}`. -/
theorem baseSource_one_eq_preimage_BBP : C.baseSource_BBP 1 =
    C.toChain.stageMap 1 ⁻¹' C.baseSet_BBP 1 ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨p, hp, rfl⟩, hp.2 rfl⟩
  · rintro ⟨⟨p', hp', hfp⟩, hT⟩
    refine ⟨?_, fun _ => hT⟩
    rw [← hfp]
    exact hp'.1

include C in
/-- Circle source points: the whole-preimage localization in the chart of the piece. -/
theorem circle_source_loc_BBP {p : W.Carrier} (hp : p ∈ C.baseSource_BBP 0) :
    ∃ (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤), q.val = p ∧
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1) ∧
      ‖S.circleEta_BIF j.1 q‖ < 401 / 100 := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
  obtain ⟨q, hq, hd, hη⟩ := C.circle_final_loc_BBP j hj
  exact ⟨j, q, hq, hd, hη⟩

include C in
/-- Slim source points: the whole-preimage localization in the chart of the piece. -/
theorem slim_source_loc_BBP {p : W.Carrier} (hp : p ∈ C.baseSource_BBP 2) :
    ∃ (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤), q.val = p ∧
      (letI := inducedMetricSpace S.completion.metric;
        dist q j.1 < 1000000 * Δ * S.rho j.1) ∧
      |S.slimEta_BIF j.1 q| < 401 / 100 * (10 ^ 5 * Δ) := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
  obtain ⟨q, hq, hd, hη⟩ := C.slim_final_loc_BBP j hj
  exact ⟨j, q, hq, hd, hη⟩

include C in
/-- Edge source points: the whole-preimage localization in the chart of the piece. -/
theorem edge_source_loc_BBP {p : W.Carrier} (hp : p ∈ C.baseSource_BBP 1) :
    ∃ (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤), q.val = p ∧
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1) ∧
      |S.edgeEta_BIF j.1 q| < 401 / 100 * Δ ∧ S.edgeHeightRaw q < 401 / 100 * Δ := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
  obtain ⟨q, hq, hd, hη, ht⟩ := C.edge_final_loc_BBP j hj (hp.2 rfl)
  exact ⟨j, q, hq, hd, hη, ht⟩

include C in
/-- **The plateau clause**: on a source `ψ_st = 1` at the chain's own input `g_st`. -/
theorem baseSource_plateau_BBP (st : Fin 3) {p : W.Carrier} (hp : p ∈ C.baseSource_BBP st) :
    (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc p) = 1 := by
  obtain ⟨-, hΔ, -⟩ := C.std
  fin_cases st
  · obtain ⟨j, q, rfl, hd, hη⟩ := C.circle_source_loc_BBP hp
    exact C.circle_plateau_cutoff_BBP j hd (by linarith)
  · obtain ⟨j, q, rfl, hd, hη, ht⟩ := C.edge_source_loc_BBP hp
    exact C.edge_plateau_cutoff_BBP j hd (by linarith) (by linarith)
  · obtain ⟨j, q, rfl, hd, hη⟩ := C.slim_source_loc_BBP hp
    exact C.slim_plateau_cutoff_BBP j hd (by linarith)

include C in
/-- **`B_st = Θ_st(f_st⁰(X_st))`**. -/
theorem baseSet_eq_later_native_BBP (st : Fin 3) :
    C.baseSet_BBP st = C.toChain.laterV2_BAUGD st ''
      (C.toChain.nativeStageMap_BIFc st '' C.baseSource_BBP st) := by
  rw [Set.image_image]
  exact Set.image_congr fun p _ => C.toChain.final_factor_V2_BAUGD st p

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
