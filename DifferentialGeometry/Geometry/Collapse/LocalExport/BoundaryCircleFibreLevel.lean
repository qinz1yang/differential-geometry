import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleLevelChain
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageLocalSheet
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalSheetTopology

/-!
# O-WF G2c: the whole circle fibre is the adjusted level; no merging at the circle stage

On `C : BoundaryGaf02ChainE DP …` with the BASES core sources `X₀ = C.baseSource_BBP 0` and bases
`B₀ = C.baseSet_BBP 0` (lane S-BASES-PORT2):

* `exists_active_of_source_OWF`: a source point forces an ACTIVE stage slot;
* `norm_kappa_lt_four_of_piece_OWF` (arithmetic): a final value in a ratio piece at distance
  `≤ R/400` from a clean value of marker `Rζ`, `ζ ≤ 1`, has `‖κ y‖ < 4ℓ`;
* `circle_native_const_OWF`: the native map `f₀⁰` is CONSTANT on every whole adjusted level
  `L_a = {q ∈ Y_j | κ_j(f₀ q) = a}`, `‖a‖ < 4` (connectedness `circle_level_connected_OWF` +
  the local one-sheet `circle_localInverse_OWF` + `eqOn_of_isPreconnected_of_locInjOn_OWF`);
* **`circle_fibre_eq_level_OWF`**: for `y ∈ B₀` in the ratio piece of chart `j`, the WHOLE fibre
  `{q ∈ W° | q ∈ X₀, f₀ q = y}` EQUALS `L_{κ_j y}`, and it is connected
  (`isConnected_circle_fibre_OWF`) — closed twin `gaf07_circle_whole_fibre_GAFC`, here without
  the global CGP07 chart;
* **`circle_later_isEmbedding_OWF`**: `Θ₀` is a topological embedding of the native base
  `f₀⁰(X₀)` (the `hemb` clause of G11 at `st = 0`; `isEmbedding_of_proper_factor_OWF`).

Register premises: `c₂ < 1/1000`, `β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`, `γ + β₂ < 1/10`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
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

/-- **A ratio-piece value has `‖κ y‖ < 4ℓ`**: `y` in the ratio piece, within `R/400` of a clean
value `z` with marker `v z = Rζ`, `ζ ≤ 1` (`‖v‖ ≤ 1`). -/
theorem norm_kappa_lt_four_of_piece_OWF {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : H →L[ℝ] F} {v : H →L[ℝ] ℝ} {R ℓ ζ : ℝ}
    (hR : 0 < R) (hℓ : 0 ≤ ℓ) (hv1 : ‖v‖ ≤ 1) {y z : H} (hyz : ‖y - z‖ ≤ R / 400)
    (hzv : v z = R * ζ) (hζ : ζ ≤ 1) (hy : y ∈ ratioPiece_BBP κ v R ℓ) : ‖κ y‖ < 4 * ℓ := by
  have hv : v y ≤ R * ζ + R / 400 := by
    have h1 : v y - v z ≤ ‖y - z‖ := by
      rw [← map_sub]
      exact (le_abs_self _).trans ((v.le_opNorm _).trans (by nlinarith [norm_nonneg (y - z)]))
    linarith
  have hRζ : R * ζ ≤ R := by nlinarith
  have h2 : R * ‖κ y‖ < 39 / 10 * ℓ * (R + R / 400) := by
    have h3 : 39 / 10 * ℓ * v y ≤ 39 / 10 * ℓ * (R + R / 400) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [hy.2]
  by_contra hn
  have hn' : 4 * ℓ ≤ ‖κ y‖ := not_lt.mp hn
  have : R * (4 * ℓ) ≤ R * ‖κ y‖ := mul_le_mul_of_nonneg_left hn' hR.le
  nlinarith

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

/-- The native stage maps are continuous on `W`. -/
theorem continuous_native_OWF (st : Fin 3) : Continuous (C.toChain.nativeStageMap_BIFc st) :=
  ((actualSlotsV2_BAUGD S).stageProj st).continuous.comp (C.stage_smooth_BAUGD st.succ).continuous

/-- **A source point forces an active slot** (an inactive slot has an empty stage core). -/
theorem exists_active_of_source_OWF (st : Fin 3) {p : W.Carrier}
    (hp : p ∈ C.baseSource_BBP st) :
    ∃ O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      ((actualSlotsV2_BAUGD S).stageCloud st) ((actualSlotsV2_BAUGD S).stageCloudEnlarged st)
      (DP.stageRadius st (Sg st)) (DP.stagePlane st), C.toChain.slot st = .active O := by
  obtain ⟨-, hΔ, -⟩ := C.std
  rcases hsl : C.toChain.slot st with O | ⟨hc, he⟩
  · exact ⟨O, rfl⟩
  · exfalso
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

include C in
/-- A point whose final circle value lies in the ratio piece of chart `j` is (the value of) a point
of `Y_j`. -/
theorem circle_mem_Y_of_piece_OWF (j : S.CircleIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 0 p ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ S.circleY_OWF j := by
  obtain ⟨q, hq, hd, hη⟩ := C.circle_final_loc_BBP j hp
  exact ⟨q, hq, hd, by linarith⟩

include C in
/-- A final circle value in the ratio piece of chart `j` has `‖κ_j y‖ < 4`. -/
theorem circle_norm_kappa_lt_OWF (j : S.CircleIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 0 p ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1) :
    ‖S.circleKappa_BBP j (C.toChain.stageMap 0 p)‖ < 4 := by
  have hE : C.toChain.stageMap 0 p = C.toChain.E p := stageProj_zero_BBP S (C.toChain.E p)
  have hp' := hp
  rw [hE] at hp'
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inl j) p := C.final_marker_pos_BBP (Sum.inl j) hp'.1
  have herr := C.final_err_le_BBP (Sum.inl j) hζ
  have hv1 : ‖(S.circleMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  have h := norm_kappa_lt_four_of_piece_OWF (S.rho_pos j.1) zero_le_one hv1 herr
    (S.circleBlock_boundaryOriginalMap_BAUGD j p).2 (S.circleCutoffW_mem_Icc_BAUGD j p).2 hp'
  rw [hE]
  linarith

/-- **The native map is constant on a whole adjusted circle level** (see the module docstring). -/
theorem circle_native_const_OWF (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000)
    (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10)
    (O : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0)
      ((actualSlotsV2_BAUGD S).stageCloud 0) ((actualSlotsV2_BAUGD S).stageCloudEnlarged 0)
      (DP.stageRadius 0 (Sg 0)) (DP.stagePlane 0))
    (hO : C.toChain.slot 0 = .active O) (j : S.CircleIdx_BAUGD) {a : ℝ²} (ha : ‖a‖ < 4) :
    ∀ x ∈ {q | q ∈ S.circleY_OWF j ∧ S.circleKappa_BBP j (C.toChain.stageMap 0 q.val) = a},
      ∀ x' ∈ {q | q ∈ S.circleY_OWF j ∧ S.circleKappa_BBP j (C.toChain.stageMap 0 q.val) = a},
        C.toChain.nativeStageMap_BIFc 0 x.val = C.toChain.nativeStageMap_BIFc 0 x'.val := by
  have hL := (C.circle_level_connected_OWF hc hβ hd j ha).isPreconnected
  have hh : ContinuousOn (fun q : W.pieceInterior ⊤ => C.toChain.nativeStageMap_BIFc 0 q.val)
      {q | q ∈ S.circleY_OWF j ∧ S.circleKappa_BBP j (C.toChain.stageMap 0 q.val) = a} :=
    ((C.continuous_native_OWF 0).comp continuous_subtype_val).continuousOn
  refine eqOn_of_isPreconnected_of_locInjOn_OWF hL hh (Zs := O.Z) ?_ (S.circleKappa_BBP j)
    (c := a) ?_ ?_
  · rintro q ⟨hq, -⟩
    exact C.toChain.native_scope_V2_BAUGD 0 O hO q.val
      (C.circle_plateau_cutoff_BBP j hq.1 (by linarith [hq.2]))
  · rintro q ⟨-, hqa⟩
    exact (congrFun (C.circle_kappa_final_eq_BBP j) q.val).symm.trans hqa
  · rintro q ⟨hq, -⟩
    obtain ⟨V, δ, ζ, hV, hmem, -, -, -, hl⟩ :=
      C.circle_localInverse_OWF hβ hγ O hO j hq.1 (by linarith [hq.2])
    exact ⟨V, hV, hmem, fun w hw w' hw' heq =>
      (hl w hw).2.symm.trans ((congrArg ζ heq).trans (hl w' hw').2)⟩

/-- **The whole circle fibre is the whole adjusted level** (see the module docstring). -/
theorem circle_fibre_eq_level_OWF (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000)
    (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (j : S.CircleIdx_BAUGD)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 0)
    (hyj : y ∈ ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1) :
    {x : W.pieceInterior ⊤ | x.val ∈ C.baseSource_BBP 0 ∧ C.toChain.stageMap 0 x.val = y} =
      {x | x ∈ S.circleY_OWF j ∧
        S.circleKappa_BBP j (C.toChain.stageMap 0 x.val) = S.circleKappa_BBP j y} := by
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy
  obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 0 hp₀
  have hpiece₀ : C.toChain.stageMap 0 p₀ ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1 := by
    rw [hfp₀]; exact hyj
  have ha : ‖S.circleKappa_BBP j y‖ < 4 := by
    have h := C.circle_norm_kappa_lt_OWF j hpiece₀
    rwa [hfp₀] at h
  obtain ⟨q₀, hq₀, hq₀Y⟩ := C.circle_mem_Y_of_piece_OWF j hpiece₀
  have hq₀L : q₀ ∈ {x : W.pieceInterior ⊤ | x ∈ S.circleY_OWF j ∧
      S.circleKappa_BBP j (C.toChain.stageMap 0 x.val) = S.circleKappa_BBP j y} :=
    ⟨hq₀Y, by rw [hq₀, hfp₀]⟩
  ext x
  constructor
  · rintro ⟨-, hxy⟩
    have hpiece : C.toChain.stageMap 0 x.val ∈
        ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1 := by
      rw [hxy]; exact hyj
    obtain ⟨q, hq, hqY⟩ := C.circle_mem_Y_of_piece_OWF j hpiece
    have hqx : q = x := Subtype.ext hq
    rw [← hqx]
    exact ⟨hqY, by rw [hq, hxy]⟩
  · intro hx
    have hconst := C.circle_native_const_OWF hc hβ hγ hd O hO j ha x hx q₀ hq₀L
    have hxy : C.toChain.stageMap 0 x.val = y := by
      rw [C.toChain.final_factor_V2_BAUGD 0 x.val, hconst,
        ← C.toChain.final_factor_V2_BAUGD 0 q₀.val, hq₀, hfp₀]
    refine ⟨⟨?_, fun h => absurd h (by decide)⟩, hxy⟩
    rw [hxy, ← hfp₀]
    exact hp₀.1

/-- **The whole circle fibre is connected**. -/
theorem isConnected_circle_fibre_OWF (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000)
    (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (j : S.CircleIdx_BAUGD)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 0)
    (hyj : y ∈ ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1) :
    IsConnected {x : W.pieceInterior ⊤ | x.val ∈ C.baseSource_BBP 0 ∧
      C.toChain.stageMap 0 x.val = y} := by
  rw [C.circle_fibre_eq_level_OWF hc hβ hγ hd j hy hyj]
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy
  have hpiece₀ : C.toChain.stageMap 0 p₀ ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1 := by
    rw [hfp₀]; exact hyj
  have ha := C.circle_norm_kappa_lt_OWF j hpiece₀
  rw [hfp₀] at ha
  exact C.circle_level_connected_OWF hc hβ hd j ha

/-- **No merging at the circle stage**: `Θ₀` is a topological embedding of `f₀⁰(X₀)`. -/
theorem circle_later_isEmbedding_OWF (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000)
    (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) :
    Topology.IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc 0 '' C.baseSource_BBP 0 =>
      C.toChain.laterV2_BAUGD 0 x) := by
  have hfun : (fun p => C.toChain.laterV2_BAUGD 0 (C.toChain.nativeStageMap_BIFc 0 p)) =
      C.toChain.stageMap 0 := funext fun p => (C.toChain.final_factor_V2_BAUGD 0 p).symm
  refine isEmbedding_of_proper_factor_OWF (C.continuous_native_OWF 0).continuousOn ?_ ?_ ?_
  · rintro _ ⟨p, -, rfl⟩
    exact (C.toChain.later_contDiffAt_V2_BAUGD 0 p).continuousAt.continuousWithinAt
  · intro Kc hK hcK
    rw [hfun]
    have hK' : Kc ⊆ C.baseSet_BBP 0 := by rw [C.baseSet_eq_later_native_BBP 0]; exact hK
    exact C.proper_of_source_eq_V2_BAUGD C.baseSource_BBP C.baseSet_BBP
      (C.baseSource_eq_preimage_BBP (by decide)) C.baseSource_one_eq_preimage_BBP
      (C.baseSource_eq_preimage_BBP (by decide)) 0 Kc hK' hcK
  · intro p hp p' hp' heq
    have hff : C.toChain.stageMap 0 p = C.toChain.stageMap 0 p' := by
      rw [C.toChain.final_factor_V2_BAUGD 0 p, C.toChain.final_factor_V2_BAUGD 0 p']
      exact heq
    obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 0 hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
    have hj' : C.toChain.stageMap 0 p' ∈
        ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1 := by
      rw [← hff]; exact hj
    have ha := C.circle_norm_kappa_lt_OWF j hj
    obtain ⟨q, hq, hqY⟩ := C.circle_mem_Y_of_piece_OWF j hj
    obtain ⟨q', hq', hq'Y⟩ := C.circle_mem_Y_of_piece_OWF j hj'
    have h := C.circle_native_const_OWF hc hβ hγ hd O hO j ha q ⟨hqY, by rw [hq]⟩ q'
      ⟨hq'Y, by rw [hq', ← hff]⟩
    rw [hq, hq'] at h
    exact h

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
