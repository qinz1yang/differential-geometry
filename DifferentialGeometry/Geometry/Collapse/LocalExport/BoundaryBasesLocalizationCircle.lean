import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesLocalization

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a (part 2): marker route, circle stage

Chain level (any marker chart `m`): `final_err_le_BBP`, `final_marker_pos_BBP`; circle instances
`circle_final_loc_BBP` (whole-preimage localization) and `circle_orig_piece_BBP` (original points
lie in the piece). See `LE/BoundaryBasesLocalization.lean`.
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

/-- The circle chart coordinate of the clean value: `κ_j(F_∂ q) = ζ_j(q) • η_j(q)`. -/
theorem circleKappa_boundaryOriginalMap_BBP (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.circleKappa_BBP j (S.boundaryOriginalMap q.val) =
      S.circleCutoffW_BAUGD j q.val • S.circleEta_BIF j.1 q := by
  have hr := S.rho_pos j.1
  change (S.rho j.1)⁻¹ • S.circleVector_BAUGD j (S.boundaryOriginalMap q.val) = _
  rw [(S.circleBlock_boundaryOriginalMap_BAUGD j q.val).1, smul_smul, ← mul_assoc,
    inv_mul_cancel₀ hr.ne', one_mul, S.circleEta_eq_circleCoordW_BAUGD]

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- `c₃ ≤ 1/512`. -/
theorem c_two_le_BBP : c 2 ≤ 1 / 512 :=
  C.toChain.numbers.2.2.2.2.2.2.2.2.2.2.2.2.1

include C in
/-- **The final value is `ρ_m/400`-close to the clean value on a marker support**:
`ζ_m(p) > 0 ⟹ ‖E p − F_∂ p‖ ≤ ρ_m/400` (`‖E − F_∂‖ < c₃ρ`, `ρ ≤ 5ρ_m/4`, `c₃ ≤ 1/512`). -/
theorem final_err_le_BBP (m : S.MarkerIdx_BAUGC) {p : W.Carrier}
    (hζ : 0 < S.markerCutoffW_BAUGD m p) :
    ‖C.toChain.E p - S.boundaryOriginalMap p‖ ≤ S.rho (S.markerCentre_BAUGC m) / 400 := by
  obtain ⟨hΛ, -, -, -, -, hV, hβ1, hb, -, hΔ1, hLΛ, -⟩ := C.std
  have hcomp := S.marker_scale_comparable_BAUGD hΛ hΔ1 hLΛ hV hβ1 hb m p hζ
  have h : ‖C.toChain.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p :=
    C.stage_error_lt_BAUGD 2 p
  have hc0 : 0 < c 2 := by
    have h' : 0 < c 2 * S.rho p := lt_of_le_of_lt (norm_nonneg _) h
    exact (mul_pos_iff_of_pos_right (S.rho_pos p)).mp h'
  have hρm := S.rho_pos (S.markerCentre_BAUGC m).val
  have h1 : c 2 * S.rho p ≤ c 2 * (5 / 4 * S.rho (S.markerCentre_BAUGC m)) :=
    mul_le_mul_of_nonneg_left hcomp.2 hc0.le
  have h2 : c 2 * (5 / 4 * S.rho (S.markerCentre_BAUGC m)) ≤
      1 / 512 * (5 / 4 * S.rho (S.markerCentre_BAUGC m)) :=
    mul_le_mul_of_nonneg_right C.c_two_le_BBP (by positivity)
  linarith

include C in
/-- **A large final marker forces a positive marker cutoff** (retained marker `(AM0)`):
`v_m(E p) > .9ρ_m ⟹ ζ_m(p) > 0`. -/
theorem final_marker_pos_BBP (m : S.MarkerIdx_BAUGC) {p : W.Carrier}
    (h : 9 / 10 * S.rho (S.markerCentre_BAUGC m) < S.markerCLM_BAUGC m (C.toChain.E p)) :
    0 < S.markerCutoffW_BAUGD m p := by
  obtain ⟨hΛ, hΔ, -, -, -, hV, hβ1, hb, -, hΔ1, hLΛ, -⟩ := C.std
  by_contra hn
  have h0 : S.markerCutoffW_BAUGD m p = 0 :=
    le_antisymm (not_lt.mp hn) (S.markerCutoffW_nonneg_BAUGD hΔ m p)
  have ham := (C.toChain.markers_V2_BAUGD hΛ hΔ1 hLΛ hV hβ1 hb).2.1 3 m p h0
  have hρ := S.rho_pos (S.markerCentre_BAUGC m).val
  have hv : S.markerCLM_BAUGC m (C.toChain.E p) ≤ S.rho (S.markerCentre_BAUGC m) / 32 :=
    (le_abs_self _).trans ham
  linarith

include C in
/-- **Circle: whole-preimage localization** of the final map: `f₀(p)` in the ratio piece of chart
`j` puts `p` in the chart domain `B(j, 200ρ_j)` with `‖η_j‖ < 4.01`. -/
theorem circle_final_loc_BBP (j : S.CircleIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 0 p ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1) ∧
      ‖S.circleEta_BIF j.1 q‖ < 401 / 100 := by
  have hE : C.toChain.stageMap 0 p = C.toChain.E p :=
    stageProj_zero_BBP S (C.toChain.E p)
  rw [hE] at hp
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inl j) p := C.final_marker_pos_BBP (Sum.inl j) hp.1
  have herr := C.final_err_le_BBP (Sum.inl j) hζ
  obtain ⟨q, rfl⟩ := S.interior_of_markerCutoffW_pos_BAUGD (Sum.inl j) hζ
  have hζ' : 0 < S.circleCutoffW_BAUGD j q.val := hζ
  have hR := S.rho_pos j.1
  have hkF := S.circleKappa_boundaryOriginalMap_BBP j q
  have hzk : ‖S.circleKappa_BBP j (S.boundaryOriginalMap q.val)‖ =
      S.circleCutoffW_BAUGD j q.val * ‖S.circleEta_BIF j.1 q‖ := by
    rw [hkF, norm_smul, Real.norm_eq_abs, abs_of_pos hζ']
  have hzv : S.circleMarker_BAUGD j (S.boundaryOriginalMap q.val) =
      S.rho j.1 * S.circleCutoffW_BAUGD j q.val :=
    (S.circleBlock_boundaryOriginalMap_BAUGD j q.val).2
  have hv1 : ‖(S.circleMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  obtain ⟨-, ha⟩ := loc_of_piece_BBP hR le_rfl (S.norm_circleKappa_le_BBP j) hv1 herr hzv hzk hp
  refine ⟨q, rfl, ?_, by linarith⟩
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hpos : 0 < S.family.circle.cutoff j.1 q := by
    rw [← S.circleCutoffW_val_BAUGD]; exact hζ'
  exact mem_ball.mp (S.family.circle.tsupport_subset_ball j.1 hj
    (subset_tsupport _ hpos.ne'))

include C in
/-- **Circle: original points lie in the piece**: `q` in the chart domain with `‖η_j‖ ≤ 3.5` has
`f₀(q)` in the ratio piece of chart `j`. -/
theorem circle_orig_piece_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ ≤ 7 / 2) :
    C.toChain.stageMap 0 q.val ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1 := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hone : S.circleCutoffW_BAUGD j q.val = 1 :=
    S.markerCutoffW_eq_one_of_core7_BAUGD hΔ (Sum.inl j) ⟨hq, hη.trans (by norm_num)⟩
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inl j) q.val := by
    change 0 < S.circleCutoffW_BAUGD j q.val
    rw [hone]; exact one_pos
  have herr := C.final_err_le_BBP (Sum.inl j) hζ
  have hR := S.rho_pos j.1
  have hzk : ‖S.circleKappa_BBP j (S.boundaryOriginalMap q.val)‖ =
      1 * ‖S.circleEta_BIF j.1 q‖ := by
    rw [S.circleKappa_boundaryOriginalMap_BBP j q, hone, one_smul, one_mul]
  have hzv : S.circleMarker_BAUGD j (S.boundaryOriginalMap q.val) = S.rho j.1 * 1 := by
    rw [(S.circleBlock_boundaryOriginalMap_BAUGD j q.val).2, hone]
  have hv1 : ‖(S.circleMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  have hE : C.toChain.stageMap 0 q.val = C.toChain.E q.val :=
    stageProj_zero_BBP S (C.toChain.E q.val)
  rw [hE]
  exact piece_of_orig_BBP hR le_rfl (S.norm_circleKappa_le_BBP j) hv1 herr hzv hzk
    (by linarith)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
