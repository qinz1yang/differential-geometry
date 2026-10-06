import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersion
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesEdgeUnitLower

/-!
# A4 / G11 (lane S-BASES-PORT), group G1c (part 2): the edge stage submersion on the boundary chain

Edge half of C14-BASES G5 (`Gaf02Chain.stage_submersion_edge_BAS`) on
`C : BoundaryGaf02ChainE DP …`, by the chart route of `LE/BoundaryBasesStageSubmersion.lean`
(circle) and `LE/BoundaryBasesStageSubmersionSlim.lean` (slim), with the derivative lower bound of
the edge chart from `LE/BoundaryBasesEdgeUnitLower.lean`.

* supply level (`BoundarySupplyCore`): `edgeKappa_BBP` (`κ_j = ρ_j⁻¹ proj₀ u_j`),
  `norm_edgeKappa_le_BBP`, `edgeEta_eq_coord_fun_BBP`, `edge_plateau_mem_nhds_BBP` (the original
  threshold-`6` plateau `dist < 100Δρ_j ∧ |η_j| < 6Δ ∧ t_B < 6Δ` is a neighbourhood),
  `edge_cutoff_eq_one_BBP` (`ζ_j = 1`, from CGP01's edge identity),
  `edgeKappa_boundaryOriginalMap_eventuallyEq_BBP` (`κ_j ∘ F_∂ = η_j` near the plateau),
  `four_le_distanceToBoundary_of_edge_plateau_BBP` (`D ≥ 4`), `edge_unit_lower_BBP`;
* chain level (`BoundaryGaf02ChainE`): `edge_plateau_mem_core_BBP`, `edge_plateau_cutoff_BBP`
  (binding `ψ₁(g₁ q') = 1` through `g₁_apply_V2_BAUGD`), `chain_c_zero_pos_BBP`,
  `edge_stage_tube_BBP`, `edgeKappa_stageProj_BBP`, `edgeKappa_mvfderiv_eq_BBP`,
  `edge_native_mvfderiv_BBP`, `edge_budget_BBP`, `edge_deriv_close_BBP`, `edge_unit_norm_BBP`;
* **`BoundaryGaf02ChainE.stage_submersion_edge_BBP`** (register premises `σ_c ≤ 1/4`,
  `b ≤ 1/(1000Δ)`; not in `C.std`): at every point of the original edge plateau
  `D(κ_j ∘ f₁⁰)` is onto `ℝ`.
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

/-- The edge chart coordinate of `H^∂`: `κ_j = ρ_j⁻¹ proj₀ u_j` (the `edgeB` vector block). -/
def edgeKappa_BBP (j : S.EdgeIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  (S.rho j.1)⁻¹ • ((EuclideanSpace.proj (0 : Fin 2)).comp (S.edgeVector_BAUGD j))

/-- `‖κ_j‖ ≤ ρ_j⁻¹` (edge). -/
theorem norm_edgeKappa_le_BBP (j : S.EdgeIdx_BAUGD) : ‖S.edgeKappa_BBP j‖ ≤ (S.rho j.1)⁻¹ := by
  have hr := S.rho_pos j.1
  unfold edgeKappa_BBP
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have h1 : ‖(EuclideanSpace.proj (0 : Fin 2)).comp (S.edgeVector_BAUGD j)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul, ContinuousLinearMap.comp_apply]
    refine (PiLp.norm_apply_le (S.edgeVector_BAUGD j y) 0).trans ?_
    exact (S.edgeVector_BAUGD j).le_opNorm y |>.trans (by
      have h2 : ‖S.edgeVector_BAUGD j‖ ≤ 1 := norm_blockVectorCLM_le _
      nlinarith [norm_nonneg y])
  calc (S.rho j.1)⁻¹ * ‖(EuclideanSpace.proj (0 : Fin 2)).comp (S.edgeVector_BAUGD j)‖
      ≤ (S.rho j.1)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hr).le
    _ = (S.rho j.1)⁻¹ := mul_one _

/-- The edge coordinate of BIFACE is the edge family's chart coordinate on `W°`. -/
theorem edgeEta_eq_coord_fun_BBP (j : S.EdgeIdx_BAUGD) :
    S.edgeEta_BIF j.1 =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.edgeB.coord_BAUGA j.1) :=
  funext (S.edgeEta_eq_coord_BAUGP2 j)

/-- **The original threshold-`6` edge plateau is a neighbourhood** of each of its points. -/
theorem edge_plateau_mem_nhds_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    letI := inducedMetricSpace S.completion.metric
    {q' : W.pieceInterior ⊤ | dist q' j.1 < 100 * Δ * S.rho j.1 ∧
      |S.edgeEta_BIF j.1 q'| < 6 * Δ ∧ S.edgeHeightRaw q' < 6 * Δ} ∈ 𝓝 q := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hball : ball j.1 (100 * Δ * S.rho j.1) ∈ 𝓝 q := isOpen_ball.mem_nhds hq
  have hcont : ContinuousAt (S.edgeEta_BIF j.1) q := by
    rw [S.edgeEta_eq_coord_fun_BBP j]
    exact (S.family.edgeB.contMDiffOn_coord_BAUGA hj).continuousOn.continuousAt hball
  have hpre : S.edgeEta_BIF j.1 ⁻¹' {t | |t| < 6 * Δ} ∈ 𝓝 q :=
    hcont.preimage_mem_nhds ((isOpen_lt continuous_abs continuous_const).mem_nhds hη)
  have hρc : Continuous (fun q' : W.pieceInterior ⊤ => S.rho q'.val) :=
    S.scale_spec.1.continuous.comp continuous_subtype_val
  have hhc : ContinuousAt S.edgeHeightRaw q := by
    unfold edgeHeightRaw
    exact (S.family.edgeB.lipschitz_smoothing.continuous.continuousAt).div hρc.continuousAt
      (S.rho_pos q.val).ne'
  have hhpre : S.edgeHeightRaw ⁻¹' {t | t < 6 * Δ} ∈ 𝓝 q :=
    hhc.preimage_mem_nhds (isOpen_lt continuous_id continuous_const |>.mem_nhds hh)
  filter_upwards [hball, hpre, hhpre] with q' h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- The edge cutoff `ζ_j` is `1` on the threshold-`6` plateau. -/
theorem edge_cutoff_eq_one_BBP (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    S.edgeCutoffW_BAUGP2 j q.val = 1 := by
  have hdom : q.val ∈ S.edgeDomW_BAUGP2 j := ⟨q, hq, rfl⟩
  have hη' : ‖S.edgeCoordW_BAUGP2 j q.val‖ < 8 * Δ := by
    rw [S.norm_edgeCoordW_val_BAUGP2]
    linarith
  rw [S.edgeCutoffW_identity_BAUGP2 hΔ j q.val hdom hη', S.edgeHeightW_val_BAUGP2]
  have h0 : cfsRamp lc87EdgeTransition 8 9 (S.edgeHeightRaw q / Δ) = 0 := by
    refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
    rw [div_le_iff₀ hΔ]
    linarith
  rw [h0, sub_zero]

/-- **On the plateau the edge chart coordinate of `F_∂` is `η_j`** near `q`. -/
theorem edgeKappa_boundaryOriginalMap_eventuallyEq_BBP (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    (fun q' : W.pieceInterior ⊤ => S.edgeKappa_BBP j (S.boundaryOriginalMap q'.val)) =ᶠ[𝓝 q]
      S.edgeEta_BIF j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  filter_upwards [S.edge_plateau_mem_nhds_BBP j hq hη hh] with q' hq'
  have hcut := S.edge_cutoff_eq_one_BBP hΔ j hq'.1 hq'.2.1 hq'.2.2
  have hblk := (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q'.val).1
  rw [hcut, mul_one, S.edgeCoordW_val_BAUGP2] at hblk
  have hr := S.rho_pos j.1
  change (S.rho j.1)⁻¹ • (EuclideanSpace.proj (0 : Fin 2)) (S.edgeVector_BAUGD j
    (S.boundaryOriginalMap q'.val)) = _
  rw [hblk, map_smul, planeAxis_apply, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    S.edgeEta_eq_coord_BAUGP2 j q']
  have hp : (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := by simp
  rw [hp]
  field_simp

/-- **An edge plateau point is far from `∂W`**: `D(q) ≥ 4`. -/
theorem four_le_distanceToBoundary_of_edge_plateau_BBP (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (j : S.EdgeIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val := by
  have hne : (.inr (.inr (.inl j)) : S.IntTag_BAUGA) ≠ S.scaleTag_BAUGA := by
    simp [scaleTag_BAUGA]
  have hcut := S.edge_cutoff_eq_one_BBP hΔ j hq hη hh
  have hslot : S.boundaryOriginalMap q.val (Sum.inl (.inr (.inr (.inl j)))) =
      S.interiorMapOn_BAUGA q (.inr (.inr (.inl j))) := by
    change S.intSlotW_BAUGA (.inr (.inr (.inl j))) q.val = _
    simp only [intSlotW_BAUGA, hne, ↓reduceIte]
    exact Subtype.val_injective.extend_apply _ _ q
  have hmk := (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).2
  rw [hcut, mul_one] at hmk
  have hnz : S.interiorMapOn_BAUGA q (.inr (.inr (.inl j))) ≠ 0 := by
    intro h0
    have h1 : S.edgeMarker_BAUGD j (S.boundaryOriginalMap q.val) = 0 := by
      change (S.boundaryOriginalMap q.val (Sum.inl (.inr (.inr (.inl j))))).snd = 0
      rw [hslot, h0]
      rfl
    rw [hmk] at h1
    exact (S.rho_pos j.1).ne' h1
  exact (S.four_lt_distanceToBoundary_of_mem_tsupport_slot_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hne
    (subset_tsupport _ hnz)).le

/-- **The edge derivative lower bound at an edge plateau point** (supply form of
`EdgeFamilyOn.unit_lower_BBP`): a unit vector `u` of `ρ_j⁻²ĝ` with `1 − (σ_c + b) ≤ dη_j(u)`. -/
theorem edge_unit_lower_BBP (hΔ1 : 1 ≤ Δ) (hb0 : 0 < b) (hb : b ≤ 1 / (1000 * Δ))
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1) :
    ∃ u : TangentSpace (𝓡 3) q, (S.rho j.1)⁻¹ ^ 2 * S.completion.metric.inner q u u = 1 ∧
      1 - (σc + b) ≤ mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q u := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨u, hu1, hu2⟩ := S.family.edgeB.unit_lower_BBP hΔ1 hb0 hb hj (mem_ball.mpr hq)
  refine ⟨u, hu1, ?_⟩
  rw [S.edgeEta_eq_coord_fun_BBP j]
  exact hu2

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- A threshold-`6` edge plateau point is a stage-`1` core point. -/
theorem edge_plateau_mem_core_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) (hΔ : 0 ≤ Δ) :
    q ∈ (actualSlotsV2_BAUGD S).stageCore 1 := by
  rw [actualSlotsV2_stageCore_BAUGD]
  refine Set.mem_biUnion (x := (.inr (.inr j) : S.MarkerIdx_BAUGC)) rfl ⟨hq, ?_, ?_⟩
  · linarith
  · linarith

/-- The edge cutoff `ψ₁` is `1` at the stage input `g₁ q'` on the threshold-`6` edge plateau. -/
theorem edge_plateau_cutoff_BBP (j : S.EdgeIdx_BAUGD) {q' : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q' j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q'| < 6 * Δ) (hh : S.edgeHeightRaw q' < 6 * Δ) :
    (actualSlotsV2_BAUGD S).cutoff 1 (C.toChain.stage (1 : Fin 3).castSucc q'.val) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.edgeB.centres := (Set.Finite.mem_toFinset _).mp j.2
  have h := C.toChain.cutoff_bindings.2.1.2.2.1 q' ⟨j.1, hj, hq, hη, hh⟩
  have e1 : C.toChain.stage (1 : Fin 3).castSucc q'.val = C.toChain.g₁ q'.val := rfl
  exact (congrArg ((actualSlotsV2_BAUGD S).cutoff 1)
    (e1.trans (C.toChain.g₁_apply_V2_BAUGD q'.val))).trans h

include C in
/-- `0 < c₀` from the CHOICE inequalities. -/
theorem chain_c_zero_pos_BBP : 0 < c 0 := by
  have hN := C.toChain.numbers
  have h0 : 0 < 5 / 3 * Ξ 0 * Sg 0 := by
    have := (hN.1 0).1; have := (hN.1 0).2.1; positivity
  exact lt_trans h0 hN.2.1

/-- **The stage-`1` tube at an edge plateau point**: the plateau is core, and
`π₁ g₁ q ∈ B(π₁ F_∂ q, r)`. -/
theorem edge_stage_tube_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    (actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.stage (1 : Fin 3).castSucc q.val) ∈
      ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))
        (DP.stageRadius 1 (Sg 1)
          ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))) := by
  have hcore := edge_plateau_mem_core_BBP j hq hη hh C.std.2.1.le
  have hN := C.toChain.numbers
  have hyv : ‖C.toChain.stage (1 : Fin 3).castSucc q.val - S.boundaryOriginalMap q.val‖ ≤
      c 0 * S.rho q.val := (C.stage_error_lt_BAUGD 0 q.val).le
  exact C.stage_tube_BBP 1 hcore C.chain_c_zero_pos_BBP.le hN.2.2.2.2.2.1 hyv

/-- `κ_j ∘ π₁ = κ_j` (the edge chart coordinate only reads the edge tag's block). -/
theorem edgeKappa_stageProj_BBP (j : S.EdgeIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 1 y) = S.edgeKappa_BBP j y := by
  have ht : (.inr (.inr (.inl j)) : S.IntTag_BAUGA) ∈ S.stageTagsV2_BAUGD 1 :=
    BoundarySupplyCore.mem_stageTagsV2_one_BAUGD.mpr rfl
  unfold BoundarySupplyCore.edgeKappa_BBP
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  unfold BoundarySupplyCore.edgeVector_BAUGD
  rw [blockVector_stageProj_BBP S 1 ht]

include C in
/-- **The `edgeB` chart derivative of `F_∂` on the plateau is that of `η_j`**. -/
theorem edgeKappa_mvfderiv_eq_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ)
    (u : TangentSpace (𝓡 3) q) :
    S.edgeKappa_BBP j (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u)) =
      mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q u := by
  have hΔ := C.std.2.1
  have hFd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      S.boundaryOriginalMap q.val :=
    ((C.stage_smooth_BAUGD 0) q.val).mdifferentiableAt (by simp)
  have hFv : MDifferentiableAt (𝓡 3)
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (fun q' : W.pieceInterior ⊤ => S.boundaryOriginalMap q'.val) q :=
    hFd.comp q (mdifferentiableAt_val_BCG7 W q)
  have f1 := mvfderiv_comp_val_BCG7 W _ q hFd u
  have f2 := mvfderiv_clm_comp_BDFB (S.edgeKappa_BBP j) hFv u
  have f3 := mvfderiv_congr_BDFB
    (S.edgeKappa_boundaryOriginalMap_eventuallyEq_BBP hΔ j hq hη hh) u
  exact (congrArg (S.edgeKappa_BBP j) f1).symm.trans (f2.symm.trans f3)

/-- **The edge native derivative** on the plateau: `D(κ_j ∘ f₁⁰)(dι u) = κ_j(Da₁(π₁ g₁)(π₁ Dg₁
(dι u)))`. -/
theorem edge_native_mvfderiv_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ)
    (u : TangentSpace (𝓡 3) q) :
    mvfderiv W.model (fun p => S.edgeKappa_BBP j (C.toChain.nativeStageMap_BIFc 1 p)) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) =
      S.edgeKappa_BBP j (fderiv ℝ (C.toChain.slot 1).map
          ((actualSlotsV2_BAUGD S).stageProj 1
            (C.toChain.stage (1 : Fin 3).castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj 1
          (mvfderiv W.model (C.toChain.stage (1 : Fin 3).castSucc)
            q.val (mfderiv (𝓡 3) W.model Subtype.val q u)))) := by
  have hcore := edge_plateau_mem_core_BBP j hq hη hh C.std.2.1.le
  have hx : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 1 := ⟨q, hcore, rfl⟩
  have hball := C.edge_stage_tube_BBP j hq hη hh
  have hda : DifferentiableAt ℝ (C.toChain.slot 1).map ((actualSlotsV2_BAUGD S).stageProj 1
      (C.toChain.stage (1 : Fin 3).castSucc q.val)) :=
    ((C.toChain.slot 1).map_contDiffAt_BAUGD hx hball).differentiableAt (by simp)
  exact C.native_mvfderiv_BBP 1 (S.edgeKappa_BBP j) (edgeKappa_stageProj_BBP j)
    (S.edge_plateau_mem_nhds_BBP j hq hη hh)
    (fun q' hq' => C.edge_plateau_cutoff_BBP j hq'.1 hq'.2.1 hq'.2.2) hda u

include C in
/-- **The CHOICE budget of the edge stage**: `Ξ₁(b_der + H₀) + H₀ + e₁ < 1/512` for the prior
derivative error `H₀ < c₀` (`C.stage_derivative_lt_BAUGD 0`). -/
theorem edge_budget_BBP {Hd : ℝ} (hHd : Hd < c 0) (q : W.Carrier) :
    Ξ 1 * (bder + Hd) + Hd + eg 1 < 1 / 512 := by
  have hN := C.toChain.numbers
  have hΞ1 := (hN.1 1).1
  have hbcut := C.bcut_nonneg_BAUGD q
  have hbder := C.bder_nonneg_BAUGD q
  have hc0 := C.chain_c_zero_pos_BBP
  have h1 : 0 ≤ (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * bcut * (bder + c 0) := by
    have := (hN.1 1).2.1
    positivity
  have h2 : Ξ 1 * Hd ≤ Ξ 1 * c 0 := mul_le_mul_of_nonneg_left hHd.le hΞ1.le
  linarith [hN.2.2.2.2.2.2.2.1, hN.2.2.2.2.2.2.2.2.1]

/-- **The edge stage derivative error on the plateau**: for `v` with `|v|_g = ρ_j`,
`‖κ_j(Da₁(π₁ g₁)(π₁ Dg₁ v)) − κ_j(π₁ DF_∂ v)‖ ≤ 1/512`. -/
theorem edge_deriv_close_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ)
    (v : TangentSpace W.model q.val) (hv : Real.sqrt (g.inner q.val v v) = S.rho j.1) :
    ‖S.edgeKappa_BBP j (fderiv ℝ (C.toChain.slot 1).map
          ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.stage (1 : Fin 3).castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj 1
          (mvfderiv W.model (C.toChain.stage (1 : Fin 3).castSucc) q.val v))) -
      S.edgeKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 1
        (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤ 1 / 512 := by
  have hcore := edge_plateau_mem_core_BBP j hq hη hh C.std.2.1.le
  have hball := C.edge_stage_tube_BBP j hq hη hh
  obtain ⟨Hd, hHd, hHdb⟩ := C.stage_derivative_lt_BAUGD 0
  have hH : ∀ w : TangentSpace W.model q.val,
      ‖mvfderiv W.model (C.toChain.stage (1 : Fin 3).castSucc) q.val w -
        mvfderiv W.model S.boundaryOriginalMap q.val w‖ ≤ Hd * Real.sqrt (g.inner q.val w w) :=
    fun w => hHdb q.val w
  have hcl := C.stage_deriv_close_BBP 1 (S.edgeKappa_BBP j) (S.norm_edgeKappa_le_BBP j) hcore
    hball hH v
  have hbud := C.edge_budget_BBP hHd q.val
  have hr := S.rho_pos j.1
  have hcl' : (S.rho j.1)⁻¹ * ((Ξ 1 * (bder + Hd) + Hd + eg 1) *
      Real.sqrt (g.inner q.val v v)) = Ξ 1 * (bder + Hd) + Hd + eg 1 := by
    rw [hv]
    field_simp
  exact (hcl.trans (le_of_eq hcl')).trans hbud.le

include C in
/-- **The normalized tangent vector of an edge plateau point**: for the unit `u` of `ρ_j⁻²ĝ`,
`|dι u|_g = ρ_j` (`ĝ = g` on `D ≥ 4`). -/
theorem edge_unit_norm_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ)
    (u : TangentSpace (𝓡 3) q)
    (hu : (S.rho j.1)⁻¹ ^ 2 * S.completion.metric.inner q u u = 1) :
    Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
      (mfderiv (𝓡 3) W.model Subtype.val q u)) = S.rho j.1 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, -⟩ := C.std
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hD4 := S.four_le_distanceToBoundary_of_edge_plateau_BBP hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he j
    hq hη hh
  have heq : ∀ y : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g y →
      S.completion.metric.inner y = (pieceInteriorMetric W g ⊤).inner y := fun y hy =>
    S.completion.inner_eq_on_agree y (S.completion.far_subset_agree hy)
  have hr := S.rho_pos j.1
  have hgv := inner_mfderiv_val_BCG7 W g S.completion.metric heq q hD4 u u
  have hI : S.completion.metric.inner q u u = S.rho j.1 ^ 2 := by
    field_simp at hu
    linarith
  rw [hgv, hI, Real.sqrt_sq hr.le]

/-- **G1c, edge: the stage submersion** (closed twin `Gaf02Chain.stage_submersion_edge_BAS`; chart
route): at every point `q` of the edge chart `j`'s ORIGINAL threshold-`6` plateau
(`dist < 100Δρ_j`, `|η_j| < 6Δ`, `t_B < 6Δ`), `D(κ_j ∘ f₁⁰)(q)` is onto `ℝ`
(`κ_j = ρ_j⁻¹ proj₀ u_j`, `f₁⁰ = π₁ g₂` the native second-stage map). Inputs:
`EdgeFamilyOn.unit_lower_BBP` (`dη_j(u) ≥ 1 − (σ_c + b)` for a unit `u`), `κ_j ∘ F_∂ = η_j` on
the plateau, `ψ₁ = 1` on the plateau (`C.cutoff_bindings`), the CFS15 derivative
`‖Da₁ − π_L‖ ≤ Ξ₁`, V3 `normal`, A3c's prior error `H₀ < c₀` and the CHOICE budget
`< c₁ ≤ 1/512`. Register premises: `σ_c ≤ 1/4`, `b ≤ 1/(1000Δ)` (neither is in `C.std`). -/
theorem stage_submersion_edge_BBP (hσ : σc ≤ 1 / 4) (hb' : b ≤ 1 / (1000 * Δ))
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
      (fun p => S.edgeKappa_BBP j (C.toChain.nativeStageMap_BIFc 1 p)) q.val) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ1 : 1 ≤ Δ := C.std.2.2.2.2.2.2.2.2.2.1
  have hb0 : 0 < b := C.std.2.2.2.2.2.2.2.1
  have hb1 : b ≤ 1 / 1000 := by
    refine hb'.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨u, hu1, hu2⟩ := S.edge_unit_lower_BBP hΔ1 hb0 hb' j hq
  have hsq := C.edge_unit_norm_BBP j hq hη hh u hu1
  have hcl := C.edge_deriv_close_BBP j hq hη hh (mfderiv (𝓡 3) W.model Subtype.val q u) hsq
  have hmain : S.edgeKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 1
      (mvfderiv W.model S.boundaryOriginalMap q.val (mfderiv (𝓡 3) W.model Subtype.val q u))) =
      mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q u :=
    (edgeKappa_stageProj_BBP j _).trans (C.edgeKappa_mvfderiv_eq_BBP j hq hη hh u)
  have hval := C.edge_native_mvfderiv_BBP j hq hη hh u
  refine surjective_of_apply_ne_zero_BBP ((mvfderiv W.model
    (fun p => S.edgeKappa_BBP j (C.toChain.nativeStageMap_BIFc 1 p)) q.val :
      TangentSpace W.model q.val →L[ℝ] ℝ) : TangentSpace W.model q.val →ₗ[ℝ] ℝ)
    (v := mfderiv (𝓡 3) W.model Subtype.val q u) ?_
  change mvfderiv W.model (fun p => S.edgeKappa_BBP j (C.toChain.nativeStageMap_BIFc 1 p)) q.val
    (mfderiv (𝓡 3) W.model Subtype.val q u) ≠ 0
  rw [hval]
  rw [hmain] at hcl
  rw [Real.norm_eq_abs, abs_le] at hcl
  intro h0
  rw [h0] at hcl
  linarith [hcl.1]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
