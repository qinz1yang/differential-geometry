import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersion

/-!
# A4 / G11 (lane S-BASES-PORT), group G1b: the slim stage submersion on the boundary chain

Completes the slim half of C14-BASES G5 (`Gaf02Chain.stage_submersion_slim_BAS`) on
`C : BoundaryGaf02ChainE DP …` by the chart route of `LE/BoundaryBasesStageSubmersion.lean`
(B-BASES-PORT G1; its timed-out slim draft split into small declarations):

* `slim_plateau_cutoff_BBP`: the binding `ψ₂(g₂ q') = 1` on the threshold-6 slim plateau, converted
  from the chain's `cutoff_bindings` through `g₂_apply_V2_BAUGD` / `g₁_apply_V2_BAUGD`;
* `chain_c_one_nonneg_BBP`, `slim_stage_tube_BBP`: `0 ≤ c₁` and the stage-2 tube
  `π₂ g₂ q ∈ B(π₂ F_∂ q, r)`;
* `slimKappa_stageProj_BBP`, `slim_native_mvfderiv_BBP`: `κ_j ∘ π₂ = κ_j` and the native
  derivative `D(κ_j ∘ f₂⁰)(dι u) = κ_j(Da₂(π₂ g₂)(π₂ Dg₂(dι u)))`;
* `slim_budget_BBP`, `slim_deriv_close_BBP`, `slim_unit_norm_BBP`: the CHOICE budget
  `Ξ₂(b_der + H₁) + H₁ + e₂ < 1/512`, the derivative error `≤ 1/512` on `|v|_g = ρ_j`, and
  `|dι u|_g = ρ_j`;
* **`BoundaryGaf02ChainE.stage_submersion_slim_BBP`** (no numeric premise: LFR20.1 gives
  `dη_j(u) > 3/4`) and its final-map form `stage_submersion_slim_final_BBP`
  (`nativeStageMap 2 = stageMap 2`).
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

/-- The slim cutoff `ψ₂` is `1` at the stage input `g₂ q'` on the threshold-`6` slim plateau. -/
theorem slim_plateau_cutoff_BBP (j : S.SlimIdx_BAUGD) {q' : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q' j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q'| < 6 * (10 ^ 5 * Δ)) :
    (actualSlotsV2_BAUGD S).cutoff 2 (C.toChain.stage (2 : Fin 3).castSucc q'.val) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  have h := C.toChain.cutoff_bindings.2.2.2.2.1 q' ⟨j.1, hj, hq, hη⟩
  have e1 : C.toChain.stage (2 : Fin 3).castSucc q'.val = C.toChain.g₂ q'.val := rfl
  have e2 := (C.toChain.g₂_apply_V2_BAUGD q'.val).trans
    (congrArg ((actualSlotsV2_BAUGD S).adjust 1 (C.toChain.slot 1).map)
      (C.toChain.g₁_apply_V2_BAUGD q'.val))
  exact (congrArg ((actualSlotsV2_BAUGD S).cutoff 2) (e1.trans e2)).trans h

include C in
/-- `0 ≤ c₁` from the CHOICE inequalities. -/
theorem chain_c_one_nonneg_BBP : 0 ≤ c 1 := by
  have hN := C.toChain.numbers
  have h0 : 0 < 5 / 3 * Ξ 0 * Sg 0 := by
    have := (hN.1 0).1; have := (hN.1 0).2.1; positivity
  have h1 : 0 ≤ 5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0 := by
    have := (hN.1 1).1; have := (hN.1 1).2.1
    have : 0 < c 0 := lt_trans h0 hN.2.1
    positivity
  linarith [hN.2.2.2.2.2.2.1, hN.2.1]

/-- **The stage-`2` tube at a slim plateau point**: the plateau is core, and
`π₂ g₂ q ∈ B(π₂ F_∂ q, r)`. -/
theorem slim_stage_tube_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    (actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stage (2 : Fin 3).castSucc q.val) ∈
      ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val))
        (DP.stageRadius 2 (Sg 2)
          ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val))) := by
  have hcore := slim_plateau_mem_core_BBP j hq hη C.std.2.1.le
  have hN := C.toChain.numbers
  have hyv : ‖C.toChain.stage (2 : Fin 3).castSucc q.val - S.boundaryOriginalMap q.val‖ ≤
      c 1 * S.rho q.val := (C.stage_error_lt_BAUGD 1 q.val).le
  exact C.stage_tube_BBP 2 hcore C.chain_c_one_nonneg_BBP hN.2.2.2.2.2.2.2.2.2.2.1 hyv

/-- `κ_j ∘ π₂ = κ_j` (the slim chart coordinate only reads the slim tag's block). -/
theorem slimKappa_stageProj_BBP (j : S.SlimIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 y) = S.slimKappa_BBP j y := by
  unfold BoundarySupplyCore.slimKappa_BBP
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  unfold BoundarySupplyCore.slimVector_BAUGD
  rw [blockVector_stageProj_BBP S 2 (S.slimTag_mem_stageTagsV2_BAUGD 2 j)]

/-- **The slim native derivative** on the plateau: `D(κ_j ∘ f₂⁰)(dι u) = κ_j(Da₂(π₂ g₂)(π₂ Dg₂
(dι u)))`. -/
theorem slim_native_mvfderiv_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (u : TangentSpace (𝓡 3) q) :
    mvfderiv W.model (fun p => S.slimKappa_BBP j (C.toChain.nativeStageMap_BIFc 2 p)) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) =
      S.slimKappa_BBP j (fderiv ℝ (C.toChain.slot 2).map
          ((actualSlotsV2_BAUGD S).stageProj 2
            (C.toChain.stage (2 : Fin 3).castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj 2
          (mvfderiv W.model (C.toChain.stage (2 : Fin 3).castSucc)
            q.val (mfderiv (𝓡 3) W.model Subtype.val q u)))) := by
  have hcore := slim_plateau_mem_core_BBP j hq hη C.std.2.1.le
  have hx : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 2 := ⟨q, hcore, rfl⟩
  have hball := C.slim_stage_tube_BBP j hq hη
  have hda : DifferentiableAt ℝ (C.toChain.slot 2).map ((actualSlotsV2_BAUGD S).stageProj 2
      (C.toChain.stage (2 : Fin 3).castSucc q.val)) :=
    ((C.toChain.slot 2).map_contDiffAt_BAUGD hx hball).differentiableAt (by simp)
  exact C.native_mvfderiv_BBP 2 (S.slimKappa_BBP j) (slimKappa_stageProj_BBP j)
    (S.slim_plateau_mem_nhds_BBP j hq hη) (fun q' hq' => C.slim_plateau_cutoff_BBP j hq'.1 hq'.2)
    hda u

include C in
/-- **The CHOICE budget of the last stage**: `Ξ₂(b_der + H₁) + H₁ + e₂ < 1/512` for the prior
derivative error `H₁ < c₁` (`C.stage_derivative_lt_BAUGD 1`). -/
theorem slim_budget_BBP {Hd : ℝ} (hHd : Hd < c 1) (q : W.Carrier) :
    Ξ 2 * (bder + Hd) + Hd + eg 2 < 1 / 512 := by
  have hN := C.toChain.numbers
  have hΞ2 := (hN.1 2).1
  have hbcut := C.bcut_nonneg_BAUGD q
  have hbder := C.bder_nonneg_BAUGD q
  have h0 : 0 < 5 / 3 * Ξ 0 * Sg 0 := by
    have := (hN.1 0).1; have := (hN.1 0).2.1; positivity
  have hc0 : 0 < c 0 := lt_trans h0 hN.2.1
  have hc1 := C.chain_c_one_nonneg_BBP
  have h1 : 0 ≤ (5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (bder + c 1) := by
    have := (hN.1 2).2.1
    positivity
  have h2 : Ξ 2 * Hd ≤ Ξ 2 * c 1 := mul_le_mul_of_nonneg_left hHd.le hΞ2.le
  linarith [hN.2.2.2.2.2.2.2.2.2.2.2.2.1, hN.2.2.2.2.2.2.2.2.2.2.2.2.2]

/-- **The slim stage derivative error on the plateau**: for `v` with `|v|_g = ρ_j`,
`‖κ_j(Da₂(π₂ g₂)(π₂ Dg₂ v)) − κ_j(π₂ DF_∂ v)‖ ≤ 1/512`. -/
theorem slim_deriv_close_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (v : TangentSpace W.model q.val)
    (hv : Real.sqrt (g.inner q.val v v) = S.rho j.1) :
    ‖S.slimKappa_BBP j (fderiv ℝ (C.toChain.slot 2).map
          ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stage (2 : Fin 3).castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj 2
          (mvfderiv W.model (C.toChain.stage (2 : Fin 3).castSucc) q.val v))) -
      S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2
        (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤ 1 / 512 := by
  have hcore := slim_plateau_mem_core_BBP j hq hη C.std.2.1.le
  have hball := C.slim_stage_tube_BBP j hq hη
  obtain ⟨Hd, hHd, hHdb⟩ := C.stage_derivative_lt_BAUGD 1
  have hH : ∀ w : TangentSpace W.model q.val,
      ‖mvfderiv W.model (C.toChain.stage (2 : Fin 3).castSucc) q.val w -
        mvfderiv W.model S.boundaryOriginalMap q.val w‖ ≤ Hd * Real.sqrt (g.inner q.val w w) :=
    fun w => hHdb q.val w
  have hcl := C.stage_deriv_close_BBP 2 (S.slimKappa_BBP j) (S.norm_slimKappa_le_BBP j) hcore
    hball hH v
  have hbud := C.slim_budget_BBP hHd q.val
  have hr := S.rho_pos j.1
  have hcl' : (S.rho j.1)⁻¹ * ((Ξ 2 * (bder + Hd) + Hd + eg 2) *
      Real.sqrt (g.inner q.val v v)) = Ξ 2 * (bder + Hd) + Hd + eg 2 := by
    rw [hv]
    field_simp
  exact (hcl.trans (le_of_eq hcl')).trans hbud.le

include C in
/-- **The normalized tangent vector of a slim plateau point**: for the unit `u` of `ρ_j⁻²ĝ`,
`|dι u|_g = ρ_j` (`ĝ = g` on `D ≥ 4`). -/
theorem slim_unit_norm_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) (u : TangentSpace (𝓡 3) q)
    (hu : (S.rho j.1)⁻¹ ^ 2 * S.completion.metric.inner q u u = 1) :
    Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
      (mfderiv (𝓡 3) W.model Subtype.val q u)) = S.rho j.1 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, -⟩ := C.std
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hD4 := S.four_le_distanceToBoundary_of_slim_plateau_BBP hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he j
    hq hη
  have heq : ∀ y : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g y →
      S.completion.metric.inner y = (pieceInteriorMetric W g ⊤).inner y := fun y hy =>
    S.completion.inner_eq_on_agree y (S.completion.far_subset_agree hy)
  have hr := S.rho_pos j.1
  have hgv := inner_mfderiv_val_BCG7 W g S.completion.metric heq q hD4 u u
  have hI : S.completion.metric.inner q u u = S.rho j.1 ^ 2 := by
    field_simp at hu
    linarith
  rw [hgv, hI, Real.sqrt_sq hr.le]

/-- **G1b, slim: the stage submersion** (closed twin `Gaf02Chain.stage_submersion_slim_BAS`;
chart route): at every point `q` of the slim chart `j`'s ORIGINAL threshold-`6` plateau,
`D(κ_j ∘ f₂⁰)(q)` is onto `ℝ` (`κ_j = ρ_j⁻¹ proj₀ u_j`, `f₂⁰ = π₂E` the native last-stage map).
Inputs: LFR20.1 of the slim chart (`dη_j(u) > 3/4` for a unit `u`), `κ_j ∘ F_∂ = η_j` on the
plateau, `ψ₂ = 1` on the plateau (`C.cutoff_bindings`), the CFS15 derivative `‖Da₂ − π_L‖ ≤ Ξ₂`,
V3 `normal`, A3c's prior error `H₁ < c₁` and the CHOICE budget `< c₂ ≤ 1/512`. No further
premise. -/
theorem stage_submersion_slim_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
      (fun p => S.slimKappa_BBP j (C.toChain.nativeStageMap_BIFc 2 p)) q.val) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨u, hu1, hu2⟩ := S.slim_derivative_lower_BBP j hq hη C.std.2.1.le
  have hsq := C.slim_unit_norm_BBP j hq hη u hu1
  have hcl := C.slim_deriv_close_BBP j hq hη (mfderiv (𝓡 3) W.model Subtype.val q u) hsq
  have hmain : S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2
      (mvfderiv W.model S.boundaryOriginalMap q.val (mfderiv (𝓡 3) W.model Subtype.val q u))) =
      mvfderiv (𝓡 3) (S.slimEta_BIF j.1) q u :=
    (slimKappa_stageProj_BBP j _).trans (C.slimKappa_mvfderiv_eq_BBP j hq hη u)
  have hval := C.slim_native_mvfderiv_BBP j hq hη u
  refine surjective_of_apply_ne_zero_BBP ((mvfderiv W.model
    (fun p => S.slimKappa_BBP j (C.toChain.nativeStageMap_BIFc 2 p)) q.val :
      TangentSpace W.model q.val →L[ℝ] ℝ) : TangentSpace W.model q.val →ₗ[ℝ] ℝ)
    (v := mfderiv (𝓡 3) W.model Subtype.val q u) ?_
  change mvfderiv W.model (fun p => S.slimKappa_BBP j (C.toChain.nativeStageMap_BIFc 2 p)) q.val
    (mfderiv (𝓡 3) W.model Subtype.val q u) ≠ 0
  rw [hval]
  rw [hmain] at hcl
  rw [Real.norm_eq_abs, abs_le] at hcl
  intro h0
  rw [h0] at hcl
  linarith [hcl.1]

/-- **G1b, slim, final-map form**: the native last-stage map is the final stage map
(`nativeStageMap_two_BIFc`), so `D(κ_j ∘ f₂)(q)` is onto `ℝ` at every slim plateau point. -/
theorem stage_submersion_slim_final_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
      (fun p => S.slimKappa_BBP j (C.toChain.stageMap 2 p)) q.val) :=
  C.stage_submersion_slim_BBP j hq hη

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
