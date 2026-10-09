import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimTransport

/-!
# PORT target: the interior slim stage table of a boundary supply (lane B-PORT-SLIMb)

The frozen port targets (PortTargets v3.1, `docs/geometrization/chapter14/evidence/boundary/
PortTargets-v3.1.lean.txt`, and the supplement `PortTargets-v3-supplement.lean.txt`), proved with the
statements verbatim:

* **`port_slim_interior_table_BAUGP`** — the interior half of the stage-`2` table on the ACTUAL slot
  `actualSlotsV2_BAUGD S`: model `Kint a ∘ Ψ a` (`Kint a = id`, `Ψ a = slimStageModel_BPS`, SGP04's full model
  `sgpFullGraph_BAUGP` of the slim centre `a`), own coordinate `Pc a = slimStageOwn_BPS`, radius preimages
  `rpre`, core preimages `pre` and references `ref`, with (M), (OWN), (Q), (TG), (SEL), (LOC), (COV), (PRE),
  (MCb), (PP-int), (SB-int), (FM*-int), (ZB*-int). Closed twin `exists_slimStagePlanes_PLN` and its
  structure theorems; boundary inputs: SGP04 on the boundary family (`slim_row_supply_BPS`), the slim
  marker layer (`BoundaryPortSlimMarkers`), the pointwise clauses (`BoundaryPortSlimClauses`, `…ClausesB`).
* **`port_slim_cloud_scale_BAUGP`** — (PRE~): two preimages of one point of `S̃₂` have `ρ(q₁) ≤ 5/3·ρ(q₂)`.

The clause lemmas `slimTable_*_BPS` state each clause for the chosen data (fixed supply).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section GenericAxis

variable {τ : Type*} [Fintype τ]

/-- The first axis coordinate of the block `t`, a `1`-Lipschitz functional on the block space. -/
def blockAxisCLM_BPS (t : τ) : BlockSpace (fun _ : τ => ℝ²) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun z => (z t).fst 0
      map_add' := fun z w => by simp
      map_smul' := fun r z => by simp } 1 (fun z => by
        rw [one_mul]
        calc ‖(z t).fst 0‖ ≤ ‖(z t).fst‖ := PiLp.norm_apply_le _ 0
          _ ≤ ‖z t‖ := WithLp.norm_fst_le _ _
          _ ≤ ‖z‖ := PiLp.norm_apply_le _ _)

theorem blockAxisCLM_apply_BPS (t : τ) (z : BlockSpace (fun _ : τ => ℝ²)) :
    blockAxisCLM_BPS t z = (z t).fst 0 :=
  rfl

theorem norm_blockAxisCLM_apply_le_BPS (t : τ) (z : BlockSpace (fun _ : τ => ℝ²)) :
    ‖blockAxisCLM_BPS t z‖ ≤ ‖z‖ := by
  rw [blockAxisCLM_apply_BPS]
  calc ‖(z t).fst 0‖ ≤ ‖(z t).fst‖ := PiLp.norm_apply_le _ 0
    _ ≤ ‖z t‖ := WithLp.norm_fst_le _ _
    _ ≤ ‖z‖ := PiLp.norm_apply_le _ _

end GenericAxis

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM) (sgnf cf zsgnf zcf : S.SlimIdx_BAUGD → W.pieceInterior ⊤ → ℝ)

/-- The slim centres are the stage-`2` centres. -/
theorem stageCentres_two_BPS :
    S.stageCentres_BIF 2 = (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres) :=
  rfl

open Classical in
/-- **The stage-`2` model** `Ψ a`: SGP04's full model `slimModelOf_BPS` of the slim centre `a` with the
chosen signs and translations (zero off the centres). -/
def slimStageModel_BPS (a : W.pieceInterior ⊤) : ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : a ∈ S.family.slim.centres then
    S.slimModelOf_BPS ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩ (sgnf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)
      (cf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩) (zsgnf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)
      (zcf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)
  else 0

/-- At a slim centre, `Kint a ∘ Ψ a = id ∘ Ψ a` is SGP04's model of `a`. -/
theorem slimStageModel_comp_BPS {a : W.pieceInterior ⊤}
    (ha : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres)) :
    ⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.slimStageModel_BPS sgnf cf zsgnf zcf a =
      S.slimModelOf_BPS ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩
        (sgnf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) (cf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩)
        (zsgnf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) (zcf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) := by
  unfold slimStageModel_BPS
  rw [dite_eq_left ha]
  rfl

open Classical in
/-- **The own coordinate** `Pc a`: the first axis coordinate of the own block of `a` (zero off the
centres). -/
def slimStageOwn_BPS (a : W.pieceInterior ⊤) : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : a ∈ S.family.slim.centres then
    blockAxisCLM_BPS (.inr (.inl ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)) else 0

theorem slimStageOwn_of_mem_BPS {a : W.pieceInterior ⊤}
    (ha : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres)) :
    S.slimStageOwn_BPS a = blockAxisCLM_BPS (.inr (.inl ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩)) := by
  unfold slimStageOwn_BPS
  rw [dite_eq_left ha]

/-- **(M)** global `C²` bounds of `Kint a ∘ Ψ a`. -/
theorem slimTable_M_BPS (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hsgn : ∀ i j, |sgnf i j| ≤ 1) (hzsgn : ∀ i k, |zsgnf i k| ≤ 1) :
    ∀ a ∈ S.stageCentres_BIF 2,
      ContDiff ℝ 2 (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.slimStageModel_BPS sgnf cf zsgnf zcf a) ∧ ∀ u,
        ‖fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.slimStageModel_BPS sgnf cf zsgnf zcf a) u‖ ≤ sgpGraphBound ∧
        ‖fderiv ℝ (fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.slimStageModel_BPS sgnf cf zsgnf zcf a)) u‖ ≤ sgpGraphBound := by
  intro a ha
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres) := ha
  rw [S.slimStageModel_comp_BPS sgnf cf zsgnf zcf ha']
  exact ⟨(S.contDiff_slimModelOf_BPS _ _ _ _ _).of_le (by simp), fun u =>
    S.slimModelOf_bounds_BPS _ _ _ _ _ hΔ1 hΛ hΛΔ he hT hσs hσs1 (hsgn _) (hzsgn _) u⟩

/-- **(OWN)** the own coordinate is a `1`-Lipschitz left inverse of the model, exact on the core. -/
theorem slimTable_OWN_BPS :
    letI := inducedMetricSpace S.completion.metric
    ∀ a ∈ S.stageCentres_BIF 2, (∀ z, ‖S.slimStageOwn_BPS a z‖ ≤ ‖z‖) ∧
      (∀ u, S.slimStageOwn_BPS a ((⇑(ContinuousLinearMap.id ℝ
        (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘ S.slimStageModel_BPS sgnf cf zsgnf zcf a) u) = u) ∧
      ∀ x : W.pieceInterior ⊤, (dist x a < 1000000 * Δ * S.rho a ∧
          |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
        S.slimStageOwn_BPS a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2)
          (S.interiorMapOn_BAUGA x)) = S.slimEta_BIF a x := by
  intro a ha
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres) := ha
  rw [S.slimStageOwn_of_mem_BPS ha', S.slimStageModel_comp_BPS sgnf cf zsgnf zcf ha']
  refine ⟨fun z => norm_blockAxisCLM_apply_le_BPS _ z, fun u => ?_, fun x hx => ?_⟩
  · rw [blockAxisCLM_apply_BPS, S.slimModelOf_own_BPS]
    simp [planeAxis_apply]
  · have hc := S.slim_cutoff_eq_one_BPS ⟨a, (Set.Finite.mem_toFinset _).mpr ha'⟩ hx.1 hx.2
    rw [blockAxisCLM_apply_BPS, PiLp.smul_apply, S.interiorMapOn_slim_block_BPS _ hc]
    have hra := S.rho_pos a
    have hk : (S.rho a)⁻¹ * (S.rho a * S.slimEta_BIF a x) = S.slimEta_BIF a x := by
      rw [← mul_assoc, inv_mul_cancel₀ hra.ne', one_mul]
    simpa [planeAxis_apply] using hk

/-- **(Q)** the model takes values in `Q₃^∂`. -/
theorem slimTable_Q_BPS :
    ∀ a ∈ S.stageCentres_BIF 2, ∀ u,
      blockRestrict (S.stageTagsV2_BAUGD 2) ((⇑(ContinuousLinearMap.id ℝ
        (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘ S.slimStageModel_BPS sgnf cf zsgnf zcf a) u) =
        (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.slimStageModel_BPS sgnf cf zsgnf zcf a) u := by
  intro a ha u
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres) := ha
  rw [S.slimStageModel_comp_BPS sgnf cf zsgnf zcf ha']
  exact S.slimModelOf_blockRestrict_BPS _ _ _ _ _ u

/-- **(TG)** value and derivative comparison on the threshold-`8` reference core. -/
theorem slimTable_TG_BPS {eg : ℝ}
    (hTG : ∀ i : S.SlimIdx_BAUGD, ∀ x : W.pieceInterior ⊤,
      (letI := inducedMetricSpace S.completion.metric
       dist x i.1 < 1000000 * Δ * S.rho i.1) →
      |S.slimEta_BIF i.1 x| ≤ 8 * (100000 * Δ) →
      ‖(S.rho i.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) -
        S.slimModelOf_BPS i (sgnf i) (cf i) (zsgnf i) (zcf i) (S.slimEta_BIF i.1 x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA y)) x w -
          fderiv ℝ (S.slimModelOf_BPS i (sgnf i) (cf i) (zsgnf i) (zcf i)) (S.slimEta_BIF i.1 x)
            (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF i.1) x w)‖ ≤
          eg * Real.sqrt ((S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w)) :
    letI := inducedMetricSpace S.completion.metric
    ∀ a ∈ S.stageCentres_BIF 2, ∀ x : W.pieceInterior ⊤,
      (dist x a < 1000000 * Δ * S.rho a ∧ |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
      ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) -
          (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.slimStageModel_BPS sgnf cf zsgnf zcf a) (S.slimEta_BIF a x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA y)) x w -
          fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.slimStageModel_BPS sgnf cf zsgnf zcf a) (S.slimEta_BIF a x)
            (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF a) x w)‖ ≤
          eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w) := by
  intro a ha x hx
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres) := ha
  simp only [S.slimStageModel_comp_BPS sgnf cf zsgnf zcf ha']
  exact hTG ⟨a, (Set.Finite.mem_toFinset _).mpr ha'⟩ x hx.1 hx.2

variable (jref : (actualSlotsV2_BAUGD S).stageCloud 2 → S.SlimIdx_BAUGD)
  (pre : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤)
  (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 → W.pieceInterior ⊤)

/-- **(SEL)**, model preimages: references in the stage centres, core-`7` preimages in `D_a`. -/
theorem slimTable_SEL_BPS (hΔ0 : 0 < Δ)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1) ∧
      |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x, (jref x).1 ∈ S.stageCentres_BIF 2 ∧ (dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1 ∧
        |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ)) ∧
      dist (pre x) (jref x).1 < stageDomain_BIF Δ 2 * S.rho (jref x).1 ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1 := by
  intro x
  have h := hpre x
  have hd := S.slimEta_abs_le_ZERO_BPS (jref x) h.1 (by linarith only [h.2.1, hΔ0])
  have hrj := S.rho_pos (jref x).1
  have h1 : 910000 * Δ * S.rho (jref x).1 < 950000 * Δ * S.rho (jref x).1 := by
    nlinarith only [mul_pos hΔ0 hrj]
  refine ⟨(Set.Finite.mem_toFinset _).mp (jref x).2, ⟨h.1, h.2.1⟩, ?_, h.2.2⟩
  rw [stageDomain_two_BPS]
  exact hd.trans h1

/-- **(LOC)** FC03 localization near a cloud point. -/
theorem slimTable_LOC_BPS {Γ sg : ℝ} (hΔ1 : 1 ≤ Δ) (hR : sg / Γ < 1 / 100)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1) ∧
      |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
      ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
        ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (jref ⟨x, hx⟩).1 / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (jref ⟨x, hx⟩).1 < 1000000 * Δ * S.rho (jref ⟨x, hx⟩).1 ∧
            |S.slimEta_BIF (jref ⟨x, hx⟩).1 q| ≤ 8 * (100000 * Δ)) ∧
          dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 2 * S.rho (jref ⟨x, hx⟩).1 ∧
          (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = y := by
  intro x hx y hy hxy
  obtain ⟨q, -, hq⟩ := hy
  have h := hpre ⟨x, hx⟩
  have hb : ‖augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) -
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre ⟨x, hx⟩).val))‖ ≤
      sg / Γ * S.rho (jref ⟨x, hx⟩).1 := by
    have he : sg * S.rho (jref ⟨x, hx⟩).1 / Γ = sg / Γ * S.rho (jref ⟨x, hx⟩).1 := by ring
    have hq' : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = y := hq
    rw [hq', h.2.2, ← he]
    exact hxy
  have hloc := S.slim_localization_BPS hΔ1 (jref ⟨x, hx⟩) h.1 h.2.1 hR hb
  exact ⟨q, hloc.1, hloc.2, hq⟩

/-- **(COV)** coverage of the coordinate ball by core points of `S̃₂`. -/
theorem slimTable_COV_BPS {Γ sg : ℝ} (hΔ1 : 1 ≤ Δ) (h2sg : 2 * sg / Γ ≤ 1 / 100)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1) ∧
      |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ u : ℝ,
      ‖u - S.slimEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
      ∃ q : W.pieceInterior ⊤, (dist q (jref ⟨x, hx⟩).1 < 1000000 * Δ * S.rho (jref ⟨x, hx⟩).1 ∧
          |S.slimEta_BIF (jref ⟨x, hx⟩).1 q| ≤ 8 * (100000 * Δ)) ∧
        dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 2 * S.rho (jref ⟨x, hx⟩).1 ∧
        S.slimEta_BIF (jref ⟨x, hx⟩).1 q = u ∧
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
          (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by
  intro x hx u hu
  have h := hpre ⟨x, hx⟩
  rw [Real.norm_eq_abs] at hu
  exact S.slim_coverage_BPS hΔ1 (jref ⟨x, hx⟩) h.2.1 (hu.trans h2sg)

/-- **(PRE)** every preimage of a cloud point lies in the core-`8` ∩ `D_a` of its reference. -/
theorem slimTable_PRE_BPS (hΔ0 : 0 < Δ)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1) ∧
      |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
      (dist q (jref ⟨x, hx⟩).1 < 1000000 * Δ * S.rho (jref ⟨x, hx⟩).1 ∧
          |S.slimEta_BIF (jref ⟨x, hx⟩).1 q| ≤ 8 * (100000 * Δ)) ∧
        dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 2 * S.rho (jref ⟨x, hx⟩).1 ∧
        S.slimEta_BIF (jref ⟨x, hx⟩).1 q = S.slimEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩) := by
  intro x hx q hq
  have h := hpre ⟨x, hx⟩
  exact (S.slim_preimage_core_BPS hΔ0 (jref ⟨x, hx⟩) h.1 (by linarith only [h.2.1, hΔ0])
    (hq.trans h.2.2.symm)).1

/-- **(MCb)** radius comparability on `S̃₂` for every selection of preimages. -/
theorem slimTable_MCb_BPS {sg : ℝ} (hsg : 0 ≤ sg) (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
      (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel x).val) = x) →
      ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
      ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
      ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
        dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
        sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
          sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x)) := by
  intro sel hsel L' hL' hLsg x hx y hy hd
  have hpx : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel x).val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by rw [hsel x hx]; exact hx
  have hpy : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel y).val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by rw [hsel y hy]; exact hy
  have hd' : dist ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel y).val))
      ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel x).val)) ≤
      L' * max (sg * S.rho (sel y).val) (sg * S.rho (sel x).val) := by
    rw [hsel y hy, hsel x hx]
    exact hd
  have hr := S.slim_scale_ratio_BPS hΛ hΔ1 hΛΔ hV hβ1 hb hsg hL' hLsg hpx hpy hd'
  have h1 := mul_le_mul_of_nonneg_left hr.1 hsg
  have h2 := mul_le_mul_of_nonneg_left hr.2 hsg
  have e1 : sg * S.rho (sel x).val / (5 / 3) = sg * (3 / 5 * S.rho (sel x).val) := by ring
  have e2 : 5 / 3 * (sg * S.rho (sel x).val) = sg * (5 / 3 * S.rho (sel x).val) := by ring
  exact ⟨by rw [e1]; exact h1, by rw [e2]; exact h2⟩

/-- **(PP-int)** small-marker kernel at every preimage. -/
theorem slimTable_PP_BPS (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 1000000 * Δ * S.rho (jref x).1) ∧
      |S.slimEta_BIF (jref x).1 (pre x)| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) :
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
        ∀ v : ℝ, ((fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.slimStageModel_BPS sgnf cf zsgnf zcf (jref ⟨x, hx⟩).1)
          (S.slimEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0 := by
  intro x hx q hq m hm v
  have h := hpre ⟨x, hx⟩
  have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨x, hx⟩).2
  rw [S.slimStageModel_comp_BPS sgnf cf zsgnf zcf hj]
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  exact S.slim_pp_point_BPS hΔ1 hΛ hΛΔ hV hβ1 hb _ _ _ _
    (fun j w => S.slimModelOf_circle_BPS _ _ _ _ _ j w)
    (fun j w => S.slimModelOf_edge_BPS _ _ _ _ _ j w)
    (fun j w => S.slimModelOf_slim_BPS _ _ _ _ _ j w) h.1 (by linarith only [h.2.1, hΔ0])
    (hq.trans h.2.2.symm) m hm _ v

/-- **(SB-int)** the whole small block of the model vanishes. -/
theorem slimTable_SB_BPS (hΔ0 : 0 < Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ a ∈ S.stageCentres_BIF 2, ∀ m : S.MarkerIdx_BAUGC,
      S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 2 * S.rho a →
      ∀ u, (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.slimStageModel_BPS sgnf cf zsgnf zcf a) u (S.markerTag_BAUGC m) = 0 := by
  intro a ha m hm u
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.centres) := ha
  rw [S.slimStageModel_comp_BPS sgnf cf zsgnf zcf ha']
  exact S.slim_small_block_BPS hΔ0 hΛ hΛΔ _ _ _ _
    (fun j w => S.slimModelOf_circle_BPS _ _ _ _ _ j w)
    (fun j w => S.slimModelOf_edge_BPS _ _ _ _ _ j w)
    (fun j w => S.slimModelOf_slim_BPS _ _ _ _ _ j w) m
    (show S.rho (S.markerCentre_BAUGC m) ≤ 99 / 100 * S.rho a from hm) u

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
