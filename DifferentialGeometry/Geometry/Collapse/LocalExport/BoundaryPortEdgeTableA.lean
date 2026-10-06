import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeTransport

/-!
# PORT target: the interior edge stage table, clause layer A (lane S-PORT-EDGE)

The clauses (M), (OWN), (Q), (TG), (SEL), (LOC), (COV), (PRE), (MCb) of
`port_edge_interior_table_BAUGP` (PortTargets v3.1,
`docs/geometrization/chapter14/evidence/boundary/PortTargets-v3.1.lean.txt`) for the chosen data
on the ACTUAL slot `actualSlotsV2_BAUGD S` (stage `1`, `f(q) = π₁F_∂(q)`, `q ∈ W°`, distances
`d_ĝ`): model `Kint a ∘ Ψ a` with `Kint a = id` and `Ψ a = edgeStageModel_BPE` (EGP06's model
`edgeModelOf_BPE` of the `edgeB` centre `a` with chosen signs `sgnf a` and translations `cf a`),
own coordinate `Pc a = edgeStageOwn_BPE`, core preimages `pre` with references `jref`
(threshold-`7` cores), radius preimages `rpre`. The clause lemmas `edgeTable_*_BPE` state each
clause for the chosen data; boundary inputs: `edge_row_supply_BPE` (EGP06,
`BoundaryPortEdgeTransport`), the pointwise clauses (`BoundaryPortEdgeClauses`) and the marker
layer (`BoundaryPortEdgeMarkers`).
Twin of lane B-PORT-SLIMb's `BoundaryPortSlimTable` (the clauses (PP-int), (SB-int), (FM*-int),
(ZB*-int) follow in `BoundaryPortEdgeTableB`).
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
def blockAxisCLM_BPE (t : τ) : BlockSpace (fun _ : τ => ℝ²) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun z => (z t).fst 0
      map_add' := fun z w => by simp
      map_smul' := fun r z => by simp } 1 (fun z => by
        rw [one_mul]
        calc ‖(z t).fst 0‖ ≤ ‖(z t).fst‖ := PiLp.norm_apply_le _ 0
          _ ≤ ‖z t‖ := WithLp.norm_fst_le _ _
          _ ≤ ‖z‖ := PiLp.norm_apply_le _ _)

theorem blockAxisCLM_apply_BPE (t : τ) (z : BlockSpace (fun _ : τ => ℝ²)) :
    blockAxisCLM_BPE t z = (z t).fst 0 :=
  rfl

theorem norm_blockAxisCLM_apply_le_BPE (t : τ) (z : BlockSpace (fun _ : τ => ℝ²)) :
    ‖blockAxisCLM_BPE t z‖ ≤ ‖z‖ := by
  rw [blockAxisCLM_apply_BPE]
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
  θ W g δn n B oM) (sgnf cf : S.EdgeIdx_BAUGD → S.IntTag_BAUGA → ℝ)

/-- The `edgeB` centres are the stage-`1` centres. -/
theorem stageCentres_one_BPE :
    S.stageCentres_BIF 1 = (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres) :=
  rfl

open Classical in
/-- **The stage-`1` model** `Ψ a`: EGP06's model `edgeModelOf_BPE` of the `edgeB` centre `a` with
the chosen signs and translations (zero off the centres). -/
def edgeStageModel_BPE (a : W.pieceInterior ⊤) : ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : a ∈ S.family.edgeB.centres then
    S.edgeModelOf_BPE ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩
      (sgnf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩) (cf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)
  else 0

/-- At an `edgeB` centre, `Kint a ∘ Ψ a = id ∘ Ψ a` is EGP06's model of `a`. -/
theorem edgeStageModel_comp_BPE {a : W.pieceInterior ⊤}
    (ha : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres)) :
    ⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.edgeStageModel_BPE sgnf cf a =
      S.edgeModelOf_BPE ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩
        (sgnf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩)
        (cf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) := by
  unfold edgeStageModel_BPE
  rw [dite_eq_left ha]
  rfl

open Classical in
/-- **The own coordinate** `Pc a`: the first axis coordinate of the own block of `a` (zero off the
centres). -/
def edgeStageOwn_BPE (a : W.pieceInterior ⊤) : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : a ∈ S.family.edgeB.centres then
    blockAxisCLM_BPE (.inr (.inr (.inl ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩))) else 0

theorem edgeStageOwn_of_mem_BPE {a : W.pieceInterior ⊤}
    (ha : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres)) :
    S.edgeStageOwn_BPE a =
      blockAxisCLM_BPE (.inr (.inr (.inl ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩))) := by
  unfold edgeStageOwn_BPE
  rw [dite_eq_left ha]

/-- A kept interior block of `f(q) = π₁F_∂(q)` is the interior formula's block. -/
theorem blockRestrict_interiorMapOn_apply_BPE (q : W.pieceInterior ⊤) (t : S.IntTag_BAUGA) :
    blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA q) t =
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) (Sum.inl t) := by
  rw [← S.augIntProj_stageOne_BPE q, augIntProjCLM_apply_BAUGC]

/-- The full edge block of the interior formula: `F_int(q)_i = (ρ_i·1 η_i(q), ρ_i·1)` where
`ζ_i(q) = 1`. -/
theorem interiorMapOn_edge_block_BPE (i : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.cutoff_BAUGA i.1 q) = 1) :
    blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA q) (.inr (.inr (.inl i))) =
      WithLp.toLp 2 ((S.rho i.1 * 1) • planeAxis (S.edgeEta_BIF i.1 q), S.rho i.1 * 1) := by
  rw [S.blockRestrict_interiorMapOn_apply_BPE q, S.edgeBlock_stageOne_BPE i q, hq]

/-- **(M)** global `C²` bounds of `Kint a ∘ Ψ a`. -/
theorem edgeTable_M_BPE
    (hM : ∀ i : S.EdgeIdx_BAUGD, ContDiff ℝ ∞ (S.edgeModelOf_BPE i (sgnf i) (cf i)) ∧
      ∀ u, ‖fderiv ℝ (S.edgeModelOf_BPE i (sgnf i) (cf i)) u‖ ≤ egpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (S.edgeModelOf_BPE i (sgnf i) (cf i))) u‖ ≤ egpGraphConst) :
    ∀ a ∈ S.stageCentres_BIF 1,
      ContDiff ℝ 2 (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.edgeStageModel_BPE sgnf cf a) ∧ ∀ u,
        ‖fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.edgeStageModel_BPE sgnf cf a) u‖ ≤ egpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (⇑(ContinuousLinearMap.id ℝ
          (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘ S.edgeStageModel_BPE sgnf cf a)) u‖ ≤
            egpGraphConst := by
  intro a ha
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres) := ha
  rw [S.edgeStageModel_comp_BPE sgnf cf ha']
  exact ⟨(hM _).1.of_le (by simp), (hM _).2⟩

/-- **(OWN)** the own coordinate is a `1`-Lipschitz left inverse of the model, exact on the core. -/
theorem edgeTable_OWN_BPE (hΔ : 0 < Δ) :
    letI := inducedMetricSpace S.completion.metric
    ∀ a ∈ S.stageCentres_BIF 1, (∀ z, ‖S.edgeStageOwn_BPE a z‖ ≤ ‖z‖) ∧
      (∀ u, S.edgeStageOwn_BPE a ((⇑(ContinuousLinearMap.id ℝ
        (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘ S.edgeStageModel_BPE sgnf cf a) u) = u) ∧
      ∀ x : W.pieceInterior ⊤, (dist x a < 100 * Δ * S.rho a ∧ |S.edgeEta_BIF a x| ≤ 8 * Δ ∧
          S.edgeHeightRaw x ≤ 8 * Δ) →
        S.edgeStageOwn_BPE a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1)
          (S.interiorMapOn_BAUGA x)) = S.edgeEta_BIF a x := by
  intro a ha
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres) := ha
  rw [S.edgeStageOwn_of_mem_BPE ha', S.edgeStageModel_comp_BPE sgnf cf ha']
  refine ⟨fun z => norm_blockAxisCLM_apply_le_BPE _ z, fun u => ?_, fun x hx => ?_⟩
  · rw [blockAxisCLM_apply_BPE, S.edgeModelOf_own_BPE]
    simp [planeAxis_apply]
  · have hc := S.edge_cutoff_eq_one_BPE hΔ ⟨a, (Set.Finite.mem_toFinset _).mpr ha'⟩ hx.1 hx.2.1
      hx.2.2
    rw [blockAxisCLM_apply_BPE, PiLp.smul_apply, S.interiorMapOn_edge_block_BPE _ hc]
    have hra := S.rho_pos a
    have hk : (S.rho a)⁻¹ * (S.rho a * S.edgeEta_BIF a x) = S.edgeEta_BIF a x := by
      rw [← mul_assoc, inv_mul_cancel₀ hra.ne', one_mul]
    simpa [planeAxis_apply] using hk

/-- **(Q)** the model takes values in `Q₂^∂`. -/
theorem edgeTable_Q_BPE :
    ∀ a ∈ S.stageCentres_BIF 1, ∀ u,
      blockRestrict (S.stageTagsV2_BAUGD 1) ((⇑(ContinuousLinearMap.id ℝ
        (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘ S.edgeStageModel_BPE sgnf cf a) u) =
        (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.edgeStageModel_BPE sgnf cf a) u := by
  intro a ha u
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres) := ha
  rw [S.edgeStageModel_comp_BPE sgnf cf ha']
  exact S.edgeModelOf_blockRestrict_BPE _ _ _ u

/-- **(TG)** value and derivative comparison on the threshold-`8` reference core. -/
theorem edgeTable_TG_BPE {eg : ℝ}
    (hTG : ∀ i : S.EdgeIdx_BAUGD, ∀ x : W.pieceInterior ⊤,
      (letI := inducedMetricSpace S.completion.metric
       dist x i.1 < 100 * Δ * S.rho i.1) →
      |S.edgeEta_BIF i.1 x| ≤ 8 * Δ → S.edgeHeightRaw x ≤ 8 * Δ →
      ‖(S.rho i.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) -
        S.edgeModelOf_BPE i (sgnf i) (cf i) (S.edgeEta_BIF i.1 x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
          fderiv ℝ (S.edgeModelOf_BPE i (sgnf i) (cf i)) (S.edgeEta_BIF i.1 x)
            (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF i.1) x w)‖ ≤
          eg * Real.sqrt ((S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w)) :
    letI := inducedMetricSpace S.completion.metric
    ∀ a ∈ S.stageCentres_BIF 1, ∀ x : W.pieceInterior ⊤,
      (dist x a < 100 * Δ * S.rho a ∧ |S.edgeEta_BIF a x| ≤ 8 * Δ ∧ S.edgeHeightRaw x ≤ 8 * Δ) →
      ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) -
          (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.edgeStageModel_BPE sgnf cf a) (S.edgeEta_BIF a x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
          fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.edgeStageModel_BPE sgnf cf a) (S.edgeEta_BIF a x)
            (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF a) x w)‖ ≤
          eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w) := by
  intro a ha x hx
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres) := ha
  simp only [S.edgeStageModel_comp_BPE sgnf cf ha']
  exact hTG ⟨a, (Set.Finite.mem_toFinset _).mpr ha'⟩ x hx.1 hx.2.1 hx.2.2

variable (jref : (actualSlotsV2_BAUGD S).stageCloud 1 → S.EdgeIdx_BAUGD)
  (pre : (actualSlotsV2_BAUGD S).stageCloud 1 → W.pieceInterior ⊤)
  (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 → W.pieceInterior ⊤)

/-- **(SEL)**, model preimages: references in the stage centres, core-`7` preimages in `D_a`. -/
theorem edgeTable_SEL_BPE (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1) ∧
      |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x, (jref x).1 ∈ S.stageCentres_BIF 1 ∧ (dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1 ∧
        |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ) ∧
      dist (pre x) (jref x).1 < stageDomain_BIF Δ 1 * S.rho (jref x).1 ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1 := by
  intro x
  have h := hpre x
  exact ⟨(Set.Finite.mem_toFinset _).mp (jref x).2, ⟨h.1, h.2.1, h.2.2.1⟩,
    S.edge_core_dist_lt_BPE hΛ hΔ0 hμ hτ hΔΛ (jref x) h.1 (by linarith only [h.2.1, hΔ0])
      (by linarith only [h.2.2.1, hΔ0]), h.2.2.2⟩

/-- **(LOC)** FC03 localization near a cloud point. -/
theorem edgeTable_LOC_BPE {Γ sg : ℝ} (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hR : sg / Γ < 1 / 100)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1) ∧
      |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
      ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
        ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (jref ⟨x, hx⟩).1 / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (jref ⟨x, hx⟩).1 < 100 * Δ * S.rho (jref ⟨x, hx⟩).1 ∧
            |S.edgeEta_BIF (jref ⟨x, hx⟩).1 q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
          dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 1 * S.rho (jref ⟨x, hx⟩).1 ∧
          (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = y := by
  intro x hx y hy hxy
  obtain ⟨j', q, -, -, htq, hq⟩ := S.exists_core_of_mem_stageCloudEnlarged_one_BPE hy
  have h := hpre ⟨x, hx⟩
  have hb : ‖augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 1
      (S.boundaryOriginalMap q.val) - (actualSlotsV2_BAUGD S).stageProj 1
      (S.boundaryOriginalMap (pre ⟨x, hx⟩).val))‖ ≤ sg / Γ * S.rho (jref ⟨x, hx⟩).1 := by
    have he : sg * S.rho (jref ⟨x, hx⟩).1 / Γ = sg / Γ * S.rho (jref ⟨x, hx⟩).1 := by ring
    rw [hq, h.2.2.2, ← he]
    exact hxy
  have hloc := S.edge_localization_BPE hΛ hΔ1 hμ hτ hΔΛ (jref ⟨x, hx⟩) h.1 h.2.1 h.2.2.1 htq hR hb
  exact ⟨q, hloc.1, hloc.2, hq⟩

/-- **(COV)** coverage of the coordinate ball by core points of `S̃₁`. -/
theorem edgeTable_COV_BPE {Γ sg : ℝ} (hΔ1 : 1 ≤ Δ) (h2sg : 2 * sg / Γ ≤ 1 / 100)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1) ∧
      |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ u : ℝ,
      ‖u - S.edgeEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
      ∃ q : W.pieceInterior ⊤, (dist q (jref ⟨x, hx⟩).1 < 100 * Δ * S.rho (jref ⟨x, hx⟩).1 ∧
          |S.edgeEta_BIF (jref ⟨x, hx⟩).1 q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
        dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 1 * S.rho (jref ⟨x, hx⟩).1 ∧
        S.edgeEta_BIF (jref ⟨x, hx⟩).1 q = u ∧
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
          (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by
  intro x hx u hu
  have h := hpre ⟨x, hx⟩
  rw [Real.norm_eq_abs] at hu
  exact S.edge_coverage_BPE hΔ1 (jref ⟨x, hx⟩) h.2.1 (hu.trans h2sg)

/-- **(PRE)** every preimage of a cloud point lies in the core-`8` ∩ `D_a` of its reference. -/
theorem edgeTable_PRE_BPE (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1) ∧
      |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ q : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = x →
      (dist q (jref ⟨x, hx⟩).1 < 100 * Δ * S.rho (jref ⟨x, hx⟩).1 ∧
          |S.edgeEta_BIF (jref ⟨x, hx⟩).1 q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
        dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 1 * S.rho (jref ⟨x, hx⟩).1 ∧
        S.edgeEta_BIF (jref ⟨x, hx⟩).1 q = S.edgeEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩) := by
  intro x hx q hq
  have h := hpre ⟨x, hx⟩
  exact (S.edge_preimage_core_BPE hΛ hΔ0 hμ hτ hΔΛ (jref ⟨x, hx⟩) h.1
    (by linarith only [h.2.1, hΔ0]) (by linarith only [h.2.2.1, hΔ0]) (hq.trans h.2.2.2.symm)).1

/-- **(MCb)** radius comparability on `S̃₁` for every selection of preimages. -/
theorem edgeTable_MCb_BPE {sg : ℝ} (hsg : 0 ≤ sg) (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
      (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (sel x).val) = x) →
      ∀ L' : ℝ, 0 ≤ L' → L' * sg ≤ 1 / 5 →
      ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
      ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
        dist y x ≤ L' * max (sg * S.rho (sel y)) (sg * S.rho (sel x)) →
        sg * S.rho (sel x) / (5 / 3) ≤ sg * S.rho (sel y) ∧
          sg * S.rho (sel y) ≤ 5 / 3 * (sg * S.rho (sel x)) := by
  intro sel hsel L' hL' hLsg x hx y hy hd
  have hpx : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (sel x).val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by rw [hsel x hx]; exact hx
  have hpy : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (sel y).val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by rw [hsel y hy]; exact hy
  have hd' : dist ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (sel y).val))
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (sel x).val)) ≤
      L' * max (sg * S.rho (sel y).val) (sg * S.rho (sel x).val) := by
    rw [hsel y hy, hsel x hx]
    exact hd
  have hr := S.edge_scale_ratio_BPE hΛ hΔ1 hΛΔ hV hβ1 hb hsg hL' hLsg hpx hpy hd'
  have h1 := mul_le_mul_of_nonneg_left hr.1 hsg
  have h2 := mul_le_mul_of_nonneg_left hr.2 hsg
  have e1 : sg * S.rho (sel x).val / (5 / 3) = sg * (3 / 5 * S.rho (sel x).val) := by ring
  have e2 : 5 / 3 * (sg * S.rho (sel x).val) = sg * (5 / 3 * S.rho (sel x).val) := by ring
  exact ⟨by rw [e1]; exact h1, by rw [e2]; exact h2⟩

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
