import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleClausesB

/-!
# PORT target: the interior circle stage table, clause layer (lane O-PORT-A)

The clauses (M), (OWN), (Q), (TG), (SEL), (LOC), (COV), (PRE), (PP-int), (SB-int), (SCL) of
`port_circle_interior_table_BAUGP` (PortTargets v3.1,
`docs/geometrization/chapter14/evidence/boundary/PortTargets-v3.1.lean.txt`) for the chosen data on
the ACTUAL slot `actualSlotsV2_BAUGD S` (stage `0`, `f(q) = π₀F_∂(q) = F_∂(q)`, `q ∈ W°`, distances
`d_ĝ`): model `Kint a ∘ Ψ a` with `Kint a = id` and `Ψ a = circleStageModel_BPC` (TCP05's model
graph of the circle centre `a` with the chosen comparison data `Acf a, …, cτf a`, pruned by CFS27:
`circleModelOf_BPC`), own coordinate `Pc a = circleStageOwn_BPC` (the vector part of the own block),
core preimages `pre` with references `jref` (threshold-`7` cores), radius preimages `rpre`. The
clause lemmas `circleTable_*_BPC` state each clause in the frozen wording; boundary inputs:
`circle_row_supply_BPC` (TCP05, `BoundaryPortCircleTransport`), the pointwise clauses
(`BoundaryPortCircleClauses`) and the marker layer (`BoundaryPortCircleClausesB`). Twin of the edge
lane's `BoundaryPortEdgeTableA` / `BoundaryPortEdgeTableB`.
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

section GenericOwn

variable {τ : Type*} [Fintype τ]

/-- The vector part of the block `t`, a `1`-Lipschitz map on the block space. -/
def blockOwnCLM_BPC (t : τ) : BlockSpace (fun _ : τ => ℝ²) →L[ℝ] ℝ² :=
  (WithLp.fstL 2 ℝ ℝ² ℝ).comp (PiLp.proj 2 (fun _ : τ => WithLp 2 (ℝ² × ℝ)) t)

omit [Fintype τ] in
theorem blockOwnCLM_apply_BPC (t : τ) (z : BlockSpace (fun _ : τ => ℝ²)) :
    blockOwnCLM_BPC t z = (z t).fst :=
  rfl

theorem norm_blockOwnCLM_apply_le_BPC (t : τ) (z : BlockSpace (fun _ : τ => ℝ²)) :
    ‖blockOwnCLM_BPC t z‖ ≤ ‖z‖ := by
  rw [blockOwnCLM_apply_BPC]
  exact (WithLp.norm_fst_le _ _).trans (PiLp.norm_apply_le _ _)

end GenericOwn

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM) (Acf : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ²)
  (ccf : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ²)
  (A1f : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ)
  (c1f : S.CircleIdx_BAUGD → S.IntTag_BAUGA → ℝ) (Bτf : S.CircleIdx_BAUGD → ℝ² →L[ℝ] ℝ)
  (cτf : S.CircleIdx_BAUGD → ℝ)

open Classical in
/-- **The stage-`0` model** `Ψ a`: TCP05's pruned model `circleModelOf_BPC` of the circle centre
`a` with the chosen comparison data (zero off the centres). -/
def circleStageModel_BPC (a : W.pieceInterior ⊤) :
    ℝ² → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : a ∈ S.family.circle.centres then
    S.circleModelOf_BPC ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩
      (Acf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩) (ccf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)
      (A1f ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩) (c1f ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)
      (Bτf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩) (cτf ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩)
  else 0

/-- At a circle centre, `Kint a ∘ Ψ a = id ∘ Ψ a` is the pruned TCP05 model of `a`. -/
theorem circleStageModel_comp_BPC {a : W.pieceInterior ⊤}
    (ha : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres)) :
    ⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a =
      S.circleModelOf_BPC ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩
        (Acf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) (ccf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩)
        (A1f ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) (c1f ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩)
        (Bτf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩)
        (cτf ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) := by
  unfold circleStageModel_BPC
  rw [dite_eq_left ha]
  rfl

open Classical in
/-- **The own coordinate** `Pc a`: the vector part of the own circle block of `a` (zero off the
centres). -/
def circleStageOwn_BPC (a : W.pieceInterior ⊤) :
    BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ² :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if h : a ∈ S.family.circle.centres then
    blockOwnCLM_BPC (.inl ⟨a, (Set.Finite.mem_toFinset _).mpr h⟩) else 0

theorem circleStageOwn_of_mem_BPC {a : W.pieceInterior ⊤}
    (ha : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres)) :
    S.circleStageOwn_BPC a = blockOwnCLM_BPC (.inl ⟨a, (Set.Finite.mem_toFinset _).mpr ha⟩) := by
  unfold circleStageOwn_BPC
  rw [dite_eq_left ha]

/-- **(M)** global `C²` bounds of `Kint a ∘ Ψ a`. -/
theorem circleTable_M_BPC
    (hM : ∀ i : S.CircleIdx_BAUGD,
      ContDiff ℝ ∞ (S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i) (cτf i)) ∧
      ∀ u, ‖fderiv ℝ (S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i) (cτf i)) u‖ ≤
          tcpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i)
          (cτf i))) u‖ ≤ tcpGraphConst) :
    ∀ a ∈ S.stageCentres_BIF 0,
      ContDiff ℝ 2 (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) ∧ ∀ u,
        ‖fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) u‖ ≤ tcpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (⇑(ContinuousLinearMap.id ℝ
          (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a)) u‖ ≤ tcpGraphConst := by
  intro a ha
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres) := ha
  rw [S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf ha']
  exact ⟨(hM _).1.of_le (by simp), (hM _).2⟩

/-- The own block of the interior formula at a threshold-`8` core point: `ρ_a⁻¹F_int(x)_a` has
vector part `η_a(x)`. -/
theorem own_block_core_BPC (i : S.CircleIdx_BAUGD) {x : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist x i.1 < 200 * S.rho i.1)
    (hη : ‖S.circleEta_BIF i.1 x‖ ≤ 8) :
    blockOwnCLM_BPC (.inl i) ((S.rho i.1)⁻¹ • S.interiorMapOn_BAUGA x) = S.circleEta_BIF i.1 x := by
  have hra := S.rho_pos i.1
  rw [blockOwnCLM_apply_BPC, PiLp.smul_apply, S.interiorMapOn_circle_block_BPC i x,
    S.circle_cutoff_eq_one_BPC i hd hη]
  change (S.rho i.1)⁻¹ • ((S.rho i.1 * 1) • S.circleEta_BIF i.1 x) = _
  rw [smul_smul, mul_one, inv_mul_cancel₀ hra.ne', one_smul]

/-- **(OWN)** the own coordinate is a `1`-Lipschitz left inverse of the model, exact on the core. -/
theorem circleTable_OWN_BPC
    (hown : ∀ (i : S.CircleIdx_BAUGD) (u : ℝ²),
      S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i) (cτf i) u (.inl i) =
        WithLp.toLp 2 (u, 1)) :
    letI := inducedMetricSpace S.completion.metric
    ∀ a ∈ S.stageCentres_BIF 0, (∀ z, ‖S.circleStageOwn_BPC a z‖ ≤ ‖z‖) ∧
      (∀ u, S.circleStageOwn_BPC a ((⇑(ContinuousLinearMap.id ℝ
        (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) u) = u) ∧
      ∀ x : W.pieceInterior ⊤, (dist x a < 200 * S.rho a ∧ ‖S.circleEta_BIF a x‖ ≤ 8) →
        S.circleStageOwn_BPC a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0)
          (S.interiorMapOn_BAUGA x)) = S.circleEta_BIF a x := by
  intro a ha
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres) := ha
  rw [S.circleStageOwn_of_mem_BPC ha', S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf ha']
  refine ⟨fun z => norm_blockOwnCLM_apply_le_BPC _ z, fun u => ?_, fun x hx => ?_⟩
  · rw [blockOwnCLM_apply_BPC, hown]
    rfl
  · rw [S.blockRestrict_stageTagsV2_zero_BPC]
    exact S.own_block_core_BPC ⟨a, (Set.Finite.mem_toFinset _).mpr ha'⟩ hx.1 hx.2

/-- **(Q)** the model takes values in `Q₁^∂` (stage `0`: all interior tags). -/
theorem circleTable_Q_BPC :
    ∀ a ∈ S.stageCentres_BIF 0, ∀ u,
      blockRestrict (S.stageTagsV2_BAUGD 0) ((⇑(ContinuousLinearMap.id ℝ
        (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) u) =
        (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
          S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) u :=
  fun _ _ _ => S.blockRestrict_stageTagsV2_zero_BPC _

/-- **(TG)** value and derivative comparison on the threshold-`8` reference core. -/
theorem circleTable_TG_BPC {eg : ℝ}
    (hTG : ∀ i : S.CircleIdx_BAUGD, ∀ x : W.pieceInterior ⊤,
      (letI := inducedMetricSpace S.completion.metric
       dist x i.1 < 200 * S.rho i.1) → ‖S.circleEta_BIF i.1 x‖ ≤ 8 →
      ‖(S.rho i.1)⁻¹ • S.interiorMapOn_BAUGA x -
          S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i) (cτf i)
            (S.circleEta_BIF i.1 x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) S.interiorMapOn_BAUGA x w -
            fderiv ℝ (S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i) (cτf i))
              (S.circleEta_BIF i.1 x) (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF i.1) x w)‖ ≤
          eg * Real.sqrt ((S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w)) :
    letI := inducedMetricSpace S.completion.metric
    ∀ a ∈ S.stageCentres_BIF 0, ∀ x : W.pieceInterior ⊤,
      (dist x a < 200 * S.rho a ∧ ‖S.circleEta_BIF a x‖ ≤ 8) →
      ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA x) -
          (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) (S.circleEta_BIF a x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA y)) x w -
          fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
            S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) (S.circleEta_BIF a x)
            (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a) x w)‖ ≤
          eg * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w) := by
  intro a ha x hx
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres) := ha
  simp only [S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf ha',
    S.blockRestrict_stageTagsV2_zero_BPC]
  exact hTG ⟨a, (Set.Finite.mem_toFinset _).mpr ha'⟩ x hx.1 hx.2

/-- **(SCL)** the scale block of the derivative of the model is zero. -/
theorem circleTable_SCL_BPC
    (hscl : ∀ (i : S.CircleIdx_BAUGD) (u v : ℝ²),
      ((fderiv ℝ (S.circleModelOf_BPC i (Acf i) (ccf i) (A1f i) (c1f i) (Bτf i) (cτf i)) u v)
        S.scaleTag_BAUGA).snd = 0) :
    ∀ a ∈ S.stageCentres_BIF 0, ∀ u v : ℝ²,
      ((fderiv ℝ (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) u v) S.scaleTag_BAUGA).snd = 0 := by
  intro a ha u v
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres) := ha
  rw [S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf ha']
  exact hscl _ u v

/-- **(SB-int)** the whole small block of the model vanishes (CFS27's pruning at `ρ(a)/2`). -/
theorem circleTable_SB_BPC :
    ∀ a ∈ S.stageCentres_BIF 0, ∀ m : S.MarkerIdx_BAUGC,
      S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 0 * S.rho a →
      ∀ u, (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf a) u (S.markerTag_BAUGC m) = 0 := by
  intro a ha m hm u
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres) := ha
  rw [S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf ha']
  have hm' : S.rho (S.markerCentre_BAUGC m) ≤ S.rho a / 2 := by
    have h : smallBlockFactor_BAUGC 0 = 1 / 2 := rfl
    rw [h] at hm
    linarith only [hm]
  exact S.circleModelOf_marker_BPC _ _ _ _ _ _ _ m hm' u

variable (jref : (actualSlotsV2_BAUGD S).stageCloud 0 → S.CircleIdx_BAUGD)
  (pre : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤)

/-- **(SEL)**, model preimages: references in the stage centres, core-`7` preimages in `D_a`. -/
theorem circleTable_SEL_BPC
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 200 * S.rho (jref x).1) ∧
      ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x, (jref x).1 ∈ S.stageCentres_BIF 0 ∧ (dist (pre x) (jref x).1 < 200 * S.rho (jref x).1 ∧
        ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7) ∧
      dist (pre x) (jref x).1 < stageDomain_BIF Δ 0 * S.rho (jref x).1 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1 := by
  intro x
  have h := hpre x
  exact ⟨(Set.Finite.mem_toFinset _).mp (jref x).2, ⟨h.1, h.2.1⟩,
    S.circle_dist_lt_ten_BPC (jref x) h.1 (by linarith only [h.2.1]), h.2.2⟩

/-- **(LOC)** FC03 localization near a cloud point. -/
theorem circleTable_LOC_BPC {Γ sg : ℝ} (hR0 : 0 ≤ sg / Γ) (hR : sg / Γ < 1 / 100)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 200 * S.rho (jref x).1) ∧
      ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
      ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0,
        ‖augIntProjCLM_BAUGC (y - x)‖ ≤ sg * S.rho (jref ⟨x, hx⟩).1 / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (jref ⟨x, hx⟩).1 < 200 * S.rho (jref ⟨x, hx⟩).1 ∧
            ‖S.circleEta_BIF (jref ⟨x, hx⟩).1 q‖ ≤ 8) ∧
          dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 0 * S.rho (jref ⟨x, hx⟩).1 ∧
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = y := by
  intro x hx y hy hxy
  obtain ⟨-, q, -, -, hq⟩ := S.exists_core_of_mem_stageCloudEnlarged_zero_BPC hy
  have h := hpre ⟨x, hx⟩
  have hb : ‖augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap q.val) - (actualSlotsV2_BAUGD S).stageProj 0
      (S.boundaryOriginalMap (pre ⟨x, hx⟩).val))‖ ≤ sg / Γ * S.rho (jref ⟨x, hx⟩).1 := by
    have he : sg * S.rho (jref ⟨x, hx⟩).1 / Γ = sg / Γ * S.rho (jref ⟨x, hx⟩).1 := by ring
    rw [hq, h.2.2, ← he]
    exact hxy
  have hloc := S.circle_localization_BPC (jref ⟨x, hx⟩) h.1 h.2.1 hR0 hR hb
  exact ⟨q, hloc.1, hloc.2, hq⟩

/-- **(COV)** coverage of the coordinate ball by core points of `S̃₀`. -/
theorem circleTable_COV_BPC {Γ sg : ℝ} (h2sg : 2 * sg / Γ ≤ 1)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 200 * S.rho (jref x).1) ∧
      ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ u : ℝ²,
      ‖u - S.circleEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩)‖ ≤ 2 * sg / Γ →
      ∃ q : W.pieceInterior ⊤, (dist q (jref ⟨x, hx⟩).1 < 200 * S.rho (jref ⟨x, hx⟩).1 ∧
          ‖S.circleEta_BIF (jref ⟨x, hx⟩).1 q‖ ≤ 8) ∧
        dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 0 * S.rho (jref ⟨x, hx⟩).1 ∧
        S.circleEta_BIF (jref ⟨x, hx⟩).1 q = u ∧
        (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
          (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 := by
  intro x hx u hu
  have h := hpre ⟨x, hx⟩
  exact S.circle_coverage_BPC (jref ⟨x, hx⟩) h.2.1 (hu.trans h2sg)

/-- **(PRE)** every preimage of a cloud point lies in the core-`8` ∩ `D_a` of its reference, with
the reference coordinate of the model preimage. -/
theorem circleTable_PRE_BPC
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 200 * S.rho (jref x).1) ∧
      ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) :
    letI := inducedMetricSpace S.completion.metric
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
      (dist q (jref ⟨x, hx⟩).1 < 200 * S.rho (jref ⟨x, hx⟩).1 ∧
          ‖S.circleEta_BIF (jref ⟨x, hx⟩).1 q‖ ≤ 8) ∧
        dist q (jref ⟨x, hx⟩).1 < stageDomain_BIF Δ 0 * S.rho (jref ⟨x, hx⟩).1 ∧
        S.circleEta_BIF (jref ⟨x, hx⟩).1 q = S.circleEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩) := by
  intro x hx q hq
  have h := hpre ⟨x, hx⟩
  exact S.circle_preimage_core_BPC (jref ⟨x, hx⟩) h.1 (by linarith only [h.2.1])
    (hq.trans h.2.2.symm)

/-- **(PP-int)** small-marker kernel at every preimage: a marker chart with `ρ(c_m) < ρ(q)/5` at a
preimage `q` of a cloud point is deleted by the pruning of the reference, so the marker of the
derivative of the model vanishes. -/
theorem circleTable_PP_BPC (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hΔ1 : 1 ≤ Δ)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 200 * S.rho (jref x).1) ∧
      ‖S.circleEta_BIF (jref x).1 (pre x)‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) :
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
        ∀ v : ℝ², ((fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
              S.circleStageModel_BPC Acf ccf A1f c1f Bτf cτf (jref ⟨x, hx⟩).1)
          (S.circleEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro x hx q hq m hm v
  have h := hpre ⟨x, hx⟩
  have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨x, hx⟩).2
  have hpc := (S.circle_preimage_core_BPC (jref ⟨x, hx⟩) h.1 (by linarith only [h.2.1])
    (hq.trans h.2.2.symm)).2.1
  rw [stageDomain_zero_BPC] at hpc
  have hra := S.rho_pos (jref ⟨x, hx⟩).1
  have hqa := (scale_mem_of_dist_lt_KC (ρ := fun x : W.pieceInterior ⊤ => S.rho x)
    S.family.lipschitz_scale hΛ hra hpc (by nlinarith only [hΛΔ, hΛ, hΔ1])).2
  change S.rho q.val ≤ 5 / 4 * S.rho (jref ⟨x, hx⟩).1 at hqa
  have hsmall : S.rho (S.markerCentre_BAUGC m) ≤ S.rho (jref ⟨x, hx⟩).1 / 2 := by
    have h1 : S.rho q.val / 5 ≤ S.rho (jref ⟨x, hx⟩).1 / 2 := by linarith only [hqa, hra]
    exact (hm.trans_le h1).le
  rw [S.circleStageModel_comp_BPC Acf ccf A1f c1f Bτf cτf hj]
  rw [fderiv_block_eq_zero_of_block_zero_BPS _ _
    (S.circleModelOf_marker_BPC _ _ _ _ _ _ _ m hsmall) _ v]
  rfl

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
