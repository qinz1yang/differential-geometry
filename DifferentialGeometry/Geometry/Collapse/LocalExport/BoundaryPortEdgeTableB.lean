import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeClausesB

/-!
# PORT target: the interior edge stage table, clause layer B (lane S-PORT-EDGE)

The clauses (PP-int) and (SB-int) of `port_edge_interior_table_BAUGP` in the frozen wording for the
chosen data of `BoundaryPortEdgeTableA` (model `Kint a ∘ Ψ a = id ∘ edgeStageModel_BPE`, core
preimages `pre` with references `jref`): `edgeTable_PP_BPE` (small-marker kernel at every preimage)
and `edgeTable_SB_BPE` (whole small block of the model). Consumer of `BoundaryPortEdgeClausesB`;
twin of `slimTable_PP_BPS`, `slimTable_SB_BPS`. The clauses (FM*-int), (ZB*-int) and the assembly of
the frozen theorem follow in `BoundaryPortEdgeTableFinal`.
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM) (sgnf cf : S.EdgeIdx_BAUGD → S.IntTag_BAUGA → ℝ)
  (jref : (actualSlotsV2_BAUGD S).stageCloud 1 → S.EdgeIdx_BAUGD)
  (pre : (actualSlotsV2_BAUGD S).stageCloud 1 → W.pieceInterior ⊤)

/-- **(PP-int)** small-marker kernel at every preimage. -/
theorem edgeTable_PP_BPE (hΔ1 : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hpre : ∀ x, (letI := inducedMetricSpace S.completion.metric
        dist (pre x) (jref x).1 < 100 * Δ * S.rho (jref x).1) ∧
      |S.edgeEta_BIF (jref x).1 (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) :
    ∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ q : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = x →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
        ∀ v : ℝ, ((fderiv ℝ
            (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
              S.edgeStageModel_BPE sgnf cf (jref ⟨x, hx⟩).1)
          (S.edgeEta_BIF (jref ⟨x, hx⟩).1 (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0 := by
  intro x hx q hq m hm v
  have h := hpre ⟨x, hx⟩
  have hj := (Set.Finite.mem_toFinset _).mp (jref ⟨x, hx⟩).2
  rw [S.edgeStageModel_comp_BPE sgnf cf hj]
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  exact S.edge_pp_point_BPE hΔ1 hΛ hΛΔ hV hβ1 hb _ _ _ h.1 (by linarith only [h.2.1, hΔ0])
    (by linarith only [h.2.2.1, hΔ0]) (hq.trans h.2.2.2.symm) m hm _ v

/-- **(SB-int)** the whole small block of the model vanishes. -/
theorem edgeTable_SB_BPE (hΔ0 : 0 < Δ) (hΛ : 0 ≤ Λ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ a ∈ S.stageCentres_BIF 1, ∀ m : S.MarkerIdx_BAUGC,
      S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 1 * S.rho a →
      ∀ u, (⇑(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))) ∘
        S.edgeStageModel_BPE sgnf cf a) u (S.markerTag_BAUGC m) = 0 := by
  intro a ha m hm u
  have ha' : a ∈ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.centres) := ha
  rw [S.edgeStageModel_comp_BPE sgnf cf ha']
  exact S.edge_small_block_BPE hΔ0 hΛ hΛΔ _ _ _ m
    (show S.rho (S.markerCentre_BAUGC m) ≤ 99 / 100 * S.rho a from hm) u

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
