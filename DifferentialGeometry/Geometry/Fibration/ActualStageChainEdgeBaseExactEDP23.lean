import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeMarkerConvention
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf05Edge
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeInterior

/-!
# EDP02 (B), base level: the exact marker on `B₂` and the actual base `B₂ ⊆ W₂`

Blueprint `master207B.tex`, EDP02 (B:6748–6835), the proof's first paragraph (B:6783–6790):
"every `w ∈ W₂` has an actual final preimage, (AM0) excludes a zero original marker [...]
Thus `w ∈ V_i`, and GAF05 gives the exact marker and coordinate patch." This is the base-level
exactness `v_i(w) = R_i` for EVERY `w ∈ B₂` (also outside `π₂E(X₂)`) that EDP04's last paragraph and
the bundle `EdgeBundle.Base := B₂` consume (the open input of lane S-EDP-FDC's G3 block).

On an enhanced chain `Ĉ : Gaf02ChainE L …` of a family `L : LocalChartPacketsC14`
(`π₂E = (gafStageQ … 1).starProjection ∘ E`, `W₂ = Ĉ.toChain.finalBase_BAS 1 = Θ₂(V₂⁰)`):

* `Gaf02ChainE.finalBase_preimage_EDP23`: every `w ∈ W₂` is `π₂E p` for a point `p` of an ORIGINAL
  threshold-6 edge plateau (`p ∈ B(k, 100Δρ_k)`, `|η_k p| < 6Δ`, `t p < 6Δ`): `w = Θ₂ w₀` with
  `w₀ ∈ V_k⁰`, CGP07's exhaustion of the patch gives `p` with `f₂ p = w₀`, and
  `π₂E = Θ₂ ∘ f₂` (`final_factor_BAS`).
* `Gaf02ChainE.edgeBase_marker_exact_EDP23`: `w ∈ W₂`, `v_i(w) ≥ .9R_i`, `‖u_i(w)‖ < 4Δ v_i(w)`
  (`Δ ≥ 2`) give `v_i(w) = R_i`. The preimage `p` of the previous item satisfies the hypotheses of
  `ratio_original_ge_EFC` at the index `i` (E-level, no `V`), so `p ∈ B(i, 100Δρ_i)` with
  `|η_i p| < 4.01Δ`; `t p < 6Δ` is inherited from the exhaustion, so GAF05's plateau
  (`gaf05_edge_stage_plateau_GAFD`) gives `v_i(E p) = R_i`, and `π₂` keeps the edge block.
* `Gaf02ChainE.edgeBase_EDP23` is EDP02's `B₂` written out (a set of the block space, defined by the
  `W₂`-membership and the strict ratio condition at one index; not a `Prop`);
  `edgeBase_ge_eq_base_EDP23` is the BASE-level equality of the two marker conventions
  (`> .9R_i` versus `≥ .9R_i`), `edgeBase_mem_patch_EDP23` the patch membership of GAF05
  (`w ∈ W₂ ∩ {v_i > .9R_i, ‖u_i‖ < 5.5ΔR_i}` with `v_i = R_i`, `‖u_i‖ < 4ΔR_i`), and
  `edgeBase_patch_iff_EDP23` the converse.

Numeric hypothesis (parameter only): `Δ ≥ 2`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz}

namespace Gaf02ChainE

/-- **EDP02's actual base `B₂`** written out (B:6748–6753): the points `w` of
`W₂ = Θ₂(V₂⁰)` having an edge index `k` with `v_k(w) > .9R_k` and `‖u_k(w)‖ < 4Δ v_k(w)`
(full norm of the vector block, as in lanes C14-FDC / C14-EDP-FDC). -/
def edgeBase_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)) :=
  {w | w ∈ Ĉ.toChain.finalBase_BAS 1 ∧
    ∃ k : L.edge.finite_centres.toFinset,
      9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w ∧
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w}

/-- Membership in `B₂` (definitional). -/
theorem mem_edgeBase_EDP23 {Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw}
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)} :
    w ∈ Ĉ.edgeBase_EDP23 ↔ w ∈ Ĉ.toChain.finalBase_BAS 1 ∧
      ∃ k : L.edge.finite_centres.toFinset,
        9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k))) w :=
  Iff.rfl

/-- **EDP02's total space `X₂ = (π₂E)⁻¹(B₂) ∩ V`** (B:6748–6753, (ED)), `V` kept as the union of its
low branch `t ≤ .35Δ` and `{s > 0, T ≤ 4Δ}` (`s = C.scale`, `T = A/s`,
`A = proj₀(gafHeightVector E)`). -/
def edgeTotal_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) : Set X :=
  {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
      Ĉ.edgeBase_EDP23} ∩
    ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})

/-- **Every point of `W₂` has an actual final preimage on an ORIGINAL threshold-6 edge plateau**
(B:6783–6784 "every `w ∈ W₂` has an actual final preimage"): `w = π₂E p` with `p ∈ B(k, 100Δρ_k)`,
`|η_k(p)| < 6Δ`, `t(p) < 6Δ` for some edge index `k`. -/
theorem finalBase_preimage_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.toChain.finalBase_BAS 1) :
    ∃ (k : L.edge.finite_centres.toFinset) (p : X), p ∈ ball k.1 (100 * Δ * ρ k.1) ∧
      |L.edge.coord k.1 p| < 6 * Δ ∧ L.edge.smoothing p / ρ p < 6 * Δ ∧
      (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E p) = w := by
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  obtain ⟨k, hk⟩ := mem_iUnion.mp (show w₀ ∈ ⋃ j, Ĉ.toChain.edgePatch_BAS j from hw₀)
  obtain ⟨p, ⟨hp, hη, ht⟩, hpw⟩ := (Ĉ.toChain.cgp07_edge_BAS Ĉ.rough k).2.1 w₀ hk
  refine ⟨k, p, hp, hη, ht, ?_⟩
  rw [Ĉ.toChain.final_factor_BAS 1 p, hpw]

/-- **The base-level exact marker** (EDP02, B:6783–6790; `Δ ≥ 2`): a point `w ∈ W₂` with
`v_i(w) ≥ .9R_i` and `‖u_i(w)‖ < 4Δ v_i(w)` has `v_i(w) = R_i` EXACTLY, whether or not `w` is
the image of a point of `V`. -/
theorem edgeBase_marker_exact_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (i : L.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.toChain.finalBase_BAS 1)
    (hv : 9 / 10 * ρ i.1 ≤ blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl i))) w)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl i))) w‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
        L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl i))) w) :
    blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl i))) w = ρ i.1 := by
  obtain ⟨k, p, -, -, htk, rfl⟩ := Ĉ.finalBase_preimage_EDP23 hw
  rw [gafStageQ_edgeMarker_FDC] at hv hu ⊢
  rw [gafStageQ_edgeVector_FDC] at hu
  obtain ⟨hball, -, hη⟩ := Ĉ.toChain.ratio_original_ge_EFC hΔ i hv hu
  exact (Ĉ.gaf05_edge_stage_plateau_GAFD i hball (by linarith) htk).2

/-- **The two marker conventions give the same base** (B:6762, B:6783–6796), at BASE level (for
every `w ∈ W₂`, not only for images of points of `V`; `Δ ≥ 2`): `B₂^≥ = B₂`. -/
theorem edgeBase_ge_eq_base_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) :
    {w | w ∈ Ĉ.toChain.finalBase_BAS 1 ∧
      ∃ k : L.edge.finite_centres.toFinset,
        9 / 10 * ρ k.1 ≤ blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k))) w} = Ĉ.edgeBase_EDP23 := by
  ext w
  constructor
  · rintro ⟨hw, k, hv, hu⟩
    have hm := Ĉ.edgeBase_marker_exact_EDP23 hΔ k hw hv hu
    have hrk := hρ k.1
    refine ⟨hw, k, ?_, hu⟩
    rw [hm]
    linarith
  · rintro ⟨hw, k, hv, hu⟩
    exact ⟨hw, k, hv.le, hu⟩

/-- **GAF05's patch clause for `B₂`** (B:6753–6755, "each indicated patch is exactly
`V_i ∩ {|u_i|/R_i < 4Δ}` and has `v_i = R_i`", first half; `Δ ≥ 2`): a point `w ∈ B₂` with
witness `k` lies in `W₂ ∩ {v_k > .9R_k, |u_k| < 5.5ΔR_k}` (`= V_k`, the image `Θ₂(V_k⁰)` of the
marked patch), `v_k(w) = R_k` and `‖u_k(w)‖ < 4ΔR_k`. -/
theorem edgeBase_mem_patch_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (k : L.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.toChain.finalBase_BAS 1)
    (hv : 9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) w)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) w‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
        L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k))) w) :
    w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
        (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ ∧
      blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w = ρ k.1 ∧
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w‖ < 4 * Δ * ρ k.1 := by
  have hm := Ĉ.edgeBase_marker_exact_EDP23 hΔ k hw hv.le hu
  have hrk := hρ k.1
  have hΔ0 : 0 < Δ := by linarith
  rw [hm] at hu
  refine ⟨⟨hw, hv, ?_⟩, hm, hu⟩
  have hax : ‖(axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k)) w‖ ≤
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w‖ := by
    rw [Real.norm_eq_abs]
    exact abs_proj_zero_le_norm_EFC _
  have h2 : 4 * Δ * ρ k.1 < 11 / 2 * Δ * ρ k.1 := by nlinarith
  linarith

/-- **The converse patch clause** (B:6753–6755, second half; `Δ ≥ 2`): a point of `W₂` in the patch
`{v_k > .9R_k, |u_k| < 5.5ΔR_k}` with `‖u_k(w)‖ < 4ΔR_k` belongs to `B₂`, with `v_k(w) = R_k`. -/
theorem edgeBase_patch_iff_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (k : L.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
      (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) w‖ < 4 * Δ * ρ k.1) :
    w ∈ Ĉ.edgeBase_EDP23 ∧ blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) w = ρ k.1 := by
  have hm : blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) w = ρ k.1 := Ĉ.gaf05_edgeBase_marker_GAFD k w hw
  refine ⟨⟨hw.1, k, ?_, ?_⟩, hm⟩
  · rw [hm]
    have hrk := hρ k.1
    linarith
  · rw [hm]
    exact hu

/-- **The base-level row of EDP02 (B), exactness part** (`Δ ≥ 2`): the exact marker on `W₂`, the
equality of the two marker conventions and the patch membership of `B₂`, as one statement on the
chain. -/
theorem edgeBase_exact_row_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) :
    (∀ (i : L.edge.finite_centres.toFinset)
      (w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)),
      w ∈ Ĉ.toChain.finalBase_BAS 1 →
      9 / 10 * ρ i.1 ≤ blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w →
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
          L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl i))) w →
      blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w = ρ i.1) ∧
    {w | w ∈ Ĉ.toChain.finalBase_BAS 1 ∧
      ∃ k : L.edge.finite_centres.toFinset,
        9 / 10 * ρ k.1 ≤ blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k))) w} = Ĉ.edgeBase_EDP23 ∧
    (∀ w ∈ Ĉ.edgeBase_EDP23, ∃ k : L.edge.finite_centres.toFinset,
      w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
          (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ ∧
        blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w‖ < 4 * Δ * ρ k.1) :=
  ⟨fun i _ hw hv hu => Ĉ.edgeBase_marker_exact_EDP23 hΔ i hw hv hu,
    Ĉ.edgeBase_ge_eq_base_EDP23 hΔ, fun _ hw => by
      obtain ⟨hW, k, hv, hu⟩ := hw
      exact ⟨k, Ĉ.edgeBase_mem_patch_EDP23 hΔ k hW hv hu⟩⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
