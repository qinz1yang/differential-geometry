import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeSublevel
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBase
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFinalSubmersion

/-!
# EDP02 (B): the actual edge base `B₂`, its patches, the total space `X₂` and the final fibre

Blueprint `master207B.tex`, EDP02 (`lem:fibration-actual-edge-height-localization`, B:6748–6835),
on an enhanced chain `Ĉ : Gaf02ChainE L …` of a family `L : LocalChartPacketsC14`
(`π₂E = (gafStageQ … 1).starProjection ∘ E`, `T = A/s`, `W₂ = Ĉ.toChain.finalBase_BAS 1`,
`B₂ = Ĉ.edgeBase_EDP23`, `X₂ = Ĉ.edgeTotal_EDP23`; group G2 of lane S-EDP02-03).

New here (the (B) clauses): `B₂` is open in `W₂` (`edgeBase_eq_inter_EDP23`), each patch of `B₂`
is `V_i ∩ {‖u_i‖ < 4ΔR_i}` with `v_i = R_i` (`edgeBase_patch_eq_EDP23`, uses the base-level
exactness of G1), `X₂` is the witnessed set `{T ≤ 4Δ, ∃ k, v_k(E) = R_k, ‖u_k(E)‖ < 4ΔR_k}`
(`edgeTotal_eq_witnessed_EDP23`), and over every `w ∈ B₂` with witness `k` the final fibre
`f₂⁻¹(w) ∩ X₂` is exactly `{x ∈ Y_k : g_k x = a, T x ≤ 4Δ}`, `a = R_k⁻¹u_k(w)`
(`edgeTotal_fibre_eq_EDP23`; GAF05's coordinate uniqueness on `V_k` and (ELoc), `Δ ≥ 2` only).

The row `Gaf02ChainE.edp02_row_EDP23` collects EVERY clause of EDP02 on the chain, each one either
proved here or by the existing theorem named in the clause table below.

CLAUSE TABLE (EDP02, B:6748–6835), clause: where.
* (ED) `B₂`, `T`, `V`, `X₂`: `edgeBase_EDP23`, `edgeTotal_EDP23` (defs).
* `B₂` open in `W₂`: `edgeBase_eq_inter_EDP23` (row clause 1).
* each patch is `V_i ∩ {|u_i|/R_i < 4Δ}` and `v_i = R_i`: `edgeBase_patch_eq_EDP23` (clause 2;
  G1's `edgeBase_marker_exact_EDP23`, GAF05).
* `> .9R_i` versus `≥ .9R_i` give the same base: `edgeBase_ge_eq_base_EDP23` (clause 3, base level;
  at `X₂`: `edgeBase_ge_eq_EFC`).
* (ELoc) for ALL preimages (with `ζ_i = 1`, `p ∈ U₂`): `stageTwo_ratio_localization_FDC`
  (clause 4).
* the smaller closed sets lie in the ambient interior of `X₂`: `smaller_set_interior_X2_EFC`
  (clause 5).
* `X₂ = (π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}` (the low branch gives `T < 4Δ`): `edgeBase_eq_heightSublevel_EFC`,
  `vertical_eq_FDC` (clause 6).
* base membership of the witnessed points: `edgeTotal_eq_witnessed_EDP23` (clause 7;
  `stageTwo_mem_base_FDC`).
* final fibre `f₂⁻¹(w) ∩ X₂`, GAF05's coordinate uniqueness: `edgeTotal_fibre_eq_EDP23`
  (clause 8).
* (EZ) on `𝓔⁰`, low branch on `X`: `edp02_final_clauses_C14_EDPE` (EDP-E G1; chain-only).
* the interior of `X₂` is `{T < 4Δ}` (numerics): `interior_edgeBase_eq_EFC` (FDC03's form).

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

/-- **`B₂` is open in `W₂`**: `B₂ = W₂ ∩ O` with `O` the open union, over the edge indices, of
`{v_k > .9R_k, ‖u_k‖ < 4Δ v_k}` (B:6753, "The base `B₂` is open in `W₂`"). -/
theorem edgeBase_eq_inter_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    ∃ O : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)), IsOpen O ∧
      Ĉ.edgeBase_EDP23 = Ĉ.toChain.finalBase_BAS 1 ∩ O := by
  refine ⟨⋃ k : L.edge.finite_centres.toFinset,
    {w | 9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w ∧
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w}, isOpen_iUnion fun k => ?_, ?_⟩
  · have hv := (blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k)))).continuous
    have hu := (blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k)))).continuous
    exact (isOpen_lt continuous_const hv).inter (isOpen_lt hu.norm (continuous_const.mul hv))
  · ext w
    simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq]
    exact Iff.rfl

/-- **Each patch of `B₂` is `V_i ∩ {‖u_i‖ < 4ΔR_i}` and has `v_i = R_i`** (B:6753–6755;
`Δ ≥ 2`): with `V_i = W₂ ∩ {v_i > .9R_i, |u_i| < 5.5ΔR_i}`,
`{w ∈ W₂ : v_i(w) > .9R_i, ‖u_i(w)‖ < 4Δ v_i(w)} = V_i ∩ {‖u_i(w)‖ < 4ΔR_i}`, and `v_i = R_i`
on it. -/
theorem edgeBase_patch_eq_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (i : L.edge.finite_centres.toFinset) :
    {w | w ∈ Ĉ.toChain.finalBase_BAS 1 ∧
      9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w ∧
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl i))) w} =
      (Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero i))
        (gafEdgeMarker L.toLocalChartFamily L.zero i) (ρ i.1) Δ) ∩
        {w | ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl i))) w‖ < 4 * Δ * ρ i.1} ∧
    ∀ w ∈ {w | w ∈ Ĉ.toChain.finalBase_BAS 1 ∧
      9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w ∧
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl i))) w},
      blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) w = ρ i.1 := by
  refine ⟨?_, fun w hw => (Ĉ.edgeBase_mem_patch_EDP23 hΔ i hw.1 hw.2.1 hw.2.2).2.1⟩
  ext w
  constructor
  · rintro ⟨hW, hv, hu⟩
    obtain ⟨hmem, -, hu'⟩ := Ĉ.edgeBase_mem_patch_EDP23 hΔ i hW hv hu
    exact ⟨hmem, hu'⟩
  · rintro ⟨hmem, hu⟩
    obtain ⟨hB, hm⟩ := Ĉ.edgeBase_patch_iff_EDP23 i hmem hu
    obtain ⟨-, k, hv, hu'⟩ := hB
    refine ⟨hmem.1, ?_, ?_⟩
    · rw [hm]
      have hrk := hρ i.1
      linarith
    · rw [hm]
      exact hu

/-- **`X₂` is the witnessed set** (B:6764–6770, B:6779–6781 and FDC01's base membership;
`Δ ≥ 2`): `X₂ = {T ≤ 4Δ} ∩ {x | ∃ k, v_k(E x) = R_k, ‖u_k(E x)‖ < 4ΔR_k}`. The inclusion `⊆` is the
exact marker on `V` (GAF05's plateau after (ELoc)); `⊇` is `stageTwo_mem_base_FDC`. -/
theorem edgeTotal_eq_witnessed_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) :
    Ĉ.edgeTotal_EDP23 =
      {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} ∩
      {x | ∃ k : L.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1} := by
  have hV := Ĉ.toChain.vertical_eq_FDC
  ext x
  constructor
  · rintro ⟨⟨hW, k, hv, hu⟩, hxV⟩
    have hT : x ∈ {p | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily
        L.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} := hV ▸ hxV
    have hv' := hv
    have hu' := hu
    rw [gafStageQ_edgeMarker_FDC] at hv' hu'
    rw [gafStageQ_edgeVector_FDC] at hu'
    have hm := Ĉ.marker_eq_of_ratio_ge_EFC hΔ k hv'.le hu' hxV
    refine ⟨hT, k, hm, ?_⟩
    rw [hm] at hu'
    exact hu'
  · rintro ⟨hT, k, hm, hu⟩
    have hxV : x ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
      Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hT⟩
    obtain ⟨hW, h9, h4⟩ := Ĉ.toChain.stageTwo_mem_base_FDC k hm hu hxV
    exact ⟨⟨hW, k, h9, h4⟩, hxV⟩

/-- **The final fibre `f₂⁻¹(w) ∩ X₂`** (B:6749, EDP04's fibre identification, GAF05's coordinate
uniqueness; `Δ ≥ 2`): for `w ∈ W₂ ∩ {v_k > .9R_k, |u_k| < 5.5ΔR_k}` with `‖u_k(w)‖ < 4ΔR_k`
(so `w ∈ B₂`, `a = R_k⁻¹u_k(w)`, `|a| < 4Δ`),
`{x ∈ X₂ : π₂E x = w} = {x ∈ Y_k : g_k x = a, T x ≤ 4Δ}`, where
`Y_k = {x ∈ B(k, 100Δρ_k) : |η_k x| < 5Δ, t x < 5Δ}` and `g_k = proj₀(u_k(E ·))/ρ_k`. -/
theorem edgeTotal_fibre_eq_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (k : L.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
      (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl k))) w‖ < 4 * Δ * ρ k.1) :
    {x | x ∈ Ĉ.edgeTotal_EDP23 ∧ (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
        (Ĉ.toChain.E x) = w} =
      {x | x ∈ ball k.1 (100 * Δ * ρ k.1) ∧ |L.edge.coord k.1 x| < 5 * Δ ∧
        L.edge.smoothing x / ρ x < 5 * Δ ∧
        EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
          (Ĉ.toChain.E x)) / ρ k.1 =
          ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k)) w ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} := by
  have hΔ0 : 0 < Δ := by linarith
  have hrk := hρ k.1
  have hmark : gafEdgeMarker L.toLocalChartFamily L.zero k w = ρ k.1 :=
    Ĉ.gaf05_edgeBase_marker_GAFD k w hw
  have hwB : w ∈ Ĉ.edgeBase_EDP23 := (Ĉ.edgeBase_patch_iff_EDP23 k hw hu).1
  set a : ℝ := ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily
    L.zero k)) w with ha_def
  have ha_eq : a = (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2)
      (blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w) := rfl
  have hiff : ∀ x : X, EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily
      L.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ →
      ((x ∈ ball k.1 (100 * Δ * ρ k.1) ∧ |L.edge.coord k.1 x| < 5 * Δ ∧
        L.edge.smoothing x / ρ x < 5 * Δ ∧
        EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
          (Ĉ.toChain.E x)) / ρ k.1 = a) ↔
        (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) = w) := by
    intro x hTx
    have hvec : blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x)) = blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero
            => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) :=
      gafStageQ_edgeVector_FDC L.toLocalChartPackets k (Ĉ.toChain.E x)
    constructor
    · rintro ⟨hp, hη, ht, hga⟩
      have hmem := Ĉ.toChain.final_submersion_edge_BAS Ĉ.rough k hp hη ht
      refine ((Ĉ.gaf05_edgeBase_chart_GAFD k).2.1).injOn hmem.1 hw ?_
      change (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
        CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
          ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))) = a
      rw [hvec, ← hga, div_eq_inv_mul]
      rfl
    · intro hxw
      have hv : 9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily
          L.zero => ℝ²) (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1
          ).starProjection (Ĉ.toChain.E x)) := by
        rw [hxw]
        exact hw.2.1
      have hu' : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
            (Ĉ.toChain.E x))‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily
              L.zero => ℝ²) (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1
          ).starProjection (Ĉ.toChain.E x)) := by
        rw [hxw]
        change ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl k))) w‖ < 4 * Δ * gafEdgeMarker L.toLocalChartFamily L.zero k w
        rw [hmark]
        exact hu
      obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.stageTwo_ratio_localization_FDC hΔ2 k hv hu'
        (Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hTx⟩)
      refine ⟨hball, by linarith, by linarith, ?_⟩
      rw [hxw] at hvec
      change EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
        CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)) /
          ρ k.1 = a
      rw [← hvec, ha_eq, div_eq_inv_mul]
  have hVeq := Ĉ.toChain.vertical_eq_FDC
  ext x
  constructor
  · rintro ⟨⟨-, hxV⟩, hxw⟩
    have hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ := by
      have h : x ∈ {p | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily
        L.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} := hVeq ▸ hxV
      exact h
    obtain ⟨hp, hη, ht, hga⟩ := (hiff x hT).mpr hxw
    exact ⟨hp, hη, ht, hga, hT⟩
  · rintro ⟨hp, hη, ht, hga, hT⟩
    have hxw := (hiff x hT).mp ⟨hp, hη, ht, hga⟩
    have hxB : (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.edgeBase_EDP23 := by
      rw [hxw]
      exact hwB
    have hxV : x ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
      Or.inr ⟨(Ĉ.toChain.scale_pos x).2, hT⟩
    exact ⟨⟨hxB, hxV⟩, hxw⟩

/-- **EDP02 (B) as ONE statement on the chain** (`Δ ≥ 2`): every clause of EDP02 for the actual
`B₂ = Ĉ.edgeBase_EDP23` and `X₂ = Ĉ.edgeTotal_EDP23` (see the clause table of the module header).
Clauses: (1) `B₂` open in `W₂`; (2) the patches (with `v_i = R_i`); (3) the marker conventions;
(4) (ELoc) for every preimage of a base point in `V`; (5) the smaller sets lie in `int X₂`;
(6) `X₂ = (π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}`; (7) `X₂` is the witnessed set; (8) the final fibre. -/
theorem edp02_row_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) :
    (∃ O : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)), IsOpen O ∧
      Ĉ.edgeBase_EDP23 = Ĉ.toChain.finalBase_BAS 1 ∩ O) ∧
    (∀ i : L.edge.finite_centres.toFinset, type_of% (Ĉ.edgeBase_patch_eq_EDP23 hΔ i)) ∧
    type_of% (Ĉ.edgeBase_ge_eq_base_EDP23 hΔ) ∧
    (∀ q ∈ Ĉ.edgeTotal_EDP23, ∀ i : L.edge.finite_centres.toFinset,
      9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E q)) →
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl i))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E q))‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
          (.inr (.inr (.inl i))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
            (Ĉ.toChain.E q)) →
      q ∈ ball i.1 (100 * Δ * ρ i.1) ∧ |L.edge.coord i.1 q| < 401 / 100 * Δ ∧
        L.edge.smoothing q / ρ q < 401 / 100 * Δ ∧ L.edge.cutoff i.1 q = 1) ∧
    (∀ (k : L.edge.finite_centres.toFinset) (x : X), x ∈ ball k.1 (100 * Δ * ρ k.1) →
      |L.edge.coord k.1 x| ≤ 35 / 10 * Δ → L.edge.smoothing x / ρ x ≤ 35 / 10 * Δ →
      x ∈ interior Ĉ.edgeTotal_EDP23) ∧
    Ĉ.edgeTotal_EDP23 = {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
        (Ĉ.toChain.E x) ∈ Ĉ.edgeBase_EDP23} ∩
      {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ} ∧
    type_of% (Ĉ.edgeTotal_eq_witnessed_EDP23 hΔ) ∧
    (∀ (k : L.edge.finite_centres.toFinset)
      (w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)),
      w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
        (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ →
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) w‖ < 4 * Δ * ρ k.1 →
      {x | x ∈ Ĉ.edgeTotal_EDP23 ∧ (gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x) = w} =
        {x | x ∈ ball k.1 (100 * Δ * ρ k.1) ∧ |L.edge.coord k.1 x| < 5 * Δ ∧
          L.edge.smoothing x / ρ x < 5 * Δ ∧
          EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
            (Ĉ.toChain.E x)) / ρ k.1 =
            ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k)) w ∧
          EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
            (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ}) := by
  refine ⟨Ĉ.edgeBase_eq_inter_EDP23, fun i => Ĉ.edgeBase_patch_eq_EDP23 hΔ i,
    Ĉ.edgeBase_ge_eq_base_EDP23 hΔ, fun q hq i hv hu => ?_,
    fun k x hball hη ht => Ĉ.smaller_set_interior_X2_EFC k hball hη ht, ?_,
    Ĉ.edgeTotal_eq_witnessed_EDP23 hΔ, fun k w hw hu => Ĉ.edgeTotal_fibre_eq_EDP23 hΔ k hw hu⟩
  · exact Ĉ.toChain.stageTwo_ratio_localization_FDC hΔ i hv hu hq.2
  · exact Ĉ.edgeBase_eq_heightSublevel_EFC

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
