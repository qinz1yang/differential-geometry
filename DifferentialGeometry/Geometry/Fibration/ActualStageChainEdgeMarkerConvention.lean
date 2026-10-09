import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRatio
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRemainder

/-!
# EDP02: the marker conventions `> .9R_i` and `≥ .9R_i` give the same `X₂`

Blueprint `master207B.tex`, EDP02 (B:6762: "Replacing the marker `>.9R_i` by `≥.9R_i` produces the
SAME base"; proof B:6783–6796). The base-level equality (for every `w ∈ W₂`, not only for images of
points of `V`) needs CGP08's later diffeomorphism and CGP05/CGP07 (BASES); here it is proved for
the actual preimages that build `X₂ = (π₂E)⁻¹(B₂) ∩ V`, which is the form FDC01–FDC04 consume:

* `Gaf02Chain.ratio_original_ge_EFC`: lane C14-FDCb's `ratio_original_FDC` with the NONSTRICT
  marker `v_i(E q) ≥ .9R_i` (same route: (AM0) at `E`, strict stage error, `ζ_i > .898`);
* `Gaf02ChainE.marker_eq_of_ratio_ge_EFC`: a point of `V` with `v_i(E q) ≥ .9R_i`,
  `|u_i(E q)| < 4Δ v_i(E q)` has `v_i(E q) = R_i` EXACTLY (GAF05's plateau), so `> .9R_i`;
* `Gaf02ChainE.edgeBase_ge_eq_EFC`: `(π₂E)⁻¹(B₂^≥) ∩ V = (π₂E)⁻¹(B₂) ∩ V`
  (`W₂ = C.finalBase_BAS 1`).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}

/-- **The original edge block under the NONSTRICT ratio condition**: `v_i(E q) ≥ .9R_i` and
`|u_i(E q)| < 4Δ v_i(E q)` (`Δ ≥ 2`) give `q ∈ U_i`, `ζ_i(q) > .898` and `|η_i(q)| < 4.01Δ`. -/
theorem ratio_original_ge_EFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (j : P.edge.finite_centres.toFinset) {q : X}
    (hv : 9 / 10 * ρ j.1 ≤ blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q))
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j))) (C.E q)) :
    q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ 898 / 1000 < P.edge.cutoff j.1 q ∧
      |P.edge.coord j.1 q| < 401 / 100 * Δ := by
  obtain ⟨hΛ, -, -, -, hLΛ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hc2 : c 2 ≤ 1 / 512 := C.numbers.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc2pos : 0 < c 2 := by
    obtain ⟨h0, h1, h2⟩ := C.accuracy_order_EDPE
    linarith
  have hrj := hρ j.1
  have hζI := cgpEdgeCutoff_mem_Icc P.toLocalChartFamily hΔ0 j.1 q
  have hζ0 : P.edge.cutoff j.1 q ≠ 0 := by
    intro h0
    have h := C.prefix_am0.2.2 (.inr (.inr j)) q h0
    change |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)| ≤ ρ j.1 / 32 at h
    have := (abs_le.mp h).2
    linarith
  have hball : q ∈ ball j.1 (100 * Δ * ρ j.1) :=
    cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inr j)) q hζ0
  have hρq : ρ q ≤ (1 + 1 / 10000) * ρ j.1 := by
    have h1 := (abs_le.mp (scale_ratio_ball_EDPE P hΛ hball)).2
    have h2 : 100 * Δ * Λ ≤ 1 / 10000 := by nlinarith
    have h4 : ρ q / ρ j.1 ≤ 1 + 1 / 10000 := by linarith
    rwa [div_le_iff₀ hrj] at h4
  have hk : c 2 * ρ q ≤ 10001 / 5120000 * ρ j.1 := by
    have h1 := mul_le_mul_of_nonneg_left hρq hc2pos.le
    have h2 : c 2 * ((1 + 1 / 10000) * ρ j.1) ≤ 1 / 512 * ((1 + 1 / 10000) * ρ j.1) :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    linarith
  have herr := C.stage_error_lt.2.2 q
  have hblk := cgpGlobalMap_edgeBlock P.toLocalChartFamily P.zero j q
  have hm0 : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q) =
        ρ j.1 * P.edge.cutoff j.1 q := by
    rw [blockMarkerCLM_apply]
    exact hblk.2
  have hv0 : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ =
        ρ j.1 * (P.edge.cutoff j.1 q * |P.edge.coord j.1 q|) := by
    rw [blockVectorCLM_apply]
    change ‖(cgpGlobalMap P.toLocalChartFamily P.zero q
      (cgpEdgeBlockTag P.toLocalChartFamily P.zero j)).fst‖ = _
    rw [hblk.1, norm_smul, norm_planeAxis, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hrj.le hζI.1), mul_assoc]
  have hmd : |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) - blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)| ≤
      ‖C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_blockMarkerCLM_le _) (norm_nonneg _))
  have hvd : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) - blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ ≤
      ‖C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ := by
    rw [← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_blockVectorCLM_le _) (norm_nonneg _))
  rw [hm0] at hmd
  set v := blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) with hvdef
  set U := ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ with hUdef
  have hav : v / ρ j.1 < P.edge.cutoff j.1 q + 10001 / 5120000 := by
    rw [div_lt_iff₀ hrj]
    have := (abs_lt.mp (lt_of_le_of_lt hmd herr)).2
    linarith
  have ha : 9 / 10 ≤ v / ρ j.1 := by
    rw [le_div_iff₀ hrj]
    linarith
  have hu' : U / ρ j.1 < 4 * Δ * (v / ρ j.1) := by
    rw [div_lt_iff₀ hrj]
    have : 4 * Δ * (v / ρ j.1) * ρ j.1 = 4 * Δ * v := by field_simp
    linarith
  have hζη : P.edge.cutoff j.1 q * |P.edge.coord j.1 q| < U / ρ j.1 + 10001 / 5120000 := by
    have htri := norm_le_insert' (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²) (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q))
      (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) (C.E q))
    rw [hv0, norm_sub_rev] at htri
    have h2 : ρ j.1 * (P.edge.cutoff j.1 q * |P.edge.coord j.1 q|) <
        ρ j.1 * (U / ρ j.1 + 10001 / 5120000) := by
      have : ρ j.1 * (U / ρ j.1) = U := by field_simp
      nlinarith
    exact lt_of_mul_lt_mul_left h2 hrj.le
  have hΔ0' : 0 < 4 * Δ := by linarith
  have hav' : 9 / 10 < (v / ρ j.1 + (P.edge.cutoff j.1 q + 10001 / 5120000)) / 2 := by linarith
  have hav'' : (v / ρ j.1 + (P.edge.cutoff j.1 q + 10001 / 5120000)) / 2 <
      P.edge.cutoff j.1 q + 10001 / 5120000 := by linarith
  have hu'' : U / ρ j.1 < 4 * Δ * ((v / ρ j.1 + (P.edge.cutoff j.1 q + 10001 / 5120000)) / 2) :=
    hu'.trans (mul_lt_mul_of_pos_left (by linarith) hΔ0')
  obtain ⟨h1, h2⟩ := fdc02_ratio_numbers_FDC hΔ le_rfl hav' hav'' hu'' hζη
  exact ⟨hball, h1, h2⟩

end Gaf02Chain

namespace Gaf02ChainE

/-- **The nonstrict marker is exact on `V`**: a point of `V` with `v_i(E q) ≥ .9R_i` and
`|u_i(E q)| < 4Δ v_i(E q)` (`Δ ≥ 2`) has `v_i(E q) = R_i`. -/
theorem marker_eq_of_ratio_ge_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    (j : L.toLocalChartFamily.edge.finite_centres.toFinset) {q : X}
    (hv : 9 / 10 * ρ j.1 ≤ blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl j))) (Ĉ.toChain.E q))
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl j))) (Ĉ.toChain.E q)‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
        L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl j))) (Ĉ.toChain.E q))
    (hV : q ∈ {p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) :
    blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
      (.inr (.inr (.inl j))) (Ĉ.toChain.E q) = ρ j.1 := by
  obtain ⟨hball, hζ, hη⟩ := Ĉ.toChain.ratio_original_ge_EFC hΔ j hv hu
  have hη8 : |L.edge.coord j.1 q| < 8 * Δ := by linarith
  have ht := Ĉ.toChain.ratio_height_FDC j hball hη8 hζ hV
  exact Ĉ.gaf05_edge_plateau_G47 j hball (by linarith)
    (by change L.edge.smoothing q / ρ q < 6 * Δ; linarith)

/-- **EDP02's marker-convention equality for the actual `X₂`** (`Δ ≥ 2`): the preimage of the
nonstrict base `B₂^≥ = ⋃_i {w ∈ W₂ : v_i(w) ≥ .9R_i, |u_i(w)| < 4Δ v_i(w)}` meets `V` in exactly
`X₂ = (π₂E)⁻¹(B₂) ∩ V`. -/
theorem edgeBase_ge_eq_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) :
    {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 ≤ blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) =
    {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) := by
  apply Subset.antisymm
  · rintro x ⟨⟨hW, k, hv, hu⟩, hV⟩
    have hv' := hv
    have hu' := hu
    rw [gafStageQ_edgeMarker_FDC] at hv' hu'
    rw [gafStageQ_edgeVector_FDC] at hu'
    have hm := Ĉ.marker_eq_of_ratio_ge_EFC hΔ k hv' hu' hV
    have hrk := hρ k.1
    refine ⟨⟨hW, k, ?_, hu⟩, hV⟩
    rw [gafStageQ_edgeMarker_FDC, hm]
    linarith
  · rintro x ⟨⟨hW, k, hv, hu⟩, hV⟩
    exact ⟨⟨hW, k, hv.le, hu⟩, hV⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
