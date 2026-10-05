import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Fibration.ActualReplacementIndexApplications

/-!
# FDC01's replacement contract on the chain object (the clauses read off `C.E`)

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7157–7243),
on one chain `C : Gaf02Chain P …` (draft 59 §3; the stage-two base map is `π₂E = π_{Q₂} ∘ C.E`);
draft 61 §6.2, step four of (Repl∂) in the closed form. NO hypothesis `q ∈ X₂` or `π₂E(q) ∈ B₂`.

* `gafStageQ_starProjection_edgeTag_FDC`, `gafStageQ_edgeMarker_FDC`, `gafStageQ_edgeVector_FDC`:
  `π_{Q₂}` keeps every edge block, so `v_j(π₂E q) = v_j(E q)` and `u_j(π₂E q) = u_j(E q)`; the
  clauses below are stated on the blocks of `C.E q` and read on `π₂E q` through these equalities.
* `Gaf02Chain.edge_block_window_FDC`: at a point `q` with `ζ_j(q) = 1` and `d(q, j) < 7Δρ(j)`,
  the final edge block satisfies `|v_j(E q) − R_j| < (5/4)c₃R_j` and
  `|u_j(E q)| < (|η_j(q)| + (5/4)c₃)R_j` (`c₃ = c 2`; `𝓔⁰`'s block is `(R_jη_j, R_j)` there,
  `|E − 𝓔⁰| < c₃ρ`, `ρ(q) < (5/4)R_j`).
* `fdc01_window_numbers_FDC`: the numbers (`c₃ ≤ 1/512`, `Δ ≥ 100`).
* `fdc01_chain_replacement_FDC` (`LocalChartPacketsC14D`, EGP04's constants first): for an edge
  index `i` whose centre is a nonslim one-stratum point, `q ∈ U_i`, `|η_i(q)| ≤ 4.01Δ`,
  `t(q) ≤ 4.01Δ`, and EVERY chain `C` on the family, a selected edge index `j ∈ J_e(i)` has
  `d(q, j) < 7Δρ(j)`, `|η_j(q)| < 2Δ`, `ζ_j(q) = 1`, the marker window
  `|v_j(E q) − R_j| < (5/4)c₃R_j` (so `v_j(E q) > .9R_j`), the strict base coordinate
  `|u_j(E q)| < 3ΔR_j` and the strict ratio `|u_j(E q)| < 4Δ v_j(E q)`.

NOT here: the EXACT marker `v_j(π₂E q) = R_j` and `π₂E(q) ∈ W₂ ∩ B₂` (GAF05 / CGP04–05 on the
stage-two zero set with the FM* planes: Gaf02ChainE + BASES).
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **The stage-two projection keeps every edge block**: `(π_{Q₂} z)_j = z_j` for an edge tag. -/
theorem gafStageQ_starProjection_edgeTag_FDC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.edge.finite_centres.toFinset)
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection z
        (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) =
      z (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) := by
  classical
  have hmem : (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) ∈
      gafStageTags P.toLocalChartFamily P.zero 1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rw [gafStageQ_starProjection, blockRestrict_apply]
  simp only [hmem, ↓reduceIte]

/-- `v_j(π₂ z) = v_j(z)` for an edge index `j` (so `v_j(π₂E q) = v_j(E q)`). -/
theorem gafStageQ_edgeMarker_FDC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.edge.finite_centres.toFinset)
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j)))
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) =
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) z := by
  rw [blockMarkerCLM_apply, blockMarkerCLM_apply, gafStageQ_starProjection_edgeTag_FDC]

/-- `u_j(π₂ z) = u_j(z)` for an edge index `j` (so `u_j(π₂E q) = u_j(E q)`). -/
theorem gafStageQ_edgeVector_FDC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.edge.finite_centres.toFinset)
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j)))
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) =
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) z := by
  rw [blockVectorCLM_apply, blockVectorCLM_apply, gafStageQ_starProjection_edgeTag_FDC]

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The final edge block near a full original edge cutoff** (FDC01's (AE) step): at `q` with
`ζ_j(q) = 1` and `d(q, j) < 7Δρ(j)`, `|v_j(E q) − R_j| < (5/4)c₃R_j` and
`|u_j(E q)| < (|η_j(q)| + (5/4)c₃)R_j`. -/
theorem edge_block_window_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X} (hζ : P.edge.cutoff j.1 q = 1)
    (hqj : dist q j.1 < 7 * Δ * ρ j.1) :
    |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j)))
        (C.E q) - ρ j.1| <
      5 / 4 * c 2 * ρ j.1 ∧
    ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j)))
        (C.E q)‖ <
      (|P.edge.coord j.1 q| + 5 / 4 * c 2) * ρ j.1 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  have hrj := hρ j.1
  have hrq := hρ q
  -- the scale at `q`
  have hρq : ρ q < 5 / 4 * ρ j.1 := by
    have h1 := P.lipschitz_scale.dist_le_mul q j.1
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist q j.1 ≤ Λ * (7 * Δ * ρ j.1) := mul_le_mul_of_nonneg_left hqj.le hΛ
    have h3 : Δ * Λ ≤ 1 / 100000000000 := by nlinarith
    have h4 : Λ * (7 * Δ * ρ j.1) ≤ 7 / 100000000000 * ρ j.1 := by
      have := mul_le_mul_of_nonneg_right h3 hrj.le
      nlinarith
    linarith [(abs_le.mp h1).2]
  have herr := C.stage_error_lt.2.2 q
  have hc : 0 < c 2 := by
    have h0 := norm_nonneg (C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q)
    by_contra hc
    have : c 2 * ρ q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) hrq.le
    linarith
  have herr' : ‖C.E q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ < 5 / 4 * c 2 * ρ j.1 := by
    have := mul_lt_mul_of_pos_left hρq hc
    linarith
  -- the original block at a full cutoff
  have hblk := cgpGlobalMap_edgeBlock P.toLocalChartFamily P.zero j q
  rw [hζ, mul_one] at hblk
  have hm0 : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q) = ρ j.1 := by
    rw [blockMarkerCLM_apply]
    exact hblk.2
  have hv0 : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ =
        |P.edge.coord j.1 q| * ρ j.1 := by
    rw [blockVectorCLM_apply]
    change ‖(cgpGlobalMap P.toLocalChartFamily P.zero q
      (cgpEdgeBlockTag P.toLocalChartFamily P.zero j)).fst‖ = _
    rw [hblk.1, norm_smul, norm_planeAxis, Real.norm_eq_abs, abs_of_pos hrj]
    ring
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
  refine ⟨?_, ?_⟩
  · rw [hm0] at hmd
    linarith
  · have htri := norm_le_insert' (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²) (.inr (.inr (.inl j))) (C.E q)) (blockVectorCLM (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl j)))
          (cgpGlobalMap P.toLocalChartFamily P.zero q))
    rw [hv0] at htri
    nlinarith

end Gaf02Chain

/-- The numbers of FDC01's chain clauses: `|η| < 2Δ`, `|M − r| < (5/4)c₃r`, `U < (|η| + (5/4)c₃)r`,
`c₃ ≤ 1/512`, `Δ ≥ 100` give `M > .9r`, `U < 3Δr` and `U < 4ΔM`. -/
theorem fdc01_window_numbers_FDC {Δ r c₃ η M U : ℝ} (hΔ : 100 ≤ Δ) (hr : 0 < r)
    (hc : c₃ ≤ 1 / 512) (hη : |η| < 2 * Δ) (hM : |M - r| < 5 / 4 * c₃ * r)
    (hU : U < (|η| + 5 / 4 * c₃) * r) :
    9 / 10 * r < M ∧ U < 3 * Δ * r ∧ U < 4 * Δ * M := by
  have hcr : c₃ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc hr.le
  have hMlo : (1 - 5 / 2048) * r < M := by
    have := (abs_lt.mp hM).1
    linarith
  have hU' : U < (2 * Δ + 5 / 2048) * r := by
    have h1 : (|η| + 5 / 4 * c₃) * r ≤ (2 * Δ + 5 / 2048) * r :=
      mul_le_mul_of_nonneg_right (by linarith) hr.le
    linarith
  have hΔr : 100 * r ≤ Δ * r := mul_le_mul_of_nonneg_right hΔ hr.le
  have hΔM : Δ * ((1 - 5 / 2048) * r) ≤ Δ * M := mul_le_mul_of_nonneg_left hMlo.le (by linarith)
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **FDC01's replacement contract on the chain** (`LocalChartPacketsC14D`, EGP04's constants
first): for an edge index `i` whose centre is a nonslim one-stratum point, `q ∈ U_i`,
`|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ` (no hypothesis `q ∈ X₂`), and every chain `C` on the family, a
selected edge index `j ∈ J_e(i)` has `d(q, j) < 7Δρ(j)`, `|η_j(q)| < 2Δ`, `ζ_j(q) = 1`,
`|v_j(E q) − R_j| < (5/4)c₃R_j`, `v_j(E q) > .9R_j`, `|u_j(E q)| < 3ΔR_j` and
`|u_j(E q)| < 4Δ v_j(E q)` (equal to the values at `π₂E q`, `gafStageQ_edgeMarker_FDC`). -/
theorem fdc01_chain_replacement_FDC {Δ β₂ : ℝ} (hΔ : 100 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz) (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ)
        (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 →
        σc ≤ 1 / 10 ^ 12 → μ * Δ < 1 / 10 ^ 4 → ∀ i ∈ P.edge.centres,
        i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1 →
        ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
        ∀ q : X, q ∈ ball i (100 * Δ * ρ i) → |P.edge.coord i q| ≤ 401 / 100 * Δ →
          P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ →
          ∃ j : P.toLocalChartPackets.edge.finite_centres.toFinset,
            j.1 ∈ egpEdgeList P.toLocalChartFamily i ∧ dist q j.1 < 7 * Δ * ρ j.1 ∧
            |P.edge.coord j.1 q| < 2 * Δ ∧ P.edge.cutoff j.1 q = 1 ∧
            |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl j)))
                (C.E q) - ρ j.1| < 5 / 4 * c 2 * ρ j.1 ∧
            9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag
                P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                (.inr (.inr (.inl j)))
                (C.E q) ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl j)))
                (C.E q)‖ < 3 * Δ * ρ j.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl j)))
                (C.E q)‖ <
              4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
                P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
                (.inr (.inr (.inl j)))
                (C.E q) := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrep⟩ := fdc01_replacement_index_C14D hΔ hβ₂ hβ₂1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    Kj Ξ Γ S eg c cw C hb hs hβ1 hLmax hμ hτ hσc hμΔ i hi hstr hns q hq hηq htq
  obtain ⟨hΛ, -, -, -, hLΛ, -⟩ := C.std
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have h1 := hrep X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ i hi hstr hns q hq hηq htq
  obtain ⟨j, hj, hlist, hqj, hηj, hζ⟩ := h1
  let jj : P.toLocalChartPackets.edge.finite_centres.toFinset :=
    ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
  obtain ⟨hmk, hvec⟩ := C.edge_block_window_FDC jj hζ hqj
  obtain ⟨h9, h3, h4⟩ := fdc01_window_numbers_FDC hΔ (hρ j) hc2 hηj hmk hvec
  exact ⟨jj, hlist, hqj, hηj, hζ, hmk, h9, h3, h4⟩

end DifferentialGeometry.Geometry.Collapse
