import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff
import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors
import DifferentialGeometry.Geometry.Metric.WholePreimageLocalization
import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization

/-!
# GAF06 / GAF07 numerical steps and GAF05's stage-one plateau on the actual original map

Blueprint `master207B.tex`, GAF06 (`lem:fibration-whole-ratio-preimage-localization`,
B:6008–6047), the numerical steps of GAF07 (B:6049–), and GAF05's source-plateau step
(`prop:fibration-exact-interior-markers`, B:5998–6005), bound to CGP01's actual original map
`𝓔⁰ = F = cgpGlobalMap L Z`. The data of the ORIGINAL map are discharged here: the block identity
`(u_i, v_i)(F p) = (R_i ζ_i(p) η_i(p), R_i ζ_i(p))` (FC01, `rfl`), `0 ≤ ζ_i ≤ 1`, and FC26's (AS)
`3R_i/4 ≤ ρ(p) ≤ 5R_i/4` at every point with positive retained cutoff (`fc26_row`). The adjusted
map `E` is an arbitrary map carrying exactly GAF02's two outputs used by these rows: (AM0) on the
segment `H_τ = (1-τ)F + τE` and the value half of (AE), `|E - F| < c₃ρ`, `c₃ < 1/1000`.

* `cgpMarkerCutoff_mem_Icc_GAF2`, `cgpGlobalMap_markerBlock_GAF2`: the original-map inputs.
* `gaf06_segment_localization` (GAF06): (RP) on the segment ⇒ positive original cutoff and
  `|η_i(p)| < 4.01 ℓ` for every retained index (circle, slim and edge) and every `ℓ ≥ 1`.
* `gaf07_marker_bounds`, `gaf07_first_inclusion`: GAF07's "no extra base points" and first
  inclusion on the actual `F`.
* `adjustmentMap_apply_eq_GAF2`, `gaf05_stageOne_plateau` (GAF05, stage one): on the original
  threshold-6 circle plateau `ψ₁(F p) = 1`, so the stage output carries every block value `c` that
  the stage projection carries at the projected input (GAF03's output `v_i(P z) = R_i`); a block
  value already present at the input is kept for any cutoff value (later stages).
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

section Generic

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- A blended adjustment `x + ψ(x) (P(Qx) - Qx)` keeps a block value `c` of a block `J` retained by
`Q` when the stage projection has it at the projected input and either the cutoff is one there or
the input already has it. -/
theorem adjustmentMap_apply_eq_GAF2 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (Pst : H → H) (ψ : H → ℝ) (J : H →L[ℝ] V) (hJQ : ∀ y, J (Q.starProjection y) = J y)
    {x : H} {c : V} (hy : J (Pst (Q.starProjection x)) = c) (hψ : ψ x = 1 ∨ J x = c) :
    J (adjustmentMap Q Pst ψ x) = c := by
  rw [adjustmentMap_apply, map_add, map_smul, map_sub, hy, hJQ]
  rcases hψ with h | h
  · rw [h, one_smul, add_sub_cancel]
  · rw [h, sub_self, smul_zero, add_zero]

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The cutoffs of the retained markers of `𝓔⁰` take values in `[0, 1]`. -/
theorem cgpMarkerCutoff_mem_Icc_GAF2
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (hΔ : 0 < Δ) (i : CGPMarkerIndex L.toLocalChartFamily) (p : X) :
    cgpMarkerCutoff L.toLocalChartFamily i p ∈ Icc (0 : ℝ) 1 := by
  rcases i with j | j | j
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h := L.circle_cutoff_apply hj p
    change L.circle.cutoff j.1 p ∈ Icc (0 : ℝ) 1
    rw [h]
    split_ifs
    · exact ⟨circleCutoffBump_LC87.nonneg, circleCutoffBump_LC87.le_one⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    change L.toLocalChartFamily.slim.cutoff j.1 p ∈ Icc (0 : ℝ) 1
    rw [slimFamily_cutoff_eq_KA2 L.toLocalChartFamily hj]
    exact (L.slim.centre j.1 hj).cutoff_mem_Icc p
  · exact cgpEdgeCutoff_mem_Icc L.toLocalChartFamily hΔ j.1 p

/-- FC01's block identity of `𝓔⁰` at a retained marker: `u_i(𝓔⁰ p) = R_i ζ_i(p) η_i(p)` and
`v_i(𝓔⁰ p) = R_i ζ_i(p)`, `R_i = ρ(c_i)`. -/
theorem cgpGlobalMap_markerBlock_GAF2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : CGPMarkerIndex L) (p : X) :
    blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpMarkerTag L Z i) (cgpGlobalMap L Z p) =
        (ρ (cgpMarkerCentre L i) * cgpMarkerCutoff L i p) • cgpCoord L Z (cgpMarkerTag L Z i) p ∧
      blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpMarkerTag L Z i) (cgpGlobalMap L Z p) =
        ρ (cgpMarkerCentre L i) * cgpMarkerCutoff L i p := by
  rcases i with j | j | j <;> exact ⟨rfl, rfl⟩

/-- FC26's (AS) at a positive retained cutoff: `3R_i/4 ≤ ρ(p) ≤ 5R_i/4`. -/
theorem cgpMarkerCutoff_scale_GAF2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (i : CGPMarkerIndex L) (p : X) (hp : 0 < cgpMarkerCutoff L i p) :
    3 * ρ (cgpMarkerCentre L i) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (cgpMarkerCentre L i) / 4 := by
  refine (fc26_row L Z hΔ hσs hσs1 hΛ hsmall).1 i p ?_
  rw [cgpMarker, ← blockMarkerCLM_apply, (cgpGlobalMap_markerBlock_GAF2 L Z i p).2]
  exact mul_pos (hρ _) hp

/-- **GAF06** on the actual original map: for every retained index `i` (circle, slim or edge),
every `ℓ ≥ 1` and every map `E` with GAF02's (AM0) on the segment `H_τ = (1-τ)F + τE` and
`|E - F| < c₃ρ`, `c₃ < 1/1000`: (RP) `v_i(H_τ p) > .9R_i`, `|u_i(H_τ p)| ≤ 4ℓ v_i(H_τ p)` force a
positive original cutoff and `|η_i(p)| < 4.01 ℓ`. -/
theorem gaf06_segment_localization
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (E : X → BlockSpace (fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)) {c₃ ℓ : ℝ}
    (hc₃ : c₃ < 1 / 1000) (hℓ : 1 ≤ ℓ) (i : CGPMarkerIndex L.toLocalChartFamily)
    (hAM0 : ∀ p, ∀ τ ∈ Icc (0 : ℝ) 1, cgpMarkerCutoff L.toLocalChartFamily i p = 0 →
      |blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i)
          ((1 - τ) • cgpGlobalMap L.toLocalChartFamily Z p + τ • E p)| ≤
        ρ (cgpMarkerCentre L.toLocalChartFamily i) / 32)
    (hAE : ∀ p, ‖E p - cgpGlobalMap L.toLocalChartFamily Z p‖ < c₃ * ρ p) :
    ∀ p, ∀ τ ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ (cgpMarkerCentre L.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i)
          ((1 - τ) • cgpGlobalMap L.toLocalChartFamily Z p + τ • E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i)
          ((1 - τ) • cgpGlobalMap L.toLocalChartFamily Z p + τ • E p)‖ ≤
        4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i)
          ((1 - τ) • cgpGlobalMap L.toLocalChartFamily Z p + τ • E p) →
      0 < cgpMarkerCutoff L.toLocalChartFamily i p ∧
        ‖cgpCoord L.toLocalChartFamily Z (cgpMarkerTag L.toLocalChartFamily Z i) p‖ <
          401 / 100 * ℓ := by
  have hΔ0 : 0 < Δ := by linarith
  exact norm_coordinate_lt_of_ratio_on_segment (cgpGlobalMap L.toLocalChartFamily Z) E
    (blockVectorCLM (cgpMarkerTag L.toLocalChartFamily Z i))
    (blockMarkerCLM (cgpMarkerTag L.toLocalChartFamily Z i)) (norm_blockVectorCLM_le _)
    (norm_blockMarkerCLM_le _) (cgpMarkerCutoff L.toLocalChartFamily i) ρ
    (cgpCoord L.toLocalChartFamily Z (cgpMarkerTag L.toLocalChartFamily Z i)) (hρ _) hℓ hc₃
    (cgpGlobalMap_markerBlock_GAF2 L.toLocalChartFamily Z i)
    (fun p => (cgpMarkerCutoff_mem_Icc_GAF2 L hΔ0 i p).1) hAM0
    (cgpMarkerCutoff_scale_GAF2 L.toLocalChartFamily Z hΔ hσs hσs1 hΛ hsmall i) hAE

/-- **GAF07, no extra base points**, on the actual original map: for every retained index and every
map `E` with (AM0) at `E` and `|E - F| < c₃ρ`: marker `> .9R_i` at `E p` forces marker
`< (1 + 1/800)R_i`, and the ratio threshold `4ℓ` puts `u_i(E p)` in the `5.5ℓR_i` ball. -/
theorem gaf07_marker_bounds
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (E : X → BlockSpace (fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)) {c₃ ℓ : ℝ}
    (hc₃ : c₃ < 1 / 1000) (hℓ : 1 ≤ ℓ) (i : CGPMarkerIndex L.toLocalChartFamily)
    (hAM0 : ∀ p, cgpMarkerCutoff L.toLocalChartFamily i p = 0 →
      |blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i) (E p)| ≤
        ρ (cgpMarkerCentre L.toLocalChartFamily i) / 32)
    (hAE : ∀ p, ‖E p - cgpGlobalMap L.toLocalChartFamily Z p‖ < c₃ * ρ p) :
    ∀ p, 9 / 10 * ρ (cgpMarkerCentre L.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i) (E p) →
      blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i) (E p) <
        (1 + 1 / 800) * ρ (cgpMarkerCentre L.toLocalChartFamily i) ∧
      (‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i) (E p)‖ <
          4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
            (cgpMarkerTag L.toLocalChartFamily Z i) (E p) →
        ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily Z => ℝ²)
          (cgpMarkerTag L.toLocalChartFamily Z i) (E p)‖ <
          11 / 2 * ℓ * ρ (cgpMarkerCentre L.toLocalChartFamily i)) := by
  have hΔ0 : 0 < Δ := by linarith
  exact marker_lt_and_norm_lt_of_marker_gt (cgpGlobalMap L.toLocalChartFamily Z) E
    (blockVectorCLM (cgpMarkerTag L.toLocalChartFamily Z i))
    (blockMarkerCLM (cgpMarkerTag L.toLocalChartFamily Z i)) (norm_blockMarkerCLM_le _)
    (cgpMarkerCutoff L.toLocalChartFamily i) ρ
    (cgpCoord L.toLocalChartFamily Z (cgpMarkerTag L.toLocalChartFamily Z i)) (hρ _) hℓ hc₃
    (cgpGlobalMap_markerBlock_GAF2 L.toLocalChartFamily Z i)
    (fun p => (cgpMarkerCutoff_mem_Icc_GAF2 L hΔ0 i p).1)
    (fun p => (cgpMarkerCutoff_mem_Icc_GAF2 L hΔ0 i p).2) hAM0
    (cgpMarkerCutoff_scale_GAF2 L.toLocalChartFamily Z hΔ hσs hσs1 hΛ hsmall i) hAE

/-- **GAF07, first inclusion**, on the actual original map: at a full-marker point with
`|η_i(p)| ≤ 3.5ℓ` the adjusted vector satisfies `|u_i(E p)| < 4ℓR_i` (for `|E - F| < c₃ρ`). -/
theorem gaf07_first_inclusion
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (E : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) {c₃ ℓ : ℝ} (hc₃ : c₃ < 1 / 1000)
    (hℓ : 1 ≤ ℓ) (i : CGPMarkerIndex L)
    (hAE : ∀ p, ‖E p - cgpGlobalMap L Z p‖ < c₃ * ρ p) :
    ∀ p, cgpMarkerCutoff L i p = 1 → ‖cgpCoord L Z (cgpMarkerTag L Z i) p‖ ≤ 7 / 2 * ℓ →
      ‖blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpMarkerTag L Z i) (E p)‖ <
        4 * ℓ * ρ (cgpMarkerCentre L i) :=
  norm_lt_four_mul_of_full_marker (cgpGlobalMap L Z) E (blockVectorCLM (cgpMarkerTag L Z i))
    (norm_blockVectorCLM_le _) (cgpMarkerCutoff L i) ρ (cgpCoord L Z (cgpMarkerTag L Z i))
    (hρ _) hℓ hc₃ (fun p => (cgpGlobalMap_markerBlock_GAF2 L Z i p).1)
    (cgpMarkerCutoff_scale_GAF2 L Z hΔ hσs hσs1 hΛ hsmall i) hAE

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNSL_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNSL_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCSL_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF05, stage one, source plateau** on the actual original map: on the original threshold-6
circle plateau (`|η_i(p)| < 6` on `B(c_i, 200ρ(c_i))`) CFS31's source cutoff is one at `𝓔⁰ p`, so
the stage-one output `Ψ₁(𝓔⁰ p) = 𝓔⁰ p + ψ₁(P(Q 𝓔⁰ p) - Q 𝓔⁰ p)` has every block value `c` of a block
`J` retained by `Q` that the stage projection `P` has at `Q 𝓔⁰ p` (GAF03 gives `v_i(P z) = R_i`). -/
theorem gaf05_stageOne_plateau
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Q : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    [Q.HasOrthogonalProjection]
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (J : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] W)
    (hJQ : ∀ y, J (Q.starProjection y) = J y) {c : W} {p : X}
    (hp : ∃ j : P.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6)
    (hPst : J (Pst (Q.starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p))) = c) :
    J (adjustmentMap Q Pst (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
      (gafCircleVector P) (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p)) = c :=
  adjustmentMap_apply_eq_GAF2 Q Pst _ J hJQ hPst
    (Or.inl ((gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1).2.2.1 p hp))

end DifferentialGeometry.Geometry.Collapse
