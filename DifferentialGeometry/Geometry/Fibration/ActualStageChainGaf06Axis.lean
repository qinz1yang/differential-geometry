import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf06
import DifferentialGeometry.Geometry.Fibration.ActualStageChainWitness

/-!
# GAF06 with the AXIS ratio for one-dimensional charts (slim, edge), on the chain object

Blueprint `master207B.tex`, GAF06 (`lem:fibration-whole-ratio-preimage-localization`,
B:6008–6047). For a one-dimensional chart (slim, edge) the blueprint's vector coordinate `u_i` is
the REAL coordinate; in the block space its value lies in `ℝ²` and the original map `𝓔⁰` puts it on
the axis (`u_i(𝓔⁰ p) = R_iζ_i(p) planeAxis(η_i(p))`). Lane C14-BASES reads it as
`axisCoordCLM_BAS ∘ u_i` (CGP07 charts, the open base `B₃ = slimBase_BAS`, GAF05's edge / slim
pieces). Since `|axis w| ≤ ‖w‖`, (RP) with the axis coordinate is WEAKER than (RP) with the full
norm, so the full-norm theorem `Gaf02Chain.gaf06_G47` does not apply; the same estimate does
(`|η_i| ζ R_i = |axis u_i(𝓔⁰ p)| ≤ |axis u_i(H_τ p)| + ‖H_τ p − 𝓔⁰ p‖`), with the same bound
`4.01ℓ`.

* `Gaf02Chain.gaf06_axis_GAFD`: for EVERY retained index `i`, every `ℓ ≥ 1`, every `p`, `τ`: (RP)
  `v_i(H_τ p) > .9R_i`, `|axis u_i(H_τ p)| ≤ 4ℓ v_i(H_τ p)` ⇒ positive original cutoff, `p` in the
  chart domain and `|axis η_i(p)| < 4.01ℓ`.
* `Gaf02Chain.gaf06_slim_axis_GAFD` (`ℓ = 10⁵Δ`): the original slim cutoff is ONE and
  `|η_i(p)| < 4.01·10⁵Δ`; `Gaf02Chain.gaf06_edge_axis_GAFD` (`ℓ = Δ`): positive cutoff and the
  TANGENTIAL bound `|η_i(p)| < 4.01Δ` only (B:6022–6023). Stated with BASES' block names
  `gafSlimVector`, `gafSlimMarker`, `gafEdgeVector`, `gafEdgeMarker`.
* `Gaf02Chain.gaf06_slim_axis_final_GAFD`, `Gaf02Chain.gaf06_edge_axis_final_GAFD`: the end point
  `τ = 1` (`H₁ = C.E`).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The axis coordinate of a block vector is a contraction. -/
theorem norm_axis_comp_blockVector_le_GAFD {κ : Type*} [Fintype κ] (t : κ) :
    ‖axisCoordCLM_BAS.comp (blockVectorCLM (V := fun _ : κ => ℝ²) t)‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [norm_axisCoordCLM_le_BAS, norm_blockVectorCLM_le (V := fun _ : κ => ℝ²) t,
      norm_nonneg axisCoordCLM_BAS, norm_nonneg (blockVectorCLM (V := fun _ : κ => ℝ²) t)])

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF06 with the axis ratio, on the chain object** (B:6008): with GAF01's `c₃ = c 2 < 1/1000`,
for EVERY retained index `i`, every `ℓ ≥ 1`, every `p` and `τ ∈ [0, 1]`, (RP) at
`H_τ p = (1 − τ)𝓔⁰ p + τ C.E p` with the AXIS coordinate of the vector block
(`v_i > .9R_i`, `|axis u_i| ≤ 4ℓ v_i`) forces a positive original cutoff, `p` in the chart domain
and `|axis η_i(p)| < 4.01ℓ`. -/
theorem gaf06_axis_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000) {ℓ : ℝ}
    (hℓ : 1 ≤ ℓ) (i : CGPMarkerIndex P.toLocalChartFamily) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ (cgpMarkerCentre P.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      ‖(axisCoordCLM_BAS.comp (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero =>
          ℝ²) (cgpMarkerTag P.toLocalChartFamily P.zero i)))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)‖ ≤
        4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      0 < cgpMarkerCutoff P.toLocalChartFamily i p ∧
        p ∈ ball (cgpMarkerCentre P.toLocalChartFamily i)
          (cgpMarkerDomain P.toLocalChartFamily i * ρ (cgpMarkerCentre P.toLocalChartFamily i)) ∧
        ‖axisCoordCLM_BAS
          (cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero i) p)‖ <
          401 / 100 * ℓ := by
  intro p t ht hmark hratio
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, hσs, hσs1, -, -, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hblock : ∀ q, (axisCoordCLM_BAS.comp (blockVectorCLM
      (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero i)))
          (cgpGlobalMap P.toLocalChartFamily P.zero q) =
        (ρ (cgpMarkerCentre P.toLocalChartFamily i) * cgpMarkerCutoff P.toLocalChartFamily i q) •
          axisCoordCLM_BAS
            (cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero i) q) ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          (cgpGlobalMap P.toLocalChartFamily P.zero q) =
        ρ (cgpMarkerCentre P.toLocalChartFamily i) * cgpMarkerCutoff P.toLocalChartFamily i q := by
    intro q
    obtain ⟨h1, h2⟩ := cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero i q
    refine ⟨?_, h2⟩
    rw [ContinuousLinearMap.comp_apply, h1, map_smul]
  obtain ⟨hpos, hη⟩ := norm_coordinate_lt_of_ratio_on_segment
    (cgpGlobalMap P.toLocalChartFamily P.zero) C.E
    (axisCoordCLM_BAS.comp (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero i)))
    (blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero i))
    (norm_axis_comp_blockVector_le_GAFD _) (norm_blockMarkerCLM_le _)
    (cgpMarkerCutoff P.toLocalChartFamily i) ρ
    (fun q => axisCoordCLM_BAS
      (cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero i) q))
    (hρ _) hℓ hc hblock
    (fun q => (cgpMarkerCutoff_mem_Icc_GAF2 P.toLocalChartFamilyQ hΔ0 i q).1)
    (C.segment_am0_param_G47 i)
    (cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ C.small_range_G47 i)
    C.stage_error_lt.2.2 p t ht hmark hratio
  exact ⟨hpos, cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 i p hpos.ne', hη⟩

/-- **GAF06, slim charts, axis ratio** (`ℓ = 10⁵Δ`, BASES' slim coordinate `axis ∘ u_j`): (RP) at
`H_τ p` puts `p` in `B(c_j, 10⁶Δρ(c_j))` with `|η_j(p)| < 4.01·10⁵Δ`, and the original slim cutoff
is ONE. -/
theorem gaf06_slim_axis_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (j : P.slim.finite_centres.toFinset) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < gafSlimMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)‖ ≤
        4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
          401 / 100 * (10 ^ 5 * Δ) ∧
        P.slim.cutoff j.1 p = 1 := by
  intro p t ht hmark hratio
  obtain ⟨-, hΔ, -⟩ := C.std
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨-, hdom, hη⟩ := C.gaf06_axis_GAFD hc hℓ (.inr (.inl j)) p t ht hmark hratio
  have hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1) := hdom
  change ‖axisCoordCLM_BAS (planeAxis ((P.slim.centre j.1 hj).coord p))‖ <
    401 / 100 * (10 ^ 5 * Δ) at hη
  rw [axisCoordCLM_planeAxis_BAS, Real.norm_eq_abs] at hη
  refine ⟨hp, hη, ?_⟩
  rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
  refine (P.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le ?_ ?_
  · convert hp using 2
    norm_num
  · nlinarith

/-- **GAF06, edge charts, axis ratio** (`ℓ = Δ`, BASES' edge coordinate `axis ∘ u_j`): (RP) at
`H_τ p` gives a positive original edge cutoff, `p ∈ B(c_j, 100Δρ(c_j))` and the TANGENTIAL bound
`|η_j(p)| < 4.01Δ`; no height bound is claimed (B:6022–6023). -/
theorem gaf06_edge_axis_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (j : P.edge.finite_centres.toFinset) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ j.1 < gafEdgeMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p)‖ ≤
        4 * Δ * gafEdgeMarker P.toLocalChartFamily P.zero j
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.E p) →
      0 < P.edge.cutoff j.1 p ∧ p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 401 / 100 * Δ := by
  intro p t ht hmark hratio
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨hpos, hdom, hη⟩ := C.gaf06_axis_GAFD hc hΔ (.inr (.inr j)) p t ht hmark hratio
  change ‖axisCoordCLM_BAS (planeAxis (P.edge.coord j.1 p))‖ < 401 / 100 * Δ at hη
  rw [axisCoordCLM_planeAxis_BAS, Real.norm_eq_abs] at hη
  exact ⟨hpos, hdom, hη⟩

/-- `H₁ = C.E` (the end point of the global segment). -/
theorem segment_one_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • C.E p = C.E p := by
  rw [sub_self, zero_smul, zero_add, one_smul]

/-- **GAF06, slim charts, axis ratio, at the final map** (`τ = 1`): `v_j(E p) > .9R_j`,
`|axis u_j(E p)| ≤ 4·10⁵Δ v_j(E p)` ⇒ `p ∈ B(c_j, 10⁶Δρ(c_j))`, `|η_j(p)| < 4.01·10⁵Δ`, cutoff
one. -/
theorem gaf06_slim_axis_final_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (j : P.slim.finite_centres.toFinset) (p : X)
    (hm : 9 / 10 * ρ j.1 < gafSlimMarker P.toLocalChartFamily P.zero j (C.E p))
    (hr : ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) (C.E p)‖ ≤
      4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero j (C.E p)) :
    p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
        401 / 100 * (10 ^ 5 * Δ) ∧
      P.slim.cutoff j.1 p = 1 :=
  C.gaf06_slim_axis_GAFD hc j p 1 ⟨zero_le_one, le_rfl⟩ (by rw [C.segment_one_GAFD]; exact hm)
    (by rw [C.segment_one_GAFD]; exact hr)

/-- **GAF06, edge charts, axis ratio, at the final map** (`τ = 1`). -/
theorem gaf06_edge_axis_final_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (j : P.edge.finite_centres.toFinset) (p : X)
    (hm : 9 / 10 * ρ j.1 < gafEdgeMarker P.toLocalChartFamily P.zero j (C.E p))
    (hr : ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.E p)‖ ≤
      4 * Δ * gafEdgeMarker P.toLocalChartFamily P.zero j (C.E p)) :
    0 < P.edge.cutoff j.1 p ∧ p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      |P.edge.coord j.1 p| < 401 / 100 * Δ :=
  C.gaf06_edge_axis_GAFD hc j p 1 ⟨zero_le_one, le_rfl⟩ (by rw [C.segment_one_GAFD]; exact hm)
    (by rw [C.segment_one_GAFD]; exact hr)

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
