import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp02RowEDP23

/-!
# EDP03 item 5 (B): the base `W₂`, the exact marker, GAF05's coordinate, the third stage

Blueprint `master207B.tex`, EDP03 (`lem:fibration-edge-original-buffer-and-height`, B:6837–6947)
with the proof of EDP04 that consumes it (B:6949–7038: "On a witnessing patch `g_i` is its actual
coordinate by GAF05", "Finally `s, A`, and therefore `V`, are unchanged by the third stage"), on an
enhanced chain `Ĉ : Gaf02ChainE L …` of a family `L : LocalChartPacketsC14`
(`π₂E = (gafStageQ … 1).starProjection ∘ E`, `W₂ = Ĉ.toChain.finalBase_BAS 1`, `g_k = u_k(E)/R_k`,
`Y_k = {x ∈ B(k, 100Δρ_k) : |η_k x| < 5Δ, t x < 5Δ}`; group G3 of lane S-EDP02-03). Item 5 of lane
C14-EDP-E's classification (sheet C14-EDP3 §4) — "`W₂`, marker `R_i`, GAF05 coordinate uniqueness
and exact marker; EDP02's (ELoc); CGP08's `Θ₂` for the third-stage clause" — is, clause by clause:

* `Gaf02ChainE.edgeDomain_base_coordinate_EDP23` (`W₂`, exact marker, GAF05's chart): on `Y_k`,
  `π₂E x ∈ W₂ ∩ {v_k > .9R_k, |u_k| < 5.5ΔR_k}`, `v_k(E x) = R_k`, `g_k x ∈ (-5.5Δ, 5.5Δ)` and
  `π₂E x = ψ_k(g_k x)` for GAF05's smooth inverse chart `ψ_k` of `W₂ ∩ {marked k}` (so `g_k` IS
  the actual coordinate of the embedded base on `Y_k`);
* `Gaf02ChainE.coordinate_uniqueness_EDP23`: for `x ∈ Y_k` and `w ∈ W₂ ∩ {marked k}`,
  `π₂E x = w ↔ g_k x = R_k⁻¹u_k(w)` (coordinate uniqueness on `V_k`);
* `Gaf02Chain.third_stage_unchanged_EDP23`: `u_{E'}(E) = u_{E'}(g₂)` and `ℓ_ρ(E) = ℓ_ρ(g₂)`
  (the third stage keeps the `E'` block and the scale block), hence `s`, `A`, `T` and `V` are
  the same whether computed from `E` or from `g₂`;
* `Gaf02ChainE.thirdStage_fibre_eq_EDP23` (CGP08's `Θ₂`, B:7033–7038): for `w₀ ∈ V₂⁰` with
  `Θ₂ w₀ ∈ B₂`, `{x ∈ V : π₂E x = Θ₂ w₀} = {x ∈ V : f₂⁰ x = w₀}` — both WHOLE restricted fibres
  (`⊆` by (ELoc) ⇒ `x ∈ U₂ ⇒ f₂⁰ x ∈ V₂⁰` and injectivity of `Θ₂` on `V₂⁰`; `⊇` by
  `π₂E = Θ₂ ∘ f₂⁰`);
* (ELoc) and the vertical set equality: group G2 (`edp02_row_EDP23`, clauses 4 and 6).

The row `Gaf02ChainE.edp03_itemB_row_EDP23` is the conjunction (numeric premise only `Δ ≥ 2`).

CLAUSE TABLE (EDP03, B:6837–6947, with the part of EDP04's proof that uses it):
* `Y_k ⊆ B(k, 8Δρ_k)`; `η_k`, `H₀` smooth on `Y_k`; `dη_k > .99`; compact `Q_k ⋐ Y_k` with
  (EBuf); `H₀` versus `t`; the collar's least singular value `> .9`: `edp03_efree_C14`
  (C14-EDP3 G1/G2, E-free; numerics `Δ ≥ 1`, `μ τ ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`, `σc ≤ 1/1000`,
  `b·1000Δ ≤ 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`).
* `g_k`, `T` smooth on `Y_k`, `s > 0`; (ETan) `|g_k − η_k| < 5c₃/4`, `‖Dg_k − Dη_k‖ < c₃`:
  `edp03_final_clauses_C14_EDPE` (C14-EDP-E G1, chain only).
* (EH) `|T − t|`, `‖DT − Dt‖ < h_*` on the band; `T < .31Δ` for `t < .3Δ`:
  `Gaf02Chain.edge_height_EH_EDPE` (C14-EDP-E G2), `edp02_final_clauses_C14_EDPE`.
* item 5 (B): this file; (ELoc), vertical set equality: `edp02_row_EDP23` (G2).
* the whole conjunction with explicit parameter premises: `Gaf02ChainE.edp03_row_EDP23`
  (file `ActualStageChainEdp03RowEDP23`).
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

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}

/-- **The third stage keeps `s` and `A`** (B:7029, "`s, A`, and therefore `V`, are unchanged by the
third stage"): the `E'` vector block and the scale block of `E = Ψ₃ ∘ g₂` are those of `g₂`. -/
theorem third_stage_unchanged_EDP23 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    gafHeightVector P.toLocalChartFamily P.zero (C.E p) =
      gafHeightVector P.toLocalChartFamily P.zero (C.g₂ p) ∧
    gafScaleMarker P.toLocalChartFamily P.zero (C.E p) =
      gafScaleMarker P.toLocalChartFamily P.zero (C.g₂ p) := by
  obtain ⟨-, hs2, -, he2, -⟩ := gafStage_kept_tags_GAF8 P.toLocalChartFamily P.zero
  have hE : ∀ t, t ∉ gafStageTags P.toLocalChartFamily P.zero 2 → C.E p t = C.g₂ p t :=
    fun t ht => (C.keeps_orthogonal_coordinates (C.g₂ p)).2.2.2.2.2.2 t ht
  refine ⟨?_, ?_⟩
  · rw [gafHeightVector, blockVectorCLM_apply, blockVectorCLM_apply, hE _ he2]
  · rw [gafScaleMarker, blockMarkerCLM_apply, blockMarkerCLM_apply, hE _ hs2]

end Gaf02Chain

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

namespace Gaf02ChainE

/-- **`W₂`, the exact marker and GAF05's chart on `Y_k`** (EDP03 item 5; B:6965–6968, B:6990–6991):
for `x ∈ Y_k`, `π₂E x ∈ W₂ ∩ {v_k > .9R_k, |u_k| < 5.5ΔR_k}`, `v_k(E x) = R_k`,
`g_k x ∈ (-5.5Δ, 5.5Δ)` and `π₂E x = ψ_k(g_k x)` for the smooth inverse chart `ψ_k` of the
embedded base piece (GAF05: `R_k⁻¹u_k : V_k → (-5.5Δ, 5.5Δ)` is a bijection with smooth
inverse). -/
theorem edgeDomain_base_coordinate_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (k : L.edge.finite_centres.toFinset) :
    ∃ ψ : ℝ → BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * Δ)) ∧
      ∀ x ∈ ball k.1 (100 * Δ * ρ k.1), |L.edge.coord k.1 x| < 5 * Δ →
        L.edge.smoothing x / ρ x < 5 * Δ →
        (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
            Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
              (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
              (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ ∧
          blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
          EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
            (Ĉ.toChain.E x)) / ρ k.1 ∈ ball (0 : ℝ) (11 / 2 * Δ) ∧
          (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) =
            ψ (EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
              (Ĉ.toChain.E x)) / ρ k.1) := by
  obtain ⟨-, hbij, ψ, hψ, hinv, -⟩ := Ĉ.gaf05_edgeBase_chart_GAFD k
  obtain ⟨-, hΔ, -⟩ := Ĉ.toChain.std
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨ψ, hψ, fun x hx hη ht => ?_⟩
  have hmem := (Ĉ.toChain.final_submersion_edge_BAS Ĉ.rough k hx hη ht).1
  have hmark := (Ĉ.gaf05_edge_stage_plateau_GAFD k hx (by linarith)
    (by change L.edge.smoothing x / ρ x < 6 * Δ; linarith)).2
  have hκ : ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
      ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) =
      EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
        (Ĉ.toChain.E x)) / ρ k.1 := by
    change (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
      CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
        ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))) = _
    rw [gafStageQ_edgeVector_FDC, div_eq_inv_mul]
    rfl
  refine ⟨hmem, hmark, ?_, ?_⟩
  · rw [← hκ]
    exact hbij.mapsTo hmem
  · rw [← hκ]
    exact (hinv.1 hmem).symm

/-- **GAF05's coordinate uniqueness on `V_k`** (B:6990–6995, EDP04's fibre identification): for
`x ∈ Y_k` and `w ∈ W₂ ∩ {v_k > .9R_k, |u_k| < 5.5ΔR_k}`, `π₂E x = w` iff
`g_k x = R_k⁻¹u_k(w)`. -/
theorem coordinate_uniqueness_EDP23 {Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw}
    (k : L.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw : w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
      (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ)
    {x : X} (hx : x ∈ ball k.1 (100 * Δ * ρ k.1)) (hη : |L.edge.coord k.1 x| < 5 * Δ)
    (ht : L.edge.smoothing x / ρ x < 5 * Δ) :
    (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) = w ↔
      EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
        (Ĉ.toChain.E x)) / ρ k.1 =
        ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k)) w := by
  have hmem := (Ĉ.toChain.final_submersion_edge_BAS Ĉ.rough k hx hη ht).1
  have hκ : ((ρ k.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
      ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) =
      EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero k
        (Ĉ.toChain.E x)) / ρ k.1 := by
    change (ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
      CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
        ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))) = _
    rw [gafStageQ_edgeVector_FDC, div_eq_inv_mul]
    rfl
  rw [← hκ]
  constructor
  · intro h
    rw [h]
  · intro h
    exact ((Ĉ.gaf05_edgeBase_chart_GAFD k).2.1).injOn hmem hw h

/-- **The third-stage clause (CGP08's `Θ₂`)** (B:7029–7038; `Δ ≥ 2`): for `w₀` in the marked base
`V₂⁰` with `Θ₂ w₀ ∈ B₂`, the WHOLE restricted fibres agree,
`{x ∈ V : π₂E x = Θ₂ w₀} = {x ∈ V : f₂⁰ x = w₀}` (`f₂⁰ = π_{Q₂} ∘ g₂ = stageMap_BAS 1`). -/
theorem thirdStage_fibre_eq_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ)
    {w₀ : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)}
    (hw₀ : w₀ ∈ Ĉ.toChain.markedBase_BAS 1)
    (hB : Ĉ.toChain.Θ_BAS 1 w₀ ∈ Ĉ.edgeBase_EDP23) :
    {x | x ∈ ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∧
      (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) =
        Ĉ.toChain.Θ_BAS 1 w₀} =
    {x | x ∈ ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∧
      Ĉ.toChain.stageMap_BAS 1 x = w₀} := by
  obtain ⟨-, k, hv, hu⟩ := hB
  ext x
  constructor
  · rintro ⟨hxV, hxw⟩
    refine ⟨hxV, ?_⟩
    have hv' : 9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero
        => ℝ²) (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x)) := by
      rw [hxw]
      exact hv
    have hu' : ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection
          (Ĉ.toChain.E x))‖ < 4 * Δ * blockMarkerCLM (V := fun _ : CGPTag
            L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) := by
      rw [hxw]
      exact hu
    obtain ⟨hball, hη, ht, -⟩ := Ĉ.toChain.stageTwo_ratio_localization_FDC hΔ k hv' hu' hxV
    have hΔ0 : 0 < Δ := by linarith
    have hpatch := Ĉ.toChain.edge_mem_patch_of_domain5_BAS k hball (by linarith)
      (by change L.edge.smoothing x / ρ x < 5 * Δ; linarith)
    have hmark : Ĉ.toChain.stageMap_BAS 1 x ∈ Ĉ.toChain.markedBase_BAS 1 :=
      mem_iUnion.mpr ⟨k, hpatch⟩
    refine (Ĉ.toChain.theta_injOn_BAS Ĉ.rough 1) hmark hw₀ ?_
    rw [← Ĉ.toChain.final_factor_BAS 1 x]
    exact hxw
  · rintro ⟨hxV, hxw⟩
    refine ⟨hxV, ?_⟩
    rw [Ĉ.toChain.final_factor_BAS 1 x, hxw]

/-- **EDP03 item 5 (B) as ONE statement on the chain** (`Δ ≥ 2`): the base coordinate (`W₂`, exact
marker, GAF05's chart) on every `Y_k`, GAF05's coordinate uniqueness, the third stage keeps `s` and
`A`, and CGP08's `Θ₂` identifies the whole restricted fibres. -/
theorem edp03_itemB_row_EDP23 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ : 2 ≤ Δ) :
    (∀ k : L.edge.finite_centres.toFinset, type_of% (Ĉ.edgeDomain_base_coordinate_EDP23 k)) ∧
    (∀ (k : L.edge.finite_centres.toFinset)
      (w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
      (hw : w ∈ Ĉ.toChain.finalBase_BAS 1 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafEdgeVector L.toLocalChartFamily L.zero k))
        (gafEdgeMarker L.toLocalChartFamily L.zero k) (ρ k.1) Δ) {x : X}
      (hx : x ∈ ball k.1 (100 * Δ * ρ k.1)) (hη : |L.edge.coord k.1 x| < 5 * Δ)
      (ht : L.edge.smoothing x / ρ x < 5 * Δ),
      type_of% (coordinate_uniqueness_EDP23 (Ĉ := Ĉ) k hw hx hη ht)) ∧
    (∀ p : X, type_of% (Ĉ.toChain.third_stage_unchanged_EDP23 p)) ∧
    (∀ (w₀ : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
      (hw₀ : w₀ ∈ Ĉ.toChain.markedBase_BAS 1) (hB : Ĉ.toChain.Θ_BAS 1 w₀ ∈ Ĉ.edgeBase_EDP23),
      type_of% (Ĉ.thirdStage_fibre_eq_EDP23 hΔ hw₀ hB)) :=
  ⟨fun k => Ĉ.edgeDomain_base_coordinate_EDP23 k,
    fun k _ hw _ hx hη ht => coordinate_uniqueness_EDP23 (Ĉ := Ĉ) k hw hx hη ht,
    fun p => Ĉ.toChain.third_stage_unchanged_EDP23 p,
    fun _ hw₀ hB => Ĉ.thirdStage_fibre_eq_EDP23 hΔ hw₀ hB⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
