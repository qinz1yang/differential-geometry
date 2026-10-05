import DifferentialGeometry.Geometry.Fibration.ActualStageChainLater
import DifferentialGeometry.Geometry.Fibration.ActualStageChainPatches
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeLimit
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEReplacement

/-!
# FDC01's `π₂E(q) ∈ W₂ ∩ B₂` on the chain object

Blueprint `master207B.tex`, FDC01 (B:7238–7240: "The original `i` coordinates put `q ∈ U₂`. GAF02
and GAF05 therefore put its final image in `W₂`"), with BASES' actual stage-two base
`W₂ = Θ₂(V₂⁰) = C.finalBase_BAS 1` (lane C14-BASES G3: `V₂⁰ = ⋃_j V_j⁰` the marked edge patches of
the stage-two zero set, `Θ₂ = Ψ₃₂`, `π₂E = Θ₂ ∘ f₂` by `final_factor_BAS`) and EDP02's (ED)
`B₂ = ⋃_i {w ∈ W₂ : v_i(w) > .9R_i, |u_i(w)| < 4Δ v_i(w)}` (written out; `|u_i| ≤ ‖u_i‖`).

* `Gaf02Chain.stageTwo_mem_finalBase_FDC`: a point of FC33's threshold-5 domain `U₂` in chart `j`
  (`q ∈ B(j, 100ΔR_j)`, `|η_j(q)| < 5Δ`, `t(q) < 5Δ`) has `π₂E(q) ∈ W₂`
  (`edge_mem_patch_of_domain5_BAS`: `f₂(q) ∈ V_j⁰`).
* `Gaf02ChainE.fdc01_base_clauses_FDC`: at a replacement index (`ζ_k = 1`, `d(q, k) < 7ΔR_k`,
  `|η_k| < 2Δ`, `t ≤ 4.01Δ`) all of FDC01's base clauses on `π₂E q`, including `π₂E(q) ∈ W₂`.
* `Gaf02Chain.stageTwo_mem_base_FDC`: an exact final marker `v_j(E q) = R_j`, `|u_j(E q)| < 4ΔR_j`
  and `q ∈ V` give `π₂E(q) ∈ W₂`, `v_j(π₂E q) > .9R_j`, `|u_j(π₂E q)| < 4Δ v_j(π₂E q)`, i.e.
  `π₂E(q) ∈ B₂` and `q ∈ X₂ = (π₂E)⁻¹(B₂) ∩ V` (localization by `fdc02_limit_point_FDC`).
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

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **`π₂E(q) ∈ W₂` on the threshold-5 edge domain** (FDC01, B:7238–7240): `q ∈ B(j, 100ΔR_j)`,
`|η_j(q)| < 5Δ`, `t(q) < 5Δ` give `π₂E(q) = Θ₂(f₂ q) ∈ Θ₂(V₂⁰) = W₂`. -/
theorem stageTwo_mem_finalBase_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X} (hq : q ∈ ball j.1 (100 * Δ * ρ j.1))
    (hη : |P.edge.coord j.1 q| < 5 * Δ) (ht : P.edge.smoothing q / ρ q < 5 * Δ) :
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q) ∈ C.finalBase_BAS 1 := by
  rw [C.final_factor_BAS 1 q]
  refine ⟨C.stageMap_BAS 1 q, ?_, rfl⟩
  change C.stageMap_BAS 1 q ∈ ⋃ k, C.edgePatch_BAS k
  exact mem_iUnion.mpr ⟨j, C.edge_mem_patch_of_domain5_BAS j hq hη ht⟩

/-- **The witnessed edge candidate lies in `X₂`**: `v_j(E q) = R_j`, `|u_j(E q)| < 4ΔR_j` and
`q ∈ V` give `π₂E(q) ∈ W₂`, `v_j(π₂E q) > .9R_j` and `|u_j(π₂E q)| < 4Δ v_j(π₂E q)` (so
`π₂E(q) ∈ B₂`, `q ∈ X₂`). -/
theorem stageTwo_mem_base_FDC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {q : X}
    (hv : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q) = ρ j.1)
    (hu : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j))) (C.E q)‖ < 4 * Δ * ρ j.1)
    (hV : q ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ}) :
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q) ∈ C.finalBase_BAS 1 ∧
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q)) ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl j))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.E q))‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (C.E q)) := by
  obtain ⟨hball, hη, ht, -⟩ := C.fdc02_limit_point_FDC j hv hu.le hV
  obtain ⟨-, hΔ, -⟩ := C.std
  have hrj := hρ j.1
  refine ⟨C.stageTwo_mem_finalBase_FDC j hball (by linarith) (by linarith), ?_, ?_⟩
  · rw [gafStageQ_edgeMarker_FDC, hv]
    linarith
  · rw [gafStageQ_edgeMarker_FDC, gafStageQ_edgeVector_FDC, hv]
    exact hu

end Gaf02Chain

namespace Gaf02ChainE

variable {vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **FDC01's base clauses at a replacement index** (enhanced chain): `ζ_k(q) = 1`,
`d(q, k) < 7ΔR_k`, `|η_k(q)| < 2Δ`, `t(q) ≤ 4.01Δ` (`Δ ≥ 100`) give (Repl) on `π₂E q`
(`v_k = R_k`, `|u_k|/R_k < 3Δ`), `π₂E(q) ∈ W₂`, and `v_k(π₂E q) > .9R_k`,
`|u_k(π₂E q)| < 4Δ v_k(π₂E q)` (so `π₂E(q) ∈ B₂`). -/
theorem fdc01_base_clauses_FDC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hΔ : 100 ≤ Δ)
    (k : P.toLocalChartFamily.edge.finite_centres.toFinset) {q : X}
    (hζ : P.edge.cutoff k.1 q = 1) (hqk : dist q k.1 < 7 * Δ * ρ k.1)
    (hηk : |P.edge.coord k.1 q| < 2 * Δ) (ht : P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E q)) = ρ k.1 ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E q))‖ / ρ k.1 < 3 * Δ ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E q) ∈
        C.toChain.finalBase_BAS 1 ∧
      9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E q)) ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E q))‖ <
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (C.toChain.E q)) := by
  have hc2 := C.toChain.c_le_BAS 2
  have hrk := hρ k.1
  have hwin := C.toChain.edge_block_window_FDC k hζ hqk
  have h3 := (fdc01_window_numbers_FDC hΔ hrk hc2 hηk hwin.1 hwin.2).2.1
  have hv := C.edge_exact_marker_FDC k (by rw [hζ]; exact one_ne_zero) (by linarith)
    (by linarith)
  have h56 := stageQ_edge_repl_FDC P.toLocalChartPackets k (C.toChain.E q) hv h3
  have hball : q ∈ ball k.1 (100 * Δ * ρ k.1) := by
    rw [mem_ball]
    nlinarith
  have hW := C.toChain.stageTwo_mem_finalBase_FDC k hball (by linarith) (by linarith)
  have h7 : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
        (C.toChain.E q))‖ < 4 * Δ * ρ k.1 := by
    have h6 := h56.2
    rw [div_lt_iff₀ hrk] at h6
    nlinarith
  have h9 : 9 / 10 * ρ k.1 < ρ k.1 := by linarith
  exact ⟨h56.1, h56.2, hW, h56.1 ▸ h9, h56.1 ▸ h7⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
