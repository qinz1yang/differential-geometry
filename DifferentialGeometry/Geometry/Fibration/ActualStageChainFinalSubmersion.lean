import DifferentialGeometry.Geometry.Fibration.ActualStageChainStageSubmersion
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSubmersionSlim

/-!
# GAF02 BASES, seventh step: the threshold-5 submersions `π_st E : U_st → W_st`

Blueprint `master207B.tex`, GAF02 (B:5797–5870: "FC33's EXACT original threshold-5 domains `U_j`
have smooth submersions `π_jE : U_j → W_j` onto their images in embedded bases of dimensions
`2, 1, 1`"); external draft 59 §4 seventh step; review 66 D66-7 step 7; review 71 D71-13. Frozen
statements (e1)–(e3) of `build-logs/scratch/C14-BASES/ParallelTargets2.lean` (lane C14-BASESb),
proved by its successor C14-BASESc. Chart form (as `W_st` in `ActualStageChainFinalBases`): the
chart coordinate of `W_st` is the LINEAR `κ_j = R_j⁻¹u_j`.

Route: `κ_j ∘ π_st ∘ E = κ_j ∘ f_st` as FUNCTIONS (`final_factor_BAS`: `π_st E = Θ_st ∘ f_st`
at every point, and `Θ_st` retains the chart's own vector block: `theta_retains_circle_BAS`,
`theta_retains_edge_BAS`, `Θ₃ = id`), so the derivative is the stage submersion's
(`stage_submersion_circle_BAS`, `stage_submersion_edge_BAS` of C14-BASESb,
`stage_submersion_slim_BAS` of C14-BASES-P) at the threshold-6 plateau point; membership in the
piece `W_st ∩ {marked j}` from the threshold-5 patch membership (`*_mem_patch_of_domain5_BAS`)
and the patch identification (`finalBase_inter_*_BAS`).

* `surjective_mfderiv_congr_BAS` (generic transport along a function equality);
* `Gaf02Chain.circle_kappa_final_eq_BAS`, `edge_kappa_final_eq_BAS`, `slim_kappa_final_eq_BAS`
  (the function identities);
* **`Gaf02Chain.final_submersion_circle_BAS`**, **`final_submersion_edge_BAS`**,
  **`final_submersion_slim_BAS`** (verbatim frozen (e1)–(e3));
* `Gaf02Chain.final_mem_finalBase_BAS` (`π_st E(U_st) ⊆ W_st`, every stage).
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

/-- Transport of a surjective manifold derivative along an equality of functions (stated
generically, so that the codomain tangent spaces `T_{f p}`, `T_{f' p}` are compared only through
the function equality). -/
theorem surjective_mfderiv_congr_BAS {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f f' : M → F}
    (h : f = f') {x : M} (hs : Surjective (mfderiv I 𝓘(ℝ, F) f' x)) :
    Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  subst h
  exact hs

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- `κ_j ∘ π₁ ∘ E = κ_j ∘ f₁` (circle chart `j`), as functions. -/
theorem circle_kappa_final_eq_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (fun q => ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E q))) =
      fun q => ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.stageMap_BAS 0 q) := by
  funext q
  rw [C.final_factor_BAS 0 q, smul_apply, smul_apply, (C.theta_retains_circle_BAS j _).1]

/-- `κ_j ∘ π₂ ∘ E = κ_j ∘ f₂` (edge chart `j`, axis coordinate), as functions. -/
theorem edge_kappa_final_eq_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) :
    (fun q => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q))) =
      fun q => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 1 q) := by
  funext q
  rw [C.final_factor_BAS 1 q, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    (C.theta_retains_edge_BAS j _).1]

/-- `κ_j ∘ π₃ ∘ E = κ_j ∘ f₃` (slim chart `j`; `Θ₃ = id`), as functions. -/
theorem slim_kappa_final_eq_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) :
    (fun q => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E q))) =
      fun q => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 2 q) := by
  funext q
  rw [C.final_factor_BAS 2 q]
  rfl

/-- **(e1) Threshold-5 submersion, circle stage** (draft 59 §4 seventh step): on FC33's original
`U₁` in chart `j`, `π₁E(p)` lies in the piece `W₁ ∩ {marked j}` and `D(κ_j ∘ π₁E)(p)` is onto.
Route: `κ_j ∘ π₁ ∘ E = κ_j ∘ f₁` as FUNCTIONS (`final_factor_BAS` + `theta_retains_circle_BAS`,
which holds for every `w`), so the derivative is `stage_submersion_circle_BAS`'s; membership from
`circle_mem_patch_of_domain5_BAS` + `final_factor_BAS` + retention. -/
theorem final_submersion_circle_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈
        C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
          (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun q =>
        ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E q))) p) := by
  refine ⟨?_, ?_⟩
  · rw [C.finalBase_inter_circle_BAS j, C.final_factor_BAS 0 p]
    exact Set.mem_image_of_mem _ (C.circle_mem_patch_of_domain5_BAS j hp hη)
  · exact surjective_mfderiv_congr_BAS (C.circle_kappa_final_eq_BAS j)
      (C.stage_submersion_circle_BAS R j hp (hη.trans (by norm_num)))

/-- **(e2) Threshold-5 submersion, edge stage.** -/
theorem final_submersion_edge_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (100 * Δ * ρ j.1)) (hη : |P.edge.coord j.1 p| < 5 * Δ)
    (ht : cgpHeight P.toLocalChartFamily p < 5 * Δ) :
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E p) ∈
        C.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q))) p) := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  refine ⟨?_, ?_⟩
  · rw [C.finalBase_inter_edge_BAS j, C.final_factor_BAS 1 p]
    exact Set.mem_image_of_mem _ (C.edge_mem_patch_of_domain5_BAS j hp hη ht)
  · exact surjective_mfderiv_congr_BAS (C.edge_kappa_final_eq_BAS j)
      (C.stage_submersion_edge_BAS R j hp (by linarith) (by linarith))

/-- **(e3) Threshold-5 submersion, slim stage** (`π₃E = f₃`, `Θ₃ = id`). -/
theorem final_submersion_slim_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 5 * (10 ^ 5 * Δ)) :
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈
        C.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E q))) p) := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  refine ⟨?_, ?_⟩
  · rw [C.finalBase_inter_slim_BAS j, C.final_factor_BAS 2 p]
    exact Set.mem_image_of_mem _ (C.slim_mem_patch_of_domain5_BAS j hp hη)
  · exact surjective_mfderiv_congr_BAS (C.slim_kappa_final_eq_BAS j)
      (C.stage_submersion_slim_BAS R j hp (by linarith))

/-- `π_st E(U_st) ⊆ W_st` at every stage (FC33's original threshold-5 domain). -/
theorem final_mem_finalBase_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (st : Fin 3) {p : X}
    (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) ∈ C.finalBase_BAS st := by
  fin_cases st
  · exact hp.elim fun j hj => (C.final_submersion_circle_BAS R j hj.1 hj.2).1.1
  · exact hp.elim fun j hj => (C.final_submersion_edge_BAS R j hj.1 hj.2.1 hj.2.2).1.1
  · exact hp.elim fun j hj => (C.final_submersion_slim_BAS R j hj.1 hj.2).1.1

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
