import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBases

/-!
# D74-2 row 6 on the whole open parent domain: no merging over FC33's `U_st`

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G18 (closes the part of G11's gap (a) that concerns the
rows' parent domains). BASES' threshold-5 membership lemmas (`circle/edge/slim_mem_patch_of_
domain5_BAS`, hypothesis-free) put `f_st(U_st)` inside the native marked base `V_st⁰`; with
`π_st ∘ E = Θ_st ∘ f_st` and no merging on `V_st⁰`:

* `Gaf02Chain.stageMap_mem_markedBase_R74`: `f_st(U_st) ⊆ V_st⁰`;
* `SmoothStageBasesOn74.fibre_domain5_R74`: for `w₀ ∈ V_st⁰`, the FINAL fibre of `Θ_st w₀` inside
  the open parent domain `U_st` is the NATIVE fibre of `w₀` inside `U_st` (both inclusions);
* `SmoothStageBasesOn74.final_eq_iff_R74`: two points of `U_st` have the same final value iff
  they have the same native value.
The whole-fibre equality OUTSIDE `U_st ∪ f_st⁻¹(V_st⁰)` stays a BASES gap (not needed by rows
whose sources lie in `U_st`).
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

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **`f_st(U_st) ⊆ V_st⁰`** (BASES' threshold-5 membership, every stage). -/
theorem Gaf02Chain.stageMap_mem_markedBase_R74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3) {p : X}
    (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    C.stageMap_BAS st p ∈ C.markedBase_BAS st := by
  fin_cases st
  · obtain ⟨j, hj, hη⟩ := hp
    exact mem_iUnion.mpr ⟨j, C.circle_mem_patch_of_domain5_BAS j hj hη⟩
  · obtain ⟨j, hj, hη, ht⟩ := hp
    exact mem_iUnion.mpr ⟨j, C.edge_mem_patch_of_domain5_BAS j hj hη ht⟩
  · obtain ⟨j, hj, hη⟩ := hp
    exact mem_iUnion.mpr ⟨j, C.slim_mem_patch_of_domain5_BAS j hj hη⟩

namespace SmoothStageBasesOn74

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}

/-- **No merging on the open parent domain**: two points of `U_st` have the same final value
`π_st E` iff they have the same native value `f_st`. -/
theorem final_eq_iff_R74 (A : SmoothStageBasesOn74 C) {st : Fin 3} {p p' : X}
    (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st)
    (hp' : p' ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p') ↔
      C.stageMap_BAS st p = C.stageMap_BAS st p' := by
  rw [A.later.final_factor st p, A.later.final_factor st p']
  exact ⟨fun h => A.later.later_injOn st (C.stageMap_mem_markedBase_R74 st hp)
    (C.stageMap_mem_markedBase_R74 st hp') h, fun h => by rw [h]⟩

/-- **D74-2 row 6 on the parent domain**: for `w₀ ∈ V_st⁰`, the final fibre of `Θ_st w₀` inside
`U_st` is the native fibre of `w₀` inside `U_st`. -/
theorem fibre_domain5_R74 (A : SmoothStageBasesOn74 C) (st : Fin 3)
    {w₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw₀ : w₀ ∈ C.markedBase_BAS st) :
    {p | p ∈ gafStageDomain5_BAS P.toLocalChartPackets st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀} =
      {p | p ∈ gafStageDomain5_BAS P.toLocalChartPackets st ∧ C.stageMap_BAS st p = w₀} := by
  ext p
  refine ⟨fun ⟨hp, he⟩ => ⟨hp, ?_⟩, fun ⟨hp, hf⟩ => ⟨hp, ?_⟩⟩
  · rw [A.later.final_factor st p] at he
    exact A.later.later_injOn st (C.stageMap_mem_markedBase_R74 st hp) hw₀ he
  · rw [A.later.final_factor st p, hf]

end SmoothStageBasesOn74

end DifferentialGeometry.Geometry.Collapse
