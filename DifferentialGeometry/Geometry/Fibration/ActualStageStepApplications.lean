import DifferentialGeometry.Geometry.Fibration.ActualStageStepPoint
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudInputs

/-!
# GAF02's stage step at one point on the actual stage data

* `gafCloud_preimage_ratio_two_GAF5`: two preimages of a core cloud point have comparable scales,
  `3/5 ρ(q) ≤ ρ(sel x) ≤ 5/3 ρ(q)` (stage `0`: equal; stages `1, 2`: CFS07 at distance zero) — the
  two-sided form of `gafCloud_preimage_ratio_GAF4`.
* `gafStage_step_value_GAF5`, `gafStage_step_deriv_GAF5`: `stage_step_value_point_GAF5` /
  `stage_step_deriv_point_GAF5` at an actual stage (`Q = gafStageQ st`, `S = gafCloud st`,
  `F = 𝓔⁰`, any selection over `S̃_st`), with the preimage ratio discharged.
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

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- **Two preimages of a core cloud point, both directions**: for every selection over `S̃_st`,
every preimage `q` of `x ∈ S_st` has `3/5 ρ(q) ≤ ρ(sel x) ≤ 5/3 ρ(q)`. -/
theorem gafCloud_preimage_ratio_two_GAF5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x) :
    ∀ x ∈ gafCloud L Z st, ∀ q, (gafStageQ L Z st).starProjection (cgpGlobalMap L Z q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q := by
  have hΔ0 : 0 ≤ Δ := by linarith
  intro x hx q hq
  rw [gafStageQ_starProjection_globalMap] at hq
  have hxe := gafCloud_subset_enlarged L Z hΔ0 st hx
  have hsx := hsel x hxe
  fin_cases st
  · have huniv := cgpProjMap_univ_GAF L Z
    have hq' : cgpGlobalMap L Z q = x := by
      rw [← huniv]
      exact hq
    have hs' : cgpGlobalMap L Z (sel x) = x := by
      rw [← huniv]
      exact hsx
    have hr := (fc04_first_cloud_scale L Z (L' := 0) (sg := 1) zero_le_one (by norm_num)).1
    have h1 := hr q
    have h2 := hr (sel x)
    rw [hq'] at h1
    rw [hs'] at h2
    have heq : ρ q = ρ (sel x) := by linarith
    have := hρ q
    rw [← heq]
    constructor <;> linarith
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 := hxe
    have hmc := (fc27_edge_cloud_scale L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap L Z (cgpQ2Tags L Z) q = x from hq,
          show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx, dist_self]
        simp)
    exact hmc
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 := hxe
    have hmc := (fc27_slim_cloud_scale L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap L Z (cgpQ3Tags L Z) q = x from hq,
          show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx, dist_self]
        simp)
    exact hmc

/-- **GAF02's value step at an actual stage** (`stage_step_value_point_GAF5` with
`Q = gafStageQ st`, `S = gafCloud st`, `F = 𝓔⁰`; the preimage ratio is
`gafCloud_preimage_ratio_two_GAF5`). -/
theorem gafStage_step_value_GAF5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag L Z => ℝ²) → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (ψ : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ) (hψI : ∀ y, ψ y ∈ Icc (0 : ℝ) 1)
    {Ξ sg E : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (hE0 : 0 ≤ E) (hE : E ≤ 3 * sg / 10)
    (hPst : ∀ x ∈ gafCloud L Z st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) (p : X)
    (hloc : f p ∈ tsupport ψ →
      (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z st)
    (hprior : ‖f p - cgpGlobalMap L Z p‖ ≤ E * ρ p) :
    ‖adjustmentMap (gafStageQ L Z st) Pst ψ (f p) - cgpGlobalMap L Z p‖ ≤
      (E + (5 / 3 * Ξ * sg + (1 + Ξ) * E)) * ρ p :=
  stage_step_value_point_GAF5 (gafStageQ L Z st) (gafCloud L Z st) sel ρ plane Pst ψ hψI hΞ hsg
    hE0 hE hPst (cgpGlobalMap L Z) f (hρ p) hloc
    (gafCloud_preimage_ratio_two_GAF5 L Z hΔ hΛ hsmall st sel hsel) hprior

/-- **GAF02's derivative step at an actual stage** (`stage_step_deriv_point_GAF5` with
`Q = gafStageQ st`, `S = gafCloud st`, `F = 𝓔⁰`; the preimage ratio is
`gafCloud_preimage_ratio_two_GAF5`). -/
theorem gafStage_step_deriv_GAF5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag L Z => ℝ²) → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (ψ : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ) (hψI : ∀ y, ψ y ∈ Icc (0 : ℝ) 1)
    {Ξ sg E bc Ld H₀ ν : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (hE0 : 0 ≤ E) (hE : E ≤ 3 * sg / 10)
    (hbc : 0 ≤ bc) (hLd : 0 ≤ Ld) (hH₀ : 0 ≤ H₀) (hν : 0 ≤ ν)
    (hPst : ∀ x ∈ gafCloud L Z st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ gafCloud L Z st, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) (p : X)
    (hloc : f p ∈ tsupport ψ →
      (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z st)
    (hprior : ‖f p - cgpGlobalMap L Z p‖ ≤ E * ρ p)
    (hf : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) f p)
    (hψd : f p ∈ tsupport ψ → DifferentiableAt ℝ ψ (f p) ∧ ‖fderiv ℝ ψ (f p)‖ ≤ bc / ρ p)
    (Nw : TangentSpace 𝓘(ℝ, E3) p → ℝ) (hN : ∀ w, 0 ≤ Nw w)
    (hfirst : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w‖ ≤ Ld * Nw w)
    (hnormal : (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z st → ∀ w,
      ‖(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)) -
          (plane ((gafStageQ L Z st).starProjection (cgpGlobalMap L Z p))).starProjection)
        ((gafStageQ L Z st).starProjection (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w))‖ ≤
        ν * Nw w)
    (hpriorD : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) f p w - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w‖ ≤
      H₀ * Nw w) :
    DifferentiableAt ℝ (adjustmentMap (gafStageQ L Z st) Pst ψ) (f p) ∧
      ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ L Z st) Pst ψ ∘ f) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w‖ ≤
        ((5 / 3 * Ξ * sg + (1 + Ξ) * E) * bc * (Ld + H₀) + Ξ * (Ld + H₀) + ν + 2 * H₀) * Nw w :=
  stage_step_deriv_point_GAF5 (gafStageQ L Z st) (gafCloud L Z st) sel ρ plane Pst ψ hψI hΞ hsg
    hE0 hE hbc hLd hH₀ hν hPst hPd (cgpGlobalMap L Z) f (hρ p) hloc
    (gafCloud_preimage_ratio_two_GAF5 L Z hΔ hΛ hsmall st sel hsel) hprior hf hψd Nw hN hfirst
    hnormal hpriorD

end Model

end DifferentialGeometry.Geometry.Collapse
