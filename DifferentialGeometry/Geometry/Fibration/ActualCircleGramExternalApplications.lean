import DifferentialGeometry.Geometry.Fibration.ActualCircleGramExternal
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# TCP01's explicit circle Gram bound on the final family `LocalChartPacketsC14`

Lane C14-FAM2b (external review 50, verdict 6, lead decision T50-2): the explicit-`γ_T` Gram
lemmas of `ActualCircleGramExternal` stated on chapter 14's one family `LocalChartPacketsC14`
(through its projection `P.toLocalChartPackets`; the circle chart is the family's own packet (i)).

* `LocalChartPacketsC14.tcp01_gram_explicit_FAM2b`: singular values of `Dη_j(x)` in
  `[1 − (γ + β₂), 1 + γ]` and `‖Dη_j(Dη_j)* − I‖ ≤ 2d + d²`, `d = γ + β₂ < 1`, `β₂ ≤ 10⁻⁷`.
* `LocalChartPacketsC14.tcp01_gram_external_FAM2b`: `< γ_T/4` for `0 < γ_T ≤ 1`, `γ ≤ γ_T/20`,
  `β₂ ≤ min(10⁻⁷, γ_T/20)`.
* `LocalChartPacketsC14.tcp01_gram_right_inverse_FAM2b`: for `γ + β₂ < 1/10`, singular values
  `> 9/10` and a right inverse of norm `≤ 1/(1 − (γ + β₂)) < 2`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **TCP01's Gram bound, explicit, on the final family**: at a circle centre `j` and
`x ∈ B(j, 200ρ(j))`, with `β₂ ≤ 10⁻⁷` and `d = γ + β₂ < 1`, the differential of the family's circle
chart in the normalized metric `ρ(j)⁻² g` has singular values in `[1 − d, 1 + γ]` and
`‖Dη_j(Dη_j)* − I‖ ≤ 2d + d²`. -/
theorem LocalChartPacketsC14.tcp01_gram_explicit_FAM2b
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (∀ ξ : ℝ², ‖ξ‖ = 1 →
      1 - (γ + β 2) ≤ ‖ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x) ξ‖ ∧
        ‖ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x) ξ‖ ≤ 1 + γ) ∧
    ‖(mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x).comp
        (ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x)) -
      ContinuousLinearMap.id ℝ ℝ²‖ ≤ 2 * (γ + β 2) + (γ + β 2) ^ 2 :=
  tcp01_gram_explicit_FAM2 P.toLocalChartPackets hβ hd hj hx

/-- **TCP01's Gram bound against an external tolerance `γ_T` on the final family** (review 50,
verdict 6): `0 < γ_T ≤ 1`, `γ ≤ γ_T/20`, `β₂ ≤ min(10⁻⁷, γ_T/20)` give
`‖Dη_j(Dη_j)* − I‖ < γ_T/4` for the family's SAME circle chart, in its normalized metric on
`B(j, 200ρ(j))`. -/
theorem LocalChartPacketsC14.tcp01_gram_external_FAM2b
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    {γT : ℝ} (hγT : 0 < γT) (hγT1 : γT ≤ 1) (hγ : γ ≤ γT / 20) (hβ : β 2 ≤ 1 / 10000000)
    (hβT : β 2 ≤ γT / 20) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ‖(mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x).comp
        (ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x)) -
      ContinuousLinearMap.id ℝ ℝ²‖ < γT / 4 :=
  tcp01_gram_external P.toLocalChartPackets hγT hγT1 hγ hβ hβT hj hx

/-- **Right inverse of the circle differential on the final family**: for `β₂ ≤ 10⁻⁷` and
`γ + β₂ < 1/10`, both singular values of `Dη_j(x)` exceed `9/10` and it has a right inverse `R`
with `‖R‖ ≤ 1/(1 − (γ + β₂)) < 2` (normalized metric `ρ(j)⁻² g`). -/
theorem LocalChartPacketsC14.tcp01_gram_right_inverse_FAM2b
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) {j : X} (hj : j ∈ P.circle.centres) {x : X}
    (hx : x ∈ ball j (200 * ρ j)) :
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (∀ ξ : ℝ², ‖ξ‖ = 1 → 9 / 10 < ‖ContinuousLinearMap.adjoint
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x) ξ‖) ∧
    ∃ R : ℝ² →L[ℝ] TangentSpace 𝓘(ℝ, E3) x,
      (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x).comp R =
        ContinuousLinearMap.id ℝ ℝ² ∧ ‖R‖ ≤ 1 / (1 - (γ + β 2)) ∧ ‖R‖ < 2 :=
  tcp01_gram_right_inverse_FAM2 P.toLocalChartPackets hβ hd hj hx

end DifferentialGeometry.Geometry.Collapse
