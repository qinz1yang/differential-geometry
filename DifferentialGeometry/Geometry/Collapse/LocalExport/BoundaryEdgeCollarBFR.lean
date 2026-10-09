import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCollarBF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRApplications

/-!
# BCG01's edge-collar cover on the extended final family, in full (lane BDRY-IDX2)

Blueprint 207B, BCG01 (`B:8806–8814`; review 51 row 2): every two-stratum point in the collar of a
selected (revised) edge chart is covered by a circle chart. Lane BCG-4's
`LocalPacketsOnBF.edgeB_collar_circle_BCG4` proves this at every point of the collar band of a
revised edge chart GIVEN the no-three input `¬ HasEuclideanSplitting x 3 (β 3)` (a producer gap at
the time). On the extended final family `LocalPacketsOnBFR` that input is the field
`rank_le_two` (lane BCG-5, `LocalPacketsOnBFR.edgeB_collar_no_three_BCG5`), so the cover holds with
no extra hypothesis:

* `LocalPacketsOnBFR.edgeB_collar_circle_IDX2`: at a revised edge centre `j`, every point `x` of the
  chart's collar band (`d(x, j) < 100Δρ(j)`, `|η_j(x)| ≤ 10Δ`, `Δ/10 ≤ F_s(x)/ρ(x) ≤ 10Δ`) is
  two-stratum, lies in `U₁` and is covered by a circle chart (`3βc ≤ β 2 < 1`, `0 ≤ γ`, `Δ ≥ 1`).

Its sequence-level binding on the ONE family of the index-corrected T3B is
`lc88_boundary_values_collar_BFR_IDX2` (LE/BoundaryValuesBFRCollarIdx.lean).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Final

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **BCG01's edge-collar cover on the extended final family, in full** (lane BDRY-IDX2): at a
revised edge centre `j`, every point `x` of the chart's collar band (`d(x, j) < 100Δρ(j)`,
`|η_j(x)| ≤ 10Δ`, `Δ/10 ≤ F_s(x)/ρ(x) ≤ 10Δ`) is two-stratum, lies in `U₁` and is covered by a
circle chart (`3βc ≤ β 2 < 1`, `0 ≤ γ`, `Δ ≥ 1`). Lane BCG-4's
`LocalPacketsOnBF.edgeB_collar_circle_BCG4` with its no-three input discharged by the field
`rank_le_two` (`LocalPacketsOnBFR.edgeB_collar_no_three_BCG5`). -/
theorem LocalPacketsOnBFR.edgeB_collar_circle_IDX2
    (F : LocalPacketsOnBFR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ) (hΔ : 1 ≤ Δ)
    {j : X} (hj : j ∈ F.edgeB.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := F.edgeB.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F.edgeB.smoothing x / ρ x) (hF2 : F.edgeB.smoothing x / ρ x ≤ 10 * Δ) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 ∧ x ∈ U₁ ∧
      ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
        dist x a < 2 * ρ a ∧
        (let c := F.circle.chart a ha
         letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
         ‖c.coord x‖ < 2 * (1 + γ)) :=
  F.toLocalPacketsOnBF.edgeB_collar_circle_BCG4 h3βc hβ2 hγ hΔ hj hx hη hF1 hF2
    (F.edgeB_collar_no_three_BCG5 hj hx)

end Final

end DifferentialGeometry.Geometry.Collapse
