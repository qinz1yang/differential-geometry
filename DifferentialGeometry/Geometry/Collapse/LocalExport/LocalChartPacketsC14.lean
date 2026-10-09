import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValueZero

/-!
# The final chapter-13 family for chapter 14 (`LocalChartPacketsC14`)

Lane C14-FAM (design `build-logs/resume/design-C14-FAM.md`, external review 48, register R1–R20,
lead decisions T48-1..7). Chapter 14's rows all work on ONE family of local chart packets.
`LocalChartPacketsC14 … vs ζ Λz` extends the merged family `LocalChartPacketsRVZ` (LFR19's slim
value tolerance `vs` and LC73's zero shell clauses; no delivered structure is edited) by the two
remaining FIELDS of the register:

* `zero_curvature` (R6): LPA05's enlarged zero-ball curvature certificate, verbatim
  (`lpa05_selected_zero_packets_with_local_comparison`, second clause, dropped by the R / Z / RVZ
  producers): `sec ≥ -(1/60)² r_c⁻²` on `B(c, 400 r_c)` at every selected zero centre `c`;
* `edge_section` (R9): EGP05's inner section of every edge chart (C14-KC's augmented LC84
  producer, same chart, same shared smoothing), normalized at the edge centre `j`: a continuous
  `s : (-8.5Δ, 8.5Δ) → X` with `η_j ∘ s = id`, `t ∘ s < Δ/100` (`t = F/ρ`, normalized) and image in
  `B(j, 10Δ)` (blueprint 207B, EGP05, B:5042–5053; CGP03 restricts it to `[-23Δ/4, 23Δ/4]`).

R4 (the requested cap for the radial difference-Lipschitz constant `εr`) is an OUTPUT of the
producer on the parameter `εr`, not a field; R5, R7, R8, R10 are lemmas or closed (design (b),
(d)–(f)). The forgetful maps are the structure projections (`toLocalChartPacketsRVZ`,
`toLocalChartPacketsRV`, `toLocalChartPacketsZ`, `toLocalChartPacketsR`, …, `toLocalChartFamily`).
Producer: `eventually_nonempty_localChartPacketsC14` (`LocalChartPacketsC14Producer`).
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The final chapter-13 family for chapter 14**: the merged family `LocalChartPacketsRVZ`
(slim value tolerance `vs`, LC73's zero shell clauses of quality `ζ`, ratios `λ ≥ Λz`) whose zero
family also carries LPA05's enlarged zero-ball curvature and whose edge charts carry EGP05's inner
sections over `(-8.5Δ, 8.5Δ)`. -/
structure LocalChartPacketsC14 (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
    extends
      LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs ζ Λz
    where
  /-- LPA05's enlarged zero-ball curvature at every selected zero centre (R6). -/
  zero_curvature : ∀ c (hc : c ∈ zero.centres), ∀ y ∈ ball c (400 * (zero.zero c hc).radius),
    SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((zero.zero c hc).radius)⁻¹ ^ 2))
  /-- EGP05's inner section of the edge chart at every edge centre, normalized there (R9). -/
  edge_section : ∀ j (hj : j ∈ edge.centres),
    let c := edge.chart j hj
    let Fs := edge.smoothing
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → X, Continuous sec ∧
      ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
        Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ

end DifferentialGeometry.Geometry.Collapse
