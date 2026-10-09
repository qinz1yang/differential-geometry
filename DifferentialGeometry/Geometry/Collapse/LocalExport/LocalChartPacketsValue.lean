import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidual
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyApplications

/-!
# LC87: the final family with LFR19's separate slim value tolerance `v_s`

`LocalChartPacketsRV … vs` extends the final family `LocalChartPacketsR` (no delivered structure is
edited) by ONE field:

* `slim_value`: at every slim centre `j`, `|η_j − u_j| < v_s` on the physical ball `B(j, 10⁶Δρ(j))`
  (`η_j = (slim.centre j hj).coord`, `u_j` the real component of the actual normalized splitting
  `(slim.centre j hj).split`). The slim chart records only LFR20's default `|η_j − u_j| < Δ/100`
  (`SlimChart.value`); SGP03 needs LFR19's separate tolerance, `0 < v_s < θ/100` (B:4523, B:4528).

The forgetful maps are the structure projections (`toLocalChartPacketsR`, …,
`toLocalChartFamilyQ`). Producer: `eventually_nonempty_localChartPacketsRV`
(`LocalChartPacketsValueProducer`), with `σs` and `vs` chosen after `Δ` and `b`, immediately before
the slim threshold `b₀` (design `build-logs/resume/design-C14-SGP-vs.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **LC87 final family with LFR19's separate slim value tolerance `vs`** (SGP03 (SB)): a
`LocalChartPacketsR` whose slim coordinate at every slim centre `j` stays within `vs` of the real
component of the actual normalized splitting on the physical ball `B(j, 10⁶Δρ(j))`. -/
structure LocalChartPacketsRV (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ)
    extends
      LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    where
  /-- LFR19's separate value tolerance at every slim centre (SGP03: `|η_j − u_j| < v_s`). -/
  slim_value : ∀ j (hj : j ∈ slim.centres), ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j),
    |(slim.centre j hj).coord x -
      (letI := (slim.centre j hj).instZ
       @KleinerLottApprox.toFun X (WithLp 2 (ℝ × (slim.centre j hj).Z))
        (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _ (β 1) (slim.centre j hj).split x).fst| < vs

end DifferentialGeometry.Geometry.Collapse
