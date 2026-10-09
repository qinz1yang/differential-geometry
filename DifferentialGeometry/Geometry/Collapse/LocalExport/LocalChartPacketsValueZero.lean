import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValue
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsZero

/-!
# LC87 with LFR19's slim value tolerance AND LC73's zero shell clauses (`LocalChartPacketsRVZ`)

The family chapter 14 consumes when a row needs the slim block and the zero block together
(TCP05/TCP06, SGP03–SGP06 with their zero analogues, EGP04 with the zero block):

`LocalChartPacketsRVZ … vs ζ Λz` extends BOTH `LocalChartPacketsRV … vs` (C14-SGP2: field
`slim_value`) and `LocalChartPacketsZ … ζ Λz` (C14-ZERO: fields `zero_shell_split`,
`zero_adapted`) over their common parent `LocalChartPacketsR`; no new field. Every theorem stated on
`LocalChartPacketsRV` or on `LocalChartPacketsZ` applies to the projections
`P.toLocalChartPacketsRV`, `P.toLocalChartPacketsZ` of the SAME family.

Producer: `eventually_nonempty_localChartPacketsRVZ` (LocalChartPacketsValueZeroProducer).
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

/-- **The final family with the slim value tolerance and LC73's zero shell clauses**: one
`LocalChartPacketsR` carrying LFR19's separate slim value tolerance `vs` (`slim_value`) and, on the
SAME zero family, X82's exact-coordinate splittings and LC73's adapted coordinates of quality `ζ`
(ratios `λ ≥ Λz`) at every point of every closed zero shell. -/
structure LocalChartPacketsRVZ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
    extends
      LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs,
      LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        ζ Λz

end DifferentialGeometry.Geometry.Collapse
