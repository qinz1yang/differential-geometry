import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDisk

/-!
# LC87: the final family with the two TCP01 chart fields

`LocalChartPacketsR` extends the G10 family `LocalChartPacketsD` (no delivered structure is edited)
by
* `circle_residual`: LFR07's residual enclosure of every circle chart, `|η_j| ≤ 8 ⇒ B(j, 10)` on
  `B(j, 200)` at normalized scale (`CircleChart` records only `|η| < 100 ⇒ B(j, 102)` and
  `η = 0 ⇒ B(j, 2)`);
* `zero_local_comparison`: LC62's neighbouring-scale bound `T/20 ≤ r_c/ρ(q)` on the CLOSED ball
  `d(c, q) ≤ 10 r_c` of every zero-model ball (`ZeroModelFamily` records only `r_c ∈ [Tρ(c), Vρ(c)]`).

Producer: `eventually_nonempty_localChartPacketsR` (LocalChartPacketsResidualProducer).
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

/-- **The final family with LFR07's residual enclosure and LC62's local comparison** (the two
chart fields TCP01 consumes): a `LocalChartPacketsD` whose circle chart at every circle centre `j`
satisfies `|η_j| ≤ 8 ⇒ B(j, 10)` on its domain `B(j, 200)` (normalized at `j`), and whose zero-model
ball at every zero centre `c` satisfies `T/20 ≤ r_c/ρ(q)` for `d(c, q) ≤ 10 r_c`. -/
structure LocalChartPacketsR (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ)
    extends LocalChartPacketsD X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    where
  /-- LFR07's residual enclosure of the circle chart at `j` (TCP01: `|η_j| ≤ 8 ⊂ D_j`). -/
  circle_residual : ∀ j (hj : j ∈ circle.centres),
    let c := circle.chart j hj
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10
  /-- LC62's neighbouring-scale bound at every zero centre (TCP01: `s₀ ≥ T/20`). -/
  zero_local_comparison : ∀ c (hc : c ∈ zero.centres), ∀ q,
    dist c q ≤ 10 * (zero.zero c hc).radius → T / 20 ≤ (zero.zero c hc).radius / ρ q

end DifferentialGeometry.Geometry.Collapse
