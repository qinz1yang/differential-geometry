import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamily
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCenterSplittingExclusion

/-!
# FDC01: an edge centre outside the zero stratum is a one-stratum point (kernel)

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7186–7190):
"EGP01 excludes a two-splitting at `p_i`, and LC18 excludes the three-stratum. The exhaustive LC16
stratification therefore makes `p_i` a one-stratum point."

* `EdgeFamily.mem_stratum_one_of_not_zero_FDC2` (kernel): at a selected edge centre `j` of an
  `EdgeFamily` (a strong edge point at its own scale, field `strong`) with qualities `b, s < 10⁻⁶`
  and `β 2 < 10⁻⁶`, the LC18 input "no `(3, β 3)`-splitting at the scale `ρ(j)`" and `j` outside
  the zero stratum give `j ∈ scaledSplittingStratum ρ hρ β 1`: the LC16 rank is at most two
  (`splittingRank_le_two_of_no_three`), not two (EGP01, `scaledSplittingRank_ne_two_of_scaled_edge`)
  and not zero.

The LC18 input is supplied on the producer's tail in `ActualEdgeCentreStratumApplications.lean`
(`eventually_edge_centre_one_stratum_FDC2`, from `exists_eventual_rank_exclusion`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- **FDC01's stratum step** (B:7186–7190, kernel): a selected edge centre with qualities
`b, s < 10⁻⁶`, `β 2 < 10⁻⁶`, no `(3, β 3)`-splitting at its own scale (LC18's input) and not in the
zero stratum is a one-stratum point (EGP01 excludes rank two). -/
theorem EdgeFamily.mem_stratum_one_of_not_zero_FDC2
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    {j : X} (hj : j ∈ F.centres)
    (h3 : ¬ @HasEuclideanSplitting.{u, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) j 3 (β 3))
    (h0 : j ∉ scaledSplittingStratum.{u, 0} ρ hρ β 0) :
    j ∈ scaledSplittingStratum.{u, 0} ρ hρ β 1 := by
  have h2 : scaledSplittingRank.{u, 0} ρ hρ β j ≠ 2 :=
    scaledSplittingRank_ne_two_of_scaled_edge.{u, 0, 0} ρ hρ β (F.strong j hj) hb hs hβ2
  have hle : scaledSplittingRank.{u, 0} ρ hρ β j ≤ 2 :=
    @splittingRank_le_two_of_no_three.{u, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) j β h3
  have hne : scaledSplittingRank.{u, 0} ρ hρ β j ≠ 0 := fun h => h0 h
  change scaledSplittingRank.{u, 0} ρ hρ β j = 1
  omega

end DifferentialGeometry.Geometry.Collapse
