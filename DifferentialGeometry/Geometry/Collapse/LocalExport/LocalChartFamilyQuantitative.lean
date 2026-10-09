import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamily
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartCutoffProfiles

/-!
# LC87: the local chart family with its actual cutoff formulas and curvature buffer

Review 42 (packets (ii) and the curvature input of (iii)): the consumers of LC87 (FC07, FC24, CGP01,
CGP02) need the ACTUAL formula of every cutoff, not only its plateau, support and smoothness, and the
enlarged-ball counts need the curvature on the enlarged balls.

`LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax` extends
`LocalChartFamily` by
* `circle_cutoff_eq`: the circle cutoff at a centre `j` is `CircleChart.formulaCutoff` of its chart
  (`𝟙_{B(j, 200)} · ψ_{8,9} ∘ η_j` at normalized scale, `ψ_{8,9} = circleCutoffBump_LC87`);
* `slim_cutoff_eq`: the slim cutoff at a centre is `SlimChart.formulaCutoff` of its packet
  (`𝟙_{B(j, 10⁶Δ)} · φ(η_j/(10⁵Δ))`, `φ = slimCutoffProfile_LC87`);
* `sectional_buffer`: LPA01's curvature `sec ≥ -(Lρ(p))⁻²` on `B(p, Lρ(p))` for every `L ≤ Lmax`
  and every point.

The fixed profiles have numerical `C²` budgets (`circleCutoffBump_budget_LC87`,
`slimCutoffProfile_budget_LC87`). Producer: `eventually_nonempty_localChartFamilyQ`
(`LocalChartFamilyQuantitativeProducer.lean`). Erratum to `LocalChartFamily.lean` (frozen): the
field `SlimCentre.Z` carries only the diameter bound `factor_dist`, it is NOT compact (its comment
"compact factor" is wrong); the compact exact factor is `SlimProductModel.W`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

/-- **The LC87 local chart family with the actual cutoff formulas and the curvature buffer.** -/
structure LocalChartFamilyQ (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax : ℝ)
    extends LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc where
  circle_cutoff_eq : ∀ j (hj : j ∈ circle.centres),
    let c := circle.chart j hj
    let ζ := circle.cutoff j
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ζ = c.formulaCutoff
  slim_cutoff_eq : ∀ j (hj : j ∈ slim.centres),
    let S := slim.centre j hj
    let P := S.packet
    letI := S.instZ
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    P.cutoff = P.toSlimChart.formulaCutoff
  sectional_buffer : ∀ L, 0 < L → L ≤ Lmax → ∀ p, ∀ y ∈ ball p (L * ρ p),
    SectionalBoundedBelowAt g y (-((L * ρ p) ^ 2)⁻¹)

end DifferentialGeometry.Geometry.Collapse
