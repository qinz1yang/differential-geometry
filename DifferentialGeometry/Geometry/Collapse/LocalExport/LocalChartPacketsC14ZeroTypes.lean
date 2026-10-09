import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Density
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CoreBoundary

/-!
# The complete closed family: the sublevel types of its own zero family (`LocalChartPacketsC14Z`)

Lane C14-FAM-Z. External review 53, §4.1 (A-Z), and dispositions-task53: the LAST extension of the
closed final family. `LocalChartPacketsC14Z … vs ζ Λz oM` extends `LocalChartPacketsC14D` (no
delivered structure is edited; every row stated on `LocalChartPacketsC14D` / `LocalChartPacketsC14`
applies through `toLocalChartPacketsC14D` / `toLocalChartPacketsC14`) by ONE field:

* `zero_sublevel_types` (LPA05's sublevel-type clause, blueprint 207A A:30548, LFR54 A:29526, on
  the family's OWN zero family): for every zero centre `c` and every `a ∈ [1/5, 2]`, the actual
  sublevel `{η_c ≤ a}` of the zero ball's radial function `η_c` (already the normalized radial
  function — not divided by the radius again) is `CompactModelSublevel oM ∨ PointSoulCoreSublevel ∨
  CircleSoulCoreSublevel ∨ ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel` of the zero ball's
  model `N_c` (the conclusion predicates of `lpa05_selected_sublevel_types_withCarrier`).

The orientation `oM` of the source is a PARAMETER of the certificate (review 53 §4.1: no
unconstrained orientation choice is stored in the family); it enters only the compact-model case.

Projections (this file):
* `LocalChartPacketsC14Z.isClosed_zero_sublevel_FAMZ`: every sublevel `{η_c ≤ a}` is closed;
* `LocalChartPacketsC14Z.zero_sublevel_carrier_FAMZ`: every sublevel `{η_c ≤ a}`, `a ∈ [1/5, 2]`,
  is the whole source (compact model), or lies in the source of an ambient partial diffeomorphism
  `Ψ` into its model with closed image (the disc core) and `Ψ '' ∂{η_c ≤ a} = ∂(Ψ '' {η_c ≤ a})`
  (boundary onto the boundary of the core).
Producer: `eventually_nonempty_localChartPacketsC14Z_FAMZ`
(`LocalChartPacketsC14ZeroTypesProducer`).
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

/-- **The complete closed family**: `LocalChartPacketsC14D` whose zero family carries the types of
its actual radial sublevels `{η_c ≤ a}`, `a ∈ [1/5, 2]` (LPA05's sublevel-type clause on the SAME
zero family; review 53 §4.1). `oM` is the orientation of the source. -/
structure LocalChartPacketsC14Z (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
    extends
      LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
        vs ζ Λz
    where
  /-- LPA05's sublevel-type clause on the family's own zero family: every actual sublevel
  `{η_c ≤ a}`, `a ∈ [1/5, 2]`, has one of LFR54's types (with LFR53's on a compact model). -/
  zero_sublevel_types : ∀ c (hc : c ∈ zero.centres), ∀ a ∈ Icc (1 / 5 : ℝ) 2,
    CompactModelSublevel oM (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    PointSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    CircleSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    ProjectiveSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    KleinSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a}

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The zero sublevels are closed** (the radial function is Lipschitz for the rescaled metric). -/
theorem LocalChartPacketsC14Z.isClosed_zero_sublevel_FAMZ
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) (a : ℝ) :
    IsClosed {x | (P.zero.zero c hc).radial x ≤ a} := by
  obtain ⟨hlip, -⟩ := (P.zero.zero c hc).radial_spec
  exact isClosed_le (@LipschitzWith.continuous X ℝ (mX.rescale ((P.zero.zero c hc).radius)⁻¹
    (inv_pos.mpr (P.zero.zero c hc).radius_pos)).toPseudoEMetricSpace _ _ _ hlip) continuous_const

/-- **The type carrier of a zero sublevel, boundary onto boundary.** By `zero_sublevel_types`, every
actual sublevel `A = {η_c ≤ a}`, `a ∈ [1/5, 2]`, is the whole source (compact model) or lies in the
source of an ambient partial diffeomorphism `Ψ` into the model `N_c` whose image is a closed disc
core, and `Ψ` carries the frontier of `A` onto the frontier of that core. -/
theorem LocalChartPacketsC14Z.zero_sublevel_carrier_FAMZ
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    {x | (P.zero.zero c hc).radial x ≤ a} = univ ∨
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) X (P.N (P.zero.zero c hc).model) ∞,
      {x | (P.zero.zero c hc).radial x ≤ a} ⊆ Ψ.source ∧
      IsClosed (Ψ '' {x | (P.zero.zero c hc).radial x ≤ a}) ∧
      Ψ '' frontier {x | (P.zero.zero c hc).radial x ≤ a} =
        frontier (Ψ '' {x | (P.zero.zero c hc).radial x ≤ a}) := by
  have hA := P.isClosed_zero_sublevel_FAMZ hc a
  rcases P.zero_sublevel_types c hc a ha with ⟨hu, -⟩ |
      ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ, hΨs, hΨi, -⟩ |
      ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ, hΨs, hΨi, -⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ,
        hΨs, hΨi, -⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, -, T₀, -, Ψ,
        hΨs, hΨi, -⟩
  · exact Or.inl hu
  all_goals
    have hcl : IsClosed (Ψ '' {x | (P.zero.zero c hc).radial x ≤ a}) := by
      rw [hΨi]
      exact isClosed_le (continuous_discCoreRadius_of_isContMDiffRiemannianBundle D)
        continuous_const
    exact Or.inr ⟨Ψ, hΨs, hcl, partialDiffeomorph_image_frontier_of_subset_source Ψ hA hΨs hcl⟩

end DifferentialGeometry.Geometry.Collapse
