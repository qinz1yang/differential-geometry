import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFR
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CoreBoundary

/-!
# The complete final boundary family (`LocalPacketsOnBFRZ`, lane BFAM-ZD)

External review 53, §4.1 (A-Z) and §4.2 (A-D), and dispositions-task53: the LAST extension of the
final boundary family. `LocalPacketsOnBFRZ … U₁ U₂ Ue₁ Ue₂ oM` extends `LocalPacketsOnBFR` (no
delivered structure is edited; every row stated on `LocalPacketsOnBFR` / `LocalPacketsOnBF`
applies through `toLocalPacketsOnBFR` / `toLocalPacketsOnBF`) by two fields:

* `zero_sublevel_types` (LPA05's sublevel-type clause on the family's OWN zero family, field text of
  the closed `LocalChartPacketsC14Z`, lane C14-FAM-Z): for every zero centre `c` and every
  `a ∈ [1/5, 2]` the actual sublevel `{η_c ≤ a}` of the stored radial function `η_c` (already
  normalized — not divided by the radius again) is `CompactModelSublevel oM ∨ PointSoulCoreSublevel
  ∨ CircleSoulCoreSublevel ∨ ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel` of the zero ball's
  model `N_c`. The orientation `oM` of the source is a PARAMETER (review 53 §4.1: no unconstrained
  orientation choice is stored in the family);
* `weak_edge_density` (BD): for every point `p` of the first region `U₁` in the LC16 one-stratum
  that is nonslim (the nonslim text of `EdgeFamilyOn.covers_nonslim`) and every weak edge `q`
  (own scale, qualities `b', s'`) with `d(q, p) < 10Δρ(p)`, there is a strong edge `a` (own scale,
  qualities `b, s`) with `d(q, a) < ρ(a)`. NO `a ∈ Ue₁` in the conclusion (review 53 §4.2: the
  eligibility is derived at the consumer from BCP04.a and its distance margin).

Projections (this file):
* `LocalPacketsOnBFRZ.isClosed_zero_sublevel_BFZD`: every sublevel `{η_c ≤ a}` is closed;
* `LocalPacketsOnBFRZ.zero_sublevel_carrier_BFZD`: every sublevel `{η_c ≤ a}`, `a ∈ [1/5, 2]`, is
  the whole source (compact model) or lies in the source of an ambient partial diffeomorphism `Ψ`
  into its model with closed image (the disc core) and `Ψ '' ∂{η_c ≤ a} = ∂(Ψ '' {η_c ≤ a})`;
* `LocalPacketsOnBFRZ.weak_edge_centre_BFZD`: the finite form on the revised edge family — if the
  strong edge given by `weak_edge_density` lies in `Ue₁`, it is within `Δρ(j)` of a centre `j` of
  the SAME `edgeB`.

Closed instance: `eventually_nonempty_localPacketsOnBFRZ_closed_BFZD`
(`BoundaryPacketsBFRZClosed`). Boundary producers: `BoundaryPacketsBFRZProducerT2` (T2B) and
`BoundaryPacketsBFRZProducerT3` (T3B).
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

/-- **The complete final boundary family** (lane BFAM-ZD): `LocalPacketsOnBFR` whose zero family
carries the types of its actual radial sublevels `{η_c ≤ a}`, `a ∈ [1/5, 2]` (LPA05's clause on the
SAME zero family; review 53 §4.1), together with LFR44 item 2 on the first region (BD; review 53
§4.2). `oM` is the orientation of the source. -/
structure LocalPacketsOnBFRZ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [hXc : CompleteSpace X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
    extends LocalPacketsOnBFR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ where
  /-- LPA05's sublevel-type clause on the family's own zero family: every actual sublevel
  `{η_c ≤ a}`, `a ∈ [1/5, 2]`, has one of LFR54's types (with LFR53's on a compact model). -/
  zero_sublevel_types : ∀ c (hc : c ∈ zero.centres), ∀ a ∈ Icc (1 / 5 : ℝ) 2,
    CompactModelSublevel oM (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    PointSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    CircleSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    ProjectiveSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a} ∨
    KleinSoulCoreSublevel (N (zero.zero c hc).model) {x | (zero.zero c hc).radial x ≤ a}
  /-- LFR44 item 2 on the first region (BD): a weak edge near a nonslim one-stratum point of `U₁`
  is within its own scale of a strong edge. -/
  weak_edge_density : ∀ p ∈ U₁, p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1 →
    ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
    ∀ q : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q Δ b' s' →
      dist q p < 10 * Δ * ρ p →
      ∃ a : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
        dist q a < ρ a

attribute [local instance] LocalPacketsOn.instMetricN LocalPacketsOn.instChartedN
  LocalPacketsOn.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The zero sublevels are closed** (the radial function is Lipschitz for the rescaled metric). -/
theorem LocalPacketsOnBFRZ.isClosed_zero_sublevel_BFZD
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) {c : X} (hc : c ∈ P.zero.centres) (a : ℝ) :
    IsClosed {x | (P.zero.zero c hc).radial x ≤ a} := by
  obtain ⟨hlip, -⟩ := (P.zero.zero c hc).radial_spec
  exact isClosed_le (@LipschitzWith.continuous X ℝ (mX.rescale ((P.zero.zero c hc).radius)⁻¹
    (inv_pos.mpr (P.zero.zero c hc).radius_pos)).toPseudoEMetricSpace _ _ _ hlip) continuous_const

/-- **The type carrier of a zero sublevel, boundary onto boundary.** By `zero_sublevel_types`, every
actual sublevel `A = {η_c ≤ a}`, `a ∈ [1/5, 2]`, is the whole source (compact model) or lies in the
source of an ambient partial diffeomorphism `Ψ` into the model `N_c` whose image is a closed disc
core, and `Ψ` carries the frontier of `A` onto the frontier of that core. -/
theorem LocalPacketsOnBFRZ.zero_sublevel_carrier_BFZD
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ}
    (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    {x | (P.zero.zero c hc).radial x ≤ a} = univ ∨
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) X (P.N (P.zero.zero c hc).model) ∞,
      {x | (P.zero.zero c hc).radial x ≤ a} ⊆ Ψ.source ∧
      IsClosed (Ψ '' {x | (P.zero.zero c hc).radial x ≤ a}) ∧
      Ψ '' frontier {x | (P.zero.zero c hc).radial x ≤ a} =
        frontier (Ψ '' {x | (P.zero.zero c hc).radial x ≤ a}) := by
  have hA := P.isClosed_zero_sublevel_BFZD hc a
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

/-- **The finite form of (BD) on the revised edge family.** For a nonslim one-stratum point `p` of
`U₁` and a weak edge `q` with `d(q, p) < 10Δρ(p)`, `weak_edge_density` gives a strong edge `a` with
`d(q, a) < ρ(a)`; if that edge lies in the edge region `Ue₁` (the eligibility a consumer derives
from its own distance margin, review 53 §4.2), it is within `Δρ(j)` of a centre `j` of the SAME
revised edge family `edgeB` (`edgeB.covers_strong`). -/
theorem LocalPacketsOnBFRZ.weak_edge_centre_BFZD
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) {p : X} (hpU : p ∈ U₁)
    (hp : p ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hns : ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))))
    {q : X} (hq : @isEdgePoint.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q Δ b' s')
    (hqp : dist q p < 10 * Δ * ρ p)
    (helig : ∀ a : X, dist q a < ρ a → a ∈ Ue₁) :
    ∃ a : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
      dist q a < ρ a ∧ a ∈ Ue₁ ∧ ∃ j ∈ P.edgeB.centres, dist a j < Δ * ρ j := by
  obtain ⟨a, ha, hqa⟩ := P.weak_edge_density p hpU hp hns q hq hqp
  have haU := helig a hqa
  obtain ⟨j, hj, haj⟩ := P.edgeB.covers_strong a haU ha
  exact ⟨a, ha, hqa, haU, j, hj, haj⟩

end DifferentialGeometry.Geometry.Collapse
