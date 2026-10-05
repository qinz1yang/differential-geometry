import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyQuantitative

/-!
# LC87: the edge charts with their recorded coarse-border composite (review-42 packet (iv))

`LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ` extends
`LocalChartFamilyQ` by `edge_coarse`: at every strong edge centre `j`, the chart's own plane map
`Q_j = (L.edge.chart j hj).Qn` (which satisfies `(Q_j z)₁ = (split z)₁`, `EdgeChart.Qn_fst`) has
LFR32's coarse-border clauses at normalized scale `(ρ(j)⁻¹ d)`: `Q_j(j) = 0`, distortion `≤ τΔ` on
`B(j, 200Δ)`, `Q_j₂ ≥ 0` there, coverage of `[-100Δ, 100Δ] × [0, 100Δ]` within `τΔ`, the closed weak
edge set `A` has `Q_j₂ ≤ τΔ` on `B(j, 190Δ)` and covers `[-100Δ, 100Δ] × {0}` within `τΔ`.
With `|η_j − split₁| < μΔ` (`EdgeChart.value`) this gives the link `|η_j − Q_j₁| < μΔ ≤ Δ/100`
on `B(j, 100Δ)` needed by FC17/FC18(ii), the edge half of FC12, EGP02 and EDP03.
Producer: `eventually_nonempty_localChartFamilyE` (`LocalChartFamilyEdgeProducer.lean`).
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

/-- **The LC87 family with cutoff formulas, curvature buffer and the edge coarse-border
composite.** -/
structure LocalChartFamilyE (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ : ℝ)
    extends LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax where
  edge_coarse : ∀ j (hj : j ∈ edge.centres),
    let c := edge.chart j hj
    let A : Set X := closure
      {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    (c.Qn j = 0 ∧
      (∀ x ∈ ball j (200 * Δ), ∀ y ∈ ball j (200 * Δ),
        (|dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ)) ∧
      (∀ x ∈ ball j (200 * Δ), 0 ≤ (c.Qn x).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ x ∈ ball j (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) ∧
      (∀ a ∈ A ∩ ball j (190 * Δ), (c.Qn a).snd ≤ τ * Δ) ∧
      (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball j (190 * Δ),
        dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ))

end DifferentialGeometry.Geometry.Collapse
