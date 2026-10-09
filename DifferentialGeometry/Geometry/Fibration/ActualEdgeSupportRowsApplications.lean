import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportRows

/-!
# Consumers of the FC18 (ii) / FC12 edge bindings

* `edgeCutoff_eq_zero_of_far_of_link`: under the coordinate link of LC87 packet (iv), an actual
  edge cutoff vanishes outside `B(j, 20Δρ(j))`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- Under the coordinate link (LC87 packet (iv)), an actual edge cutoff vanishes outside
`B(j, 20Δρ(j))`. -/
theorem edgeCutoff_eq_zero_of_far_of_link
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΛ : 0 ≤ Λ) {j : X} (hj : j ∈ L.edge.centres) {τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ)
    (hτsmall : τ < 1 / 10000) (hscale : Λ < 1 / (1000000 * Δ))
    (hend : Λ < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000) (hbs : b < s / 100000)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hμ : μ ≤ 1 / 10) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧
      ((∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |L.edge.coord j x - (Q x).fst| ≤ Δ / 100) →
        ∀ x, x ∉ ball j (20 * Δ * ρ j) → L.edge.cutoff j x = 0) := by
  obtain ⟨Q, h0, -, -, -, hsupp⟩ := fc18_edge_row L hΛ hj hΔ hτ hτsmall hscale hend hb'domain
    hs'domain hb'error hs'error hsb' hss' hbs hΔΛ hμ
  refine ⟨Q, h0, fun hlink x hx => ?_⟩
  obtain ⟨hS, hB⟩ := hsupp hlink
  by_contra hne
  exact hx (hB (hS (subset_tsupport _ hne)))

end DifferentialGeometry.Geometry.Collapse
