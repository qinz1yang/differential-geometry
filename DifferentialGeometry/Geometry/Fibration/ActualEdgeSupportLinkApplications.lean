import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink

/-!
# Consumers of the unconditional FC18 (ii) on `LocalChartFamilyE`

* `edgeCutoff_eq_zero_of_farE`: an actual edge cutoff vanishes outside `B(j, 20Δρ(j))`.
* `edgeCutoff_contMDiffE`: every actual edge cutoff is smooth (no margin input).
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ : ℝ}

/-- An actual edge cutoff vanishes outside `B(j, 20Δρ(j))`. -/
theorem edgeCutoff_eq_zero_of_farE
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {j : X} (hj : j ∈ L.edge.centres) {x : X}
    (hx : x ∉ ball j (20 * Δ * ρ j)) : L.edge.cutoff j x = 0 := by
  obtain ⟨hS, hB, -⟩ := fc18_edge_rowE L hΛ hΔ hμ hτ hΔΛ hj
  by_contra hne
  exact hx (hB (hS (subset_tsupport _ hne)))

/-- Every actual edge cutoff of `LocalChartFamilyE` is smooth. -/
theorem edgeCutoff_contMDiffE
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {j : X} (hj : j ∈ L.edge.centres) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.edge.cutoff j) :=
  L.edge.contMDiff_cutoff_of_margin hΔ L.contMDiff_scale.continuous
    (edge_margin_rowE L hΛ hΔ hμ hτ hΔΛ j hj)

end DifferentialGeometry.Geometry.Collapse
