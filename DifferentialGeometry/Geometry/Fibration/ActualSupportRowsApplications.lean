import DifferentialGeometry.Geometry.Fibration.ActualSupportRows

/-!
# Consumers of the FC14 / FC17 / FC18 (slim) bindings

* `fc18_slim_cutoff_eq_zero_of_far`: an actual slim cutoff vanishes outside `B(j, 950000Δρ(j))`.
* `fc17_weak_edge_point_low`: every weak edge point (own scale) near an actual strong-edge centre
  sits below height `Δ/10` in the centre's original composite chart.
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

/-- An actual slim cutoff vanishes outside `B(j, 950000Δρ(j))`. -/
theorem fc18_slim_cutoff_eq_zero_of_far
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    {j : X} (hj : j ∈ L.slim.centres) {x : X} (hx : x ∉ ball j (950000 * Δ * ρ j)) :
    L.slim.cutoff j x = 0 := by
  obtain ⟨hS, hB, -, -⟩ := fc18_slim_row L hΔ hj
  by_contra hne
  exact hx (hB (hS (subset_tsupport _ hne)))

/-- Every weak edge point within `120Δ` (normalized) of an actual strong-edge centre is below
height `Δ/10` in the centre's original composite chart. -/
theorem fc17_weak_edge_point_low
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΛ : 0 ≤ Λ) {j : X} (hj : j ∈ L.edge.centres) {τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ)
    (hτsmall : τ < 1 / 10000) (hscale : Λ < 1 / (1000000 * Δ))
    (hend : Λ < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000) (hbs : b < s / 100000) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧
      ∀ z : X, @GC.MetricGeometry.isEdgePoint.{u, 0} X (mX.rescale (ρ z)⁻¹ (inv_pos.mpr (hρ z))) z Δ b' s' →
        (ρ j)⁻¹ * dist z j < 120 * Δ → (Q z).snd < Δ / 10 := by
  obtain ⟨Q, h0, -, -, -, hlow⟩ := fc17_row L hΛ hj hΔ hτ hτsmall hscale hend hb'domain
    hs'domain hb'error hs'error hsb' hss' hbs
  exact ⟨Q, h0, fun z hz hzj => hlow z (subset_closure hz) hzj⟩

end DifferentialGeometry.Geometry.Collapse
