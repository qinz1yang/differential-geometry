import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphModel

/-!
# Consumer of SGP04's model: FC25's regularity and Hessian inputs for SGP06

SGP06 applies FC25 (`hausdorffDist_coordinate_graph_coverage_le`, GraphCoverageAdapters) "with
Hessian bound `C_*`" to the model graph `Φ_i`. Its hypotheses `hreg` (`C²` at every parameter of
the test ball) and `hsecond` (`‖iteratedFDeriv 2 Φ_i‖ ≤ C_*` there) are supplied by
`contDiff_sgpFullGraph` and `sgp04_full_model_bounds` (`sgp06_model_inputs`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **FC25's model inputs for SGP06**: on every closed parameter ball the full model graph `Φ_i`
is `C²` with `‖iteratedFDeriv 2 Φ_i‖ ≤ C_*` (the `hreg`, `hsecond` hypotheses of
`hausdorffDist_coordinate_graph_coverage_le` with `B = C_*`). -/
theorem sgp06_model_inputs
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hs0 : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂) (a₀ R : ℝ) :
    (∀ u ∈ closedBall a₀ R, ContDiffAt ℝ 2 (sgpFullGraph L Z i sgn c zsgn zc) u) ∧
      ∀ u ∈ closedBall a₀ R,
        ‖iteratedFDeriv ℝ 2 (sgpFullGraph L Z i sgn c zsgn zc) u‖ ≤ sgpGraphBound :=
  ⟨fun u _ => ((contDiff_sgpFullGraph L Z i sgn c zsgn zc).of_le (by simp)).contDiffAt,
    fun u _ => (sgp04_full_model_bounds L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0 huniq
      u).2.2⟩

end DifferentialGeometry.Geometry.Collapse
