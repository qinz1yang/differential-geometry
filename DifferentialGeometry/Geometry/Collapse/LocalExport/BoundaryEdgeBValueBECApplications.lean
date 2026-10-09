import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBValueBEC

/-!
# Consumer: EGP04 (EC) value clause on the closed specialization of the boundary family

`egp04_edgeB_value_ofClosedC14_BEC`: `egp04_edgeB_value_BEC` applied to the closed
specialization `LocalPacketsOnBF.ofClosedC14 P` of the boundary family (all four regions `univ`,
`edgeB` = the closed edge family, so `i, j` range over `P.edge.centres`), for every closed
`LocalChartPacketsC14` `P`; these are inhabited on a tail of every closed standing sequence
(`eventually_nonempty_localChartPacketsC14`; the closed final boundary family
`eventually_nonempty_localPacketsOnBFRZ_closed_BFZD` is assembled from the same specialization), so
the conclusion is used on actual families, not vacuously.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **EGP04 (EC), value clause, on the closed specialization of the boundary family.** For every
closed `LocalChartPacketsC14` `P` (compact carrier), every closed edge centre `i` and every closed
edge centre `j` whose `cutoff_BAUGA` support (in the boundary family `ofClosedC14 P`) meets `D_i`:
one sign `a` with `|s_j η_j − (a η_i + s_j η_j(i))| < θ` on `D_i`, `η` the boundary edge
coordinates. -/
theorem egp04_edgeB_value_ofClosedC14_BEC {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V vs ζ Λz),
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 →
      s < 1 / 1000000 → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
      μ * Δ < θ / 100 →
      ∀ (i : X) (hi : i ∈ P.edge.centres) (j : X) (hj : j ∈ P.edge.centres),
      (tsupport ((LocalPacketsOnBF.ofClosedC14 P).edgeB.cutoff_BAUGA j) ∩
        ball i (20 * Δ * ρ i)).Nonempty →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * (LocalPacketsOnBF.ofClosedC14 P).edgeB.coord_BCG1 j hj x -
          (a * (LocalPacketsOnBF.ofClosedC14 P).edgeB.coord_BCG1 i hi x +
            ρ j / ρ i * (LocalPacketsOnBF.ofClosedC14 P).edgeB.coord_BCG1 j hj i)| < θ := by
  obtain ⟨σ, hσ, hσ1, η, hη, h⟩ := egp04_edgeB_value_BEC hθ hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
  exact h (LocalPacketsOnBF.ofClosedC14 P).toLocalPacketsOnB

end DifferentialGeometry.Geometry.Collapse
