import DifferentialGeometry.Geometry.Fibration.ActualReplacementEdgeBall
import DifferentialGeometry.Geometry.Fibration.ActualEdgeHeightFactors
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: FDC03's nonslim edge-ball coverage on `LocalChartPacketsC14`

* `fdc03_nonslim_edge_ball_C14`: on the family of `LocalChartPacketsC14`, every nonslim point of
  the LC16 one-stratum lies in an actual edge ball `B(j, 2Δρ(j))` with `|η_j| < 3.1Δ`, `t < 3.1Δ`
  and full edge cutoff `ζ_j = 1` (FDC03, B:7327–7330, the part free of the final map), and the
  edge cutoff sum `Σ_{I_e} ζ_i` is at least one there. Consumes `fdc03_nonslim_edge_ball_FDC1`
  and `le_cgpEdgeSum_GAFS`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **FDC03's nonslim edge-ball coverage** (`LocalChartPacketsC14`): a nonslim point `x` of the
LC16 one-stratum lies in an actual edge ball `B(j, 2Δρ(j))` with `|η_j(x)| < 3.1Δ`,
`t(x) < 3.1Δ`, `ζ_j(x) = 1`, and the edge cutoff sum at `x` is at least one. -/
theorem fdc03_nonslim_edge_ball_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) (hσc : σc ≤ 1 / 2) (hμ : μ ≤ 1 / 100) (hΛ : 0 ≤ Λ)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {x : X} (hx : x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1)
    (hns : ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) _ x (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))) :
    ∃ j ∈ P.edge.centres, dist x j < 2 * Δ * ρ j ∧ |P.edge.coord j x| < 31 / 10 * Δ ∧
      cgpHeight P.toLocalChartFamily x < 31 / 10 * Δ ∧ P.edge.cutoff j x = 1 ∧
      1 ≤ cgpEdgeSum P.toLocalChartFamily x := by
  obtain ⟨j, hj, hd, hη, ht, hζ⟩ :=
    fdc03_nonslim_edge_ball_FDC1 P.toLocalChartFamily hΔ hσc hμ hΛ hΔΛ hx hns
  refine ⟨j, hj, hd, hη, ht, hζ, ?_⟩
  have hsum := le_cgpEdgeSum_GAFS P.toLocalChartFamily hΔ
    ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ x
  change P.edge.cutoff j x ≤ _ at hsum
  rw [hζ] at hsum
  exact hsum

end DifferentialGeometry.Geometry.Collapse
