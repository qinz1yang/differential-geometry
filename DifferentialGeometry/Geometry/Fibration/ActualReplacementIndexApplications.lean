import DifferentialGeometry.Geometry.Fibration.ActualReplacementIndex
import DifferentialGeometry.Geometry.Fibration.ActualBorderWitness
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14DensityApplications

/-!
# FDC01's replacement edge index on `LocalChartPacketsC14D` (the part free of the final map)

Blueprint `master207B.tex`, FDC01 (`lem:fibration-actual-replacement-edge-chart`, B:7157–7243),
on the family with LFR44 item 2 (`LocalChartPacketsC14D`, lane C14-FAM3):

* `fdc01_replacement_index_C14D`: for an edge index `i` whose centre is a nonslim one-stratum
  point, and `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, there is a selected edge index
  `j ∈ J_e(i)` with `d(q, j) < 7Δρ(j)`, `|η_j(q)| < 2Δ` and `ζ_j(q) = 1` — FDC01's (Repl) clauses
  `|η_j(q)| < 2Δ`, `ζ_j(q) = 1` and "the distance estimate just obtained also puts `q` in its
  original smooth `j` domain" (B:7236–7238). Composition of (WB) `fdc01_border_witness_FDC1`,
  LFR44 item 2 `LocalChartPacketsC14D.fdc01_replacement_centre_FAM3` (`d(q', j) < (Δ + 2)ρ(j)`) and
  EGP04 `fdc01_replacement_row_FDC1` (`θ = 1/100`, `Δ ≥ 100`).

NOT here (they concern the final map `E` or its domains): that `p_i` IS nonslim one-stratum for
`q ∈ M₂` (the zero exclusion needs ZSP02's `int Z`, the slim exclusion GAF07 + (SK)); the clauses
`v_j(π₂E(q)) = R_j`, `|u_j(π₂E(q))|/R_j < 3Δ` and `π₂E(q) ∈ B₂` (GAF02, GAF05, (AE)).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **FDC01's replacement edge index** (`LocalChartPacketsC14D`): with the EGP04 thresholds
`b, β 1 ≤ η₀`, `Lc ≤ Lmax` and the original bounds, for an edge index `i` whose centre is a
nonslim one-stratum point and `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`: some selected
edge index `j ∈ J_e(i)` has `d(q, j) < 7Δρ(j)`, `|η_j(q)| < 2Δ` and `ζ_j(q) = 1`. -/
theorem fdc01_replacement_index_C14D {Δ β₂ : ℝ} (hΔ : 100 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 10 ^ 12 →
        μ * Δ < 1 / 10 ^ 4 → ∀ i ∈ P.edge.centres,
        i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1 →
        ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
        ∀ q : X, q ∈ ball i (100 * Δ * ρ i) → |P.edge.coord i q| ≤ 401 / 100 * Δ →
          P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ →
          ∃ j ∈ P.edge.centres, j ∈ egpEdgeList P.toLocalChartFamily i ∧
            dist q j < 7 * Δ * ρ j ∧ |P.edge.coord j q| < 2 * Δ ∧ P.edge.cutoff j q = 1 := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := fdc01_replacement_row_FDC1 (Δ := Δ) (by linarith) hβ₂ hβ₂1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X mX _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ i hi hstr hns q hq hηq htq
  have hΔ0 : 0 < Δ := by linarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  obtain ⟨q', hE, hq'i, hqq', hη', ht'⟩ :=
    fdc01_border_witness_FDC1 P.toLocalChartFamilyE hΔ0 hΛ hμ hτ hlam hi hq hηq htq
  obtain ⟨-, -, -, j, hj, -, hq'j, -⟩ :=
    P.fdc01_replacement_centre_FAM3 hΛ (by linarith) (by linarith) hstr hns hE hq'i
  obtain ⟨hlist, hqj, hcq, hζ⟩ := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ
    P.toLocalChartFamilyE hb hs hβ1 hLmax hΛ hLΛ (hμ.trans (by norm_num))
    (hτ.trans (by norm_num)) hσc hμΔ i hi q q' hq'i hqq' hη' ht' htq (Δ + 2) (by linarith) j hj
    hq'j
  refine ⟨j, hj, hlist, hqj, ?_, hζ⟩
  linarith

end DifferentialGeometry.Geometry.Collapse
