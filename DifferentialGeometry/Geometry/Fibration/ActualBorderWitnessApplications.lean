import DifferentialGeometry.Geometry.Fibration.ActualBorderWitness
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBuffer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: FDC01's original steps (enclosure and weak-border witness) on `LocalChartPacketsC14`

* `fdc01_original_steps_C14`: on the family of `LocalChartPacketsC14`, for an edge index `i` and
  `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ` (FDC01's hypotheses without `q ∈ M₂`):
  EDP03's enclosure `d(q, i) < 6Δρ(i)` (B:7175–7176) and an actual weak edge point `q'` with (WB)
  (B:7201–7215), tiny `t(q')` and full original `i` cutoff at `q'`. Consumes
  `fdc01_border_witness_FDC1`, `LocalChartFamilyE.edge_enclosure_KC` and
  `EdgeFamily.cutoff_eq_one_of_le`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **FDC01's original steps** (`LocalChartPacketsC14`): for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`
and `t(q) ≤ 4.01Δ`: `d(q, i) < 6Δρ(i)`, and an actual weak edge point `q'` with
`d(q', i) < 4.1Δρ(i)`, `d(q, q') < 4.2Δρ(i)`, `|η_i(q') − η_i(q)| < Δ/100`, `t(q') < Δ/100` and
`ζ_i(q') = 1`. -/
theorem fdc01_original_steps_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) {i : X} (hi : i ∈ P.edge.centres) {q : X}
    (hq : q ∈ ball i (100 * Δ * ρ i)) (hηq : |P.edge.coord i q| ≤ 401 / 100 * Δ)
    (htq : P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ) :
    dist q i < 6 * Δ * ρ i ∧
      ∃ q' : X, @isEdgePoint.{0, 0} X (mX.rescale (ρ q')⁻¹ (inv_pos.mpr (hρ q'))) q' Δ b' s' ∧
        dist q' i < 41 / 10 * Δ * ρ i ∧ dist q q' < 42 / 10 * Δ * ρ i ∧
        |P.edge.coord i q' - P.edge.coord i q| < Δ / 100 ∧
        P.edge.smoothing q' / ρ q' < Δ / 100 ∧ P.edge.cutoff i q' = 1 := by
  have henc := (P.toLocalChartFamilyE.edge_enclosure_KC hΔ hμ hτ hlam hi (a := 401 / 100)
    (by norm_num) (by norm_num) hq hηq htq).2 (by norm_num)
  obtain ⟨q', hE, hq'i, hqq', hη', ht'⟩ :=
    fdc01_border_witness_FDC1 P.toLocalChartFamilyE hΔ hΛ hμ hτ hlam hi hq hηq htq
  refine ⟨henc, q', hE, hq'i, hqq', hη', ht', ?_⟩
  have hq'B : q' ∈ ball i (100 * Δ * ρ i) := by
    rw [mem_ball]
    have := mul_pos hΔ (hρ i)
    linarith
  have hη8 : |P.edge.coord i q'| ≤ 8 * Δ := by
    have h := abs_sub_abs_le_abs_sub (P.edge.coord i q') (P.edge.coord i q)
    linarith
  exact P.edge.cutoff_eq_one_of_le hΔ hi hq'B hη8 (by linarith)

end DifferentialGeometry.Geometry.Collapse
