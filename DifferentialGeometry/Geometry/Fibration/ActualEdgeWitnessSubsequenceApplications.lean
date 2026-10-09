import DifferentialGeometry.Geometry.Fibration.ActualEdgeWitnessSubsequence
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBuffer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: FDC02's limit point satisfies FDC01's original hypotheses, on `LocalChartPacketsC14`

* `fdc02_limit_original_inputs_C14`: on the family of `LocalChartPacketsC14`, let `q_n → q` with
  witnessing edge centres `i_n` such that `q_n ∈ U_{i_n}`, `|η_{i_n}(q_n)| ≤ 4.01Δ`,
  `t(q_n) ≤ 4.01Δ` (what (ELoc) gives at every `q_n ∈ X₂`). Then one centre `i` witnesses a
  subsequence converging to `q`, and the LIMIT satisfies FDC01's original hypotheses
  `q ∈ U_i`, `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, with `d(q, i) ≤ 6Δρ(i)` (FDC02, B:7259–7276:
  "Neither calculation assumes that the limit already belongs to `B₂` or `W₂`. FDC01 now gives a
  replacement index …"). Consumes `fdc02_witness_subsequence_FDC1`, EDP03's enclosure
  `LocalChartFamilyE.edge_enclosure_KC`, the Lipschitz bounds of `η_i`, `F` and `ρ`.
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

/-- **FDC02's limit and FDC01's hypotheses** (`LocalChartPacketsC14`): for `q_n → q` with edge
centres `i_n`, `q_n ∈ U_{i_n}`, `|η_{i_n}(q_n)| ≤ 4.01Δ`, `t(q_n) ≤ 4.01Δ`: some centre `i` and a
subsequence `φ` have `i_{φ n} = i`, `q_{φ n} → q`, and `d(q, i) ≤ 6Δρ(i)`, `q ∈ U_i`,
`|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`. -/
theorem fdc02_limit_original_inputs_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) {qs : ℕ → X} {q : X} (hq : Tendsto qs atTop (𝓝 q))
    {w : ℕ → X} (hw : ∀ n, w n ∈ P.edge.centres)
    (hU : ∀ n, qs n ∈ ball (w n) (100 * Δ * ρ (w n)))
    (hη : ∀ n, |P.edge.coord (w n) (qs n)| ≤ 401 / 100 * Δ)
    (ht : ∀ n, P.edge.smoothing (qs n) / ρ (qs n) ≤ 401 / 100 * Δ) :
    ∃ i ∈ P.edge.centres, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, w (φ n) = i) ∧
      Tendsto (qs ∘ φ) atTop (𝓝 q) ∧ dist q i ≤ 6 * Δ * ρ i ∧ q ∈ ball i (100 * Δ * ρ i) ∧
      |P.edge.coord i q| ≤ 401 / 100 * Δ ∧ P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ := by
  obtain ⟨i, hi, φ, hφ, hφi, hlim⟩ := fdc02_witness_subsequence_FDC1 P.toLocalChartFamily hq hw
  have hUi : ∀ n, qs (φ n) ∈ ball i (100 * Δ * ρ i) := fun n => by
    have h := hU (φ n)
    rwa [hφi n] at h
  have hηi : ∀ n, |P.edge.coord i (qs (φ n))| ≤ 401 / 100 * Δ := fun n => by
    have h := hη (φ n)
    rwa [hφi n] at h
  have henc : ∀ n, dist (qs (φ n)) i < 6 * Δ * ρ i := fun n =>
    (P.toLocalChartFamilyE.edge_enclosure_KC hΔ hμ hτ hlam hi (a := 401 / 100) (by norm_num)
      (by norm_num) (hUi n) (hηi n) (ht (φ n))).2 (by norm_num)
  -- the distance to `i` at the limit
  have hdist : dist q i ≤ 6 * Δ * ρ i :=
    le_of_tendsto' (hlim.dist tendsto_const_nhds) fun n => (henc n).le
  have hball : q ∈ ball i (100 * Δ * ρ i) := by
    rw [mem_ball]
    have := mul_pos hΔ (hρ i)
    linarith
  -- the tangential coordinate at the limit
  have hc0 : 0 ≤ max (1 + σc) 0 / ρ i := div_nonneg (le_max_right _ _) (hρ i).le
  have hLc : LipschitzWith (Real.toNNReal (max (1 + σc) 0 / ρ i)) (P.edge.coord i) :=
    LipschitzWith.of_dist_le_mul fun y z => by
      rw [Real.coe_toNNReal _ hc0, Real.dist_eq]
      exact P.edge.coord_lipschitz_max_KC4 hi y z
  have hcoord : |P.edge.coord i q| ≤ 401 / 100 * Δ :=
    le_of_tendsto' (((continuous_abs.comp hLc.continuous).tendsto q).comp hlim) hηi
  -- the height at the limit
  have hF := (P.edge.lipschitz_smoothing.continuous.tendsto q).comp hlim
  have hR := (P.lipschitz_scale.continuous.tendsto q).comp hlim
  have hheight : P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ :=
    le_of_tendsto' (hF.div hR (hρ q).ne') fun n => ht (φ n)
  exact ⟨i, hi, φ, hφ, hφi, hlim, hdist, hball, hcoord, hheight⟩

end DifferentialGeometry.Geometry.Collapse
