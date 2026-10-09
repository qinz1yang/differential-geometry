import DifferentialGeometry.Geometry.Fibration.ActualReplacementExclusions
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBuffer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: FDC01's exclusion inputs at an edge centre, on `LocalChartPacketsC14`

* `fdc01_exclusion_inputs_C14`: on the family of `LocalChartPacketsC14`, for an edge index `i`
  and `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ` (FDC01's hypotheses without `q ∈ M₂`):
  `d(q, i) < 6Δρ(i)` (EDP03); if the centre `i` is zero-stratum, a selected zero centre `z` has
  `i ∈ B(z, R_z/10)` and `d(q, z) < .38R_z`; if `i` is a slim one-stratum point, a selected slim
  centre `k` has `d(q, k) < 9Δρ(k)` and `|η_k(q)| < 10Δ` (B:7175–7194, the parts free of `E`).
  Consumes `LocalChartFamilyE.edge_enclosure_KC`, `fdc01_zero_exclusion_FDC1` and
  `fdc01_slim_exclusion_FDC1`.
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14Ex_FDC1
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14Ex_FDC1
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14Ex_FDC1
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FDC01's exclusion inputs** (`LocalChartPacketsC14`): for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`
and `t(q) ≤ 4.01Δ`: `d(q, i) < 6Δρ(i)`; a zero-stratum centre `i` lies in a selected tenth-radius
zero ball `B(z, R_z/10)` with `d(q, z) < .38R_z`; a slim one-stratum centre `i` gives a selected
slim centre `k` with `d(q, k) < 9Δρ(k)` and `|η_k(q)| < 10Δ`. -/
theorem fdc01_exclusion_inputs_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    {i : X} (hi : i ∈ P.edge.centres) {q : X} (hq : q ∈ ball i (100 * Δ * ρ i))
    (hηq : |P.edge.coord i q| ≤ 401 / 100 * Δ) (htq : P.edge.smoothing q / ρ q ≤ 401 / 100 * Δ) :
    dist q i < 6 * Δ * ρ i ∧
      (i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0 →
        ∃ z, ∃ hz : z ∈ P.zero.centres, dist i z < (P.zero.zero z hz).radius / 10 ∧
          dist q z < 38 / 100 * (P.zero.zero z hz).radius) ∧
      (i ∈ scaledSplittingStratum.{0, 0} ρ hρ β 1 →
        (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) _ i (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
        ∃ k, ∃ hk : k ∈ P.slim.centres, dist q k < 9 * Δ * ρ k ∧
          |(P.slim.centre k hk).coord q| < 10 * Δ) := by
  have henc := (P.toLocalChartFamilyE.edge_enclosure_KC hΔ hμ hτ hlam hi (a := 401 / 100)
    (by norm_num) (by norm_num) hq hηq htq).2 (by norm_num)
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := hlam.trans (by norm_num)
  exact ⟨henc, fun h0 => fdc01_zero_exclusion_FDC1 P.toLocalChartPackets hΔ hΛ hΔΛ hT h0 henc,
    fun h1 hsl => fdc01_slim_exclusion_FDC1 P.toLocalChartFamily hΔ hΛ hΔΛ hσs hσs1 h1 hsl henc⟩

end DifferentialGeometry.Geometry.Collapse
