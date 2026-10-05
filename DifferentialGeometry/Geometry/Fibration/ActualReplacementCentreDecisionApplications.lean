import DifferentialGeometry.Geometry.Fibration.ActualReplacementCentreDecision
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCentreStratumApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# FDC01's part free of the final map, on the final closed family `LocalChartPacketsC14Z`

Blueprint `master207B.tex`, FDC01 (B:7157–7243); draft 61 §6.2, steps one to three of (Repl∂)
in the closed form: (1) the selected centre `p_i` is a nonslim one-stratum point, (2) the weak
border witness of the SAME smoothing and the LFR44.2 density witness (`weak_edge_density`),
(3) eligibility `j ∈ J_e(i)` before the EGP comparison.

* `eventually_fdc01_efree_C14Z_FDC` (consumer, on LC20's eventual tail and LC02's scale window,
  which the producer `eventually_nonempty_localChartPacketsC14Z_FAMZ` outputs next to the family):
  for every family `LocalChartPacketsC14Z` on that scale, every edge index `i` and every
  `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, outside every selected zero ball
  `B(z, .38R_z)` and every selected slim region `{d(q, k) < 9Δρ(k), |η_k(q)| < 10Δ}` (the two
  original-coordinate consequences of `q ∈ M₂`): `p_i` is one-stratum and nonslim, and some
  selected edge index `j ∈ J_e(i)` has `d(q, j) < 7Δρ(j)`, `|η_j(q)| < 2Δ` and `ζ_j(q) = 1`.
  Composes `fdc01_centre_exclusions_FDC`, `eventually_edge_centre_one_stratum_FDC2` and
  `eventually_fdc01_replacement_index_FDC2` through the projection `toLocalChartPacketsC14D`.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **FDC01 without the final map, on the final closed family** (LC20's tail, LC02's window):
for `q ∈ U_i` with `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`, outside every selected zero ball
`B(z, .38R_z)` and every selected slim region `{d(q, k) < 9Δρ(k), |η_k(q)| < 10Δ}`, the centre
`p_i` is a nonslim one-stratum point and a selected edge index `j ∈ J_e(i)` has `d(q, j) < 7Δρ(j)`,
`|η_j(q)| < 2Δ`, `ζ_j(q) = 1`. -/
theorem eventually_fdc01_efree_C14Z_FDC {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hΛ₀ : 0 < Λ₀) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧ ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (Y : ℕ → Type) [mY : ∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E3 (Y i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (Y i)] [∀ i, CompactSpace (Y i)]
        (gY : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (Y i))
        (hmY : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b)),
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : Y i), ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p) →
      ∀ᶠ i in atTop, ∀ (ρY : Y i → ℝ) (hρY : ∀ y, 0 < ρY y),
        (∀ p, firstVolumeScale (gY i) p w / 2 ≤ ρY p ∧
          ρY p ≤ 2 * firstVolumeScale (gY i) p (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3))) →
        ∀ (Λ : ℝ) (βY : ℕ → ℝ) (σs : ℝ) (K : ℕ)
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
          (oM : ManifoldOrientation 𝓘(ℝ, E3) (Y i) 3),
        βY 3 ≤ threeSplittingExclusionThreshold.{0, 0} → βY 2 < 1 / 1000000 →
        b < 1 / 1000000 → b ≤ η₀ → s < 1 / 1000000 → βY 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 10 ^ 12 →
        μ * Δ < 1 / 10 ^ 4 → 1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 →
        ∀ P : LocalChartPacketsC14Z (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz oM,
        ∀ j ∈ P.edge.centres, ∀ q : Y i, q ∈ ball j (100 * Δ * ρY j) →
          |P.edge.coord j q| ≤ 401 / 100 * Δ → P.edge.smoothing q / ρY q ≤ 401 / 100 * Δ →
          (∀ z (hz : z ∈ P.zero.centres), 38 / 100 * (P.zero.zero z hz).radius ≤ dist q z) →
          (∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρY k →
            10 * Δ ≤ |(P.slim.centre k hk).coord q|) →
          j ∈ scaledSplittingStratum.{0, 0} ρY hρY βY 1 ∧
          ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
            Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
            Nonempty (@KleinerLottApprox (Y i) (WithLp 2 (ℝ × Z))
              ((mY i).rescale (ρY j)⁻¹ (inv_pos.mpr (hρY j))) _ j (WithLp.toLp 2 ((0 : ℝ), z))
                (βY 1))) ∧
          ∃ k ∈ P.edge.centres, k ∈ egpEdgeList P.toLocalChartFamily j ∧
            dist q k < 7 * Δ * ρY k ∧ |P.edge.coord k q| < 2 * Δ ∧ P.edge.cutoff k q = 1 := by
  obtain ⟨Lc, η₀, hLc, hη₀, w₁, hw₁, hrep⟩ :=
    eventually_fdc01_replacement_index_FDC2 hΔ hβ₂ hβ₂1 hΛ₀
  obtain ⟨w₂, hw₂, hone⟩ := eventually_edge_centre_one_stratum_FDC2 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, min w₁ w₂, lt_min hw₁ hw₂, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [hrep w hw (lt_of_lt_of_le hww (min_le_left _ _)) hwc Y gY hmY α hα hstand,
    hone w hw (lt_of_lt_of_le hww (min_le_right _ _)) hwc Y gY hmY α hα hstand] with n hn1 hn2
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM hβ3 hβ2 hb
    hbη hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hT hσs hσs1 P j hj q hq hηq htq hZ hS
  have hΔ0 : 0 < Δ := by linarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  obtain ⟨h0, hns⟩ := fdc01_centre_exclusions_FDC P.toLocalChartPacketsC14 hΔ0 hΛ hμ hτ hlam hT
    hσs hσs1 hj hq hηq htq hZ hS
  have h1 := hn2 ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz hβ3
    hβ2 hb hs P.toLocalChartPacketsC14D j hj h0
  exact ⟨h1, hns h1, hn1 ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    hβ3 hβ2 hb hbη hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ P.toLocalChartPacketsC14D j hj h0 (hns h1) q
    hq hηq htq⟩

end DifferentialGeometry.Geometry.Collapse
