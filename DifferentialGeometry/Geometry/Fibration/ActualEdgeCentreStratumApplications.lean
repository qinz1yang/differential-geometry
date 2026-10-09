import DifferentialGeometry.Geometry.Fibration.ActualEdgeCentreStratum
import DifferentialGeometry.Geometry.Fibration.ActualReplacementIndexApplications
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.RankExclusion

/-!
# FDC01's stratum step on the producer's tail, and the replacement index without a stratum input

Blueprint `master207B.tex`, FDC01 (B:7186–7190 and B:7217–7238), on the final family
`LocalChartPacketsC14D`:

* `eventually_edge_centre_one_stratum_FDC2` (binding): on LC20's eventual tail of the standing
  closed sequence (`exists_eventual_rank_exclusion`, LC18's threshold), for every scale `ρ` in
  LC02's window (which `eventually_nonempty_localChartPacketsC14D` outputs next to the family,
  with `Λ₀` its `Λ`), all LC16 thresholds with `β 3` at most LC18's threshold and
  `β 2 < 10⁻⁶`, qualities `b, s < 10⁻⁶`, and every family `LocalChartPacketsC14D` on that
  scale: every selected edge centre outside the zero stratum is a one-stratum point. No
  three-splitting hypothesis remains.
* `eventually_fdc01_replacement_index_FDC2` (consumer): FDC01's replacement index
  (`fdc01_replacement_index_C14D`) on the same tail with its input "`p_i` is one-stratum" replaced
  by "`p_i` is not zero-stratum" — the form in which FDC01 obtains it (the zero exclusion,
  B:7177–7185, needs ZSP02's `int Z`, i.e. the final map).
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

/-- **FDC01's stratum step on LC20's tail** (`LocalChartPacketsC14D`): for every scale in LC02's
window, `β 3` at most LC18's threshold, `β 2, b, s < 10⁻⁶` and every final family on that scale,
a selected edge centre outside the zero stratum is a one-stratum point. -/
theorem eventually_edge_centre_one_stratum_FDC2 {Λ₀ : ℝ} (hΛ₀ : 0 < Λ₀) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (Y : ℕ → Type) [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E3 (Y i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (Y i)] [∀ i, CompactSpace (Y i)]
        (gY : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (Y i))
        (hmY : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b)),
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : Y i), ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p) →
      ∀ᶠ i in atTop, ∀ (ρY : Y i → ℝ) (hρY : ∀ y, 0 < ρY y),
        (∀ p, firstVolumeScale (gY i) p w / 2 ≤ ρY p ∧
          ρY p ≤ 2 * firstVolumeScale (gY i) p (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3))) →
        ∀ (Λ : ℝ) (βY : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ),
        βY 3 ≤ threeSplittingExclusionThreshold.{0, 0} → βY 2 < 1 / 1000000 →
        b < 1 / 1000000 → s < 1 / 1000000 →
        ∀ P : LocalChartPacketsC14D (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz,
        ∀ j ∈ P.edge.centres, j ∉ scaledSplittingStratum.{0, 0} ρY hρY βY 0 →
          j ∈ scaledSplittingStratum.{0, 0} ρY hρY βY 1 := by
  obtain ⟨w₀, hw₀, htail⟩ :=
    exists_eventual_rank_exclusion (I := 𝓘(ℝ, E3)) finrank_euclideanSpace_fin hΛ₀
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc Y _ _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with i hi
  intro ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz hβ3 hβ2 hb hs
    P j hj h0
  exact P.edge.mem_stratum_one_of_not_zero_FDC2 hb hs hβ2 hj
    ((hi j (ρY j) (hρY j) (hwin j).1 (hwin j).2).1 (βY 3) hβ3) h0

/-- **FDC01's replacement edge index on the producer's tail** (`LocalChartPacketsC14D`): the
conclusion of `fdc01_replacement_index_C14D` for an edge index `j` whose centre is nonslim and NOT
zero-stratum (the one-stratum input is supplied by `eventually_edge_centre_one_stratum_FDC2`): some
selected edge index `k ∈ J_e(j)` has `d(q, k) < 7Δρ(k)`, `|η_k(q)| < 2Δ` and `ζ_k(q) = 1`. -/
theorem eventually_fdc01_replacement_index_FDC2 {Δ β₂ Λ₀ : ℝ} (hΔ : 100 ≤ Δ) (hβ₂ : 0 < β₂)
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
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ),
        βY 3 ≤ threeSplittingExclusionThreshold.{0, 0} → βY 2 < 1 / 1000000 →
        b < 1 / 1000000 → b ≤ η₀ → s < 1 / 1000000 → βY 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 10 ^ 12 →
        μ * Δ < 1 / 10 ^ 4 →
        ∀ P : LocalChartPacketsC14D (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz,
        ∀ j ∈ P.edge.centres, j ∉ scaledSplittingStratum.{0, 0} ρY hρY βY 0 →
        ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox (Y i) (WithLp 2 (ℝ × Z))
            ((mY i).rescale (ρY j)⁻¹ (inv_pos.mpr (hρY j))) _ j (WithLp.toLp 2 ((0 : ℝ), z))
              (βY 1))) →
        ∀ q : Y i, q ∈ ball j (100 * Δ * ρY j) → |P.edge.coord j q| ≤ 401 / 100 * Δ →
          P.edge.smoothing q / ρY q ≤ 401 / 100 * Δ →
          ∃ k ∈ P.edge.centres, k ∈ egpEdgeList P.toLocalChartFamily j ∧
            dist q k < 7 * Δ * ρY k ∧ |P.edge.coord k q| < 2 * Δ ∧ P.edge.cutoff k q = 1 := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrep⟩ := fdc01_replacement_index_C14D hΔ hβ₂ hβ₂1
  obtain ⟨w₀, hw₀, htail⟩ := eventually_edge_centre_one_stratum_FDC2 hΛ₀
  refine ⟨Lc, η₀, hLc, hη₀, w₀, hw₀, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with i hi
  intro ρY hρY hwin Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz hβ3 hβ2 hb
    hbη hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ P j hj h0 hns q hq hηq htq
  exact hrep (Y i) (gY i) (hmY i) ρY hρY Λ βY σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
    ζ Λz P hbη hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ j hj
    (hi ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz hβ3 hβ2 hb hs
      P j hj h0) hns q hq hηq htq

end DifferentialGeometry.Geometry.Collapse
