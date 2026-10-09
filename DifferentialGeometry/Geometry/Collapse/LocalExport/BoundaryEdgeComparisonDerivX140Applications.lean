import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeComparisonDerivX140
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZClosed
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypesProducer

/-!
# X140 closed-family derivative consumer

On one tail of every closed standing sequence, the actual `LocalPacketsOnBFRZ` family furnished
by `eventually_nonempty_localPacketsOnBFRZ_closed_BFZD` satisfies the derivative-only EGP04 edgeB
row. The derivative tier's thresholds are selected before the closed sequence parameters; its
row hypotheses are explicit in the nested parameter clauses and passed at the actual tail. The
existing value clause is imported separately and is not restated here.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **X140 derivative on the actual closed boundary family.** The closed producer's full parameter
telescope is retained. On its eventual tail, each produced `LocalPacketsOnBFRZ` family carries the
one-sign derivative conclusion for every BCG1 edge pair. -/
theorem eventually_edgeB_derivative_BFRZ_closed_X140 (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 →
        100 / β₂ < Δ → Δ₀ ≤ Δ →
        β₂ < 1 / 1000000 →
      ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → τ ≤ 1 / 100 →
        σc ≤ θ ^ 2 / 10 ^ 8 → μ * Δ < θ / 100 →
        140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < 1 / 1000000 →
        s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 →
        ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ →
        σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
        ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b ≤ η₀ → b < bc₀ → b < b₁ →
        100 * Δ < b⁻¹ → b < bd₀ →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ →
        β 1 ≤ η₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
      ∀ hor : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3,
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧
        ∀ Lmax : ℝ, 0 < Lmax → Lc ≤ Lmax → ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ F : LocalPacketsOnBFRZ (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' univ univ univ univ (hor i),
        let L := F.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
        ∀ i₀, i₀ ∈ L.edgeB.centres → ∀ j, j ∈ egpEdgeList_BAUGP L i₀ →
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i₀ (20 * Δ * ρ i₀), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              (ρ i₀)⁻¹ ^ 2 * (g i).inner x w w = 1 →
                |ρ j / ρ i₀ * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x w -
                  a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i₀) x w| < θ := by
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14Z_FAMZ K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀,
    fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ hβ₂1 => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have hβ₂small' : β₂ < 100 := by linarith
    have h1 : 1 < 100 / β₂ := by
      rw [lt_div_iff₀ hβ₂]
      simpa using hβ₂small'
    linarith
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ :=
    egp04_edgeB_derivative_region_X140 hΔ1 hβ₂ hβ₂1 hθ hθ1
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ :=
    h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨Lc, η₀, hLc, hη₀, τ₀, hτ₀, bc₀, hbc₀,
    fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hτ1 hσcθ hμθ
      hθ hε8 hμ8
      s b' s' hs hssmall hs1e6 hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ :=
    h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
      s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁,
    fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  have hΔ0 : 0 < Δ := by
    have hpos : 0 < 100 / β₂ := by positivity
    linarith
  have hden : 0 < 100 * Δ := mul_pos (by norm_num) hΔ0
  have hLΛ : 1000000 * Δ * Λ < 1 / 100000 := by
    have hsmall : s' / (100 * Δ) < τ / 100000000000 := by
      calc
        s' / (100 * Δ) < (τ * Δ / 1000000000) / (100 * Δ) :=
          div_lt_div_of_pos_right hs'e hden
        _ = τ / 100000000000 := by field_simp [hΔ0.ne']; ring
    have hτsmall : τ / 100000000000 ≤ 1 / 10000000000000 := by
      calc
        τ / 100000000000 ≤ (1 / 100) / 100000000000 :=
          div_le_div_of_nonneg_right hτ1 (by norm_num)
        _ = 1 / 10000000000000 := by norm_num
    calc
      1000000 * Δ * Λ < 1000000 * Δ *
          (s' / (100000000 * Δ ^ 2)) :=
        mul_lt_mul_of_pos_left hend (mul_pos (by norm_num) hΔ0)
      _ = s' / (100 * Δ) := by field_simp [hΔ0.ne']; ring
      _ < τ / 100000000000 := hsmall
      _ ≤ 1 / 10000000000000 := hτsmall
      _ < 1 / 100000 := by norm_num
  obtain ⟨w₀, hw₀, h⟩ :=
    h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  -- Closed rank exclusion at the same scale, as in the existing closed-family proof.
  obtain ⟨w₁, hw₁, hR⟩ := exists_eventual_scaled_strata_without_three.{0, 0, 0, 0}
    (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) hdim hΛ
  refine ⟨min w₀ w₁, lt_min hw₀ hw₁, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw (hww.trans_le (min_le_left _ _)) hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbη hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβη hβone hβ3 ζ cap hβζ hζone hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap
  refine ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ',
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ :=
    h T hT hTΛ e he he1 X g hmetric α hα hstand hder hor
  obtain ⟨i₀, hi₀⟩ :=
    hR w hw (hww.trans_le (min_le_right _ _)) hwc X g hmetric α hα hstand
  refine ⟨V, hTV, δ, hδ0, hδδ', fun Lmax hLmax hLcLmax => ?_⟩
  filter_upwards [h Lmax hLmax, eventually_ge_atTop i₀] with i hi hii
  obtain ⟨-, ρ, hρpos, hρb, P, -⟩ := hi
  let F : LocalPacketsOnBFRZ (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
      σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' univ univ univ univ (hor i) := {
    toLocalPacketsOnBFR :=
      { toLocalPacketsOnBF :=
          LocalPacketsOnBF.ofClosedC14 P.toLocalChartPacketsC14D.toLocalChartPacketsC14
        rank_le_two := fun x _ => (hi₀ i hii ρ hρpos (fun p => (hρb p).1.le)
          (fun p => (hρb p).2.le) β hβ3).1 x }
    zero_sublevel_types := P.zero_sublevel_types
    weak_edge_density := fun p _ hp hns q hq hqp =>
      P.weak_edge_density p hp hns q hq hqp }
  have hder := hrow F hbη hs1e6 hβη hLcLmax (le_of_lt hΛ) hLΛ
    (by linarith) hτ1 hσcθ hμθ
  exact ⟨ρ, hρpos, hρb, F, hder⟩

end DifferentialGeometry.Geometry.Collapse
