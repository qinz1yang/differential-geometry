import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZClosed

/-!
# Consumer of the boundary whole-list counts: the closed instance of `LocalPacketsOnBFRZ`
(lane B-COUNT, G1–G2)

`eventually_whole_support_counts_BFRZ_closed_BCNT`: non-vacuous use of G1 and G2 — the statement of
the closed instance `eventually_nonempty_localPacketsOnBFRZ_closed_BFZD` (lane BFAM-ZD; every clause
verbatim) with the three count requests added at their construction times (`10⁶ΔΛ < 10⁻⁵` with the
`Λ` requests, `1600·10⁶Δ ≤ T` with `T`, `4(10 + 4·10⁶Δ + Δ/3) ≤ Lmax` with `Lmax`): on one tail of
every closed standing sequence the complete final boundary family exists and, at EVERY point, its
TCP01 list (circle, `edgeB`, slim at `B(p, 10ρ(p))`), its EGP02 list (`edgeB`, slim at
`B(p, 20Δρ(p))`) and its SGP01 list (slim at `B(p, .95Lρ(p))`) have at most `N_TCP` entries, with
at most one zero support meeting `B(p, 10ρ(p))`. (`1 ≤ Δ` follows from `Δ > 100/β₂`, `β₂ < 1/100`.)
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

attribute [local instance] LocalPacketsOn.instMetricN LocalPacketsOn.instChartedN
  LocalPacketsOn.instMetricC

/-- **Consumer (closed instance): the boundary whole-list counts on a tail of every closed standing
sequence.** The statement of `eventually_nonempty_localPacketsOnBFRZ_closed_BFZD` with the count
requests `10⁶ΔΛ < 10⁻⁵`, `1600·10⁶Δ ≤ T`, `4(10 + 4·10⁶Δ + Δ/3) ≤ Lmax`; conclusion: the family `F`
and, at every point, G1 (`tcp01_support_count_BFRZ`) and the list halves of G2
(`egp02_whole_count_BFRZ`, `sgp01_whole_count_BFRZ`). -/
theorem eventually_whole_support_counts_BFRZ_closed_BCNT (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
        1000000 * Δ * Λ < 1 / 100000 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → 1600 * (1000000 * Δ) ≤ T →
      ∀ e : ℝ, 0 < e → e < 1 / 40 →
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
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ F : LocalPacketsOnBFRZ (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' univ univ univ univ (hor i),
        ∀ p : X i,
          ((bdCircleList_BCNT F.toLocalPacketsOnB p (10 * ρ p)).ncard +
              (bdEdgeBList_BCNT F.toLocalPacketsOnB p (10 * ρ p)).ncard +
              (bdSlimList_BCNT F.toLocalPacketsOnB p (10 * ρ p)).ncard ≤ tcp01SupportBound ∧
            (zeroMeetingListOn_BCNT F.zero p 10).ncard ≤ 1) ∧
          (bdEdgeBList_BCNT F.toLocalPacketsOnB p (20 * Δ * ρ p)).ncard +
              (bdSlimList_BCNT F.toLocalPacketsOnB p (20 * Δ * ρ p)).ncard ≤ tcp01SupportBound ∧
          (bdSlimList_BCNT F.toLocalPacketsOnB p (950000 * Δ * ρ p)).ncard ≤ tcp01SupportBound := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localPacketsOnBFRZ_closed_BFZD K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h1 : 1 < 100 / β₂ := by
      rw [lt_div_iff₀ hβ₂]
      linarith
    linarith
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁,
    fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 hLΛ => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 hβ1b hβone hβ3 ζ cap hβζ hζone hcap
  refine ⟨εr, δ', Λ', hεr, hεr4, hεrcap, hδ', hΛ',
    fun T hT hTΛ hT16 e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ0, hδδ', fun Lmax hLmax hLmaxB => ?_⟩
  filter_upwards [h Lmax hLmax] with i hi
  obtain ⟨ρ, hρpos, hρb, ⟨F⟩⟩ := hi
  exact ⟨ρ, hρpos, hρb, F, fun p =>
    ⟨tcp01_support_count_BFRZ F hΛ.le hΔ1 hLΛ hLmaxB he1 hT16 p,
      (egp02_whole_count_BFRZ F hΛ.le hΔ1 hLΛ hLmaxB he1 hT16 p).1,
      (sgp01_whole_count_BFRZ F hΛ.le hΔ1 hLΛ hLmaxB he1 hT16 p).1⟩⟩

end DifferentialGeometry.Geometry.Collapse
