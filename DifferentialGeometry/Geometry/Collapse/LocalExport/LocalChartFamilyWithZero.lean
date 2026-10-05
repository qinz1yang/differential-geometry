import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyProducer
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SelectedZeroPackets

/-!
# LC87 items 1–3: the local chart family with its zero kind, on one tail

Blueprint row LC87 (`def:collapse-local-export-certificate`, master207A:31053), item 1 ("LC80
zero-model balls and cores, with original radial functions") together with items 2–3 for the
circle, slim and edge kinds (`LocalChartFamily`). LPA05 (A:30548) produces the zero kind on LPA04's
single assignment and tail; LPA06 (A:30586) puts the four kinds together.

* `LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V`: a
  `LocalChartFamily` and, at the SAME scale `ρ`, models `N, C, o` with an LC80 zero-model family
  `ZeroModelFamily 𝓘(ℝ, ℝ³) X g ρ hρ β N C o δ εr e T V` (finitely many disjoint zero-model balls
  of radii in `[Tρ, Vρ]` meeting the zero stratum, tenth-radius cover, cone maps, the ORIGINAL radial
  functions with LC31's cutoffs, the core identifications, at most one end).
* `eventually_nonempty_localChartFamilyWithZero`: the producer. Parameters: those of
  `eventually_nonempty_localChartFamily` through `ζ` (standing `K ≥ 10`, `A` first, since the slim
  thresholds use them before `b₀`); then LPA05's `εr, δ'` and `Λ' = max(Λ'_tail, Λ'_LPA05)`;
  `T ≥ 20Λ'`, `e`; the sequence (with `hder` after `hstand`, orientation); then `V ≥ T` and the cone
  error `δ < δ'` (LPA02/LPA05: they depend on the sequence); ONE tail. The tail's own LCP04
  zero conjunct is not used: LPA05 makes its own selection.
  Proof: `eventually_nonempty_localChartFamily` (with `V := T`) and
  `lpa05_selected_zero_packets_with_witnesses` applied to the family's own scale (continuous, below
  LPA01's bound `2 r_p(w')` by LC02).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Data

variable (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

/-- **The LC87 local chart family with its zero kind** (items 1–3): the circle, slim and edge
families of `LocalChartFamily` and, at the same scale and parameter assignment, the LC80
zero-model family with its models. DATA with proofs of its fields. -/
structure LocalChartFamilyWithZero (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc δ εr e T V : ℝ)
    extends LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc where
  /-- The nonnegatively curved models and their cones, indexed by the centres. -/
  N : X → Type
  C : X → Type
  [instMetricN : ∀ a, MetricSpace (N a)]
  [instChartedN : ∀ a, ChartedSpace E3 (N a)]
  [instMetricC : ∀ a, MetricSpace (C a)]
  o : ∀ a, C a
  /-- The LC80 zero-model family at the same scale. -/
  zero : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V

end Data

/-- **Producer of the LC87 local chart family with its zero kind.** See the module docstring. -/
theorem eventually_nonempty_localChartFamilyWithZero
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
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
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartFamilyWithZero (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc δ εr e T V) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartFamily.{0, 0} hσs hσs1 K (by omega) A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h w hw hww hwc b hb hbs hbc hbb₁ hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨_εz, _δz, Λz, -, -, -, h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  obtain ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5, h5⟩ :=
    lpa05_selected_zero_packets_with_witnesses hβ1 hβone hβζ hζone
  refine ⟨εr, δ', max Λz Λ5, hεr, hεr4, hδ', lt_max_of_lt_right hΛ5,
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h5⟩ := h5 T hT
    ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans hTΛ) e he he1 X g hmetric
    α hα hstand K hK A hA hder Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [h T T hT ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hTΛ)
    le_rfl X g hmetric α hα hstand hder hor, h5] with i hi h5i
  obtain ⟨ρ, hρpos, hρb, ⟨L⟩, -⟩ := hi
  obtain ⟨N, C, mN, cN, -, mC, o, -, Z, -⟩ :=
    h5i ρ hρpos L.contMDiff_scale.continuous (fun p => (hρb p).2.le)
  exact ⟨ρ, hρpos, hρb, ⟨{ L with
    N := N
    C := C
    instMetricN := mN
    instChartedN := cN
    instMetricC := mC
    o := o
    zero := Z }⟩⟩

end DifferentialGeometry.Geometry.Collapse
