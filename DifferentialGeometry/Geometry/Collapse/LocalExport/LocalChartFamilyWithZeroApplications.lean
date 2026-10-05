import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyWithZero
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBallApplications

/-!
# Consumers of the local chart family with its zero kind (LPA06's exhaustion by the four kinds)

* `LocalChartFamilyWithZero.exhaustion_four_kinds`: every point lies in the tenth-radius ball of a
  selected zero-model ball or in the plateau (cutoff `= 1`) of a circle, slim or edge cutoff — LPA06
  (A:30625–30627): "Together with that cover and the absence of three-strata, these actual local
  domains exhaust `M`".
* `LocalChartFamilyWithZero.disjoint_zero_cutoffs`: the zero cutoffs of distinct centres have
  disjoint supports (A:30651–30653), for `e < 1/10`.
* `eventually_localChartFamilyWithZero_exhaustion`: on the producer's tail.
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
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace LocalChartFamilyWithZero

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc δ εr e T V : ℝ}

/-- The model metrics of the zero kind, as a local instance. -/
local instance instMetricN_LC87
    (L : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (a : X) : MetricSpace (L.N a) :=
  L.instMetricN a

/-- The model charts of the zero kind, as a local instance. -/
local instance instChartedN_LC87
    (L : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (a : X) : ChartedSpace E3 (L.N a) :=
  L.instChartedN a

/-- The cone metrics of the zero kind, as a local instance. -/
local instance instMetricC_LC87
    (L : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (a : X) : MetricSpace (L.C a) :=
  L.instMetricC a

/-- **LPA06's exhaustion by the four kinds.** Every point lies in the tenth-radius ball of a
selected zero-model ball or in the plateau of a circle, slim or edge cutoff. -/
theorem exhaustion_four_kinds
    (L : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (hΔ : 0 < Δ) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (x : X) :
    (∃ i, ∃ hi : i ∈ L.zero.centres, x ∈ ball i ((L.zero.zero i hi).radius / 10)) ∨
      (∃ j ∈ L.circle.centres, L.circle.cutoff j x = 1) ∨
      (∃ j ∈ L.slim.centres, L.slim.cutoff j x = 1) ∨
      ∃ j ∈ L.edge.centres, L.edge.cutoff j x = 1 := by
  rcases L.exists_cutoff_eq_one hΔ hσs hσs1 x with h0 | h
  · exact Or.inl (L.zero.exists_mem_tenth_ball h0)
  · exact Or.inr h

/-- The zero cutoffs of distinct selected centres have disjoint closed supports (`e < 1/10`). -/
theorem disjoint_zero_cutoffs
    (L : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (he : e < 1 / 10) {i j : X} (hi : i ∈ L.zero.centres) (hj : j ∈ L.zero.centres)
    (hij : i ≠ j) :
    Disjoint (tsupport (fun x => annularCutoff cutoffProfile ((L.zero.zero i hi).radial x)))
      (tsupport (fun x => annularCutoff cutoffProfile ((L.zero.zero j hj).radial x))) :=
  L.zero.disjoint_tsupport_cutoff he hi hj hij

end LocalChartFamilyWithZero

attribute [local instance] LocalChartFamilyWithZero.instMetricN_LC87
  LocalChartFamilyWithZero.instChartedN_LC87 LocalChartFamilyWithZero.instMetricC_LC87

/-- **Consumer of `eventually_nonempty_localChartFamilyWithZero`.** On ONE tail there is a local
chart family with its zero kind whose zero tenth-balls and circle, slim and edge plateaus exhaust the
manifold. -/
theorem eventually_localChartFamilyWithZero_exhaustion
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
        ∃ L : LocalChartFamilyWithZero (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc δ εr e T V, ∀ x : X i,
        (∃ c, ∃ hc : c ∈ L.zero.centres, x ∈ ball c ((L.zero.zero c hc).radius / 10)) ∨
          (∃ j ∈ L.circle.centres, L.circle.cutoff j x = 1) ∨
          (∃ j ∈ L.slim.centres, L.slim.cutoff j x = 1) ∨
          ∃ j ∈ L.edge.centres, L.edge.cutoff j x = 1 := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartFamilyWithZero hσs hσs1 K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
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
  obtain ⟨εr, δ', Λ', hεr, hεr4, hδ', hΛ', h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εr, δ', Λ', hεr, hεr4, hδ', hΛ',
    fun T hT hTΛ e he he1 X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [h] with i hi
  obtain ⟨ρ, hρpos, hρb, ⟨L⟩⟩ := hi
  exact ⟨ρ, hρpos, hρb, L, L.exhaustion_four_kinds hΔpos hσs.le hσs1⟩

end DifferentialGeometry.Geometry.Collapse
