import DifferentialGeometry.Geometry.Collapse.SimultaneousEdgeCollars

/-!
# Consumer: ONE distance smoothing for the whole strong-edge family on LPA04's tail

From `eventually_simultaneous_local_cover_with_edge_collars`: on one tail and one scale, the
selected strong-edge family carries ONE nonnegative `(1+ε)`-Lipschitz function `F` that is
`μΔρ(p)`-close to the distance to the closed weak edge set at every centre (A:30535–30539:
"For any later finite strong-edge family, LFR33/LFR38 use ONE smoothing of d_{E′}").
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **One shared edge smoothing on LPA04's tail.** -/
theorem eventually_shared_edge_smoothing_on_tail (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ ε μ τ : ℝ, 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p, ∃ Je : Set (X i), Je.Finite ∧
        (∀ j ∈ Je, @isEdgePoint.{u, 0} (X i)
          ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) j Δ b s) ∧
        ∃ F : X i → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          ∀ p ∈ Je, ∀ x, |F x - infDist x (closure {y | @isEdgePoint.{u, 0} (X i)
            ((mX i).rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'})| < μ * (Δ * ρ p) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_simultaneous_local_cover_with_edge_collars.{uE, uH, u, 0}
    (E := E) (H := H) (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun ε μ τ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs hssmall
    hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, ha₀, h⟩ := h 0 ε μ τ le_rfl hσ₀.le hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs hssmall hsb'
    hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, ha₀, fun b hb hbs hbc hsource => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget
    hend => ?_⟩
  obtain ⟨εz, δ', Λ', -, -, hΛ', h⟩ :=
    h β hβ2 hβ1 hβ1b hβone hβ3 ((β 1 + 1) / 2) (by linarith) (by linarith)
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [h w hw hww hwc (20 * Λ') (20 * Λ') (by positivity) le_rfl le_rfl X g hmetric α
    hα hstand] with i hi
  obtain ⟨ρ, hρpos, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Je, -, -, -, -, -, hJefin, hJeE,
    -, -, -, -, hcollar, -⟩ := hi
  obtain ⟨F, hF0, hFL, hF⟩ := hcollar
  exact ⟨ρ, hρpos, Je, hJefin, hJeE, F, hF0, hFL, fun p hp => (hF p hp).1⟩

end DifferentialGeometry.Geometry.Collapse
