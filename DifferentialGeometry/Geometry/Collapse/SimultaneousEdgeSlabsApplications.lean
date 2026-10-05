import DifferentialGeometry.Geometry.Collapse.SimultaneousEdgeSlabs

/-!
# Consumer: the side boundary of every actual edge slab is a regular level of `(f, F/ρ)`

From `eventually_simultaneous_local_cover_with_regular_edge_slabs`: on ONE tail and scale, at every
strong-edge centre `p ∈ Je` the actual coordinate `f` and the ONE smoothing `F` satisfy: at every
point `x` with `d(x, p) < 100Δρ(p)`, `|f x| < 4Δ` and `F x / ρ x = 4Δ` (the side boundary of the
actual slab `{|f| < 4Δ, F/ρ ≤ 4Δ}`), the pair `(f, F/ρ)` has surjective differential (the
source half of LFR28.4).
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
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Consumer: regular side boundary of the actual edge slabs.** See the module docstring. -/
theorem eventually_edge_slab_side_boundary_regular
    (hdim : Module.finrank ℝ E = 3) {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) :
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
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ T V : ℝ, 0 < T → 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ (K : ℕ) (A : ℝ → ℝ → ℝ), (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, (∀ p, 0 < ρ p) ∧ ∃ Je : Set (X i), Je.Finite ∧
        ∃ F : X i → ℝ, ∀ p ∈ Je, ∃ f : X i → ℝ, f p = 0 ∧
          ∀ x, dist x p < 100 * Δ * ρ p → |f x| < 4 * Δ → F x / ρ x = 4 * Δ →
            Function.Surjective
              (mvfderiv (I := I) (edgeReferenceCoordinates ![f, fun z => F z / ρ z]) x) := by
  obtain ⟨a₂, ha₂, h⟩ :=
    eventually_simultaneous_local_cover_with_regular_edge_slabs.{uE, uH, u}
      (E := E) (H := H) (I := I) hdim hσs hσs1
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
  refine ⟨a₀, b₁, ha₀, hb₁, fun b hb hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ', fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand K A hA hder =>
    ?_⟩
  filter_upwards [h w hw hww hwc T V hT hTΛ hTV X g hmetric α hα hstand K A hA hder] with i hi
  obtain ⟨ρ, hρpos, -, -, -, -, Js, -, -, -, -, -, -, Je, hJefin, -, -, F, -, -, hedge⟩ := hi
  refine ⟨ρ, hρpos, Je, hJefin, F, fun p hp => ?_⟩
  obtain ⟨f, hfp, O, -, -, -, -, -, -, hband⟩ := hedge p hp
  refine ⟨f, hfp, fun x hx hfx hFx => ?_⟩
  have hρp := hρpos p
  have hρx := hρpos x
  have hfun : (fun z => F z / ρ p / (ρ z / ρ p)) = fun z => F z / ρ z :=
    funext fun z => div_div_div_cancel_right₀ hρp.ne' (F z) (ρ z)
  have hxR : (ρ p)⁻¹ * dist x p < 100 * Δ := by
    rw [inv_mul_lt_iff₀ hρp]
    linarith
  have hratio : F x / ρ p / (ρ x / ρ p) = 4 * Δ := by
    rw [div_div_div_cancel_right₀ hρp.ne']
    exact hFx
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨-, hsurj⟩ := hband x hxR (by linarith [abs_nonneg (f x)]) (by rw [hratio]; linarith)
    (by rw [hratio]; linarith)
  have hs := hsurj x (by
    change (ρ p)⁻¹ * dist x x < 100 * (ρ x / ρ p)
    rw [dist_self, mul_zero]
    positivity)
  rwa [hfun] at hs

end DifferentialGeometry.Geometry.Collapse
