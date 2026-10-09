import DifferentialGeometry.Geometry.Collapse.SimultaneousLocalCoverSkeletonReordered

/-!
# Consumer of the reordered skeleton: the covering balls exhaust the manifold

From `eventually_simultaneous_local_cover_reordered` (blueprint parameter order: `w` is fixed
BEFORE the strong quality `b` and the tolerances `β`): on ONE tail and scale there are finite
circle, slim and strong-edge families such that every point is in the zero stratum, in a circle
ball `B(j, 2ρ(j))`, in a slim ball `B(j, 2Δρ(j))` or within `2Δρ(j)` of a strong edge
(LPA06, A:30613–30615).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Consumer: the covering balls exhaust the manifold (reordered chain).** -/
theorem eventually_covering_balls_exhaust_reordered (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ →
      ∀ s : ℝ, 0 < s → s < 1 / 100 → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < 1 / 100 → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T V : ℝ, 0 < T → 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p, ∃ J Js Je : Set (X i),
        J.Finite ∧ Js.Finite ∧ Je.Finite ∧
        ∀ x : X i, x ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
          (∃ j ∈ J, x ∈ ball j (2 * ρ j)) ∨ (∃ j ∈ Js, x ∈ ball j (2 * (Δ * ρ j))) ∨
          ∃ j ∈ Je, dist x j < 2 * Δ * ρ j := by
  obtain ⟨a₂, ha₂, h⟩ :=
    eventually_simultaneous_local_cover_reordered.{uE, uH, u, 0} (E := E) (H := H) (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ s hs hssmall => ?_⟩
  obtain ⟨a₀, ha₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ s hs hssmall
  refine ⟨a₀, ha₀, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbsmall => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h w hw hww hwc b hb hbsmall
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ', fun T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [h T V hT hTΛ hTV X g hmetric α hα hstand] with i hi
  obtain ⟨ρ, hρpos, -, -, -, -, -, -, -, -, -, J, hJfin, -, -, -, -, Js, Je, hJsfin, -, -, -, -,
    hJefin, -, -, -, -, -, hcov, -⟩ := hi
  exact ⟨ρ, hρpos, J, Js, Je, hJfin, hJsfin, hJefin, hcov⟩

end DifferentialGeometry.Geometry.Collapse
