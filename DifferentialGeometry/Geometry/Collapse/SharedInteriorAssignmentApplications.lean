import DifferentialGeometry.Geometry.Collapse.SharedInteriorAssignment

/-!
# Consumer: on the shared tail, every point is of rank at most one or circle-covered

Blueprint `master207A.tex`, LPA06 (A:30630–30633: "Together with that cover and the absence of
three-strata, these actual local domains exhaust M"), the circle part: with LPA04's existing-rows
assignment (`eventually_shared_interior_assignment`), every point of the late manifold lies in the
LC16 stratum of rank zero or one, or in a covering ball `B(j, 2ρ_j)` of the finite circle family,
on which the circle cutoff equals one. The rank-zero and rank-one points are the domains of the
zero, strong-edge and slim families (rows LPA05, LFR28/LFR38, LFR20).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH u

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Every late point is of rank at most one or lies in a circle covering ball.** -/
theorem eventually_low_rank_or_circle_covered (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β : ℕ → ℝ, 0 < β 2 → β 2 ≤ β₀ → β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ Λ : ℝ, 0 < Λ → Λ * 2000000 ≤ 1 / 100 → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p, ∃ J : Set (X i), J.Finite ∧
        J ⊆ scaledSplittingStratum.{u, 0} ρ hρpos β 2 ∧
        ∀ p : X i, p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
          p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∨ ∃ j ∈ J, p ∈ ball j (2 * ρ j) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_shared_interior_assignment.{uE, uH, u} (E := E) (H := H)
    (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun β hβ hββ₀ hβ3 σ hσ hσa hση Λ hΛ hΛsmall => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h β hβ hββ₀ hβ3 σ hσ hσa hση Λ hΛ hΛsmall
  refine ⟨w₀, hw₀, fun w hw hww₀ hwc X _ _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [h w hw hww₀ hwc X g hmetric α hα hstand] with i hi
  obtain ⟨ρ, hρpos, -, -, -, -, -, -, -, hstrata, -, J, hfin, hJS, -, hcov, -⟩ := hi
  refine ⟨ρ, hρpos, J, hfin, hJS, fun p => ?_⟩
  rcases hstrata p with h0 | h1 | h2
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · obtain ⟨j, hj, hsub⟩ := hcov p h2
    exact Or.inr (Or.inr ⟨j, hj, hsub (mem_ball_self (hρpos p))⟩)

end DifferentialGeometry.Geometry.Collapse
