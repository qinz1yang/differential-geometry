import DifferentialGeometry.Geometry.Collapse.SimultaneousLocalCoverSkeleton

/-!
# Consumer: the three nonzero families cover the complement of the zero stratum, with ONE early
# multiplicity bound

LPA06 (A:30645–30652): "Choose the integer bound strictly larger than the last number; it depends
on the fixed numerical C only, NOT on Δ, w′ or the late manifold. Sum three such bounds for the three
families." From `eventually_simultaneous_local_cover`: on one tail and one scale, the circle, slim
and strong-edge families cover every point outside the zero stratum, and at every point the number
of their support balls (`B(j, 2·10⁶ρ(j))`, resp. `B(j, 2·10⁶Δρ(j))`) is at most
`2 N₀ + N₁`, a number fixed before `Δ`, `w′` and the manifold.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The nonzero families of LPA06 with their summed early multiplicity.** -/
theorem eventually_nonzero_families_cover_with_multiplicity (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ →
      ∀ s : ℝ, 0 < s → s < 1 / 100 → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ b : ℝ, 0 < b → b < 1 / 100 → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p, ∃ J Js Je : Set (X i),
        J.Finite ∧ Js.Finite ∧ Je.Finite ∧
        (∀ x : X i, x ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
          (∃ j ∈ J, x ∈ ball j (2 * ρ j)) ∨ (∃ j ∈ Js, x ∈ ball j (2 * (Δ * ρ j))) ∨
          ∃ j ∈ Je, dist x j < 2 * Δ * ρ j) ∧
        ∀ x : X i, ((J ∩ {j | x ∈ ball j (2000000 * ρ j)}).ncard : ℝ) +
            (Js ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard +
            (Je ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard ≤
          2 * (modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) +
            modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
                (4 * (1 + 2 * 2000000 + 1 / 3)) /
              modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3) := by
  obtain ⟨a₂, ha₂, h⟩ :=
    eventually_simultaneous_local_cover.{uE, uH, u, 0} (E := E) (H := H) (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ s hs hssmall => ?_⟩
  obtain ⟨a₀, ha₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ s hs hssmall
  refine ⟨a₀, ha₀, fun b hb hbsmall => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbsmall
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 => ?_⟩
  obtain ⟨εz, δ', Λ', -, -, hΛ', h⟩ :=
    h β hβ2 hβ1 hβ1b hβone hβ3 ((β 1 + 1) / 2) (by linarith) (by linarith)
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44
  refine ⟨w₀, hw₀, fun w hw hww hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [h w hw hww hwc (20 * Λ') (20 * Λ') (by positivity) le_rfl le_rfl X g hmetric α
    hα hstand] with i hi
  obtain ⟨ρ, hρpos, -, -, -, -, -, -, -, -, -, J, hJfin, -, -, -, hJmult, Js, Je, hJsfin, -, -, -,
    hJsmult, hJefin, -, -, -, -, hJemult, hcov, -⟩ := hi
  refine ⟨ρ, hρpos, J, Js, Je, hJfin, hJsfin, hJefin, hcov, fun x => ?_⟩
  linarith [hJmult x, hJsmult x, hJemult x]

end DifferentialGeometry.Geometry.Collapse
