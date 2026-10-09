import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierConvergenceTransfer
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

/-!
# Consumer of the chart transfer (lane LFR49-A, group G3)

`CarrierRechart.exists_comparison_data`: comparison maps `j i : N → Y i` in LFR48's input shape
(order `k ≥ m + 1`, exhaustion, `C^m` coefficient convergence in the charts of `N`, distortion at
`q`) give comparison maps `jc i = j i ∘ id` FROM the re-charted carrier `N' = CarrierRechart e Λ`
(`e` of class `C^s`, `m + 1 ≤ s`) of order `m + 1`, with the same values, exhaustion, `C^m`
coefficient convergence to the transported metric `CarrierRechart.metric` in the charts of `N'`,
and distortion at `⟨q⟩`: exactly LFR48's input on `N'` with `K' = m + 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open GC.MetricGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {X : Type*} [TopologicalSpace X] [ChartedSpace (ModelProd EB F) X]
  [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X]
  {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]

/-- **Comparison maps from the re-charted carrier (LFR48's input on `N'`).** -/
theorem CarrierRechart.exists_comparison_data (Λ : (EB × F) ≃L[ℝ] E) {s : ℕ∞}
    (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) {m : ℕ} {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hmn : (m : ℕ∞ω) ≤ n) (hms : (m : ℕ∞ω) + 1 ≤ s)
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)] (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {k : ℕ∞ω} (hmk : (m : ℕ∞ω) + 1 ≤ k)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) k) (q : N)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L m
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → Y i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε) :
    ∃ jc : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (CarrierRechart e.toHomeomorph Λ) (Y i)
        ((m + 1 : ℕ) : ℕ∞ω),
      (∀ i (y : CarrierRechart e.toHomeomorph Λ), jc i y = j i y.point) ∧
      (∀ i (y : CarrierRechart e.toHomeomorph Λ), y ∈ (jc i).source ↔ y.point ∈ (j i).source) ∧
      (∀ C : Set (CarrierRechart e.toHomeomorph Λ), IsCompact C →
        ∀ᶠ i in atTop, C ⊆ (jc i).source) ∧
      (∀ (y : CarrierRechart e.toHomeomorph Λ) (L : Set E), IsCompact L →
        L ⊆ (extChartAt 𝓘(ℝ, E) y).target →
        MapCPConvergenceOn L m
          (fun i => pullbackMetricCoefficients (g i)
            ((jc i : CarrierRechart e.toHomeomorph Λ → Y i) ∘ (extChartAt 𝓘(ℝ, E) y).symm))
          (chartCoeff (CarrierRechart.metric Λ e G hmn hms) y)) ∧
      (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
        ∀ x ∈ ball (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) R,
        ∀ y ∈ ball (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) R,
          |dist (jc i x) (jc i y) - dist x y| < ε) := by
  have hm1 : (((m + 1 : ℕ) : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 := by push_cast; rfl
  have h1 : ((m + 1 : ℕ) : ℕ∞ω) ≤ (s : ℕ∞ω) := by rw [hm1]; exact hms
  have h2 : ((m + 1 : ℕ) : ℕ∞ω) ≤ k := by rw [hm1]; exact hmk
  let jc : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (CarrierRechart e.toHomeomorph Λ) (Y i)
      ((m + 1 : ℕ) : ℕ∞ω) := fun i =>
    (DifferentialGeometry.PartialDiffeomorph.ofLE
      (CarrierRechart.identity Λ e).toPartialDiffeomorph h1).trans
      (DifferentialGeometry.PartialDiffeomorph.ofLE (j i) h2)
  have hsrc : ∀ i (y : CarrierRechart e.toHomeomorph Λ),
      y ∈ (jc i).source ↔ y.point ∈ (j i).source := fun i y =>
    ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  refine ⟨jc, fun i y => rfl, hsrc, fun C hC => ?_, fun y L hL hLt => ?_, fun R ε hε => ?_⟩
  · filter_upwards [hexh _ (hC.image (CarrierRechart.identity Λ e).continuous)] with i hi y hy
    exact (hsrc i y).mpr (hi (mem_image_of_mem _ hy))
  · exact CarrierRechart.mapCPConvergenceOn_chartCoeff Λ e G hmn hms g hmk j hexh hconv y hL hLt
  · filter_upwards [hdist R ε hε] with i hi x hx y hy
    exact hi x.point hx y.point hy

end DifferentialGeometry.Geometry.Collapse
