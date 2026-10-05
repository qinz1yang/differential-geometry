import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierConvergenceTransferApplications
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.SmoothComparisonMaps
import DifferentialGeometry.Topology.FiberBundle.Separation
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# LFR48 on the re-charted carrier (lane LFR49-FIN, group G1)

LFR49's noncompact branch (master207A, LFR49, A:29096) needs SMOOTH comparison maps FROM the
re-charted soul carrier `N' = CarrierRechart e Λ` (LFR49-A, `CarrierRechart.lean`). The chart
transfer `CarrierRechart.exists_comparison_data` gives LFR48's input on `N'` at order `K' = 2`,
except that LFR48 (`exists_smooth_comparison_maps_of_finite_limit`) wants the base point in the
source of EVERY comparison map, while the exhaustion only gives it eventually.

* `exists_partialDiffeomorph_mem_source_apply_eq`: between two smooth manifolds over the same
  vector space any point is sent to any point by a smooth partial diffeomorphism (chart,
  translation, inverse chart).
* `CarrierRechart.exists_smooth_comparison_maps`: the comparison maps of order `≥ 2` of a finite
  model `N` (exhaustion, `C¹` coefficient convergence, distortion at `q`) give SMOOTH pointed
  comparison maps `jt` from `N'` with `jt i ⟨q⟩ = j i q` for EVERY `i`, exhaustion, `C¹`
  convergence to the transported metric in every chart of `N'`, distortion at `⟨q⟩` and the
  strict-radius coverage. The finitely many indices with `q ∉ (j i).source` are replaced by the
  partial diffeomorphisms of the first item before LFR48 is applied; all clauses of LFR48's input
  are insensitive to finitely many indices.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open GC.MetricGeometry

section Fallback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ, E) ∞ P]

/-- Between two smooth manifolds over the same vector space, any point is sent to any point by a
smooth partial diffeomorphism: the chart at `x`, a translation, the inverse chart at `y`. -/
theorem exists_partialDiffeomorph_mem_source_apply_eq (x : M) (y : P) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M P ∞, x ∈ Φ.source ∧ Φ x = y := by
  let c := DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, E) ∞ x
  let d := DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, E) ∞ y
  let τ := (DifferentialGeometry.Topology.translateDiffeomorph
    (extChartAt 𝓘(ℝ, E) y y - extChartAt 𝓘(ℝ, E) x x)).toPartialDiffeomorph
  have hτ : τ (c x) = extChartAt 𝓘(ℝ, E) y y := by
    change extChartAt 𝓘(ℝ, E) x x + (extChartAt 𝓘(ℝ, E) y y - extChartAt 𝓘(ℝ, E) x x) = _
    abel
  refine ⟨(c.trans τ).trans d.symm, ?_, ?_⟩
  · rw [_root_.PartialDiffeomorph.trans_source, _root_.PartialDiffeomorph.trans_source]
    refine ⟨⟨mem_extChartAt_source x, mem_univ _⟩, ?_⟩
    change τ (c x) ∈ (extChartAt 𝓘(ℝ, E) y).target
    rw [hτ]
    exact mem_extChartAt_target y
  · change (extChartAt 𝓘(ℝ, E) y).symm (τ (c x)) = y
    rw [hτ]
    exact extChartAt_to_inv y

end Fallback

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {X : Type*} [TopologicalSpace X] [ChartedSpace (ModelProd EB F) X]
  [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X]
  {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
  [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)] [∀ i, SigmaCompactSpace (Y i)] [∀ i, CompleteSpace (Y i)]

/-- **LFR48 on the re-charted carrier.** Comparison maps `j i : N → Y i` of order `≥ 2` with
exhaustion, `C¹` coefficient convergence to `G` and distortion at `q` give SMOOTH comparison
maps `jt i` from `N' = CarrierRechart e Λ` (`e` of class `C^s`, the transported metric of order
`m ≥ 1`, `m ≤ n`, `m + 1 ≤ s`) with `⟨q⟩` in every source and `jt i ⟨q⟩ = j i q` for EVERY `i`,
exhaustion, `C¹` convergence to the transported metric in every chart of `N'`, distortion at
`⟨q⟩`, and the coverage `B(jt i ⟨q⟩, a) ⊆ jt i (B(⟨q⟩, b))` for `0 < a < b`. -/
theorem CarrierRechart.exists_smooth_comparison_maps (Λ : (EB × F) ≃L[ℝ] E) {s : ℕ∞}
    (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N) {m n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hmn : m ≤ n) (hms : m + 1 ≤ s) (hm : 1 ≤ m)
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {k : ℕ∞ω} (hk : ((2 : ℕ) : ℕ∞ω) ≤ k)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) k) (q : N)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → Y i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε) :
    ∃ jt : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (CarrierRechart e.toHomeomorph Λ) (Y i) ∞,
      (∀ i, (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) ∈ (jt i).source ∧ jt i ⟨q⟩ = j i q) ∧
      (∀ C : Set (CarrierRechart e.toHomeomorph Λ), IsCompact C →
        ∀ᶠ i in atTop, C ⊆ (jt i).source) ∧
      (∀ (y : CarrierRechart e.toHomeomorph Λ) (L : Set E), IsCompact L →
        L ⊆ (extChartAt 𝓘(ℝ, E) y).target →
        MapCPConvergenceOn L 1
          (fun i => pullbackMetricCoefficients (g i)
            ((jt i : CarrierRechart e.toHomeomorph Λ → Y i) ∘ (extChartAt 𝓘(ℝ, E) y).symm))
          (chartCoeff (CarrierRechart.metric Λ e G hmn hms) y)) ∧
      (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
        ∀ x ∈ ball (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) R,
        ∀ y ∈ ball (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) R,
          |dist (jt i x) (jt i y) - dist x y| < ε) ∧
      (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
        ball (jt i ⟨q⟩) a ⊆ (jt i : CarrierRechart e.toHomeomorph Λ → Y i) ''
          ball (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) b) := by
  classical
  have h1n : ((1 : ℕ) : ℕ∞ω) ≤ n := by
    rw [Nat.cast_one]
    exact hm.trans hmn
  have h1s : ((1 : ℕ) : ℕ∞ω) + 1 ≤ (s : ℕ∞ω) := by
    rw [Nat.cast_one]
    exact (add_le_add hm le_rfl).trans hms
  have h1k : ((1 : ℕ) : ℕ∞ω) + 1 ≤ k := by
    refine le_trans (le_of_eq ?_) hk
    norm_num
  obtain ⟨jc, hjc, hsrc, hcexh, hcconv, hcdist⟩ :=
    CarrierRechart.exists_comparison_data Λ e (m := 1) G h1n h1s g h1k j q hexh hconv hdist
  -- the finitely many indices with `q ∉ (j i).source`
  have hfb : ∀ i, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (CarrierRechart e.toHomeomorph Λ)
      (Y i) ∞, (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) ∈ Φ.source ∧ Φ ⟨q⟩ = j i q :=
    fun i => exists_partialDiffeomorph_mem_source_apply_eq _ _
  choose fb hfbsrc hfbval using hfb
  have h2 : ((1 + 1 : ℕ) : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  obtain ⟨j', hj'⟩ : ∃ j' : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
      (CarrierRechart e.toHomeomorph Λ) (Y i) ((1 + 1 : ℕ) : ℕ∞ω),
      ∀ i, (q ∈ (j i).source → j' i = jc i) ∧
        (q ∉ (j i).source → j' i = DifferentialGeometry.PartialDiffeomorph.ofLE (fb i) h2) :=
    ⟨fun i => if q ∈ (j i).source then jc i
      else DifferentialGeometry.PartialDiffeomorph.ofLE (fb i) h2,
      fun i => ⟨fun h => by simp [h], fun h => by simp [h]⟩⟩
  have hev : ∀ᶠ i in atTop, j' i = jc i := by
    filter_upwards [hexh {q} isCompact_singleton] with i hi
    exact (hj' i).1 (hi rfl)
  have hpt : ∀ i, (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) ∈ (j' i).source ∧
      j' i ⟨q⟩ = j i q := by
    intro i
    by_cases hq : q ∈ (j i).source
    · rw [(hj' i).1 hq]
      exact ⟨(hsrc i _).mpr hq, hjc i _⟩
    · rw [(hj' i).2 hq]
      exact ⟨hfbsrc i, hfbval i⟩
  have hexh' : ∀ C : Set (CarrierRechart e.toHomeomorph Λ), IsCompact C →
      ∀ᶠ i in atTop, C ⊆ (j' i).source := fun C hC => by
    filter_upwards [hev, hcexh C hC] with i hi hiC
    rw [hi]
    exact hiC
  have hconv' : ∀ (y : CarrierRechart e.toHomeomorph Λ) (L : Set E), IsCompact L →
      L ⊆ (extChartAt 𝓘(ℝ, E) y).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i)
          ((j' i : CarrierRechart e.toHomeomorph Λ → Y i) ∘ (extChartAt 𝓘(ℝ, E) y).symm))
        (chartCoeff (CarrierRechart.metric Λ e G h1n h1s) y) := by
    intro y L hL hLt ε hε
    obtain ⟨k0, hk0⟩ := hcconv y L hL hLt ε hε
    obtain ⟨k1, hk1⟩ := eventually_atTop.mp hev
    refine ⟨max k0 k1, fun i hi r hr x hx => ?_⟩
    simp only [hk1 i (le_of_max_le_right hi)]
    exact hk0 i (le_of_max_le_left hi) r hr x hx
  have hdist' : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      ∀ x ∈ ball (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) R,
      ∀ y ∈ ball (⟨q⟩ : CarrierRechart e.toHomeomorph Λ) R,
        |dist (j' i x) (j' i y) - dist x y| < ε := by
    intro R ε hε
    filter_upwards [hev, hcdist R ε hε] with i hi hiR
    rw [hi]
    exact hiR
  obtain ⟨jt, hjtpt, -, -, hjtexh, hjtconv, hjtdist, hjtcov⟩ :=
    exists_smooth_comparison_maps_of_finite_limit (K := 2) (by norm_num) g hmetric
      (fun i => j i q) (CarrierRechart.metric Λ e G h1n h1s) ⟨q⟩ j' hpt hexh' hconv' hdist'
  refine ⟨jt, hjtpt, hjtexh, fun y L hL hLt => hjtconv y L hL hLt, hjtdist,
    fun a b ha hab => ?_⟩
  filter_upwards [hjtcov a b ha hab] with i hi
  rw [(hjtpt i).2]
  exact hi

end Comparison

end DifferentialGeometry.Geometry.Collapse
