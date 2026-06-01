import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity
import DifferentialGeometry.Analysis.Sobolev.Chart.TransitionPipeline
import DifferentialGeometry.Analysis.Sobolev.Chart.Transition
import DifferentialGeometry.Analysis.Sobolev.Chart.DensityInfra
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Integral.Measure.Family

/-!
# Helper lemmas for the smooth-density argument on `W^{1,p}_chart(M)`

This module collects helper lemmas surrounding the chart-pullback construction
`chartPullback I α ψ` and finite sums thereof. These lemmas are designed to be
combined with the per-chart smooth-density theorem
`MemWkp.exists_smooth_compactSupport_approx` and the chart-transition
quantitative chain rule
`SmoothDiffeoBoundedAtOrder.wkpNorm_comp_le` to produce smooth approximations
in `W^{1,p}_chart(M)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- A finite sum of smooth chart-pullbacks is smooth on `M`, provided each
summand has smooth Euclidean data with compact support inside the
corresponding chart target. -/
theorem contMDiff_finset_sum_chartPullback
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    {ι : Type*} (S : Finset ι) (α : ι → M)
    (ψ : ι → EuclN → ℝ)
    (hψ_smooth : ∀ i ∈ S, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hψ_cpt : ∀ i ∈ S, HasCompactSupport (ψ i))
    (hψ_supp : ∀ i ∈ S,
      tsupport (ψ i) ⊆ chartTargetEuclid (I := I) (M := M) (α i)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ∑ i ∈ S, chartPullback I (α i) (ψ i) x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact contMDiff_const
  | insert i S hiS ih =>
      have h_smooth_i : ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartPullback I (α i) (ψ i)) :=
        chartPullback_contMDiff (I := I) (M := M) (α i)
          (hψ_smooth i (Finset.mem_insert_self i S))
          (hψ_cpt i (Finset.mem_insert_self i S))
          (hψ_supp i (Finset.mem_insert_self i S))
      have ih' : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun x : M => ∑ j ∈ S, chartPullback I (α j) (ψ j) x) := by
        refine ih ?_ ?_ ?_
        · intro j hj
          exact hψ_smooth j (Finset.mem_insert.mpr (Or.inr hj))
        · intro j hj
          exact hψ_cpt j (Finset.mem_insert.mpr (Or.inr hj))
        · intro j hj
          exact hψ_supp j (Finset.mem_insert.mpr (Or.inr hj))
      have h_eq : (fun x : M => ∑ j ∈ insert i S, chartPullback I (α j) (ψ j) x) =
          (fun x : M => chartPullback I (α i) (ψ i) x +
            ∑ j ∈ S, chartPullback I (α j) (ψ j) x) := by
        funext x
        rw [Finset.sum_insert hiS]
      rw [h_eq]
      exact h_smooth_i.add ih'

omit [IsManifold I ∞ M] in
/-- `chartPushed` is linear in the underlying scalar field: for any sum
`∑ i ∈ S, f i x`, `chartPushed ρ α (Σ_i f_i)` equals the pointwise sum of
`chartPushed ρ α (f_i)`. -/
lemma chartPushed_finset_sum
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    {ι : Type*} (S : Finset ι) (f : ι → M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => ∑ i ∈ S, f i x) =
      (fun y => ∑ i ∈ S,
        chartPushed (I := I) (M := M) ρ α (f i) y) := by
  classical
  funext y
  unfold chartPushed
  rw [Finset.mul_sum]

omit [IsManifold I ∞ M] in
/-- `chartPushed` is additive. -/
lemma chartPushed_sub
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (u v : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x - v x) =
      (fun y =>
        chartPushed (I := I) (M := M) ρ α u y -
          chartPushed (I := I) (M := M) ρ α v y) := by
  funext y
  unfold chartPushed
  ring

/-- `MemWkpChart` is closed under finite sums (as a Finset sum). -/
theorem MemWkpChart_finset_sum
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {ι : Type*} (S : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ i ∈ S, MemWkpChart (I := I) (M := M) g k p (f i)) :
    MemWkpChart (I := I) (M := M) g k p (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkpChart_zero_fun (I := I) (M := M) g hp
  | insert i S hiS ih =>
      have hi : MemWkpChart (I := I) (M := M) g k p (f i) :=
        hf i (Finset.mem_insert_self i S)
      have ih' : MemWkpChart (I := I) (M := M) g k p
          (fun x : M => ∑ j ∈ S, f j x) :=
        ih (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
      have h_eq : (fun x : M => ∑ j ∈ insert i S, f j x) =
          (fun x : M => f i x + ∑ j ∈ S, f j x) := by
        funext x
        rw [Finset.sum_insert hiS]
      rw [h_eq]
      exact MemWkpChart_add (I := I) (M := M) g hp hi ih'

/-- The chart-based norm of a finite sum is bounded by the sum of chart-based
norms. -/
theorem wkpNormChart_finset_sum_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {ι : Type*} (S : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ i ∈ S, MemWkpChart (I := I) (M := M) g k p (f i)) :
    wkpNormChart (I := I) (M := M) g k p (fun x => ∑ i ∈ S, f i x) ≤
      ∑ i ∈ S, wkpNormChart (I := I) (M := M) g k p (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [wkpNormChart_zero_fun (I := I) (M := M) g hp]
  | insert i S hiS ih =>
      have hi : MemWkpChart (I := I) (M := M) g k p (f i) :=
        hf i (Finset.mem_insert_self i S)
      have hS_mem : ∀ j ∈ S, MemWkpChart (I := I) (M := M) g k p (f j) :=
        fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj))
      have hS_sum_mem : MemWkpChart (I := I) (M := M) g k p
          (fun x : M => ∑ j ∈ S, f j x) :=
        MemWkpChart_finset_sum (I := I) (M := M) g hp S f hS_mem
      have h_eq : (fun x : M => ∑ j ∈ insert i S, f j x) =
          (fun x : M => f i x + ∑ j ∈ S, f j x) := by
        funext x
        rw [Finset.sum_insert hiS]
      rw [h_eq, Finset.sum_insert hiS]
      have h_tri := wkpNormChart_add_le (I := I) (M := M) g hp hi hS_sum_mem
      refine h_tri.trans ?_
      gcongr
      exact ih hS_mem

/-- On a compact manifold with the canonical chart-atlas POU, the chart-pushed
function `chartPushed (chartAtlasPOU I M) α u` vanishes on `chartTargetEuclid α`
outside the compact set `toEuclidean '' ((extChartAt I α) '' tsupport (ρ_α))`. -/
theorem chartPushed_eq_zero_off_compact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ toEuclidean '' ((extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α) :
        M → ℝ)))) :
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y = 0 :=
  DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_support_subset_compact_in_target
    (I := I) (M := M) α u y hy_target hy_off

/-- On a compact manifold, the chart-based norm equals a finite sum over the
set `chartAtlasPOU_finset` (the indices where the partition-of-unity
weight has non-empty support). -/
theorem wkpNormChart_eq_finset_sum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) g k p u =
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I) (M := M),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hf_zero_off : ∀ α : M, α ∉
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M) → f α = 0 := by
    intro α hα
    have hρ_zero : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : M → ℝ) x = 0 := by
      intro x
      exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hα x
    have hChartPushed_zero : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_zero]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_eq_sum hf_zero_off]

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
