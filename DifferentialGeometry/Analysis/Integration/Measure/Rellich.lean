import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.LocalRestriction
import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import DifferentialGeometry.External.DeGiorgi.LpFunctionToolkit
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Mathlib.Analysis.InnerProductSpace.EuclideanDist


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma chartAtlasPOU_finset_sum_eq_one
    [T2Space M] [CompactSpace M]
    (x : M) :
    ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I) (M := M),
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x = 1 := by
  classical
  have hsubset :
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).finsupport x ⊆
        DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I) (M := M) := by
    intro α hα
    rw [DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset_mem]
    rw [SmoothPartitionOfUnity.mem_finsupport] at hα
    exact ⟨x, hα⟩
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).sum_finsupport' x
    (Set.mem_univ x) hsubset

theorem riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
    [T2Space M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hF_supp : ∀ x, x ∉ (chartAt H α).source → F x = 0) :
    ∫⁻ x, F x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) =
      ∫⁻ x, F x ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α) := by
  exact DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_eq_chartLocalMeasure_of_hasCompactSupport
    g (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
    hF (isClosed_tsupport F).isCompact hF_supp

def pullbackToM
    (I : ModelWithCorners ℝ E H) (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      w (toEuclidean (extChartAt I α x))
    else 0

omit [IsManifold I ∞ M] in
lemma pullbackToM_apply_of_mem (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    pullbackToM (M := M) I α w x =
      w (toEuclidean (extChartAt I α x)) := by
  classical
  unfold pullbackToM; simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_apply_of_notMem (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    pullbackToM (M := M) I α w x = 0 := by
  classical
  unfold pullbackToM; simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_support_subset_source (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    Function.support (pullbackToM (M := M) I α w) ⊆ (chartAt H α).source := by
  intro x hx
  by_contra h
  apply hx
  exact pullbackToM_apply_of_notMem (M := M) (I := I) α w h

omit [IsManifold I ∞ M] in
lemma pullbackToM_zero_of_notMem_source (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    pullbackToM (M := M) I α w x = 0 :=
  pullbackToM_apply_of_notMem (M := M) (I := I) α w hx

omit [IsManifold I ∞ M] in
lemma pullbackToM_add (α : M)
    (w₁ w₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    pullbackToM (M := M) I α (fun y => w₁ y + w₂ y) =
      fun x => pullbackToM (M := M) I α w₁ x +
        pullbackToM (M := M) I α w₂ x := by
  classical
  funext x
  unfold pullbackToM
  by_cases hx : x ∈ (chartAt H α).source
  · simp [hx]
  · simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_sub (α : M)
    (w₁ w₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    pullbackToM (M := M) I α (fun y => w₁ y - w₂ y) =
      fun x => pullbackToM (M := M) I α w₁ x -
        pullbackToM (M := M) I α w₂ x := by
  classical
  funext x
  unfold pullbackToM
  by_cases hx : x ∈ (chartAt H α).source
  · simp [hx]
  · simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_chartPushed
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (u : M → ℝ) :
    pullbackToM (M := M) I α
      (chartPushed (I := I) (M := M) ρ α u) =
        fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · rw [pullbackToM_apply_of_mem (M := M) (I := I) α _ hx]
    unfold chartPushed
    have htoeucl : toEuclidean.symm (toEuclidean (extChartAt I α x)) = extChartAt I α x := by
      simp
    rw [htoeucl]
    have hsymm : (extChartAt I α).symm (extChartAt I α x) = x := by
      apply (extChartAt I α).left_inv
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hx
    rw [hsymm]
  · rw [pullbackToM_apply_of_notMem (M := M) (I := I) α _ hx]
    have hxnotsupp : x ∉ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      intro hcontra
      exact hx (hρ α hcontra)
    have hρα_zero : ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport hxnotsupp
    rw [hρα_zero]
    ring

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
