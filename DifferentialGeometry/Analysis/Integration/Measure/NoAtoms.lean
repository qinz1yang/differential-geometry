import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.LinearAlgebra.Dimension.Finite


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma chartLocalMeasure_singleton
    [T1Space M] [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    chartLocalMeasure (I := I) g x₀ {x} = 0 := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne _))
  haveI : NoAtoms (modelHaar (E := E)) := inferInstance
  have htarget : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hx_meas : MeasurableSet ({x} : Set M) :=
    (isClosed_singleton (x := x)).measurableSet
  rw [chartLocalMeasure_def]
  set ν : Measure E :=
    ((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))) with hνdef
  have hac : ν ≪ (modelHaar (E := E)).restrict (extChartAt I x₀).target := by
    rw [hνdef]; exact withDensity_absolutelyContinuous _ _
  have haemeas : AEMeasurable ((extChartAt I x₀).symm) ν :=
    (aemeasurable_extChartAt_symm_restrict_target (I := I) x₀).mono' hac
  rw [Measure.map_apply_of_aemeasurable haemeas hx_meas]
  refine hac ?_
  rw [Measure.restrict_apply' htarget]
  refine Set.Subsingleton.measure_zero ?_ _
  intro y₁ hy₁ y₂ hy₂
  have h1 : (extChartAt I x₀).symm y₁ = x := hy₁.1
  have h2 : (extChartAt I x₀).symm y₂ = x := hy₂.1
  have hsrc1 : y₁ ∈ (extChartAt I x₀).symm.source := by
    rw [PartialEquiv.symm_source]; exact hy₁.2
  have hsrc2 : y₂ ∈ (extChartAt I x₀).symm.source := by
    rw [PartialEquiv.symm_source]; exact hy₂.2
  exact (extChartAt I x₀).symm.injOn hsrc1 hsrc2 (h1.trans h2.symm)

theorem riemannianVolumeMeasure_singleton
    [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianVolumeMeasure (I := I) (M := M) g {x} = 0 := by
  have hx_meas : MeasurableSet ({x} : Set M) :=
    (isClosed_singleton (x := x)).measurableSet
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def,
    Measure.sum_apply _ hx_meas]
  refine ENNReal.tsum_eq_zero.mpr fun α => ?_
  exact (withDensity_absolutelyContinuous _ _)
    (chartLocalMeasure_singleton (I := I) g α x)

instance instNoAtoms_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) :
    NoAtoms (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ⟨fun x => riemannianVolumeMeasure_singleton (I := I) g x⟩

end Measure
end Integral
end DifferentialGeometry
