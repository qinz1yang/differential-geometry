import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff dimension of a closed Riemannian manifold

For a smooth metric `g` on a compact connected manifold modelled on `E`, the distance of `g`
(`inducedMetricSpace g`) has Hausdorff dimension at most `finrank ℝ E`. The proof is lane A3's
exact identity `normalizedHausdorffMeasure (finrank ℝ E) = riemannianVolumeMeasure g`
(`normalizedHausdorffMeasure_eq_riemannianVolumeMeasure`) and finiteness of the Riemannian
volume of a compact manifold: the Hausdorff measure of dimension `finrank ℝ E` of the whole
space is finite, hence the dimension bound. This is the dimension input of AC55 for the
Riemannian bindings of LC66, LC76 and LC77.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- A compact connected smooth Riemannian manifold, with the distance of its metric, has
Hausdorff dimension at most the dimension of its model space. -/
theorem dimH_univ_le_finrank_inducedMetricSpace {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [CompactSpace M] (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    dimH (univ : Set M) ≤ Module.finrank ℝ E := by
  let _ := inducedMetricSpace g
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨hRM, hEnorm, hcont⟩ := inducedMetricSpace_riemannian g
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  have h := normalizedHausdorffMeasure_eq_riemannianVolumeMeasure g hEnorm
  have _ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I) g
  have hne : (normalizedHausdorffMeasure (Module.finrank ℝ E) : Measure M) univ ≠ ⊤ := by
    rw [h]
    exact measure_ne_top _ _
  have hμ : μH[(Module.finrank ℝ E : ℝ)] (univ : Set M) ≠ ⊤ := by
    intro htop
    apply hne
    simp only [normalizedHausdorffMeasure, Measure.smul_apply]
    rw [htop]
    exact ENNReal.mul_top (by exact_mod_cast (euclideanHausdorffFactor_pos _).ne')
  have hd := dimH_le_of_hausdorffMeasure_ne_top (d := (Module.finrank ℝ E : NNReal))
    (s := (univ : Set M)) (by simpa only [NNReal.coe_natCast] using hμ)
  simpa only [ENNReal.coe_natCast] using hd

end DifferentialGeometry.Geometry.Metric
