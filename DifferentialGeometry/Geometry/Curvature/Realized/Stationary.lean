import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open Bundle Manifold MeasureTheory Set Filter
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

noncomputable def stationaryMetricFamily
    (g : SmoothRiemannianMetric I M) :
    MetricConnectionFamily (I := I) (M := M) Real where
  metric := fun _ => g
  connection := fun _ => leviCivitaConnectionOfMetric (I := I) g
  metricCompatible := fun _ =>
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g

omit [SigmaCompactSpace M] [T2Space M] in
lemma metricFamilySmoothOn_stationary
    (g : SmoothRiemannianMetric I M) (D : RealTimeInterval) :
    MetricFamilySmoothOn (I := I) (M := M) D (stationaryMetricFamily g).metric where
  coeff x X Y := by
    simpa [stationaryMetricFamily] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => g.inner x X Y) D.regular)
  coeff_cont x X Y := by
    simpa [stationaryMetricFamily] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => g.inner x X Y) D.carrier)
  metricTensor_cont := by
    have hconst : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => metricTensorField (I := I) g x) := by
      apply DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet_of_chartBasisComp
        (N := fun x₀ => (trivializationAt E (TangentSpace I) x₀).baseSet)
        (hN := fun x₀ => (Trivialization.open_baseSet _).mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀))
      intro x₀ idx
      have heq :
          (fun q : {t : ℝ // t ∈ D.carrier} × M =>
            metricTensorField (I := I) g q.2
              (fun k : Fin 2 =>
                DifferentialGeometry.Integral.Measure.chartBasisVecFiber
                  (I := I) x₀ (idx k) q.2)) =
          fun q : {t : ℝ // t ∈ D.carrier} × M =>
            DifferentialGeometry.Integral.Measure.chartGramMatrix
              (I := I) g x₀ q.2 (idx 0) (idx 1) := by
        funext q
        rw [metricTensorField_apply,
          DifferentialGeometry.Integral.Measure.chartGramMatrix_apply]
      rw [heq]
      have hcont : ContinuousOn (fun x : M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x₀ x
            (idx 0) (idx 1))
          (trivializationAt E (TangentSpace I) x₀).baseSet :=
        (DifferentialGeometry.Integral.Measure.chartGramMatrix_entry_contMDiffOn
          (I := I) g x₀ (idx 0) (idx 1)).continuousOn
      have hproj : ContinuousOn (fun q : {t : ℝ // t ∈ D.carrier} × M => q.2)
          {q : {t : ℝ // t ∈ D.carrier} × M |
            q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
        (continuous_snd : Continuous (fun q : {t : ℝ // t ∈ D.carrier} × M => q.2)).continuousOn
      exact hcont.comp hproj (fun q hq => hq)
    exact Tensor0SFamilyContinuousOnSet.congr hconst (by
      intro t _ht x
      simp [stationaryMetricFamily])
  frameCompSmooth := by
    intro Idx _hFintype frame u hframe i j
    have hinner : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g.inner x (frame i x) (frame j x)) u :=
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffOn_frame
        g frame hframe i j
    have hproj : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2)
        (D.regular ×ˢ u) := by
      simpa using (contMDiffOn_snd (I := 𝓘(ℝ, ℝ)) (J := I) (n := (∞ : WithTop ℕ∞))
        (s := D.regular ×ˢ u))
    have hmaps : Set.MapsTo (fun p : ℝ × M => p.2) (D.regular ×ˢ u) u :=
      fun p hp => hp.2
    have hcomp := hinner.comp hproj hmaps
    simpa [stationaryMetricFamily] using hcomp

end Curvature
end Geometry
end DifferentialGeometry
