import DifferentialGeometry.Geometry.Metric.Family.TensorNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.UpperSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lowerSemicontinuous_redDensity_of_complete_bounded_curvature
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K) :
    LowerSemicontinuous (fun y : M ↦ redDensity S T x y tau) := by
  let phi : Real → Real := fun r ↦ Real.exp
    (-r / (2 * Real.sqrt tau) -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  have hphi : Continuous phi := by
    dsimp only [phi]
    fun_prop
  have hphiAnti : Antitone phi := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    gcongr
  simpa only [Function.comp_def, phi, redDensity, redLength, neg_div] using
    hphi.comp_upperSemicontinuous_antitone
      (upperSemicontinuous_lCost_of_complete_bounded_curvature S hS K T hg x tau
        htau hreg hRm) hphiAnti

theorem measurable_redDensity_of_complete_bounded_curvature
    [MeasurableSpace M] [OpensMeasurableSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K) :
    Measurable (fun y : M ↦ redDensity S T x y tau) :=
  (lowerSemicontinuous_redDensity_of_complete_bounded_curvature S hS K T hg x tau
    htau hreg hRm).measurable

section Compact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

theorem lowerSemicontinuous_redDensity_of_compact
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular) :
    LowerSemicontinuous (fun y : M => redDensity S T x y tau) := by
  have hcarrier : Icc (T - tau) T ⊆ D.carrier := hreg.trans D.regular_subset
  obtain ⟨C, hC⟩ := Tensor0SBundle.exists_normSq0S_le_of_isCompact
    S.base.metric (fun t x => S.base.rm04 t x)
    (hS.smoothMetric.metricTensor_cont.mono hcarrier)
    (hS.rm04Cont.mono hcarrier) isCompact_Icc isCompact_univ
  exact lowerSemicontinuous_redDensity_of_complete_bounded_curvature S hS C T
    (RiemannianMetricComplete.of_compact (S.base.metric T)) x tau htau hreg
    (fun q hq z => hC q hq z (mem_univ _))

theorem measurable_redDensity_of_compact
    [MeasurableSpace M] [OpensMeasurableSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular) :
    Measurable (fun y : M => redDensity S T x y tau) :=
  (lowerSemicontinuous_redDensity_of_compact S hS T x tau htau hreg).measurable

end Compact

end DifferentialGeometry.PDE.RicciFlow.Perelman
