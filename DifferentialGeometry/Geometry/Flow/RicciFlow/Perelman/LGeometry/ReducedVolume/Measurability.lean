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

end DifferentialGeometry.PDE.RicciFlow.Perelman
