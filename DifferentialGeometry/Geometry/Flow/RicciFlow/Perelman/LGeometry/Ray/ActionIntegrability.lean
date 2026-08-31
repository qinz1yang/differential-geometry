import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem intervalIntegrable_lRegSpeedSq_lRegCurve
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {B : Real}
    (hB : 0 < B) (hdom : B ∈ lRegDomain S T x Z) :
    IntervalIntegrable (lRegSpeedSq S T (lRegCurve S T x Z)) volume 0 B := by
  let alpha : Real → M := lRegCurve S T x Z
  have halpha : IsLRegCurveOn S T alpha (Set.Icc (0 : Real) B) x Z := by
    simpa only [alpha, Set.uIcc_of_le hB.le] using
      lRegCurve_isReg (I := I) S hS T x Z hB hdom
  have hcontinuous : ContinuousOn (lRegSpeedSq S T alpha)
      (Set.Icc (0 : Real) B) := by
    intro s hs
    exact (hasDerivAt_lRegSpeedSq (I := I) S hS T halpha hs).continuousAt.continuousWithinAt
  have hcontinuous' : ContinuousOn (lRegSpeedSq S T alpha)
      (Set.uIcc (0 : Real) B) := by
    simpa only [Set.uIcc_of_le hB.le] using hcontinuous
  simpa only [alpha] using hcontinuous'.intervalIntegrable

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem intervalIntegrable_lRegLagrangian_lRegCurve
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {B : Real}
    (hB : 0 < B) (hdom : B ∈ lRegDomain S T x Z) :
    IntervalIntegrable (lRegLagrangian S T (lRegCurve S T x Z)) volume 0 B := by
  let alpha : Real → M := lRegCurve S T x Z
  have hkin : IntervalIntegrable (lRegSpeedSq S T alpha) volume 0 B := by
    simpa only [alpha] using
      intervalIntegrable_lRegSpeedSq_lRegCurve (I := I) S hS T x Z hB hdom
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have halpha : ContinuousOn alpha (Set.Icc (0 : Real) B) :=
    (lRegCurve_c1On (I := I) S hS T x Z hdom).continuousOn
  have hpair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.Icc (0 : Real) B) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk halpha
  have hmaps : Set.MapsTo (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.Icc (0 : Real) B) (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro s hs
    exact ⟨D.regular_subset (lRegDomain_reg S T x Z
      (lRegDomain_seg S T x Z hdom hs.1 hs.2)), Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun s : Real ↦ S.scalar (T - s ^ 2) (alpha s))
      (Set.Icc (0 : Real) B) := by
    simpa only [Function.comp_def] using
      hSc.scalar_continuousOn.comp hpair hmaps
  have hpotential : IntervalIntegrable
      (fun s : Real ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume 0 B := by
    have hcoefficient : Continuous (fun s : Real ↦ 2 * s ^ 2) :=
      continuous_const.mul (continuous_id.pow 2)
    have hcontinuous := hcoefficient.continuousOn.mul hscalar
    have hcontinuous' : ContinuousOn
        (fun s : Real ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
        (Set.uIcc (0 : Real) B) := by
      rw [Set.uIcc_of_le hB.le]
      with_unfolding_all exact hcontinuous
    exact hcontinuous'.intervalIntegrable
  change IntervalIntegrable (fun s : Real ↦
    (1 / 2 : Real) * lRegSpeedSq S T alpha s +
      2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) volume 0 B
  exact (hkin.const_mul (1 / 2 : Real)).add hpotential

end DifferentialGeometry.PDE.RicciFlow.Perelman
