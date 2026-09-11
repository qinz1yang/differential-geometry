import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy

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
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem integrableOn_inner_lVelocity_lRegularizedCurve
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (g : SmoothRiemannianMetric I M)
    {a b : Real} (hdom : Icc a b ⊆ lRegularizedDomain S T x Z) :
    IntegrableOn (fun s ↦ g.inner (lRegularizedCurve S T x Z s)
      (lVelocity (I := I) (lRegularizedCurve S T x Z) s)
      (lVelocity (I := I) (lRegularizedCurve S T x Z) s)) (Icc a b) := by
  apply Geometry.Riemannian.integrableOn_inner_mfderiv_self_of_contMDiffOn
  intro s hs
  have hpair : ContMDiffAt 𝓘(Real, Real) (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      ((fun r : Real ↦ (Z, r)) : Real → E × Real) s :=
    (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  exact (((lRegularizedCurve_smooth S hS T x (hdom hs)).comp s hpair).of_le
    (by norm_num)).contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem intervalIntegrable_lRegularizedSpeedSq_lRegularizedCurve
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {B : Real}
    (hB : 0 < B) (hdom : B ∈ lRegularizedDomain S T x Z) :
    IntervalIntegrable (lRegularizedSpeedSq S T (lRegularizedCurve S T x Z)) volume 0 B := by
  let alpha : Real → M := lRegularizedCurve S T x Z
  have halpha : IsLRegularizedCurveOn S T alpha (Set.Icc (0 : Real) B) x Z := by
    simpa only [alpha, Set.uIcc_of_le hB.le] using
      lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x Z hB hdom
  have hcontinuous : ContinuousOn (lRegularizedSpeedSq S T alpha)
      (Set.Icc (0 : Real) B) := by
    intro s hs
    exact (hasDerivAt_lRegularizedSpeedSq (I := I) S hS T halpha hs).continuousAt.continuousWithinAt
  have hcontinuous' : ContinuousOn (lRegularizedSpeedSq S T alpha)
      (Set.uIcc (0 : Real) B) := by
    simpa only [Set.uIcc_of_le hB.le] using hcontinuous
  simpa only [alpha] using hcontinuous'.intervalIntegrable

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem intervalIntegrable_lRegularizedLagrangian_lRegularizedCurve
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {B : Real}
    (hB : 0 < B) (hdom : B ∈ lRegularizedDomain S T x Z) :
    IntervalIntegrable (lRegularizedLagrangian S T (lRegularizedCurve S T x Z)) volume 0 B := by
  let alpha : Real → M := lRegularizedCurve S T x Z
  have hkin : IntervalIntegrable (lRegularizedSpeedSq S T alpha) volume 0 B := by
    simpa only [alpha] using
      intervalIntegrable_lRegularizedSpeedSq_lRegularizedCurve (I := I) S hS T x Z hB hdom
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have halpha : ContinuousOn alpha (Set.Icc (0 : Real) B) :=
    (lRegularizedCurve_c1On (I := I) S hS T x Z hdom).continuousOn
  have hpair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.Icc (0 : Real) B) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk halpha
  have hmaps : Set.MapsTo (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.Icc (0 : Real) B) (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro s hs
    exact ⟨D.regular_subset (lRegularizedDomain_regularity S T x Z
      (lRegularizedDomain_segment S T x Z hdom hs.1 hs.2)), Set.mem_univ _⟩
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
    (1 / 2 : Real) * lRegularizedSpeedSq S T alpha s +
      2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) volume 0 B
  exact (hkin.const_mul (1 / 2 : Real)).add hpotential

end DifferentialGeometry.PDE.RicciFlow.Perelman
