import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


def intrinsicReducedVolume {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) (tau : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp
    (-(lCost S T p x tau / (2 * Real.sqrt tau)) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
    ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau))


def normalizedShrinkerMass (g : SmoothRiemannianMetric I M) (f : M → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp
    (-f x - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
    ∂riemannianVolumeMeasure (I := I) (M := M) g


def IsHamiltonNormalizedPotential (g : SmoothRiemannianMetric I M) (f : M → ℝ) : Prop :=
  ∀ x : M, metricScalarAt g x +
    g.inner x (gradientFun g f x) (gradientFun g f x) = f x


theorem normalizedShrinkerMass_add_const
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (c : ℝ) :
    normalizedShrinkerMass g (fun x => f x + c) =
      ENNReal.ofReal (Real.exp (-c)) * normalizedShrinkerMass g f := by
  unfold normalizedShrinkerMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

end Intrinsic

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicReducedVolume_eq_redVolume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) (tau : ℝ) :
    intrinsicReducedVolume S T p tau = redVolume S T p tau := rfl

theorem exists_gradientRicciSoliton_isHamiltonNormalizedPotential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hsol : gradientRicciSoliton (I := I) g f 1) :
    ∃ f' : C^∞⟮I, M; ℝ⟯,
      gradientRicciSoliton (I := I) g f' 1 ∧
        IsHamiltonNormalizedPotential (I := I) g f' := by
  obtain ⟨f', hsol', hham⟩ :=
    DifferentialGeometry.Geometry.gradientRicciSoliton_exists_hamiltonNormalized hsol
  refine ⟨f', hsol', fun x => ?_⟩
  simpa only [one_mul, Connection.gradient_eq_gradFun] using hham x

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
