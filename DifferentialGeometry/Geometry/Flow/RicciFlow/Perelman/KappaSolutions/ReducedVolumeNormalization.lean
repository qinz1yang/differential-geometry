import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Scaling


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory
open DifferentialGeometry.PDE.RicciFlow.Entropy
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

theorem normalizedShrinkerMass_eq_const_mul_lintegral
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    normalizedShrinkerMass (I := I) (M := M) g f =
      ENNReal.ofReal ((4 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (-f x)) ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  unfold normalizedShrinkerMass
  have hrpow : (4 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))) := by
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
    congr 1
    ring_nf
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi) _)]
  congr 1
  rw [hrpow, ← Real.exp_add]
  congr 1
  ring_nf

theorem normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity
    (g : SmoothRiemannianMetric I M) {tau : ℝ} (htau : 0 < tau) (f : M → ℝ) :
    normalizedShrinkerMass (scaleMetric tau⁻¹ (inv_pos.mpr htau) g) f =
      ∫⁻ x, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) tau f x)
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) 1 f x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (scaleMetric tau⁻¹ (inv_pos.mpr htau) g) := by
      rw [normalizedShrinkerMass_eq_const_mul_lintegral,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi) _)]
      simp only [perelmanDensity, perelmanDensityPrefactor, mul_one]
      rfl
    _ = _ := by
      simpa only [inv_mul_cancel₀ htau.ne', setLIntegral_univ] using
        setLIntegral_perelmanDensity_scaleMetric g (inv_pos.mpr htau) htau f Set.univ

theorem normalizedShrinkerMass_eq_lintegral_perelmanDensity_one
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    normalizedShrinkerMass g f = ∫⁻ x,
      ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) 1 f x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  have hg : scaleMetric 1 zero_lt_one g = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner, one_mul]
  simpa only [inv_one, hg] using
    normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity g zero_lt_one f

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
    [T2Space M] [ConnectedSpace M]
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
