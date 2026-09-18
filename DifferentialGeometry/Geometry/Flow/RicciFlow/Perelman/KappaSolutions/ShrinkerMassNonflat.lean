import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianMass

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem normalizedShrinkerMass_eq_one_of_isGaussian
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1)
    (hnormal : hamiltonNormalized g f 1) :
    normalizedShrinkerMass g f = 1 := by
  rw [normalizedShrinkerMass_eq_const_mul_lintegral,
    isGaussianGradientRicciSoliton_lintegral_exp_neg_of_hamiltonNormalized hGaussian hnormal,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi) _),
    ← Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi)]
  simp only [neg_div, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one]

theorem normalizedShrinkerMass_eq_one_of_scalar_eq_zero
    [ConnectedSpace M] [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton g f)
    {x : M} (hx : metricScalarAt g x = 0) :
    normalizedShrinkerMass g f = 1 :=
  normalizedShrinkerMass_eq_one_of_isGaussian
    (normalizedGradientRicciSoliton_isGaussian_of_scalar_eq_zero h hx)
    (normalizedGradientRicciSoliton_hamilton_normalized h)

theorem scalar_pos_of_normalizedShrinkerMass_ne_one
    [ConnectedSpace M] [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton g f)
    (hmass : normalizedShrinkerMass g f ≠ 1) (x : M) :
    0 < metricScalarAt g x :=
  lt_of_le_of_ne (normalizedGradientRicciSoliton_scalar_nonneg h x)
    (fun hx => hmass (normalizedShrinkerMass_eq_one_of_scalar_eq_zero h hx.symm))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
