import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianHamiltonNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianRigidity
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform


noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem normalizedShrinkerMass_gaussian :
    normalizedShrinkerMass (I := 𝓘(ℝ, E)) (euclideanMetric (E := E))
      (gaussianPotential (E := E)) = 1 := by
  let q : E → ℝ := fun x => Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2)
  have hi : (∫ x, q x) =
      (4 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := E) (b := (1 / 4 : ℝ)) (by norm_num)
    rw [show Real.pi / (1 / 4 : ℝ) = 4 * Real.pi by ring] at h
    exact h
  have hqi : Integrable q := Integrable.of_integral_ne_zero (by
    rw [hi]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne')
  have hqpos : 0 ≤ᵐ[volume] q :=
    Filter.Eventually.of_forall (fun x => Real.exp_nonneg _)
  have hL : (∫⁻ x, ENNReal.ofReal (q x)) =
      ENNReal.ofReal ((4 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hqi hqpos, hi]
  let c : ℝ := ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)
  have hpoint (x : E) : Real.exp (-gaussianPotential x - c) =
      Real.exp (-c) * q x := by
    rw [← Real.exp_add]
    congr 1
    rw [gaussianPotential_apply]
    ring
  have hfactor : Real.exp (-c) =
      (4 * Real.pi) ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
    congr 1
    dsimp only [c]
    ring
  unfold normalizedShrinkerMass
  rw [riemannianVolumeMeasure_euclideanMetric]
  change (∫⁻ x, ENNReal.ofReal (Real.exp (-gaussianPotential x - c))) = 1
  simp_rw [hpoint, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hL,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), hfactor,
    ← Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi)]
  simp

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem normalizedShrinkerMass_eq_one_of_isGaussian_of_hamiltonNormalized
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hgaussian : isGaussianGradientRicciSoliton (E := E) g f 1)
    (hnormal : hamiltonNormalized (I := I) g f 1) :
    normalizedShrinkerMass (I := I) g f = 1 := by
  obtain ⟨hone, Psi, hmetric, hpotential⟩ :=
    isGaussianGradientRicciSoliton_exists_diffeomorph_of_hamiltonNormalized
      hgaussian hnormal
  have hmetric' : Diffeomorph.pullbackMetricCross euclideanMetric Psi = g := by
    rw [hmetric]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner, one_mul]
  have hpotential' (x : M) : f x = gaussianPotential (Psi x) :=
    congrArg (fun q : C^∞⟮I, M; ℝ⟯ => q x) hpotential
  have hmass : normalizedShrinkerMass (I := I) g f =
      normalizedShrinkerMass (I := 𝓘(ℝ, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) := by
    unfold normalizedShrinkerMass
    rw [← hmetric', riemannianVolumeMeasure_pullback_cross]
    have hmeas : Measurable (fun y : M => ENNReal.ofReal (Real.exp
        (-f y - ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))) :=
      ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp (f.contMDiff.continuous.measurable.neg.sub measurable_const))
    rw [lintegral_map hmeas Psi.symm.contMDiff.continuous.measurable]
    apply lintegral_congr
    intro x
    rw [hpotential', Psi.apply_symm_apply]
  rw [hmass, normalizedShrinkerMass_gaussian]

variable [ConnectedSpace M] [NeZero (Module.finrank ℝ E)]

theorem normalizedGradientRicciSoliton_scalar_pos_of_mass_lt_one
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hsol : normalizedGradientRicciSoliton (I := I) g f)
    (hmass : normalizedShrinkerMass (I := I) g f < 1) (x : M) :
    0 < metricScalarAt (I := I) g x := by
  apply normalizedGradientRicciSoliton_scalar_pos_of_not_isGaussian hsol
  intro hgaussian
  have heq := normalizedShrinkerMass_eq_one_of_isGaussian_of_hamiltonNormalized
    hgaussian (normalizedGradientRicciSoliton_hamilton_normalized hsol)
  rw [heq] at hmass
  exact (lt_irrefl (1 : ℝ≥0∞)) hmass

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
