import DifferentialGeometry.Analysis.ODE.GradientFlow
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem gradientRicciSoliton_hasDerivAt_scalar_comp_integralCurve
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    {γ : Real → M}
    (hγ : IsMIntegralCurve γ (fun x ↦ gradFun (I := I) g f x))
    (t : Real) :
    HasDerivAt ((fun x : M ↦ metricScalarAt (I := I) g x) ∘ γ)
      (2 * ricciTensor (I := I) g (γ t)
        (gradFun (I := I) g f (γ t)) (gradFun (I := I) g f (γ t))) t := by
  have hsmooth := metricScalar_smooth (I := I) (M := M) g
  have hraw := DifferentialGeometry.Analysis.ODE.hasDerivAt_df_comp_integralCurve
    (I := I) (fun x : M ↦ metricScalarAt (I := I) g x) hsmooth
    (fun x ↦ gradFun (I := I) g f x) hγ t
  change HasDerivAt ((fun x : M ↦ metricScalarAt (I := I) g x) ∘ γ)
    (mvfderiv (I := I) (fun x : M ↦ metricScalarAt (I := I) g x) (γ t)
      (gradFun (I := I) g f (γ t))) t at hraw
  convert hraw using 1
  rw [← differential1FormFun_apply_eq_mvfderiv]
  exact (gradientRicciSoliton_differential_scalar (I := I) h (γ t)
    (gradFun (I := I) g f (γ t))).symm

theorem gradientRicciSoliton_scalar_comp_integralCurve_monotone_of_ricci_nonneg
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      0 ≤ ricciTensor (I := I) g x v v)
    {γ : Real → M}
    (hγ : IsMIntegralCurve γ (fun x ↦ gradFun (I := I) g f x)) :
    Monotone ((fun x : M ↦ metricScalarAt (I := I) g x) ∘ γ) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun t ↦ gradientRicciSoliton_hasDerivAt_scalar_comp_integralCurve
      (I := I) h hγ t)
  intro t
  exact mul_nonneg (by norm_num) (hRic (γ t) (gradFun (I := I) g f (γ t)))

variable [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_exp_neg_mul_potential_comp_integralCurve_antitone
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {γ : Real → M}
    (hγ : IsMIntegralCurve γ (fun x ↦ gradFun (I := I) g f x)) :
    Antitone (fun s : Real ↦ Real.exp (-s) * f (γ s)) := by
  let q : Real → Real := fun s ↦ Real.exp (-s) * f (γ s)
  let q' : Real → Real := fun s ↦
    -Real.exp (-s) * metricScalarAt (I := I) g (γ s)
  have hF : ∀ s : Real, HasDerivAt ((f : M → Real) ∘ γ)
      (g.inner (γ s) (gradFun (I := I) g f (γ s))
        (gradFun (I := I) g f (γ s))) s := fun s ↦
    DifferentialGeometry.Analysis.ODE.hasDerivAt_comp_integralCurve_gradientFun
      (I := I) g (f : M → Real) f.contMDiff hγ s
  have hq : ∀ s : Real, HasDerivAt q (q' s) s := by
    intro s
    have hexp : HasDerivAt (fun r : Real ↦ Real.exp (-r)) (-Real.exp (-s)) s := by
      simpa only [mul_neg, mul_one] using!
        (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
    have hmul : HasDerivAt q
        ((-Real.exp (-s)) * f (γ s) + Real.exp (-s) *
          g.inner (γ s) (gradFun (I := I) g f (γ s))
            (gradFun (I := I) g f (γ s))) s := by
      simpa only [q, Function.comp_apply] using! hexp.mul (hF s)
    convert hmul using 1
    dsimp only [q']
    have hpot := normalizedGradientRicciSoliton_potential_equation (I := I) h (γ s)
    rw [← hpot]
    ring
  refine antitone_of_hasDerivAt_nonpos hq ?_
  intro s
  change -Real.exp (-s) * metricScalarAt (I := I) g (γ s) ≤ 0
  have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h (γ s)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hR

end DifferentialGeometry.Geometry
