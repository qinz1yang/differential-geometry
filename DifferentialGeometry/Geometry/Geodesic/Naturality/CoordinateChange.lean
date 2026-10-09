import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.ODE.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem hasFDerivAt_tangent_lift {f : E → F} {z : E × E}
    (hf : ContDiffAt ℝ 2 f z.1) :
    HasFDerivAt (fun p : E × E => (f p.1, fderiv ℝ f p.1 p.2))
      (((fderiv ℝ f z.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((fderiv ℝ f z.1).comp (ContinuousLinearMap.snd ℝ E E) +
          ((fderiv ℝ (fderiv ℝ f) z.1).comp
            (ContinuousLinearMap.fst ℝ E E)).flip z.2)) z := by
  have hfst : HasFDerivAt (fun p : E × E => p.1)
      (ContinuousLinearMap.fst ℝ E E) z := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) z := hasFDerivAt_snd
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) z.1 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hf.differentiableAt (by norm_num)).hasFDerivAt.comp z hfst).prodMk
    ((hDf.hasFDerivAt.comp z hfst).clm_apply hsnd)

theorem fderiv_tangent_lift_geodesic_spray
    {A : E → E →L[ℝ] E →L[ℝ] E} {C : F → F →L[ℝ] F →L[ℝ] F}
    {f : E → F} {z : E × E} (hf : ContDiffAt ℝ 2 f z.1)
    (hcompat : ∀ v,
      fderiv ℝ (fderiv ℝ f) z.1 v v +
          C (f z.1) (fderiv ℝ f z.1 v) (fderiv ℝ f z.1 v) =
        fderiv ℝ f z.1 (A z.1 v v)) :
    fderiv ℝ (fun p : E × E => (f p.1, fderiv ℝ f p.1 p.2)) z
        (z.2, -A z.1 z.2 z.2) =
      (fderiv ℝ f z.1 z.2,
        -C (f z.1) (fderiv ℝ f z.1 z.2) (fderiv ℝ f z.1 z.2)) := by
  rw [(hasFDerivAt_tangent_lift hf).fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', add_apply,
    ContinuousLinearMap.flip_apply, map_neg]
  apply Prod.ext
  · rfl
  · rw [← hcompat z.2]
    abel_nf

theorem isIntegralCurveOn_tangent_lift_geodesic
    {A : E → E →L[ℝ] E →L[ℝ] E} {C : F → F →L[ℝ] F →L[ℝ] F}
    {f : E → F} {γ : ℝ → E × E} {s : Set ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ z => (z.2, -A z.1 z.2 z.2)) s)
    (hf : ∀ t ∈ s, ContDiffAt ℝ 2 f (γ t).1)
    (hcompat : ∀ t ∈ s, ∀ v,
      fderiv ℝ (fderiv ℝ f) (γ t).1 v v +
          C (f (γ t).1) (fderiv ℝ f (γ t).1 v) (fderiv ℝ f (γ t).1 v) =
        fderiv ℝ f (γ t).1 (A (γ t).1 v v)) :
    IsIntegralCurveOn (fun t => (f (γ t).1, fderiv ℝ f (γ t).1 (γ t).2))
      (fun _ z => (z.2, -C z.1 z.2 z.2)) s := by
  intro t ht
  have h := (hasFDerivAt_tangent_lift (hf t ht)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivWithinAt t (hγ t ht)
  rw [fderiv_tangent_lift_geodesic_spray (hf t ht) (hcompat t ht)] at h
  exact h

end DifferentialGeometry.Geometry.Connection
