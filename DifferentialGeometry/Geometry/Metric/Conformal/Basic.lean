import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem contMDiff_conformalMetric_inner_section
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) :
    ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun y : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun y : M => TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
        y (Real.exp (2 * u y) • g.inner y)) := by
  let : (y : M) → TopologicalSpace
      (TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real) := fun _ => inferInstance
  have h : ContMDiff I 𝓘(Real, Real) ∞ (fun x => Real.exp (2 * u x)) :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul u.contMDiff)
  convert
    h.smul_section (I := I) (F := E →L[Real] E →L[Real] Real)
      (V := fun y : M => TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
      g.contMDiff using 1
  with_reducible_and_instances rfl

def conformalMetric (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) :
    SmoothRiemannianMetric I M where
  inner x := Real.exp (2 * u x) • g.inner x
  symm x v w := (scaleMetric (Real.exp (2 * u x)) (Real.exp_pos _) g).symm x v w
  pos x v hv := (scaleMetric (Real.exp (2 * u x)) (Real.exp_pos _) g).pos x v hv
  isVonNBounded x := (scaleMetric (Real.exp (2 * u x)) (Real.exp_pos _) g).isVonNBounded x
  contMDiff := contMDiff_conformalMetric_inner_section g u

@[simp] theorem conformalMetric_inner
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (x : M) (v w : TangentSpace I x) :
    (conformalMetric g u).inner x v w = Real.exp (2 * u x) * g.inner x v w :=
  rfl

@[simp] theorem conformalMetric_zero (g : SmoothRiemannianMetric I M) :
    conformalMetric g 0 = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change Real.exp (2 * 0) * g.inner x v w = g.inner x v w
  rw [mul_zero, Real.exp_zero, one_mul]

theorem conformalMetric_add (g : SmoothRiemannianMetric I M)
    (u v : C^∞⟮I, M; Real⟯) :
    conformalMetric g (u + v) = conformalMetric (conformalMetric g u) v := by
  apply SmoothRiemannianMetric.ext_inner
  intro x a b
  change Real.exp (2 * (u x + v x)) * g.inner x a b =
    Real.exp (2 * v x) * (Real.exp (2 * u x) * g.inner x a b)
  rw [mul_add, Real.exp_add]
  ring

@[simp] theorem conformalMetric_neg (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I, M; Real⟯) :
    conformalMetric (conformalMetric g u) (-u) = g := by
  rw [← conformalMetric_add, add_neg_cancel, conformalMetric_zero]

theorem conformalMetric_const (g : SmoothRiemannianMetric I M) (c : Real) :
    conformalMetric g (ContMDiffMap.const c) =
      scaleMetric (Real.exp (2 * c)) (Real.exp_pos _) g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

end DifferentialGeometry
