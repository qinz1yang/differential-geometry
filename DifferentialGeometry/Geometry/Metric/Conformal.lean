import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def conformalMetric (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) : SmoothRiemannianMetric I M where
  inner x := Real.exp (2 * f x) • g.inner x
  symm x v w := by
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul, g.symm x v w]
  pos x v hv := by
    simpa [ContinuousLinearMap.smul_apply, smul_eq_mul] using
      mul_pos (Real.exp_pos (2 * f x)) (g.pos x v hv)
  isVonNBounded x := by
    set c : Real := Real.exp (2 * f x) with hcdef
    have hc : 0 < c := Real.exp_pos _
    by_cases hlarge : 1 <= c
    · refine (g.isVonNBounded x).subset ?_
      intro v hv
      simp only [Set.mem_setOf_eq] at hv ⊢
      by_cases hv0 : v = 0
      · simp [hv0]
      · have hpos := g.pos x v hv0
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hv
        nlinarith
    · have hsmall : c < 1 := lt_of_not_ge hlarge
      let L : TangentSpace I x →L[Real] TangentSpace I x :=
        c⁻¹ • (1 : TangentSpace I x →L[Real] TangentSpace I x)
      refine ((g.isVonNBounded x).image L).subset ?_
      intro v hv
      simp only [Set.mem_setOf_eq] at hv
      refine ⟨c • v, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hv
        have hscale :
            g.inner x (c • v) (c • v) =
              c * (c * g.inner x v v) := by
          simp [smul_eq_mul]
        rw [hscale]
        nlinarith
      · calc
          L (c • v) = c⁻¹ • (c • v) := by
            simp [L, smul_smul, mul_comm]
          _ = v := by
            rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  contMDiff := sorry

@[simp] theorem conformalMetric_inner
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    (conformalMetric f hf g).inner x v w = Real.exp (2 * f x) * g.inner x v w :=
  rfl

end DifferentialGeometry
