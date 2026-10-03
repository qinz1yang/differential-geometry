import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Manifold
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section

open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def euclideanBilinear : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

private def coordinateBilinear (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  euclideanBilinear - (1 + ‖x‖ ^ 2)⁻¹ • (innerSL ℝ x).smulRight (innerSL ℝ x)

private theorem coordinateBilinear_apply (x v w : E) :
    coordinateBilinear x v w = inner ℝ v w - inner ℝ x v * inner ℝ x w / (1 + ‖x‖ ^ 2) := by
  change inner ℝ v w - (1 + ‖x‖ ^ 2)⁻¹ * (inner ℝ x v * inner ℝ x w) = _
  rw [div_eq_mul_inv]
  ring

private theorem coordinateBilinear_symm (x v w : E) :
    coordinateBilinear x v w = coordinateBilinear x w v := by
  rw [coordinateBilinear_apply, coordinateBilinear_apply, real_inner_comm v w,
    mul_comm (inner ℝ x v) (inner ℝ x w)]

private theorem coordinateBilinear_lower (x v : E) :
    ‖v‖ ^ 2 / (1 + ‖x‖ ^ 2) ≤ coordinateBilinear x v v := by
  rw [coordinateBilinear_apply, real_inner_self_eq_norm_sq, le_sub_iff_add_le, ← add_div,
    div_le_iff₀ (show 0 < 1 + ‖x‖ ^ 2 by positivity)]
  have h := real_inner_mul_inner_self_le x v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith

private theorem coordinateBilinear_pos (x v : E) (hv : v ≠ 0) :
    0 < coordinateBilinear x v v :=
  lt_of_lt_of_le (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) (by positivity))
    (coordinateBilinear_lower x v)

private theorem coordinateBilinear_bounded (x : E) :
    Bornology.IsVonNBounded ℝ {v : E | coordinateBilinear x v v < 1} := by
  rw [NormedSpace.isVonNBounded_iff']
  refine ⟨Real.sqrt (1 + ‖x‖ ^ 2), fun v hv => ?_⟩
  have h := lt_of_le_of_lt (coordinateBilinear_lower x v) hv
  have hs : ‖v‖ ^ 2 < 1 + ‖x‖ ^ 2 := by
    simpa only [one_mul] using (div_lt_iff₀ (show 0 < 1 + ‖x‖ ^ 2 by positivity)).mp h
  calc
    ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt hs.le

private theorem contDiff_coordinateBilinear : ContDiff ℝ ∞ (coordinateBilinear (E := E)) := by
  have hi : ContDiff ℝ ∞ (fun x : E => innerSL ℝ x) := (innerSL ℝ).contDiff
  have hr : ContDiff ℝ ∞ (fun x : E => (innerSL ℝ x).smulRight (innerSL ℝ x)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).contDiff.comp hi).clm_apply hi
  have hd : ContDiff ℝ ∞ (fun x : E => (1 + ‖x‖ ^ 2)⁻¹) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).inv fun x => by positivity
  exact contDiff_const.sub (hd.smul hr)

private def metricInner (x : Hyperboloid E) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
  coordinateBilinear (E := E) x.space

private theorem coordinateBilinear_section_contMDiff :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : Hyperboloid E => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : Hyperboloid E =>
          TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ)
        x (metricInner x)) := by
  intro x
  rw [Bundle.contMDiffAt_section]
  have h := contDiff_coordinateBilinear.contMDiff.comp
    (contMDiff_space (E := E) (n := ∞))
  convert h.contMDiffAt using 1
  ext y v w
  rw [hom_trivializationAt_apply]
  have hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, chartAt_eq_spaceHomeomorph]
    trivial
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  have hs (u : E) : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symm y u = u := by
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) _ hy, tangent_trivializationAt_symmL]
    rfl
  rw [hs v, hs w]
  change (Bundle.Trivial.trivialization (Hyperboloid E) ℝ).linearMapAt ℝ y _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization]
  rfl

def riemannianMetric : SmoothRiemannianMetric 𝓘(ℝ, E) (Hyperboloid E) where
  inner := metricInner
  symm x v w := coordinateBilinear_symm (E := E) x.space v w
  pos x v hv := coordinateBilinear_pos x.space v hv
  isVonNBounded x := coordinateBilinear_bounded x.space
  contMDiff := coordinateBilinear_section_contMDiff

theorem riemannianMetric_inner (x : Hyperboloid E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    riemannianMetric.inner x v w =
      inner ℝ (NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x v))
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x w)) -
        inner ℝ x.space (NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x v)) *
          inner ℝ x.space (NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x w)) /
            (1 + ‖x.space‖ ^ 2) := by
  rw [mfderiv_spaceDiffeomorph]
  exact coordinateBilinear_apply x.space v w

theorem norm_sq_div_le_riemannianMetric_inner_self (x : Hyperboloid E) (v : TangentSpace 𝓘(ℝ, E) x) :
    ‖NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x v)‖ ^ 2 / (1 + ‖x.space‖ ^ 2) ≤
      riemannianMetric.inner x v v := by
  rw [mfderiv_spaceDiffeomorph]
  exact coordinateBilinear_lower x.space v

end DifferentialGeometry.Hyperboloid
