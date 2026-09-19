import DifferentialGeometry.Topology.Manifold.SublevelCutoff
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private theorem mvfderiv_sublevelCutoff (ρ : C^∞⟮I, M; ℝ⟯) (R : ℝ)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (sublevelCutoff ρ R) x v =
      deriv CutoffProfile.value (ρ x / R) / R * mvfderiv I ρ x v := by
  let φ : ℝ → ℝ := fun s => CutoffProfile.value (s / R)
  have hφ : HasDerivAt φ (deriv CutoffProfile.value (ρ x / R) / R) (ρ x) := by
    simpa only [φ, Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using!
      ((CutoffProfile.contDiff.differentiable (by simp) (ρ x / R)).hasDerivAt.comp
        (ρ x) ((hasDerivAt_id (ρ x)).div_const R))
  have hchain := mvfderiv_comp_apply (I := 𝓘(ℝ)) (I' := I)
    (f := ρ) (g := φ) x hφ.differentiableAt.mdifferentiableAt
      (ρ.contMDiff.mdifferentiableAt (by simp)) v
  rw [mvfderiv_real_model_eq_fderiv, hφ.hasFDerivAt.fderiv,
    ← mvfderiv_real_eq_mfderiv I ρ x v] at hchain
  simpa only [sublevelCutoff, φ, Function.comp_def,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using! hchain

variable [IsManifold I ∞ M]

theorem abs_mvfderiv_sublevelCutoff_le (g : SmoothRiemannianMetric I M)
    (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R) {C : ℝ}
    (hρ : ∀ x, ∀ v : TangentSpace I x,
      |mvfderiv I ρ x v| ≤ C * Real.sqrt (g.inner x v v))
    (x : M) (v : TangentSpace I x) :
    |mvfderiv I (sublevelCutoff ρ R) x v| ≤
      (CutoffProfile.derivBound * C / R) * Real.sqrt (g.inner x v v) := by
  rw [mvfderiv_sublevelCutoff, abs_mul, abs_div, abs_of_pos hR]
  calc
    |deriv CutoffProfile.value (ρ x / R)| / R * |mvfderiv I ρ x v| ≤
        (CutoffProfile.derivBound / R) * |mvfderiv I ρ x v| :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (CutoffProfile.abs_deriv_le_derivBound _) hR.le)
        (abs_nonneg _)
    _ ≤ (CutoffProfile.derivBound / R) * (C * Real.sqrt (g.inner x v v)) :=
      mul_le_mul_of_nonneg_left (hρ x v)
        (div_nonneg CutoffProfile.derivBound_nonneg hR.le)
    _ = _ := by ring

variable [FiniteDimensional ℝ E]

theorem grad_norm_sublevelCutoff_le (g : SmoothRiemannianMetric I M)
    (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R) {C : ℝ} (hC : 0 ≤ C)
    (hρ : ∀ x, ∀ v : TangentSpace I x,
      |mvfderiv I ρ x v| ≤ C * Real.sqrt (g.inner x v v)) (x : M) :
    Real.sqrt (g.inner x (Geometry.Operator.gradFun g (sublevelCutoff ρ R) x)
      (Geometry.Operator.gradFun g (sublevelCutoff ρ R) x)) ≤
        CutoffProfile.derivBound * C / R := by
  apply grad_norm_le_of_mvfderiv_bound g
    (div_nonneg (mul_nonneg CutoffProfile.derivBound_nonneg hC) hR.le)
  exact abs_mvfderiv_sublevelCutoff_le g ρ hR hρ x

theorem tendsto_grad_norm_sublevelCutoff (g : SmoothRiemannianMetric I M)
    (ρ : C^∞⟮I, M; ℝ⟯) {C : ℝ} (hC : 0 ≤ C)
    (hρ : ∀ x, ∀ v : TangentSpace I x,
      |mvfderiv I ρ x v| ≤ C * Real.sqrt (g.inner x v v)) (x : M) :
    Tendsto (fun R : ℝ => Real.sqrt
      (g.inner x (Geometry.Operator.gradFun g (sublevelCutoff ρ R) x)
        (Geometry.Operator.gradFun g (sublevelCutoff ρ R) x))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => Real.sqrt_nonneg _) _
    (tendsto_id.const_div_atTop (CutoffProfile.derivBound * C))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact grad_norm_sublevelCutoff_le g ρ hR hC hρ x

end DifferentialGeometry.Analysis
