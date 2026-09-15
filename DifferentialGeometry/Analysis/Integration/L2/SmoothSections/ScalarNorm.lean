import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Tensor.RSTensor.RankZero
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Integral.L2.SmoothCcTensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private theorem tensor_eval_scalar0
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
      (1 : ℝ))) Fin.elim0 = TensorRSField.scalar0 S.toSection x := by
  unfold TensorRSField.scalar0 TensorRSField.rs0
  simp only [toFun_apply, Tensor0SField.toScalarField]
  rfl

private theorem tensor_inner_scalar0
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) (x : M) :
    tensorInnerPointwise g 0 0 x (S.toFun x) (T.toFun x) =
      TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x := by
  unfold tensorInnerPointwise
  rw [tensorInnerPointwise_0s_zero_arity, lowerAllUpperIndices_apply,
    lowerAllUpperIndices_apply]
  have hS : (separableFormAt g x 0
        (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    apply ContinuousMultilinearMap.ext
    intro w
    rw [separableFormAt_apply]
    simp
  rw [hS]
  exact congrArg₂ (· * ·) (tensor_eval_scalar0 g S x) (tensor_eval_scalar0 g T x)

variable [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem inner_eq_integral_scalar0_mul
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) :
    inner ℝ S T = ∫ x, TensorRSField.scalar0 S.toSection x *
      TensorRSField.scalar0 T.toSection x ∂riemannianVolumeMeasure I M g := by
  rw [SmoothCcTensor.inner_def]
  unfold tensorL2Inner
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (tensor_inner_scalar0 g S T)

theorem memLp_scalar0 (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) (p : ℝ≥0∞) :
    MemLp (TensorRSField.scalar0 S.toSection) p
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let _ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  apply (TensorRSField.scalar0_smooth S.toSection).continuous.memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport
  intro x hx
  apply subset_tsupport S.toFun
  rw [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  unfold TensorRSField.scalar0 TensorRSField.rs0 Tensor0SField.toScalarField
  change (S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
    (1 : ℝ)) Fin.elim0 = 0
  rw [hzero]
  rfl

theorem norm_eq_scalar0_eLpNorm (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) :
    ‖S‖ = ENNReal.toReal (eLpNorm (TensorRSField.scalar0 S.toSection)
      2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let f := TensorRSField.scalar0 S.toSection
  have hf := memLp_scalar0 g S 2
  rw [← Lp.norm_toLp f hf]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  rw [inner_eq_integral_scalar0_mul, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx]
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, pow_two]

end DifferentialGeometry.Integral.L2.SmoothCcTensor
