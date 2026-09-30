import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normSq0S_one_le_iff (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) {C : ℝ} (hC : 0 ≤ C) :
    normSq0S (I := I) g x 1 α ≤ C ^ 2 ↔
      ∀ v : TangentSpace I x, |α (fun _ => v)| ≤ C * Real.sqrt (g.inner x v v) := by
  let v := cotangentSharp (I := I) g x α
  have hnorm : normSq0S (I := I) g x 1 α = g.inner x v v := rfl
  have hv : 0 ≤ g.inner x v v := metric_inner_self_nonneg g x v
  have heval (w : TangentSpace I x) : g.inner x v w = α (fun _ => w) :=
    cotangentSharp_inner g x α w
  rw [hnorm]
  constructor
  · intro h w
    rw [← heval]
    exact (SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic
      g x v w).trans
      (mul_le_mul_of_nonneg_right ((Real.sqrt_le_iff).mpr ⟨hC, h⟩) (Real.sqrt_nonneg _))
  · intro h
    have hs := h v
    rw [← heval, abs_of_nonneg hv] at hs
    have hroot : Real.sqrt (g.inner x v v) ≤ C := by
      nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg (g.inner x v v)]
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg (g.inner x v v)]

theorem normSq0S_one_le_of_metric_le (g h : SmoothRiemannianMetric I M) (x : M)
    {C : ℝ} (hC : 0 ≤ C)
    (hcomp : ∀ v : TangentSpace I x, g.inner x v v ≤ C * h.inner x v v)
    (α : Tensor0SSpace 1 I x) :
    normSq0S (I := I) h x 1 α ≤ C * normSq0S (I := I) g x 1 α := by
  have hα := normSq0S_nonneg g x 1 α
  have hbound := (normSq0S_one_le_iff g x α (Real.sqrt_nonneg _)).mp
    (le_of_eq (Real.sq_sqrt hα).symm)
  have hroot := (normSq0S_one_le_iff h x α
    (mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg _))).mpr
    (fun v => (hbound v).trans (by
      calc
        Real.sqrt (normSq0S g x 1 α) * Real.sqrt (g.inner x v v) ≤
            Real.sqrt (normSq0S g x 1 α) * Real.sqrt (C * h.inner x v v) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hcomp v)) (Real.sqrt_nonneg _)
        _ = (Real.sqrt C * Real.sqrt (normSq0S g x 1 α)) * Real.sqrt (h.inner x v v) := by
          rw [Real.sqrt_mul hC]; ring))
  simpa only [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hα] using hroot

end DifferentialGeometry.Tensor0SBundle
