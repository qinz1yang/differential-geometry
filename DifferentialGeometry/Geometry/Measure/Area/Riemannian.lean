import DifferentialGeometry.Geometry.Measure.Area.TwoJacobian
import DifferentialGeometry.Geometry.Metric.Scaling










noncomputable section

open Bundle Manifold DifferentialGeometry
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def tangentTwoJacobian (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)

theorem tangentTwoJacobian_nonneg (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) : 0 ≤ tangentTwoJacobian g v w := Real.sqrt_nonneg _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tangentTwoJacobian_sq (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    tangentTwoJacobian g v w ^ 2 = g.inner x v v * g.inner x w w - g.inner x v w ^ 2 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact twoJacobian_sq v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tangentTwoJacobian_le (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) :
    tangentTwoJacobian g v w ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact (twoJacobian_le_norm_mul v w).trans_eq (by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]; rfl)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
@[simp] theorem tangentTwoJacobian_smul_self (g : SmoothRiemannianMetric I M) {x : M}
    (v : TangentSpace I x) (c : ℝ) : tangentTwoJacobian g v (c • v) = 0 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact twoJacobian_smul_self v c

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tangentTwoJacobian_of_conformal (g : SmoothRiemannianMetric I M) {x : M}
    {v w : TangentSpace I x} (horth : g.inner x v w = 0)
    (heq : g.inner x v v = g.inner x w w) : tangentTwoJacobian g v w = g.inner x v v := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  unfold tangentTwoJacobian
  rw [horth, zero_pow (by decide : 2 ≠ 0), sub_zero, ← heq]
  exact Real.sqrt_mul_self (@real_inner_self_nonneg (TangentSpace I x) _ _ v)


theorem tangentTwoJacobian_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) {x : M} (v w : TangentSpace I x) :
    tangentTwoJacobian (scaleMetric c hc g) v w = c * tangentTwoJacobian g v w := by
  unfold tangentTwoJacobian
  simp only [scaleMetric_inner]
  have h : (c * g.inner x v v) * (c * g.inner x w w) - (c * g.inner x v w) ^ 2 =
      c ^ 2 * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

section Comparison

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tangentTwoJacobian_le_of_combinations (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) {x : M} {y : N}
    {v w : TangentSpace I x} {v' w' : TangentSpace J y} {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ,
      Real.sqrt (h.inner y (a • v' + b • w') (a • v' + b • w')) ≤
        L * Real.sqrt (g.inner x (a • v + b • w) (a • v + b • w))) :
    tangentTwoJacobian h v' w' ≤ L ^ 2 * tangentTwoJacobian g v w := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  apply twoJacobian_le_of_norm_combinations_le (v := v) (w := w) (v' := v') (w' := w') hL
  intro a b
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  exact hbound a b

end Comparison

end DifferentialGeometry.Geometry
