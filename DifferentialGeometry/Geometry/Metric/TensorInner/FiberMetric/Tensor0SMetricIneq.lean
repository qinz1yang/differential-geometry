import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

set_option autoImplicit false

namespace Tensor0SBundle

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner0S_comm
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A :=
  (tensor0SMetricData (I := I) g x s).inner_comm A B

theorem inner0S_sub_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (B - C) =
      inner0S (I := I) g x s A B - inner0S (I := I) g x s A C := by
  rw [inner0S_comm (I := I) g x s A (B - C), inner0S_sub_left,
    inner0S_comm (I := I) g x s B A, inner0S_comm (I := I) g x s C A]

theorem inner0S_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat) (c : Real)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (c • A) B = c * inner0S (I := I) g x s A B := by
  unfold inner0S MetricFiberData.inner
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem inner0S_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat) (c : Real)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (c • B) = c * inner0S (I := I) g x s A B := by
  rw [inner0S_comm (I := I) g x s A (c • B), inner0S_smul_left,
    inner0S_comm (I := I) g x s B A]

theorem normSq0S_add
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A + B) =
      normSq0S (I := I) g x s A + 2 * inner0S (I := I) g x s A B +
        normSq0S (I := I) g x s B := by
  simp only [normSq0S_eq_inner, inner0S_add_left, inner0S_add_right]
  rw [inner0S_comm (I := I) g x s B A]
  ring

theorem normSq0S_sub
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A - B) =
      normSq0S (I := I) g x s A - 2 * inner0S (I := I) g x s A B +
        normSq0S (I := I) g x s B := by
  simp only [normSq0S_eq_inner, inner0S_sub_left, inner0S_sub_right]
  rw [inner0S_comm (I := I) g x s B A]
  ring

theorem normSq0S_neg
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (-A) = normSq0S (I := I) g x s A := by
  have h : (-A : Tensor0SSpace s I x) = (-1 : Real) • A := by
    rw [neg_one_smul]
  rw [h]
  simp only [normSq0S_eq_inner]
  rw [inner0S_smul_left, inner0S_smul_right]
  ring

theorem abs_inner0S_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    |inner0S (I := I) g x s A B| ≤
      Real.sqrt (normSq0S (I := I) g x s A) *
        Real.sqrt (normSq0S (I := I) g x s B) := by
  have hcs := Real.sqrt_le_sqrt (inner0S_sq_le_mul (I := I) g x s A B)
  rwa [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (normSq0S_nonneg (I := I) g x s A)] at hcs

theorem two_inner0S_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    2 * inner0S (I := I) g x s A B ≤
      normSq0S (I := I) g x s A + normSq0S (I := I) g x s B := by
  have h := normSq0S_nonneg (I := I) g x s (A - B)
  rw [normSq0S_sub] at h
  linarith

theorem neg_two_inner0S_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    -(normSq0S (I := I) g x s A + normSq0S (I := I) g x s B) ≤
      2 * inner0S (I := I) g x s A B := by
  have h := normSq0S_nonneg (I := I) g x s (A + B)
  rw [normSq0S_add] at h
  linarith

theorem normSq0S_add_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A + B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have h := two_inner0S_le (I := I) g x s A B
  rw [normSq0S_add]
  linarith

theorem normSq0S_sub_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A - B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have h := neg_two_inner0S_le (I := I) g x s A B
  rw [normSq0S_sub]
  linarith

theorem sqrt_normSq0S_add_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g x s (A + B)) ≤
      Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B) := by
  have hA := normSq0S_nonneg (I := I) g x s A
  have hB := normSq0S_nonneg (I := I) g x s B
  have hsA : Real.sqrt (normSq0S (I := I) g x s A) ^ 2 =
      normSq0S (I := I) g x s A := Real.sq_sqrt hA
  have hsB : Real.sqrt (normSq0S (I := I) g x s B) ^ 2 =
      normSq0S (I := I) g x s B := Real.sq_sqrt hB
  have hcs : inner0S (I := I) g x s A B ≤
      Real.sqrt (normSq0S (I := I) g x s A) *
        Real.sqrt (normSq0S (I := I) g x s B) :=
    le_trans (le_abs_self _) (abs_inner0S_le (I := I) g x s A B)
  have hexp : (Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B)) ^ 2 =
      normSq0S (I := I) g x s A +
        2 * (Real.sqrt (normSq0S (I := I) g x s A) *
          Real.sqrt (normSq0S (I := I) g x s B)) +
        normSq0S (I := I) g x s B := by
    rw [add_sq, hsA, hsB]; ring
  have key : normSq0S (I := I) g x s (A + B) ≤
      (Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B)) ^ 2 := by
    rw [normSq0S_add, hexp]
    linarith
  calc Real.sqrt (normSq0S (I := I) g x s (A + B))
      ≤ Real.sqrt ((Real.sqrt (normSq0S (I := I) g x s A) +
          Real.sqrt (normSq0S (I := I) g x s B)) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (normSq0S (I := I) g x s A) +
          Real.sqrt (normSq0S (I := I) g x s B) :=
        Real.sqrt_sq (by positivity)

theorem sqrt_normSq0S_sub_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g x s (A - B)) ≤
      Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B) := by
  rw [sub_eq_add_neg]
  refine le_trans (sqrt_normSq0S_add_le (I := I) g x s A (-B)) ?_
  rw [normSq0S_neg]

end

end Tensor0SBundle
