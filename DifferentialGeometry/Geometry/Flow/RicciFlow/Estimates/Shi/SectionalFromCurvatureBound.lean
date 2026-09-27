import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceCutoff
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
  [SigmaCompactSpace M] [T2Space M]

section Algebra

private theorem isAlgCurvForm_sub_smul_self {V : Type*} [AddCommGroup V]
    [Module Real V] {B : V → V → V → V → Real} (hB : IsAlgCurvForm B)
    (v w : V) (c : Real) :
    B v (w - c • v) (w - c • v) v = B v w w v := by
  have hsmul2 : ∀ (a : Real) (X Y Z W : V), B X (a • Y) Z W = a * B X Y Z W := by
    intro a X Y Z W
    rw [hB.anti_first X (a • Y), hB.smul_left, hB.anti_first Y X]
    ring
  have hsmul3 : ∀ (a : Real) (X Y Z W : V), B X Y (a • Z) W = a * B X Y Z W := by
    intro a X Y Z W
    rw [hB.pair_swap X Y (a • Z) W, hB.smul_left, hB.pair_swap Z W X Y]
  have hd1 : ∀ X Z W : V, B X X Z W = 0 := by
    intro X Z W
    have h := hB.anti_first X X Z W
    linarith
  have hd2 : ∀ X Y Z : V, B X Y Z Z = 0 := by
    intro X Y Z
    have h := hB.anti_last X Y Z Z
    linarith
  have hrw : w - c • v = w + (-c) • v := by
    rw [neg_smul, ← sub_eq_add_neg]
  calc B v (w - c • v) (w - c • v) v
      = B v (w + (-c) • v) (w + (-c) • v) v := by rw [hrw]
    _ = B v w (w + (-c) • v) v + B v ((-c) • v) (w + (-c) • v) v :=
        hB.add_two v w ((-c) • v) (w + (-c) • v) v
    _ = B v w (w + (-c) • v) v + (-c) * B v v (w + (-c) • v) v := by
        rw [hsmul2]
    _ = B v w (w + (-c) • v) v := by rw [hd1]; ring
    _ = B v w w v + B v w ((-c) • v) v :=
        hB.add_three v w w ((-c) • v) v
    _ = B v w w v + (-c) * B v w v v := by rw [hsmul3]
    _ = B v w w v := by rw [hd2]; ring

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricRm04StandardAt_sub_smul_self
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) (c : Real) :
    metricRm04StandardAt (I := I) (M := M) g x v (w - c • v) (w - c • v) v =
      metricRm04StandardAt (I := I) (M := M) g x v w w v :=
  isAlgCurvForm_sub_smul_self
    (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (M := M) g x))
    v w c

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 2 M]
  [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem abs_metricRm04StandardAt_le
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |metricRm04StandardAt (I := I) (M := M) g x v w w v| ≤
      Real.sqrt (normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) *
        (g.inner x v v * g.inner x w w) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hvv : 0 ≤ g.inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg
      (I := I) (M := M) g x v
  have hww : 0 ≤ g.inner x w w :=
    DifferentialGeometry.metric_inner_self_nonneg
      (I := I) (M := M) g x w
  have hprod :
      (∏ a : Fin 4, Real.sqrt (g.inner x
          ((vec4 (I := I) v w w v) a) ((vec4 (I := I) v w w v) a))) =
        g.inner x v v * g.inner x w w := by
    rw [Fin.prod_univ_four]
    change Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
        Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v) =
      g.inner x v v * g.inner x w w
    calc Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
          Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v)
        = Real.sqrt (g.inner x v v) ^ 2 * Real.sqrt (g.inner x w w) ^ 2 := by ring
      _ = g.inner x v v * g.inner x w w := by
          rw [Real.sq_sqrt hvv, Real.sq_sqrt hww]
  have hCS := abs_apply_le_sqrt_normSq0S (I := I) g x 4 basis hON
    (metricRm04At (I := I) (M := M) g x) (vec4 (I := I) v w w v)
  rw [hprod] at hCS
  exact hCS

end Algebra

section Sectional

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le
    (g : SmoothRiemannianMetric I M) (y : M) {C : Real}
    (hC : normSq0S (I := I) g y 4 (metricRm04At (I := I) (M := M) g y) ≤ C) :
    SectionalBoundedBelowAt (I := I) g y (-Real.sqrt C) := by
  classical
  intro v w
  set N : Real :=
    Real.sqrt (normSq0S (I := I) g y 4 (metricRm04At (I := I) (M := M) g y)) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hNC : N ≤ Real.sqrt C := Real.sqrt_le_sqrt hC
  have harea : 0 ≤ g.inner y v v * g.inner y w w - g.inner y v w ^ 2 := by
    have hcs := DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
      (I := I) (M := M) g y v w
    linarith
  have hvv : 0 ≤ g.inner y v v :=
    DifferentialGeometry.metric_inner_self_nonneg
      (I := I) (M := M) g y v
  rcases eq_or_lt_of_le hvv with hv0 | hvpos
  · have hv : v = 0 := by
      by_contra hne
      exact absurd (g.pos y v hne) (by rw [← hv0]; exact lt_irrefl 0)
    have hzero : metricRm04StandardAt (I := I) (M := M) g y v w w v = 0 := by
      have h : (metricRm04At (I := I) (M := M) g y) (vec4 (I := I) v w w v) = 0 :=
        ContinuousMultilinearMap.map_coord_zero _ 0 (by simp [vec4, hv])
      exact h
    rw [hzero, ← hv0]
    have hvw : g.inner y v w = 0 := by rw [hv]; simp
    rw [hvw]
    simp
  · set c : Real := g.inner y v w / g.inner y v v with hc
    set u : TangentSpace I y := w - c • v with hu
    have huu : g.inner y u u =
        g.inner y w w - g.inner y v w ^ 2 / g.inner y v v := by
      have hexp : g.inner y u u =
          g.inner y w w - 2 * c * g.inner y v w + c ^ 2 * g.inner y v v := by
        rw [hu]
        simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
        rw [g.symm y v w]
        ring
      rw [hexp, hc]
      field_simp
      ring
    have hprod : g.inner y v v * g.inner y u u =
        g.inner y v v * g.inner y w w - g.inner y v w ^ 2 := by
      rw [huu]
      field_simp
    have hkey := abs_metricRm04StandardAt_le (I := I) g y v u
    rw [metricRm04StandardAt_sub_smul_self (I := I) g y v w c] at hkey
    rw [hprod] at hkey
    have hlow : -(N * (g.inner y v v * g.inner y w w - g.inner y v w ^ 2)) ≤
        metricRm04StandardAt (I := I) (M := M) g y v w w v :=
      neg_le_of_abs_le hkey
    have hmul : N * (g.inner y v v * g.inner y w w - g.inner y v w ^ 2) ≤
        Real.sqrt C * (g.inner y v v * g.inner y w w - g.inner y v w ^ 2) :=
      mul_le_mul_of_nonneg_right hNC harea
    have hgoal : -Real.sqrt C *
        (g.inner y v v * g.inner y w w - g.inner y v w ^ 2) ≤
        -(N * (g.inner y v v * g.inner y w w - g.inner y v w ^ 2)) := by
      linarith
    exact le_trans hgoal hlow

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem sectionalBoundedBelowAt_of_curvature_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {K : Real} (hK : 0 ≤ K) (y : M)
    (hcurv : nablaKRm04NormSqIntrinsic (I := I) S 0 0 y ≤ K ^ 2) :
    SectionalBoundedBelowAt (I := I) (S.base.metric 0) y (-K) := by
  have hnorm : normSq0S (I := I) (S.base.metric 0) y 4
      (metricRm04At (I := I) (M := M) (S.base.metric 0) y) ≤ K ^ 2 := by
    have h : normSq0S (I := I) (S.base.metric 0) y 4 (S.base.rm04 0 y) ≤ K ^ 2 := by
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
        Nat.add_zero] using hcurv
    simpa only [SolutionFamily.rm04, metricRm04_apply] using h
  have h := sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le
    (I := I) (S.base.metric 0) y hnorm
  rwa [Real.sqrt_sq hK] at h

end Sectional

end DifferentialGeometry.PDE.RicciFlow

end
