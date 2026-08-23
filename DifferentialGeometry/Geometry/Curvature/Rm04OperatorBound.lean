import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Metric.InnerExpansion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open scoped BigOperators Manifold ContDiff
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rm04_eq_inner
    (g : SmoothRiemannianMetric I M) (q : M)
    (J V W : TangentSpace I q) :
    metricRm04StdAt (I := I) (M := M) g q J V V W =
      g.inner q W
        (riemannOp (LeviCivita (I := I) g) q J V V) := by
  have hcov :=
    DifferentialGeometry.leviCivita_contMDiffCovariantDerivativeLocally
      (I := I) g
  rw [metricRm04StdAt_apply,
    DifferentialGeometry.metricRm04At_eq_riemannCurvature04At,
    CovariantDerivative.riemannCurvature04At_apply_const,
    DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
      (cov := LeviCivita (I := I) g) (hcov := hcov)]

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem rm04_slot_prod_le
    {Idx : Type*} [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {q : M}
    (basis : Module.Basis Idx Real (TangentSpace I q))
    (hON : forall i j : Idx,
      g.inner q (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (J V : TangentSpace I q) (i : Idx) :
    (∏ a : Fin 4, Real.sqrt (g.inner q
        ((vec4 (I := I) J V V (basis i)) a)
        ((vec4 (I := I) J V V (basis i)) a))) <=
      Real.sqrt (g.inner q J J) *
        (Real.sqrt (g.inner q V V)) ^ 2 := by
  have hunit : Real.sqrt (g.inner q (basis i) (basis i)) = 1 := by
    rw [hON i i]
    simp
  rw [Fin.prod_univ_four]
  simp [DifferentialGeometry.Geometry.Curvature.vec4, hunit, pow_two]
  ring_nf
  exact le_rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemann_quad_le
    {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {q : M}
    (basis : Module.Basis Idx Real (TangentSpace I q))
    (hON : ∀ i j : Idx,
      g.inner q (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    {K : Real}
    (hRm :
      Real.sqrt (normSq0S (I := I) g q 4
        (metricRm04At (I := I) (M := M) g q)) ≤ K)
    (J V : TangentSpace I q) :
    g.inner q
        (riemannOp (LeviCivita (I := I) g) q J V V) J ≤
      K * g.inner q J J * g.inner q V V := by
  letI := Fintype.ofFinite Idx
  have hJJ : 0 ≤ g.inner q J J :=
    by
      rcases eq_or_ne J 0 with hzero | hne
      · simp [hzero]
      · exact (g.pos q J hne).le
  have hVV : 0 ≤ g.inner q V V :=
    by
      rcases eq_or_ne V 0 with hzero | hne
      · simp [hzero]
      · exact (g.pos q V hne).le
  have hprod :
      (∏ a : Fin 4, Real.sqrt (g.inner q
          ((vec4 (I := I) J V V J) a)
          ((vec4 (I := I) J V V J) a))) =
        g.inner q J J * g.inner q V V := by
    rw [Fin.prod_univ_four]
    change
      Real.sqrt (g.inner q J J) * Real.sqrt (g.inner q V V) *
          Real.sqrt (g.inner q V V) * Real.sqrt (g.inner q J J) =
        g.inner q J J * g.inner q V V
    calc
      Real.sqrt (g.inner q J J) * Real.sqrt (g.inner q V V) *
          Real.sqrt (g.inner q V V) * Real.sqrt (g.inner q J J) =
          (Real.sqrt (g.inner q J J)) ^ 2 *
            (Real.sqrt (g.inner q V V)) ^ 2 := by ring
      _ = g.inner q J J * g.inner q V V := by
        rw [Real.sq_sqrt hJJ, Real.sq_sqrt hVV]
  have hCS := abs_apply_le_sqrt_normSq0S
    (I := I) g q 4 basis hON
    (metricRm04At (I := I) (M := M) g q)
    (vec4 (I := I) J V V J)
  rw [hprod] at hCS
  have habs :
      |g.inner q J
          (riemannOp (LeviCivita (I := I) g) q J V V)| ≤
        Real.sqrt (normSq0S (I := I) g q 4
          (metricRm04At (I := I) (M := M) g q)) *
            (g.inner q J J * g.inner q V V) := by
    rw [← rm04_eq_inner (I := I) g q J V J]
    simpa only [metricRm04StdAt_apply] using hCS
  calc
    g.inner q
        (riemannOp (LeviCivita (I := I) g) q J V V) J =
        g.inner q J
          (riemannOp (LeviCivita (I := I) g) q J V V) := g.symm _ _ _
    _ ≤ |g.inner q J
          (riemannOp (LeviCivita (I := I) g) q J V V)| := le_abs_self _
    _ ≤ Real.sqrt (normSq0S (I := I) g q 4
          (metricRm04At (I := I) (M := M) g q)) *
            (g.inner q J J * g.inner q V V) := habs
    _ ≤ K * (g.inner q J J * g.inner q V V) :=
      mul_le_mul_of_nonneg_right hRm (mul_nonneg hJJ hVV)
    _ = K * g.inner q J J * g.inner q V V := by ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannOp_sq_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    (g : SmoothRiemannianMetric I M) (q : M)
    (basis : Module.Basis Idx Real (TangentSpace I q))
    (hcard : Fintype.card Idx =
      Module.finrank Real (TangentSpace I q))
    (hON : forall i j : Idx,
      g.inner q (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (J V : TangentSpace I q) :
    g.inner q
        (riemannOp (LeviCivita (I := I) g) q J V V)
        (riemannOp (LeviCivita (I := I) g) q J V V) <=
      (Fintype.card Idx : Real) *
        (Real.sqrt (normSq0S (I := I) g q 4
            (metricRm04At (I := I) (M := M) g q)) *
          Real.sqrt (g.inner q J J) *
          (Real.sqrt (g.inner q V V)) ^ 2) ^ 2 := by
  classical
  let Rv : TangentSpace I q :=
    riemannOp (LeviCivita (I := I) g) q J V V
  let B : Real :=
    Real.sqrt (normSq0S (I := I) g q 4
      (metricRm04At (I := I) (M := M) g q)) *
      Real.sqrt (g.inner q J J) *
      (Real.sqrt (g.inner q V V)) ^ 2
  have hB : 0 <= B := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (sq_nonneg _)
  rw [DifferentialGeometry.Geometry.Riemannian.inner_self_eq_sum_sq
    (I := I) g q hcard basis hON Rv]
  calc
    (∑ i : Idx, (g.inner q (basis i) Rv) ^ 2) <=
        ∑ _i : Idx, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hCS := abs_apply_le_sqrt_normSq0S
        (I := I) g q 4 basis hON
        (metricRm04At (I := I) (M := M) g q)
        (vec4 (I := I) J V V (basis i))
      have hprod := rm04_slot_prod_le
        (I := I) g basis hON J V i
      have habs : |g.inner q (basis i) Rv| <= B := by
        rw [← rm04_eq_inner (I := I) g q J V (basis i)]
        calc
          |metricRm04StdAt (I := I) (M := M) g q J V V (basis i)| <=
              Real.sqrt (normSq0S (I := I) g q 4
                (metricRm04At (I := I) (M := M) g q)) *
                (∏ a : Fin 4, Real.sqrt (g.inner q
                  ((vec4 (I := I) J V V (basis i)) a)
                  ((vec4 (I := I) J V V (basis i)) a))) := by
            simpa [metricRm04StdAt_apply] using hCS
          _ <= B := by
            simpa only [B, mul_assoc] using
              mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg _)
      have hsquare :
          |g.inner q (basis i) Rv| ^ 2 <= B ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hB).2 habs
      simpa [sq_abs] using hsquare
    _ = (Fintype.card Idx : Real) * B ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card Idx : Real) *
        (Real.sqrt (normSq0S (I := I) g q 4
            (metricRm04At (I := I) (M := M) g q)) *
          Real.sqrt (g.inner q J J) *
          (Real.sqrt (g.inner q V V)) ^ 2) ^ 2 := rfl

end Connection
end Integral
end DifferentialGeometry
