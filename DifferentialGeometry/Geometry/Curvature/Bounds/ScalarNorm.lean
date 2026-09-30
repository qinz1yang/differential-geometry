import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem scalar_abs_le_rm (g : SmoothRiemannianMetric I M) (x : M) :
    |metricScalarAt (I := I) (M := M) g x| ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have htrace : metricScalarAt (I := I) (M := M) g x =
      ∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricScalarAt_def (I := I) g x,
      metricTracePair0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x))))
        hinv (metricRicciAt (I := I) (M := M) g x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp only [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      have hij : i ≠ j := fun hij => hji hij.symm
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hij, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [htrace]
  calc
    |∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (basis i) (basis i))| ≤
        ∑ i, |metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (basis i) (basis i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        (Module.finrank ℝ (TangentSpace I x) : ℝ) *
          Real.sqrt (normSq0S (I := I) g x 4
            (metricRm04At (I := I) (M := M) g x)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Fintype.card_fin] using
        metricRicciComp_le (I := I) (M := M) g basis hON i i
    _ = (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

omit [SigmaCompactSpace M] in
theorem metricScalarAt_eq_zero_of_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (hE : Module.finrank ℝ E = 0) (x : M) :
    metricScalarAt (I := I) g x = 0 := by
  have h := scalar_abs_le_rm g x
  change |metricScalarAt (I := I) g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * _ at h
  simpa only [hE, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, abs_nonpos_iff] using h

omit [SigmaCompactSpace M] in
theorem sq_mul_scalar_abs_le_of_rm_bound
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ}
    (hbound : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    r ^ 2 * |metricScalarAt g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by
  have hsq : (r ^ 2 * Real.sqrt (normSq0S g x 4 (metricRm04At g x))) ^ 2 ≤ 1 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt (normSq0S_nonneg _ _ _ _)]
    exact hbound
  have hnorm : r ^ 2 * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ 1 := by
    nlinarith
  have hscalar := scalar_abs_le_rm g x
  change |metricScalarAt g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 * _ at hscalar
  have hscaled := mul_le_mul_of_nonneg_right hscalar (sq_nonneg r)
  have hdim := mul_le_mul_of_nonneg_left hnorm (sq_nonneg (Module.finrank ℝ E : ℝ))
  nlinarith

omit [SigmaCompactSpace M] in
theorem scalar_abs_le_div_sq_of_rm_bound
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ} (hr : r ≠ 0)
    (hbound : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    |metricScalarAt g x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 / r ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_ne_zero hr)).mpr
  simpa only [mul_comm] using sq_mul_scalar_abs_le_of_rm_bound g x hbound

end DifferentialGeometry.Geometry.Curvature

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance nonnegativeScalarNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem sqrt_metricRm_normSq_le_finrank_sq_mul_scalar
    (g : SmoothRiemannianMetric I M) (x : M)
    (hoperator : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * metricScalarAt (I := I) g x := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  let Rm : Tensor04At (I := I) (M := M) x := metricRm04At (I := I) g x
  let R : ℝ := metricScalarAt (I := I) g x
  have hR : 0 ≤ R := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative g x hoperator
  have hOp := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (I := I) g x).mp hoperator
  let curvature := metricCurvatureSections (I := I) g
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) g x) (metricRm04 (I := I) g x) :=
    rm04LowersRm13At_of_realizes (I := I) g (metricCov (I := I) g)
      (metricRm13 (I := I) g) (metricRm04 (I := I) g)
      curvature.rm13Realizes curvature.rm04Realizes x
  have hTrace (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
      metricRicciAt (I := I) g x (vec2 (basis i) (basis j)) =
        ∑ a, Rm (vec4 (basis a) (basis i) (basis j) (basis a)) := by
    simpa only [Rm, metricRicci_apply, metricRm04_apply] using
      ricci_diag_eq_sum_rm04_diag_of_orthonormal
      (I := I) g basis (metricRicci (I := I) g) (metricRm13 (I := I) g)
        (metricRm04 (I := I) g) curvature.ricciRealizes hLower hON i j
  have hsec (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
      0 ≤ Rm (vec4 (basis i) (basis j) (basis j) (basis i)) := by
    simpa [metricRm04StandardAt_apply, Rm, vec4] using
      hOp 1 (fun _ => 1) (fun _ => basis i) (fun _ => basis j)
  have hdiag (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
      Rm (vec4 (basis i) (basis j) (basis j) (basis i)) ≤ R := by
    have hrow : Rm (vec4 (basis i) (basis j) (basis j) (basis i)) ≤
        metricRicciAt (I := I) g x (vec2 (basis j) (basis j)) := by
      rw [hTrace j j]
      exact Finset.single_le_sum (fun k _ => hsec k j) (Finset.mem_univ i)
    have hupper := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      g x hoperator (basis j)
    rw [hON j j, ite_eq_left rfl, mul_one] at hupper
    change metricRicciAt (I := I) g x (vec2 (basis j) (basis j)) ≤ R / 2 at hupper
    linarith
  have hsym := mem_algebraicCurvatureTensorSubmodule.mp
    (metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x)
  have hcomponents (i j k l : Fin (Module.finrank ℝ (TangentSpace I x))) :
      |Rm (vec4 (basis i) (basis j) (basis k) (basis l))| ≤ R := by
    have hlast : Rm (vec4 (basis i) (basis j) (basis l) (basis k)) =
        -Rm (vec4 (basis i) (basis j) (basis k) (basis l)) := by
      simpa only [Rm, tensor04StandardAt, vec4] using
        hsym.anti_last (basis i) (basis j) (basis l) (basis k)
    have hcross : Rm (vec4 (basis k) (basis l) (basis j) (basis i)) =
        -Rm (vec4 (basis i) (basis j) (basis k) (basis l)) := by
      calc
        _ = Rm (vec4 (basis j) (basis i) (basis k) (basis l)) := by
          simpa only [Rm, tensor04StandardAt, vec4] using
            hsym.pair_swap (basis k) (basis l) (basis j) (basis i)
        _ = _ := by
          simpa only [Rm, tensor04StandardAt, vec4] using
            hsym.anti_first (basis j) (basis i) (basis k) (basis l)
    have hplus : 0 ≤
        (Rm (vec4 (basis i) (basis j) (basis j) (basis i)) +
          Rm (vec4 (basis i) (basis j) (basis l) (basis k))) +
        (Rm (vec4 (basis k) (basis l) (basis j) (basis i)) +
          Rm (vec4 (basis k) (basis l) (basis l) (basis k))) := by
      simpa [Fin.sum_univ_two, metricRm04StandardAt_apply, Rm, vec4] using
        hOp 2 ![1, 1] ![basis i, basis k] ![basis j, basis l]
    have hminus : 0 ≤
        (Rm (vec4 (basis i) (basis j) (basis j) (basis i)) -
          Rm (vec4 (basis i) (basis j) (basis l) (basis k))) +
        (-Rm (vec4 (basis k) (basis l) (basis j) (basis i)) +
          Rm (vec4 (basis k) (basis l) (basis l) (basis k))) := by
      simpa [Fin.sum_univ_two, metricRm04StandardAt_apply, Rm, vec4, sub_eq_add_neg] using
        hOp 2 ![1, -1] ![basis i, basis k] ![basis j, basis l]
    rw [hlast, hcross] at hplus hminus
    exact abs_le.mpr ⟨by linarith [hdiag i j, hdiag k l],
      by linarith [hdiag i j, hdiag k l]⟩
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hnorm : normSq0S (I := I) g x 4 Rm ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * R) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 4 basis hinv]
    calc
      _ ≤ ∑ _a : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x)), R ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        have hcomp : component0S (I := I) basis Rm a =
            Rm (vec4 (basis (a 0)) (basis (a 1)) (basis (a 2)) (basis (a 3))) := by
          rw [component0S_apply]
          congr 1
          funext b
          fin_cases b <;> simp [vec4]
        rw [hcomp]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr
          (hcomponents (a 0) (a 1) (a 2) (a 3))
      _ = ((Module.finrank ℝ E : ℝ) ^ 2 * R) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        change (Module.finrank ℝ E : ℝ) ^ 4 * R ^ 2 = _
        ring
  exact (Real.sqrt_le_left (mul_nonneg (sq_nonneg _) hR)).mpr hnorm

end DifferentialGeometry.Geometry.Curvature

end
