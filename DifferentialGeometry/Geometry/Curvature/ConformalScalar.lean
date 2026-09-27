import DifferentialGeometry.Geometry.Curvature.Conformal
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Bundle DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
private theorem metricRm04StandardAt_smul_four
    (g : SmoothRiemannianMetric I M) (x : M) (t : ℝ) (u v : TangentSpace I x) :
    metricRm04StandardAt g x (t • u) (t • v) (t • v) (t • u) =
      t ^ 4 * metricRm04StandardAt g x u v v u := by
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedSpace
  rw [rm04_eq_inner_riem, rm04_eq_inner_riem]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem scalar_conformal_frame_trace
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    metricScalarAt (conformalMetricOfContDiff g F hF) x = Real.exp (-(4 * F x)) *
      ∑ i, ∑ j, metricRm04StandardAt (conformalMetricOfContDiff g F hF) x (B j) (B i) (B i) (B j) := by
  let S := fun i => Real.exp (-F x) • B i
  have hc : Real.exp (2 * F x) * Real.exp (-F x) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hS : ∀ i j, (conformalMetricOfContDiff g F hF).inner x (S i) (S j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    dsimp only [S]
    rw [conformalMetricOfContDiff_inner]
    simp only [map_smul, smul_apply, smul_eq_mul, hB]
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte, mul_one]
      nlinarith [hc]
    · simp only [hij, ↓reduceIte, mul_zero]
  rw [metricScalarAt_eq_sum_metricRm04StandardAt _ x S hS]
  simp only [S, metricRm04StandardAt_smul_four, ← Finset.mul_sum]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem sum_conformal_correction (n : ℕ) (H : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ) (Q : ℝ) (hQ : ∑ i, d i ^ 2 = Q) :
    (∑ i, ∑ j, (-H j j - H i i + 2 * H j i * (if j = i then 1 else 0) +
      d j ^ 2 + d i ^ 2 - 2 * d j * d i * (if j = i then 1 else 0) -
      Q * (1 - (if j = i then (1 : ℝ) else 0) ^ 2))) =
      -2 * (n - 1 : ℝ) * (∑ i, H i i) - (n - 1 : ℝ) * (n - 2 : ℝ) * Q := by
  classical
  have hdiag : (∑ i : Fin n, ∑ j : Fin n, (1 - if j = i then (1 : ℝ) else 0)) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hd : (∑ i : Fin n, 2 * d i * d i) = 2 * Q := by
    calc
      _ = ∑ i : Fin n, 2 * d i ^ 2 := Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [← Finset.mul_sum, hQ]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    mul_ite, mul_one, mul_zero, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [← Finset.mul_sum, hQ]
  rw [hdiag, hd]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem metricScalarAt_conformalMetric
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : M) :
    metricScalarAt (conformalMetricOfContDiff g F hF) x = Real.exp (-(2 * F x)) *
      (metricScalarAt g x - 2 * ((Module.finrank ℝ E : ℝ) - 1) *
        laplacian (LeviCivita g) g F x -
        ((Module.finrank ℝ E : ℝ) - 1) * ((Module.finrank ℝ E : ℝ) - 2) *
          g.inner x (gradFun g F x) (gradFun g F x)) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g x
  let H := fun i j => hessFun g F x (B i) (B j)
  let d := fun i => mvfderiv I F x (B i)
  let Q := g.inner x (gradFun g F x) (gradFun g F x)
  let C := fun i j => -H j j - H i i + 2 * H j i * (if j = i then 1 else 0) +
    d j ^ 2 + d i ^ 2 - 2 * d j * d i * (if j = i then 1 else 0) -
    Q * (1 - (if j = i then (1 : ℝ) else 0) ^ 2)
  have hQ : ∑ i, d i ^ 2 = Q := (inner_gradFun_self_eq_sum_sq g F x B hB).symm
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      metricRm04StandardAt (conformalMetricOfContDiff g F hF) x (B j) (B i) (B i) (B j) =
        Real.exp (2 * F x) * (metricRm04StandardAt g x (B j) (B i) (B i) (B j) + C i j) := by
    rw [metricRm04StdAt_conformalMetric_plane]
    simp only [hB, ↓reduceIte, mul_one]
    dsimp only [C, H, d, Q]
    ring
  have hsum : (∑ i, ∑ j, C i j) =
      -2 * ((Module.finrank ℝ E : ℝ) - 1) * laplacian (LeviCivita g) g F x -
      ((Module.finrank ℝ E : ℝ) - 1) * ((Module.finrank ℝ E : ℝ) - 2) * Q := by
    have hh := sum_conformal_correction (Module.finrank ℝ E) H d Q hQ
    change (∑ i, ∑ j, C i j) = _ at hh
    rw [show (∑ i, H i i) = laplacian (LeviCivita g) g F x from
      (laplacian_eq_sum_hessFun g F hF x B hB).symm] at hh
    exact hh
  rw [scalar_conformal_frame_trace g F hF x B hB]
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [← metricScalarAt_eq_sum_metricRm04StandardAt g x B hB, hsum, ← mul_assoc, ← Real.exp_add]
  have he : -(4 * F x) + 2 * F x = -(2 * F x) := by ring
  rw [he]
  dsimp only [Q]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem metricScalarAt_conformalMetric_three
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (hdim : Module.finrank ℝ E = 3) (x : M) :
    metricScalarAt (conformalMetricOfContDiff g F hF) x = Real.exp (-(2 * F x)) *
      (metricScalarAt g x - 4 * ΔG g ⟨F, hF⟩ x -
        2 * g.inner x (gradFun g F x) (gradFun g F x)) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  rw [← laplacian_levi_eq g hF x]
  simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 from by norm_num,
    show (3 : ℝ) - 2 = 1 from by norm_num, mul_one, show (2 : ℝ) * 2 = 4 from by norm_num] using
      metricScalarAt_conformalMetric g F hF x

end DifferentialGeometry.Geometry.Curvature
