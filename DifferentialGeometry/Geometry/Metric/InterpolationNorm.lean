import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Metric.Conformal.Basic
import DifferentialGeometry.Tensor.Metric.CompactBounds
import DifferentialGeometry.Tensor.Metric.ScaleNorm
import DifferentialGeometry.Geometry.Metric.Construction.ConvexCombination
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem metricTensorField_conformal_convexComb_sub
    (g₀ h : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) :
    metricTensorField (conformalMetricOfContDiff (h.convexComb (scaleMetric η hη g₀) χ hχ hχ01) F hF) -
      metricTensorField (conformalMetricOfContDiff g₀ F hF) =
    tensor0SFieldSmulByFun ∞ (fun x => Real.exp (2 * F x) * χ x)
      ((Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hF)).mul hχ)
      (metricTensorField h - metricTensorField g₀) +
    (η - 1) • tensor0SFieldSmulByFun ∞ (fun x => Real.exp (2 * F x) * (1 - χ x))
      ((Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hF)).mul
        (contMDiff_const.sub hχ)) (metricTensorField g₀) := by
  apply DFunLike.ext
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  change metricTensorField
      (conformalMetricOfContDiff (h.convexComb (scaleMetric η hη g₀) χ hχ hχ01) F hF) x v -
    metricTensorField (conformalMetricOfContDiff g₀ F hF) x v =
    (Real.exp (2 * F x) * χ x) * (metricTensorField h x v - metricTensorField g₀ x v) +
      (η - 1) * ((Real.exp (2 * F x) * (1 - χ x)) * metricTensorField g₀ x v)
  rw [metricTensorField_apply, metricTensorField_apply, metricTensorField_apply,
    metricTensorField_apply, conformalMetricOfContDiff_inner, conformalMetricOfContDiff_inner,
    convexComb_inner, scaleMetric_inner]
  simp only [smul_eq_mul]
  ring

variable [T2Space M]

private theorem exists_all_orders_bound (R : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (I := I) (M := M) ∞ r) (k : ℕ) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ k, ∀ x ∈ K,
      Real.sqrt (normSq0S R x (r + j) (iterCov R r T j x)) ≤ C := by
  classical
  have hb := fun j => DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_on_compact R T j hK
  choose C hCpos hC using hb
  have hn : (Finset.range (k + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
  refine ⟨(Finset.range (k + 1)).sup' hn C,
    (hCpos 0).trans_le (Finset.le_sup' C (Finset.mem_range.mpr (Nat.zero_lt_succ k))), ?_⟩
  intro j hj x hx
  exact (hC j x hx).trans (Finset.le_sup' C (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

private theorem exists_weight_bound (R : SmoothRiemannianMetric I M)
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (k : ℕ) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (T : Tensor0SField (I := I) (M := M) ∞ r)
      (ε : ℝ), 0 ≤ ε →
      (∀ j ≤ k, ∀ x ∈ K, Real.sqrt (normSq0S R x (r + j) (iterCov R r T j x)) ≤ ε) →
      ∀ j ≤ k, ∀ x ∈ K,
        Real.sqrt (normSq0S R x (r + j)
          (iterCov R r (tensor0SFieldSmulByFun ∞ φ hφ T) j x)) ≤ C * ε := by
  obtain ⟨Cφ, hCφpos, hCφ⟩ := exists_all_orders_bound R
    (Tensor0SField.fromScalarField ∞ φ hφ) k hK
  refine ⟨2 ^ k * Cφ, mul_pos (by positivity) hCφpos, ?_⟩
  intro r T ε hε hT j hj x hx
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis R x
  have hinv : MetricInverseInBasis R x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have hb := metricInverseInBasis_of_orthonormal R basis hON
    intro i l
    simpa [identityInvMetric, diagonalInvMetric] using hb i l
  refine (iterCov_smulF_le R x basis hinv j φ hφ T).trans ?_
  calc
    _ ≤ ∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) * Cφ * ε := by
      apply Finset.sum_le_sum
      intro c hc
      have hck : c ≤ k := (Nat.le_of_lt_succ (Finset.mem_range.mp hc)).trans hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hCφ c hck x hx) (Nat.cast_nonneg _))
        (hT (j - c) ((Nat.sub_le j c).trans hj) x hx)
        (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hCφpos.le)
    _ = (2 : ℝ) ^ j * Cφ * ε := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ k * Cφ * ε := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hj) hCφpos.le) hε

theorem exists_metricDerivENormSupOn_conformal_convexComb_bound
    (g₀ R : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {K : Set M} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : SmoothRiemannianMetric I M) (η : ℝ) (hη : 0 < η),
      metricDerivENormSupOn K k
        (conformalMetricOfContDiff (h.convexComb (scaleMetric η hη g₀) χ hχ hχ01) F hF)
        (conformalMetricOfContDiff g₀ F hF) R ≤
      ENNReal.ofReal C * (metricDerivENormSupOn K k h g₀ R + ENNReal.ofReal |η - 1|) := by
  let φ : M → ℝ := fun x => Real.exp (2 * F x) * χ x
  have hφ : ContMDiff I 𝓘(ℝ) ∞ φ :=
    (Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hF)).mul hχ
  let ψ : M → ℝ := fun x => Real.exp (2 * F x) * (1 - χ x)
  have hψ : ContMDiff I 𝓘(ℝ) ∞ ψ :=
    (Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hF)).mul (contMDiff_const.sub hχ)
  let Tψ := tensor0SFieldSmulByFun ∞ ψ hψ (metricTensorField g₀)
  obtain ⟨Cφ, hCφpos, hCφ⟩ := exists_weight_bound R φ hφ k hK
  obtain ⟨Cψ, hCψpos, hCψ⟩ := exists_all_orders_bound R Tψ k hK
  refine ⟨max Cφ Cψ, hCφpos.trans_le (le_max_left _ _), ?_⟩
  intro h η hη
  let N := metricDerivENormSupOn K k h g₀ R
  have hN : N ≠ ⊤ := by
    rw [show N = metricDerivENormSupOn K k h g₀ R from rfl,
      metricDerivENormSupOn_eq_ofReal_of_isCompact hK]
    exact ENNReal.ofReal_ne_top
  have hT : ∀ j ≤ k, ∀ x ∈ K,
      Real.sqrt (normSq0S R x (2 + j)
        (iterCov R 2 (metricTensorField h - metricTensorField g₀) j x)) ≤ N.toReal := by
    intro j hj x hx
    obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis R x
    have hinv : MetricInverseInBasis R x basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
      have hb := metricInverseInBasis_of_orthonormal R basis hON
      intro i l
      simpa [identityInvMetric, diagonalInvMetric] using hb i l
    rw [← metricDerivNorm_eq_iterCov h g₀ R j basis hinv]
    exact (ENNReal.ofReal_le_iff_le_toReal hN).mp
      (ofReal_metricDerivNorm_le_sup K k h g₀ R hj hx)
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x hx
  have hpoint : metricDerivNorm j
      (conformalMetricOfContDiff (h.convexComb (scaleMetric η hη g₀) χ hχ hχ01) F hF)
      (conformalMetricOfContDiff g₀ F hF) R x ≤ max Cφ Cψ * (N.toReal + |η - 1|) := by
    obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis R x
    have hinv : MetricInverseInBasis R x basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
      have hb := metricInverseInBasis_of_orthonormal R basis hON
      intro i l
      simpa [identityInvMetric, diagonalInvMetric] using hb i l
    rw [metricDerivNorm_eq_iterCov _ _ R j basis hinv,
      metricTensorField_conformal_convexComb_sub, iterCov_add,
      DifferentialGeometry.Geometry.Tensor.iterCov_smul]
    change Real.sqrt (normSq0S R x (2 + j)
      (iterCov R 2 (tensor0SFieldSmulByFun ∞ φ hφ
          (metricTensorField h - metricTensorField g₀)) j x +
        (η - 1) • iterCov R 2 Tψ j x)) ≤ _
    calc
      _ ≤ Real.sqrt (normSq0S R x (2 + j)
          (iterCov R 2 (tensor0SFieldSmulByFun ∞ φ hφ
            (metricTensorField h - metricTensorField g₀)) j x)) +
          Real.sqrt (normSq0S R x (2 + j) ((η - 1) • iterCov R 2 Tψ j x)) :=
        sqrt_normSq0S_add_le R _ _ basis hinv
      _ ≤ Cφ * N.toReal + |η - 1| * Cψ := by
        rw [sqrt_normSq0S_smul]
        exact add_le_add
          (hCφ 2 (metricTensorField h - metricTensorField g₀) N.toReal
            ENNReal.toReal_nonneg hT j hj x hx)
          (mul_le_mul_of_nonneg_left (hCψ j hj x hx) (abs_nonneg _))
      _ ≤ max Cφ Cψ * N.toReal + max Cφ Cψ * |η - 1| := by
        exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
          (by simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left (le_max_right Cφ Cψ) (abs_nonneg (η - 1)))
      _ = _ := by ring
  calc
    ENNReal.ofReal _ ≤ ENNReal.ofReal (max Cφ Cψ * (N.toReal + |η - 1|)) :=
      ENNReal.ofReal_le_ofReal hpoint
    _ = ENNReal.ofReal (max Cφ Cψ) * (N + ENNReal.ofReal |η - 1|) := by
      rw [ENNReal.ofReal_mul (hCφpos.trans_le (le_max_left _ _)).le,
        ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _), ENNReal.ofReal_toReal hN]

end DifferentialGeometry.Geometry.Metric
