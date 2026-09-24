import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricCovDeriv_scaleMetric_left (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (m : ℕ) :
    metricCovDeriv (scaleMetric c hc g) gRef m = c • metricCovDeriv g gRef m := by
  have hfield : metricTensorField (scaleMetric c hc g) = c • metricTensorField g := by
    ext x v
    simp [metricTensorField_apply, scaleMetric_inner, smul_eq_mul]
  rw [metricCovDeriv_eq_covDerivOfField, hfield, covDerivOfField_smul,
    ← metricCovDeriv_eq_covDerivOfField]

theorem metricCovDerivNorm_self_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricCovDerivNorm 0 g g x = Real.sqrt (Module.finrank ℝ E : ℝ) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g x
  have hinv : MetricInverseInBasis g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hcard := normSq0S_metricTensor0S_eq_card g basis _ hinv
  have hfield : metricTensorField g x = metricTensor0S g x := by
    ext v
    rw [metricTensorField_apply, metricTensor0S_apply]
  change Real.sqrt (normSq0S g x 2 (metricTensorField g x)) = _
  rw [hfield, hcard, Fintype.card_fin]
  rfl

theorem metricDerivNorm_scaleMetric_both_left (c : ℝ) (hc : 0 < c)
    (g h gRef : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    metricDerivNorm m (scaleMetric c hc g) (scaleMetric c hc h) gRef x =
      c * metricDerivNorm m g h gRef x := by
  simp only [metricDerivNorm, metricDiffCovDerivAt,
    metricCovDeriv_scaleMetric_left, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [← smul_sub, sqrt_normSq0S_smul, abs_of_pos hc]

theorem metricDerivNorm_scaleMetric_self (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    metricDerivNorm m (scaleMetric c hc g) g g x =
      if m = 0 then |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) else 0 := by
  have hdiff : metricDiffCovDerivAt m (scaleMetric c hc g) g g x =
      (c - 1) • metricCovDeriv g g m x := by
    simp only [metricDiffCovDerivAt, metricCovDeriv_scaleMetric_left,
      ContMDiffSection.coe_smul, Pi.smul_apply, sub_smul, one_smul]
  rw [metricDerivNorm, hdiff, sqrt_normSq0S_smul]
  change |c - 1| * metricCovDerivNorm m g g x = _
  cases m with
  | zero => simp only [metricCovDerivNorm_self_zero, ite_true]
  | succ m => simp only [covNorm_self_succ, mul_zero, Nat.succ_ne_zero, ite_false]

theorem metricDerivNorm_scaleMetric_left_le (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    metricDerivNorm m (scaleMetric c hc g) gRef gRef x ≤
      c * metricDerivNorm m g gRef gRef x +
        |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  have h := metricDerivNorm_triangle m (scaleMetric c hc g)
    (scaleMetric c hc gRef) gRef gRef x
  rw [metricDerivNorm_scaleMetric_both_left, metricDerivNorm_scaleMetric_self] at h
  have herror : (if m = 0 then |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) else 0) ≤
      |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) := by
    split_ifs
    · exact le_rfl
    · positivity
  exact h.trans (add_le_add_right herror _)

theorem metricDerivENormSupOn_scaleMetric_left_le (K : Set M) (p : ℕ)
    (c : ℝ) (hc : 0 < c) (g gRef : SmoothRiemannianMetric I M) :
    metricDerivENormSupOn K p (scaleMetric c hc g) gRef gRef ≤
      ENNReal.ofReal c * metricDerivENormSupOn K p g gRef gRef +
        ENNReal.ofReal (|c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) := by
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro m hm x hx
  calc
    ENNReal.ofReal (metricDerivNorm m (scaleMetric c hc g) gRef gRef x) ≤
        ENNReal.ofReal (c * metricDerivNorm m g gRef gRef x +
          |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) :=
      ENNReal.ofReal_le_ofReal (metricDerivNorm_scaleMetric_left_le c hc g gRef m x)
    _ = ENNReal.ofReal c * ENNReal.ofReal (metricDerivNorm m g gRef gRef x) +
        ENNReal.ofReal (|c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) := by
      have hn : 0 ≤ metricDerivNorm m g gRef gRef x := Real.sqrt_nonneg _
      rw [ENNReal.ofReal_add (mul_nonneg hc.le hn) (by positivity),
        ENNReal.ofReal_mul hc.le]
    _ ≤ _ := add_le_add_left
      (mul_le_mul le_rfl (ofReal_metricDerivNorm_le_sup K p g gRef gRef hm hx)
        (by positivity) (by positivity)) _

theorem metricDerivENormSupOn_scaleMetric_left_lt (K : Set M) (p : ℕ)
    (c : ℝ) (hc : 0 < c) (g gRef : SmoothRiemannianMetric I M) {ε : ℝ}
    (hsmall : metricDerivENormSupOn K p g gRef gRef < ENNReal.ofReal ε) :
    metricDerivENormSupOn K p (scaleMetric c hc g) gRef gRef <
      ENNReal.ofReal (c * ε + |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) := by
  have hε : 0 < ε := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hsmall)
  calc
    metricDerivENormSupOn K p (scaleMetric c hc g) gRef gRef ≤
        ENNReal.ofReal c * metricDerivENormSupOn K p g gRef gRef +
          ENNReal.ofReal (|c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) :=
      metricDerivENormSupOn_scaleMetric_left_le K p c hc g gRef
    _ < ENNReal.ofReal c * ENNReal.ofReal ε +
        ENNReal.ofReal (|c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) :=
      ENNReal.add_lt_add_right ENNReal.ofReal_ne_top
        (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hc))
          ENNReal.ofReal_ne_top hsmall)
    _ = _ := by
      rw [ENNReal.ofReal_add (mul_nonneg hc.le hε.le) (by positivity),
        ENNReal.ofReal_mul hc.le]

theorem metricDerivENormSupOn_scaleMetric_self {K : Set M} (hK : K.Nonempty) (p : ℕ)
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    metricDerivENormSupOn K p (scaleMetric c hc g) g g =
      ENNReal.ofReal (|c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ)) := by
  apply le_antisymm
  · simpa only [metricDerivENormSupOn_self, mul_zero, zero_add] using
      metricDerivENormSupOn_scaleMetric_left_le K p c hc g g
  · obtain ⟨x, hx⟩ := hK
    have h := ofReal_metricDerivNorm_le_sup K p (scaleMetric c hc g) g g
      (Nat.zero_le p) hx
    simpa only [metricDerivNorm_scaleMetric_self, ite_true] using h


theorem metricDerivNorm_scaleMetric_same_metric
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (g gRef : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    metricDerivNorm j (scaleMetric c hc g) (scaleMetric d hd g) gRef x =
      |c - d| * metricCovDerivNorm j g gRef x := by
  simp only [metricDerivNorm, metricDiffCovDerivAt,
    metricCovDeriv_scaleMetric_left, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [← sub_smul, sqrt_normSq0S_smul]
  rfl

theorem metricCovDerivNorm_scaleMetric_left
    (c : ℝ) (hc : 0 < c) (g gRef : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    metricCovDerivNorm j (scaleMetric c hc g) gRef x =
      c * metricCovDerivNorm j g gRef x := by
  simp only [metricCovDerivNorm, metricCovDeriv_scaleMetric_left,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [sqrt_normSq0S_smul, abs_of_pos hc]


end DifferentialGeometry.Geometry.Metric
