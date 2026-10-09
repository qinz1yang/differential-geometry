import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.UniformComparison_S76

/-!
# CH12-S76 G3b: three-metric `C^m` closeness (the derivative part of S7 v2, no chart identity)

On a manifold with three metrics `h, g1, k`: if `g1` is `δ`-close to `h` in `C^m` w.r.t. `h` and `g1`
is `δ`-close to `k` in `C^m` w.r.t. `k`, then `k` is `ε`-close to `h` in `C^m` w.r.t. `h`.
Route: `uniform_comparison_S76` (uniform constant; all a-priori jet bounds come from the two
hypotheses by chaining through `g1`), then the triangle inequality.
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal BigOperators

namespace GC.LongTime.Ch12

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]

/-- `metricDerivNorm` as a plain tensor norm (copy of the private lemma of
`Metric/ReferenceNormComparison`). -/
theorem metricDerivNorm_eq_tensor_norm_S76
    (g h R : SmoothRiemannianMetric (𝓡 3) M) (j : ℕ) (x : M) :
    metricDerivNorm j g h R x = Real.sqrt (normSq0S R x (2 + j)
      (iterCov R 2 (metricTensorField g - metricTensorField h) j x)) := by
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis R x
  have hinv : MetricInverseInBasis R x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)))) := by
    have hb := metricInverseInBasis_of_orthonormal R basis hON
    intro i l
    simpa [identityInvMetric, diagonalInvMetric] using hb i l
  exact metricDerivNorm_eq_iterCov g h R j basis hinv

/-- For `j ≥ 1`, the jet of a metric `R₁` w.r.t. `R₀` is `metricDerivNorm j R₁ R₀ R₀`. -/
theorem sqrt_normSq0S_iterCov_metric_S76
    (R₀ R₁ : SmoothRiemannianMetric (𝓡 3) M) (j : ℕ) (hj : 1 ≤ j) (x : M) :
    Real.sqrt (normSq0S R₀ x (2 + j) (iterCov R₀ 2 (metricTensorField R₁) j x)) =
      metricDerivNorm j R₁ R₀ R₀ x := by
  rw [metricDerivNorm_eq_tensor_norm_S76]
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  have h := iterCov_add (I := 𝓡 3) R₀ 2 (metricTensorField R₁ - metricTensorField R₀)
    (metricTensorField R₀) (a + 1)
  rw [sub_add_cancel, iterCov_metric_zero, add_zero] at h
  rw [h]

/-- Order-0 closeness gives metric equivalence with constant `2`. -/
theorem metric_equiv_two_S76 (g h : SmoothRiemannianMetric (𝓡 3) M) (x : M) {δ : ℝ}
    (hδ : δ ≤ 1 / 2) (hg : metricDerivNorm 0 g h h x ≤ δ) (v : TangentSpace (𝓡 3) x) :
    (2 : ℝ)⁻¹ * h.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ 2 * h.inner x v v := by
  have hn := abs_apply_le_norm0S h x 2
    ((metricTensorField g - metricTensorField h) x) ![v, v]
  rw [metricDerivNorm_eq_tensor_norm_S76] at hg
  have hev : ((metricTensorField g - metricTensorField h) x) ![v, v] =
      g.inner x v v - h.inner x v v := by
    have e1 := metricTensorField_apply (I := 𝓡 3) g x ![v, v]
    have e2 := metricTensorField_apply (I := 𝓡 3) h x ![v, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
    change (metricTensorField g x - metricTensorField h x) ![v, v] = _
    rw [sub_apply, e1, e2]
  have hpos : 0 ≤ h.inner x v v := metric_inner_self_nonneg h x v
  rw [hev, Fin.prod_univ_two] at hn
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hn
  rw [Real.mul_self_sqrt hpos] at hn
  have hnn : Real.sqrt (normSq0S h x (2 + 0) (iterCov h 2 (metricTensorField g - metricTensorField h) 0 x)) ≤ δ := hg
  have hn2 : Real.sqrt (normSq0S h x 2 ((metricTensorField g - metricTensorField h) x)) ≤ δ := hnn
  have habs : |g.inner x v v - h.inner x v v| ≤ δ * h.inner x v v :=
    hn.trans (mul_le_mul_of_nonneg_right hn2 hpos)
  have h1 := (abs_le.mp habs)
  constructor <;> nlinarith [h1.1, h1.2, hpos]

/-- Reverse metric equivalence (`R₀ := g`, `R₁ := h`) from order-0 closeness. -/
theorem metric_equiv_two_rev_S76 (g h : SmoothRiemannianMetric (𝓡 3) M) (x : M) {δ : ℝ}
    (hδ : δ ≤ 1 / 2) (hg : metricDerivNorm 0 g h h x ≤ δ) (v : TangentSpace (𝓡 3) x) :
    (2 : ℝ)⁻¹ * g.inner x v v ≤ h.inner x v v ∧ h.inner x v v ≤ 2 * g.inner x v v := by
  have := metric_equiv_two_S76 g h x hδ hg v
  constructor <;> linarith [this.1, this.2]

/-- **Three-metric closeness.**  `δ` depends only on `(M, m, ε)`. -/
theorem three_metric_closeness_S76 (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h g1 k : SmoothRiemannianMetric (𝓡 3) M),
      (∀ x : M, ∀ j ≤ m, metricDerivNorm j g1 h h x < δ) →
      (∀ x : M, ∀ j ≤ m, metricDerivNorm j g1 k k x < δ) →
      ∀ x : M, ∀ j ≤ m, metricDerivNorm j k h h x < ε := by
  obtain ⟨C, hC, hcomp⟩ := uniform_comparison_S76 (I := 𝓡 3) (M := M) m 2 1 (by norm_num)
    (by norm_num)
  refine ⟨min (min (1 / 2) (1 / C)) (ε / (2 * (C ^ 2 + 1))), ?_, ?_⟩
  · refine lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  intro h g1 k h1 h2
  set δ := min (min (1 / 2 : ℝ) (1 / C)) (ε / (2 * (C ^ 2 + 1))) with hδdef
  have hδ2 : δ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδC : δ ≤ 1 / C := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε / (2 * (C ^ 2 + 1)) := min_le_right _ _
  have hCδ : C * δ ≤ 1 := by
    calc C * δ ≤ C * (1 / C) := mul_le_mul_of_nonneg_left hδC hC.le
      _ = 1 := by field_simp
  have hδ1 : δ ≤ 1 := by linarith
  have hδpos : 0 < δ := lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  -- the tensors
  -- Step P1': ‖∇^{g1,j}(h - g1)‖_{g1} ≤ C δ  (comparison h → g1)
  have hP1 : ∀ x : M, ∀ j ≤ m, metricDerivNorm j h g1 g1 x ≤ C * δ := by
    intro x j hj
    rw [metricDerivNorm_eq_tensor_norm_S76]
    refine hcomp h g1 isOpen_univ (fun y _ v => metric_equiv_two_S76 g1 h y hδ2
      (le_of_lt (h1 y 0 (Nat.zero_le _))) v) ?_ (metricTensorField h - metricTensorField g1) x
      (mem_univ x) δ hδpos.le ?_ j hj
    · intro i hi hi1 y _
      rw [sqrt_normSq0S_iterCov_metric_S76 h g1 i hi1 y]
      exact (h1 y i hi).le.trans hδ1
    · intro i hi
      rw [← metricDerivNorm_eq_tensor_norm_S76, metricDerivNorm_symm]
      exact (h1 x i hi).le
  -- Step X: ‖∇^{g1,j}(g1 - k)‖_{g1} ≤ C δ  (comparison k → g1)
  have hX : ∀ x : M, ∀ j ≤ m, metricDerivNorm j g1 k g1 x ≤ C * δ := by
    intro x j hj
    rw [metricDerivNorm_eq_tensor_norm_S76]
    refine hcomp k g1 isOpen_univ (fun y _ v => metric_equiv_two_S76 g1 k y hδ2
      (le_of_lt (h2 y 0 (Nat.zero_le _))) v) ?_ (metricTensorField g1 - metricTensorField k) x
      (mem_univ x) δ hδpos.le ?_ j hj
    · intro i hi hi1 y _
      rw [sqrt_normSq0S_iterCov_metric_S76 k g1 i hi1 y]
      exact (h2 y i hi).le.trans hδ1
    · intro i hi
      rw [← metricDerivNorm_eq_tensor_norm_S76]
      exact (h2 x i hi).le
  -- Step Y: ‖∇^{h,j}(g1 - k)‖_h ≤ C (C δ)  (comparison g1 → h)
  have hY : ∀ x : M, ∀ j ≤ m, metricDerivNorm j g1 k h x ≤ C * (C * δ) := by
    intro x j hj
    rw [metricDerivNorm_eq_tensor_norm_S76]
    refine hcomp g1 h isOpen_univ (fun y _ v => metric_equiv_two_rev_S76 g1 h y hδ2
      (le_of_lt (h1 y 0 (Nat.zero_le _))) v) ?_ (metricTensorField g1 - metricTensorField k) x
      (mem_univ x) (C * δ) (by positivity) ?_ j hj
    · intro i hi hi1 y _
      rw [sqrt_normSq0S_iterCov_metric_S76 g1 h i hi1 y]
      exact (hP1 y i hi).trans hCδ
    · intro i hi
      rw [← metricDerivNorm_eq_tensor_norm_S76]
      exact hX x i hi
  intro x j hj
  have htri := metricDerivNorm_triangle (I := 𝓡 3) j k g1 h h x
  have hs : metricDerivNorm j k g1 h x = metricDerivNorm j g1 k h x := metricDerivNorm_symm j _ _ _ x
  have hY' := hY x j hj
  have hh1 := h1 x j hj
  have hbound : C * (C * δ) + δ ≤ ε / 2 := by
    have : C * (C * δ) + δ = (C ^ 2 + 1) * δ := by ring
    rw [this]
    calc (C ^ 2 + 1) * δ ≤ (C ^ 2 + 1) * (ε / (2 * (C ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_left hδε (by positivity)
      _ = ε / 2 := by field_simp
  linarith

end GC.LongTime.Ch12
