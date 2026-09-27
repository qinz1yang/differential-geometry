import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifferenceBounds
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Relowering
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.ReloweringNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.MetricShift

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle (normSq0S_neg normSq0S_add_le)
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem metric_tensor_norm_sq (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g x 2 (metricTensorField (I := I) g x) =
      (Module.finrank ℝ E : ℝ) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hfield : metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
    ext v
    rw [metricTensorField_apply, metricTensor0S_apply]
  rw [hfield]
  have hcard := normSq0S_metricTensor0S_eq_card (I := I) g basis _ hinv
  rw [Fintype.card_fin, show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] at hcard
  exact hcard

private theorem relower_norm_sq_le (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) (x : M) :
    normSq0S (I := I) g₂ x (s + 1) (reLower (I := I) g₁ g₂ T x) ≤
      (Module.finrank ℝ E : ℝ) ^ (s + 3) *
        (normSq0S (I := I) g₂ x (s + 1) (T x) *
          normSq0S (I := I) g₂ x 2 (metricTensorField (I := I) g₁ x)) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g₂ x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g₂ basis hON
  let V := (Tensor0SSpace.product (T x) (metricTensorField (I := I) g₁ x)).domDomCongr
    (reLowerPermutationWithTwoInputs s)
  have hprod := normSq0S_prod (I := I) g₂ x basis hinv (T x) (metricTensorField (I := I) g₁ x)
  have hperm := normSq0S_domDomCongr (I := I) g₂ x basis hinv
    (reLowerPermutationWithTwoInputs s)
    (Tensor0SSpace.product (T x) (metricTensorField (I := I) g₁ x))
  have htr := traceNormSq_le (I := I) (s := s + 1) g₂ x V
  have hrel : reLower (I := I) g₁ g₂ T x = metricTraceFirstTwo0STensor (I := I) g₂ V := by
    rw [reLower, metricTraceFirstTwoField_apply]
    congr 1
    rw [Tensor0SField.domDomCongr_apply]
    congr 1
    ext slots
    simp only [tensor0SField_product_apply, Tensor0SSpace.product_apply]
  rw [← hrel] at htr
  rw [show V = (Tensor0SSpace.product (T x) (metricTensorField (I := I) g₁ x)).domDomCongr
    (reLowerPermutationWithTwoInputs s) from rfl, hperm, hprod] at htr
  simpa only [Nat.add_assoc] using htr

private theorem relower_norm_sq_le_of_metric_equiv
    (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) (x : M)
    {C : ℝ} (hC : 1 ≤ C)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * g₁.inner x v v ≤ g₂.inner x v v ∧ g₂.inner x v v ≤ C * g₁.inner x v v) :
    normSq0S (I := I) g₁ x (s + 1) (reLower (I := I) g₁ g₂ T x) ≤
      (Module.finrank ℝ E : ℝ) ^ (s + 4) * C ^ (s + 3) *
        normSq0S (I := I) g₂ x (s + 1) (T x) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hsymm := metric_equiv_symm (I := I) g₁ g₂ x hC heq
  have hmet := normSq0S_upper_le_of_equiv (I := I) g₁ g₂ x 2 hC heq
    (metricTensorField (I := I) g₁ x)
  rw [metric_tensor_norm_sq] at hmet
  have hrel := relower_norm_sq_le (I := I) g₁ g₂ T x
  have hcomp := normSq0S_upper_le_of_equiv (I := I) g₂ g₁ x (s + 1) hC hsymm
    (reLower (I := I) g₁ g₂ T x)
  refine hcomp.trans ((mul_le_mul_of_nonneg_left hrel (pow_nonneg hC0 _)).trans ?_)
  have hT := normSq0S_nonneg (I := I) g₂ x (s + 1) (T x)
  have hn : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc C ^ (s + 1) * ((Module.finrank ℝ E : ℝ) ^ (s + 3) *
        (normSq0S (I := I) g₂ x (s + 1) (T x) *
          normSq0S (I := I) g₂ x 2 (metricTensorField (I := I) g₁ x)))
      ≤ C ^ (s + 1) * ((Module.finrank ℝ E : ℝ) ^ (s + 3) *
        (normSq0S (I := I) g₂ x (s + 1) (T x) * (C ^ 2 * (Module.finrank ℝ E : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmet hT) (pow_nonneg hn _))
          (pow_nonneg hC0 _)
    _ = _ := by simp only [pow_add]; ring

variable [T2Space M]

private theorem relower_derivative_norm_sq_le
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4) (x : M)
    {C : ℝ} (hC : 1 ≤ C)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * g₁.inner x v v ≤ g₂.inner x v v ∧ g₂.inner x v v ≤ C * g₁.inner x v v) :
    normSq0S (I := I) g₁ x 5
        (metricNabla0S (I := I) g₁ (reLower (I := I) g₁ g₂ T) x) ≤
      4 * (Module.finrank ℝ E : ℝ) ^ 8 * C ^ 7 *
          normSq0S (I := I) g₂ x 5 (metricNabla0S (I := I) g₂ T x) +
        (16 * (Module.finrank ℝ E : ℝ) ^ 11 * C ^ 8 +
          32 * (Module.finrank ℝ E : ℝ) ^ 12 * C ^ 6) *
            connectionDifferenceSq (I := I) g₁ g₂ x * normSq0S (I := I) g₂ x 4 (T x) := by
  let n : ℝ := Module.finrank ℝ E
  let P := reLower (I := I) g₁ g₂ T
  let X := reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T)
  let K := -lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁)
  let Y := reLowerPair (I := I) g₂ T K
  let Z := lapDiffFlux (I := I) g₁ g₂ P
  let a := connectionDifferenceSq (I := I) g₁ g₂ x
  let r := normSq0S (I := I) g₂ x 4 (T x)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [connectionDifferenceSq_def]
    exact normSq0S_nonneg (I := I) g₁ x 3 _
  have hr : 0 ≤ r := normSq0S_nonneg (I := I) g₂ x 4 (T x)
  have hsymm := metric_equiv_symm (I := I) g₁ g₂ x hC heq
  have hP : normSq0S (I := I) g₁ x 4 (P x) ≤ n ^ 7 * C ^ 6 * r :=
    relower_norm_sq_le_of_metric_equiv (I := I) g₁ g₂ T x hC heq
  have hX : normSq0S (I := I) g₁ x 5 (X x) ≤ n ^ 8 * C ^ 7 *
      normSq0S (I := I) g₂ x 5 (metricNabla0S (I := I) g₂ T x) :=
    relower_norm_sq_le_of_metric_equiv (I := I) g₁ g₂ _ x hC heq
  have hK1 : normSq0S (I := I) g₁ x 3 (K x) ≤ 4 * n ^ 4 * a := by
    change normSq0S (I := I) g₁ x 3
      (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁) x) ≤ _
    rw [normSq0S_neg]
    have hh := fluxNormSq_le (I := I) g₁ g₂ (metricTensorField (I := I) g₁) x
    rw [metric_tensor_norm_sq] at hh
    convert hh using 1
    simp only [Nat.cast_ofNat, n, a]
    ring
  have hK : normSq0S (I := I) g₂ x 3 (K x) ≤ C ^ 3 * (4 * n ^ 4 * a) :=
    (normSq0S_upper_le_of_equiv (I := I) g₁ g₂ x 3 hC heq (K x)).trans
      (mul_le_mul_of_nonneg_left hK1 (pow_nonneg hC0 _))
  have hY : normSq0S (I := I) g₁ x 5 (Y x) ≤ 4 * n ^ 11 * C ^ 8 * a * r := by
    have hh := reLowerPairSq_le (I := I) g₂ T K x
    have hc := normSq0S_upper_le_of_equiv (I := I) g₂ g₁ x 5 hC hsymm (Y x)
    refine hc.trans ((mul_le_mul_of_nonneg_left hh (pow_nonneg hC0 _)).trans ?_)
    calc C ^ 5 * (n ^ 7 * (r * normSq0S (I := I) g₂ x 3 (K x)))
        ≤ C ^ 5 * (n ^ 7 * (r * (C ^ 3 * (4 * n ^ 4 * a)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hr) (pow_nonneg hn _))
            (pow_nonneg hC0 _)
      _ = _ := by ring
  have hZ : normSq0S (I := I) g₁ x 5 (Z x) ≤ 16 * n ^ 12 * C ^ 6 * a * r := by
    have hh := fluxNormSq_le (I := I) g₁ g₂ P x
    have hp' := mul_le_mul_of_nonneg_left hP (show 0 ≤ 16 * n ^ 5 * a by positivity)
    refine hh.trans ?_
    convert hp' using 1 <;> simp only [n, a, r] <;> ring
  have hsplit : metricNabla0S (I := I) g₁ P x = (X x + Y x) + Z x := by
    have hh := congrArg (fun F => F x) (nabla_reLower_flux (I := I) g₁ g₂ T)
    change metricNabla0S (I := I) g₂ P x = X x + Y x at hh
    change metricNabla0S (I := I) g₁ P x = (X x + Y x) +
      (metricNabla0S (I := I) g₁ P x - metricNabla0S (I := I) g₂ P x)
    rw [← hh]
    abel
  have hinner := normSq0S_add_le (I := I) g₁ x 5 (X x) (Y x)
  have houter := normSq0S_add_le (I := I) g₁ x 5 (X x + Y x) (Z x)
  change normSq0S (I := I) g₁ x 5 (metricNabla0S (I := I) g₁ P x) ≤ _
  rw [hsplit]
  calc normSq0S (I := I) g₁ x 5 ((X x + Y x) + Z x)
      ≤ 4 * normSq0S (I := I) g₁ x 5 (X x) +
        4 * normSq0S (I := I) g₁ x 5 (Y x) +
        2 * normSq0S (I := I) g₁ x 5 (Z x) := by linarith
    _ ≤ 4 * (n ^ 8 * C ^ 7 * normSq0S (I := I) g₂ x 5
        (metricNabla0S (I := I) g₂ T x)) +
        4 * (4 * n ^ 11 * C ^ 8 * a * r) +
        2 * (16 * n ^ 12 * C ^ 6 * a * r) := by linarith
    _ = _ := by dsimp [n, a, r]; ring

private theorem relower_curvature_section (g₁ g₂ : SmoothRiemannianMetric I M) :
    reLower (I := I) g₁ g₂
        (CovariantDerivative.rm04Section (I := I) g₂ (metricCov (I := I) g₂)
          (metricCov_smooth (I := I) g₂)) =
      CovariantDerivative.rm04Section (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) := by
  classical
  apply DFunLike.ext
  intro x
  apply ContinuousMultilinearMap.ext
  intro tail
  change Tensor0SSpace.eval (reLower (I := I) g₁ g₂
    (CovariantDerivative.rm04Section (I := I) g₂ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂)) x) tail =
    Tensor0SSpace.eval (CovariantDerivative.riemannCurvature04At (I := I) g₁
      (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x) tail
  have hupd : Function.update tail (Fin.last 3)
      (sharpFlat (I := I) g₁ g₂ x (tail (Fin.last 3))) =
      vec4 (I := I) (tail 0) (tail 1) (tail 2)
        (sharpFlat (I := I) g₁ g₂ x (tail (Fin.last 3))) := by
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  have htail : tail = vec4 (I := I) (tail 0) (tail 1) (tail 2) (tail (Fin.last 3)) := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [reLower_apply, CovariantDerivative.rm04Section_apply, hupd]
  change CovariantDerivative.riemannCurvature04At (I := I) g₂ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x
      (vec4 (I := I) (tail 0) (tail 1) (tail 2)
        (sharpFlat (I := I) g₁ g₂ x (tail (Fin.last 3)))) = _
  rw [CovariantDerivative.riemannCurvature04At_apply_const]
  conv_rhs => rw [htail]
  change _ = CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
    (metricCov_smooth (I := I) g₂) x
    (vec4 (I := I) (tail 0) (tail 1) (tail 2) (tail (Fin.last 3)))
  rw [CovariantDerivative.riemannCurvature04At_apply_const,
    g₂.symm x (sharpFlat (I := I) g₁ g₂ x (tail (Fin.last 3))), inner_sharpFlat]
  exact g₁.symm x _ _

theorem norm_sq_cross_curvature_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {C : ℝ} (hC : 1 ≤ C)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * g₁.inner x v v ≤ g₂.inner x v v ∧ g₂.inner x v v ≤ C * g₁.inner x v v) :
    normSq0S (I := I) g₁ x 4
        (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
          (metricCov_smooth (I := I) g₂) x) ≤
      (Module.finrank ℝ E : ℝ) ^ 7 * C ^ 6 *
        normSq0S (I := I) g₂ x 4 (metricRm04At (I := I) g₂ x) := by
  have h := relower_norm_sq_le_of_metric_equiv (I := I) g₁ g₂
    (CovariantDerivative.rm04Section (I := I) g₂ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂)) x hC heq
  rw [relower_curvature_section] at h
  exact h

theorem norm_sq_covariant_derivative_cross_curvature_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {C : ℝ} (hC : 1 ≤ C)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * g₁.inner x v v ≤ g₂.inner x v v ∧ g₂.inner x v v ≤ C * g₁.inner x v v) :
    normSq0S (I := I) g₁ x 5
        (metricNabla0S (I := I) g₁
          (CovariantDerivative.rm04Section (I := I) g₁ (metricCov (I := I) g₂)
            (metricCov_smooth (I := I) g₂)) x) ≤
      4 * (Module.finrank ℝ E : ℝ) ^ 8 * C ^ 7 *
          normSq0S (I := I) g₂ x 5
            (metricNabla0S (I := I) g₂
              (CovariantDerivative.rm04Section (I := I) g₂ (metricCov (I := I) g₂)
                (metricCov_smooth (I := I) g₂)) x) +
        (16 * (Module.finrank ℝ E : ℝ) ^ 11 * C ^ 8 +
          32 * (Module.finrank ℝ E : ℝ) ^ 12 * C ^ 6) *
            connectionDifferenceSq (I := I) g₁ g₂ x *
              normSq0S (I := I) g₂ x 4 (metricRm04At (I := I) g₂ x) := by
  have h := relower_derivative_norm_sq_le (I := I) g₁ g₂
    (CovariantDerivative.rm04Section (I := I) g₂ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂)) x hC heq
  rw [relower_curvature_section] at h
  exact h

end DifferentialGeometry.Geometry.Curvature
