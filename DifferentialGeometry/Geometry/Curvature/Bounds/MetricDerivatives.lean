import DifferentialGeometry.Geometry.Curvature.Bounds.ReferenceDerivatives
import DifferentialGeometry.Geometry.Connection.DifferenceJets
import DifferentialGeometry.Geometry.Connection.MixedDerivativeBounds
import DifferentialGeometry.Tensor.Metric.CompactBounds


noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (metricLoweredConnectionDifferenceField)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Tensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem finite_bound (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s) (j : ℕ) :
    ∃ a > 0, ∀ s ≤ j, A s ≤ a := by
  have hn := Finset.sum_nonneg (s := Finset.range (j + 1)) (fun s _ => hA s)
  refine ⟨1 + ∑ s ∈ Finset.range (j + 1), A s, by linarith, ?_⟩
  intro s hs
  have h := Finset.single_le_sum (s := Finset.range (j + 1)) (fun t _ => hA t)
    (Finset.mem_range.mpr (by omega : s < j + 1))
  linarith

private theorem lowered_curvature_bound
    (j : ℕ) (ell B A : ℝ) (hell : 0 < ell) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ C > 0, ∀ (G g : SmoothRiemannianMetric I M) (x : M),
      (∀ v : TangentSpace I x, ell * G.inner x v v ≤ g.inner x v v) →
      (∀ s ≤ j + 2, metricCovDerivNorm s g G x ≤ B) →
      Real.sqrt (normSq0S G x (4 + j) (iterCov G 4 (metricRm04 G) j x)) ≤ A →
      Real.sqrt (normSq0S G x (4 + j)
        (iterCov G 4
          (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)) j x)) ≤ C := by
  obtain ⟨a, ha, hconnection⟩ :=
    exists_connection_difference_derivatives_bound (I := I) (M := M)
      (j + 1) ell B hell hB
  obtain ⟨C, hC, hbound⟩ :=
    exists_iterCov_rm04Section_uniform_bound (I := I) (M := M) j a A ha.le hA
  refine ⟨C, hC, ?_⟩
  intro G g x hl hj hR
  exact hbound G g x hR
    (fun s hs => hconnection G g x hl (fun t _ ht => hj t (by omega)) s hs)

omit [BoundarylessManifold I M] in
private theorem metric_tensor_jet_bound (G g : SmoothRiemannianMetric I M)
    (x : M) (s : ℕ) (B : ℝ) (hj : metricCovDerivNorm s g G x ≤ B) :
    Real.sqrt (normSq0S G x (2 + s)
      (iterCov G 2 (metricTensorField g) s x)) ≤ B := by
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G x
  have hi := metricInverseInBasis_identity_of_orthonormal G b hb
  rw [← metricCovDerivNorm_eq_iterCov g G s b hi]
  exact hj

theorem exists_pos_bound_reference_curvature_derivative_of_metric_jets
    (j : ℕ) (ell B A : ℝ) (hell : 0 < ell) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ C > 0, ∀ (G g : SmoothRiemannianMetric I M) (x : M),
      (∀ v : TangentSpace I x, ell * G.inner x v v ≤ g.inner x v v) →
      (∀ s ≤ j + 2, metricCovDerivNorm s g G x ≤ B) →
      (∀ s ≤ j, Real.sqrt (normSq0S G x (4 + s)
        (iterCov G 4 (metricRm04 G) s x)) ≤ A) →
      Real.sqrt (normSq0S G x (4 + j) (iterCov G 4 (metricRm04 g) j x)) ≤ C := by
  choose P hP hPb using fun s : ℕ =>
    lowered_curvature_bound (I := I) (M := M) s ell B A hell hB hA
  obtain ⟨K, hK, hbound⟩ :=
    exists_iterCov_metricRm04_relowering_bound (I := I) (M := M) j
  let S : ℝ := ∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) * P c * B
  have hS : 0 ≤ S := Finset.sum_nonneg fun c _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP c).le) hB
  refine ⟨1 + K * S, by positivity, ?_⟩
  intro G g x hl hj hR
  have h := hbound G g x
  dsimp only at h
  have hs : (∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) *
      Real.sqrt (normSq0S G x (4 + c)
        (iterCov G 4
          (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)) c x)) *
      Real.sqrt (normSq0S G x (2 + (j - c))
        (iterCov G 2 (metricTensorField g) (j - c) x))) ≤ S := by
    apply Finset.sum_le_sum
    intro c hc
    have hcj : c ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hp := hPb c G g x hl (fun s hs => hj s (by omega)) (hR c hcj)
    have hm := metric_tensor_jet_bound G g x (j - c) B (hj (j - c) (by omega))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hm
      (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hP c).le)
  have hs' := mul_le_mul_of_nonneg_left hs hK.le
  linarith only [h, hs']

theorem exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets
    (j : ℕ) (L B A : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ C > 0, ∀ (G g : SmoothRiemannianMetric I M) (x : M),
      (∀ v : TangentSpace I x,
        L⁻¹ * G.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ L * G.inner x v v) →
      (∀ s ≤ j + 2, metricCovDerivNorm s g G x ≤ B) →
      (∀ s ≤ j, Real.sqrt (normSq0S G x (4 + s)
        (iterCov G 4 (metricRm04 G) s x)) ≤ A) →
      Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) ≤ C := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hell : 0 < L⁻¹ := inv_pos.mpr hLp
  choose P hP hPb using fun s : ℕ =>
    exists_pos_bound_reference_curvature_derivative_of_metric_jets
      (I := I) (M := M) s L⁻¹ B A hell hB hA
  obtain ⟨a, ha, haB⟩ :=
    exists_connection_difference_derivatives_bound (I := I) (M := M) j L⁻¹ B hell hB
  obtain ⟨b, hb, hbB⟩ := finite_bound P (fun s => (hP s).le) j
  obtain ⟨K, hK, hmixed⟩ :=
    exists_mixed_iterCov_bound (I := I) (M := M) 4 j (by norm_num) a b ha.le hb.le
  refine ⟨1 + Real.sqrt (L ^ (4 + j)) * K, by positivity, ?_⟩
  intro G g x hequiv hj hR
  have hl (v : TangentSpace I x) := (hequiv v).1
  have hconnection (s : ℕ) (hs : s < j) :
      Real.sqrt (normSq0S G x (3 + s)
        (iterCov G 3 (metricLoweredConnectionDifferenceField G g) s x)) ≤ a :=
    haB G g x hl (fun t _ ht => hj t (by omega)) s hs.le
  have hreference (s : ℕ) (hs : s ≤ j) :
      Real.sqrt (normSq0S G x (4 + s) (iterCov G 4 (metricRm04 g) s x)) ≤ b :=
    (hPb s G g x hl (fun t ht => hj t (by omega))
      (fun t ht => hR t (ht.trans hs))).trans (hbB s hs)
  have ht := hmixed G g (metricRm04 g) x hconnection hreference j 0 (by omega)
  change Real.sqrt (normSq0S G x (4 + j) (iterCov g 4 (metricRm04 g) j x)) ≤ K at ht
  have hn := sqrt_normSq0S_le_of_metric_equiv G g x (4 + j) hL hequiv
    (iterCov g 4 (metricRm04 g) j x)
  have hm := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (L ^ (4 + j)))
  linarith only [hn, hm]

theorem exists_pos_bound_intrinsic_curvature_derivative_on_compact_of_metric_jets
    (G : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    (j : ℕ) (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (g : SmoothRiemannianMetric I M) (x : M), x ∈ K →
      (∀ v : TangentSpace I x,
        L⁻¹ * G.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ L * G.inner x v v) →
      (∀ s ≤ j + 2, metricCovDerivNorm s g G x ≤ B) →
      Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) ≤ C := by
  choose P hP hPb using fun s : ℕ =>
    exists_pos_bound_iterCov_on_compact G (metricRm04 G) s hK
  obtain ⟨A, hA, hAb⟩ := finite_bound P (fun s => (hP s).le) j
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets
      (I := I) (M := M) j L B A hL hB hA.le
  refine ⟨C, hC, ?_⟩
  intro g x hx hequiv hj
  exact hbound G g x hequiv hj (fun s hs => (hPb s x hx).trans (hAb s hs))

end DifferentialGeometry.Geometry.Curvature
