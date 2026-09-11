import DifferentialGeometry.Geometry.Curvature.ConnectionDifferenceBounds
import DifferentialGeometry.Geometry.Curvature.Relowering
import DifferentialGeometry.Geometry.Connection.DifferenceJets
import DifferentialGeometry.Geometry.Connection.MixedDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.DerivativeBounds
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Tensor DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance (U : Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

private theorem actual_reference_jet_restriction (U : Opens E3) (j : ℕ) (x : U) :
    Real.sqrt (normSq0S (metric.restrictOpen U) x (4 + j)
      (iterCov (metric.restrictOpen U) 4 (metricRm04 (metric.restrictOpen U)) j x)) =
    Real.sqrt (normSq0S metric (x : E3) (4 + j) (iterCov metric 4 (metricRm04 metric) j (x : E3))) := by
  have hr : metricRm04 (metric.restrictOpen U) = restrictOpen0S 4 (V := U) (metricRm04 metric) := by
    apply DFunLike.ext
    intro q
    apply tensor0SSpace_ext (I := 𝓡 3) 4 q
    intro w
    have ht := metricRm04StandardAt_restrictOpen metric U q (w 0) (w 1) (w 2) (w 3)
    simp only [mfderiv_subtype_val_apply] at ht
    have hw : vec4 (w 0) (w 1) (w 2) (w 3) = w := by
      funext i
      fin_cases i <;> rfl
    change metricRm04 (metric.restrictOpen U) q (vec4 (w 0) (w 1) (w 2) (w 3)) =
      metricRm04 metric (q : E3) (vec4 (w 0) (w 1) (w 2) (w 3)) at ht
    rw [hw] at ht
    exact ht
  rw [hr, iter_cov_restrict_open, normSq0S_restrictOpen_apply]
  rfl

private theorem finite_budget (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s) (j : ℕ) :
    ∃ a > 0, ∀ s ≤ j, A s ≤ a := by
  have hn := Finset.sum_nonneg (s := Finset.range (j + 1)) (fun s _ => hA s)
  refine ⟨1 + ∑ s ∈ Finset.range (j + 1), A s, by linarith, ?_⟩
  intro s hs
  have h := Finset.single_le_sum (s := Finset.range (j + 1)) (fun t _ => hA t)
    (Finset.mem_range.mpr (by omega : s < j + 1))
  linarith

private theorem lowered_curvature_bound (j : ℕ) (ell B : ℝ) (hell : 0 < ell) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (U : Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U) (q : U),
      (∀ v : TangentSpace (𝓡 3) q, ell * (metric.restrictOpen U).inner q v v ≤ g.inner q v v) →
      (∀ s ≤ j + 2, metricDerivNorm s g (metric.restrictOpen U) (metric.restrictOpen U) q ≤ B) →
      Real.sqrt (normSq0S (metric.restrictOpen U) q (4 + j)
        (iterCov (metric.restrictOpen U) 4
          (CovariantDerivative.rm04Section (metric.restrictOpen U) (metricCov g) (metricCov_smooth g)) j q)) ≤ C := by
  choose A hA hAb using fun s : ℕ =>
    exists_connection_difference_derivative_bound_on_opens metric s ell B hell hB
  obtain ⟨a, ha, hbudget⟩ := finite_budget A (fun s => (hA s).le) (j + 1)
  obtain ⟨K, hK, hcap⟩ := exists_pos_bound_iterCov_metricRm04 j
  obtain ⟨C, hC, hbound⟩ := exists_iterCov_rm04Section_uniform_bound_on_opens (E := E3) j a K ha.le hK.le
  refine ⟨C, hC, ?_⟩
  intro U g q hl hj
  apply hbound U (metric.restrictOpen U) g q
  · rw [actual_reference_jet_restriction]
    exact hcap (q : E3)
  · intro s hs
    exact (hAb s U g q hl (fun t ht => hj t (by omega))).trans (hbudget s hs)

private theorem varying_metric_jet_bound (U : Opens E3)
    (g : SmoothRiemannianMetric (𝓡 3) U) (q : U) (s : ℕ) (B : ℝ)
    (hj : metricDerivNorm s g (metric.restrictOpen U) (metric.restrictOpen U) q ≤ B) :
    Real.sqrt (normSq0S (metric.restrictOpen U) q (2 + s)
      (iterCov (metric.restrictOpen U) 2 (metricTensorField g) s q)) ≤ Real.sqrt 3 + B := by
  let G := metric.restrictOpen U
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G q
  have hi := metricInverseInBasis_identity_of_orthonormal G b hb
  rw [← metricCovDerivNorm_eq_iterCov g G s b hi]
  have h := covNorm_le_add s g G G q
  have hs : metricCovDerivNorm s G G q ≤ Real.sqrt 3 := by
    cases s with
    | zero => simpa using (metricCovDerivNorm_self_zero G q).le
    | succ s => rw [covNorm_self_succ]; positivity
  linarith only [h, hs, hj]

theorem exists_pos_bound_reference_curvature_derivative_of_metric_jets_on_opens
    (j : ℕ) (ell B : ℝ) (hell : 0 < ell) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (U : Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U) (q : U),
      (∀ v : TangentSpace (𝓡 3) q, ell * (metric.restrictOpen U).inner q v v ≤ g.inner q v v) →
      (∀ s ≤ j + 2, metricDerivNorm s g (metric.restrictOpen U) (metric.restrictOpen U) q ≤ B) →
      Real.sqrt (normSq0S (metric.restrictOpen U) q (4 + j)
        (iterCov (metric.restrictOpen U) 4 (metricRm04 g) j q)) ≤ C := by
  choose P hP hPb using fun s : ℕ => lowered_curvature_bound s ell B hell hB
  obtain ⟨K, hK, hbound⟩ := exists_iterCov_metricRm04_relowering_bound_on_opens (E := E3) j
  let H := Real.sqrt 3 + B
  have hH : 0 ≤ H := add_nonneg (Real.sqrt_nonneg _) hB
  let S : ℝ := ∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) * P c * H
  have hS : 0 ≤ S := Finset.sum_nonneg fun c _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP c).le) hH
  refine ⟨1 + K * S, by positivity, ?_⟩
  intro U g q hl hj
  have h := hbound U (metric.restrictOpen U) g q
  dsimp only at h
  have hs : (∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) *
      Real.sqrt (normSq0S (metric.restrictOpen U) q (4 + c)
        (iterCov (metric.restrictOpen U) 4
          (CovariantDerivative.rm04Section (metric.restrictOpen U) (metricCov g) (metricCov_smooth g)) c q)) *
      Real.sqrt (normSq0S (metric.restrictOpen U) q (2 + (j - c))
        (iterCov (metric.restrictOpen U) 2 (metricTensorField g) (j - c) q))) ≤ S := by
    apply Finset.sum_le_sum
    intro c hc
    have hcj := Finset.mem_range.mp hc
    have hp := hPb c U g q hl (fun s hs => hj s (by omega))
    have hm := varying_metric_jet_bound U g q (j - c) B (hj (j - c) (by omega))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hm
      (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hP c).le)
  have hs' := mul_le_mul_of_nonneg_left hs hK.le
  linarith only [h, hs']

theorem exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets_on_opens
    (j : ℕ) (ell B : ℝ) (hell : 0 < ell) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (U : Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U) (q : U),
      (∀ v : TangentSpace (𝓡 3) q, ell * (metric.restrictOpen U).inner q v v ≤ g.inner q v v) →
      (∀ s ≤ j + 2, metricDerivNorm s g (metric.restrictOpen U) (metric.restrictOpen U) q ≤ B) →
      Real.sqrt (normSq0S g q (4 + j) (iterCov g 4 (metricRm04 g) j q)) ≤ C := by
  choose P hP hPb using fun s : ℕ =>
    exists_pos_bound_reference_curvature_derivative_of_metric_jets_on_opens s ell B hell hB
  choose A hA hAb using fun s : ℕ =>
    exists_connection_difference_derivative_bound_on_opens metric s ell B hell hB
  obtain ⟨a, ha, haB⟩ := finite_budget A (fun s => (hA s).le) j
  obtain ⟨b, hb, hbB⟩ := finite_budget P (fun s => (hP s).le) j
  obtain ⟨K, hK, hmixed⟩ := exists_mixed_iterCov_bound_on_opens (E := E3) 4 j (by norm_num) a b ha.le hb.le
  let D := max 1 (max ell⁻¹ (1 + B))
  have hD : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hinv : D⁻¹ ≤ ell := (inv_le_comm₀ hDpos hell).2
    ((le_max_left _ _).trans (le_max_right _ _))
  have hupper : 1 + B ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨1 + Real.sqrt (D ^ (4 + j)) * K, by positivity, ?_⟩
  intro U g q hl hj
  let G := metric.restrictOpen U
  have hL (s : ℕ) (hs : s < j) :
      Real.sqrt (normSq0S G q (3 + s) (iterCov G 3 (metricLoweredConnectionDifferenceField G g) s q)) ≤ a :=
    (hAb s U g q hl (fun t ht => hj t (by omega))).trans (haB s hs.le)
  have hR (s : ℕ) (hs : s ≤ j) : Real.sqrt (normSq0S G q (4 + s) (iterCov G 4 (metricRm04 g) s q)) ≤ b :=
    (hPb s U g q hl (fun t ht => hj t (by omega))).trans (hbB s hs)
  have ht := hmixed U G g (metricRm04 g) q hL hR j 0 (by omega)
  change Real.sqrt (normSq0S G q (4 + j) (iterCov g 4 (metricRm04 g) j q)) ≤ K at ht
  have hequiv (v : TangentSpace (𝓡 3) q) :
      D⁻¹ * G.inner q v v ≤ g.inner q v v ∧ g.inner q v v ≤ D * G.inner q v v := by
    have hv : 0 ≤ G.inner q v v := metric_inner_self_nonneg G q v
    constructor
    · exact (mul_le_mul_of_nonneg_right hinv hv).trans (hl v)
    · exact (inner_bounds_of_metricDerivNorm_le G g q (hj 0 (by omega)) v).2.trans
        (mul_le_mul_of_nonneg_right hupper hv)
  have hn := sqrt_normSq0S_le_of_metric_equiv G g q (4 + j) hD hequiv (iterCov g 4 (metricRm04 g) j q)
  have hm := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (D ^ (4 + j)))
  linarith only [hn, hm]
end DifferentialGeometry.PDE.RicciFlow.StandardCap
