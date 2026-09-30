import DifferentialGeometry.Geometry.Curvature.ConnectionDifference
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Tensor
open DifferentialGeometry.Geometry.Connection (metricLoweredConnectionDifferenceField)
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem jet_add_le (U : Opens E) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    {r : ℕ} (T V : Tensor0SField (I := 𝓘(ℝ, E)) (M := U) ∞ r) (j : ℕ) (x : U) :
    Real.sqrt (normSq0S G x (r + j) (iterCov G r (T + V) j x)) ≤
      Real.sqrt (normSq0S G x (r + j) (iterCov G r T j x)) +
        Real.sqrt (normSq0S G x (r + j) (iterCov G r V j x)) := by
  rw [iterCov_add]
  exact DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_add_le G x (r + j) _ _

private theorem jet_sub_le (U : Opens E) (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    {r : ℕ} (T V : Tensor0SField (I := 𝓘(ℝ, E)) (M := U) ∞ r) (j : ℕ) (x : U) :
    Real.sqrt (normSq0S G x (r + j) (iterCov G r (T - V) j x)) ≤
      Real.sqrt (normSq0S G x (r + j) (iterCov G r T j x)) +
        Real.sqrt (normSq0S G x (r + j) (iterCov G r V j x)) := by
  rw [iterCov_sub]
  exact DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_sub_le G x (r + j) _ _

theorem exists_iterCov_rm04Section_connection_bound_on_opens (j : ℕ) :
    ∃ C > 0, ∀ (U : Opens E) (G g : SmoothRiemannianMetric 𝓘(ℝ, E) U) (x : U),
      let L := metricLoweredConnectionDifferenceField G g
      let S := CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)
      Real.sqrt (normSq0S G x (4 + j) (iterCov G 4 S j x)) ≤
        Real.sqrt (normSq0S G x (4 + j) (iterCov G 4 (metricRm04 G) j x)) +
          2 * Real.sqrt (normSq0S G x (3 + (j + 1)) (iterCov G 3 L (j + 1) x)) +
          2 * C * ∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) *
            Real.sqrt (normSq0S G x (3 + c) (iterCov G 3 L c x)) *
            Real.sqrt (normSq0S G x (3 + (j - c)) (iterCov G 3 L (j - c) x)) := by
  obtain ⟨C, hC, htrace⟩ := exists_iter_cov_metric_trace_first_two_bound_on_opens (E := E) 4 j
  refine ⟨C, hC, ?_⟩
  intro U G g x
  dsimp only
  obtain ⟨e₁, e₂, e₃, e₄, he⟩ := exists_rm04Section_connection_difference (I := 𝓘(ℝ, E)) (M := U)
  let L := metricLoweredConnectionDifferenceField G g
  let D := covStep G 3 L
  let P := tensor0SFieldProduct ∞ L L
  let Q := metricTraceFirstTwoField G (Tensor0SField.domDomCongr ∞ e₄ P)
  let T₁ := Tensor0SField.domDomCongr ∞ e₁ D
  let T₂ := Tensor0SField.domDomCongr ∞ e₂ D
  let T₃ := Tensor0SField.domDomCongr ∞ e₃ Q
  let N (T : Tensor0SField (I := 𝓘(ℝ, E)) (M := U) ∞ 4) :=
    Real.sqrt (normSq0S G x (4 + j) (iterCov G 4 T j x))
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G x
  have hi := metricInverseInBasis_identity_of_orthonormal G b hb
  have hperm (e : Fin 4 ≃ Fin 4) (T : Tensor0SField (I := 𝓘(ℝ, E)) (M := U) ∞ 4) :
      N (Tensor0SField.domDomCongr ∞ e T) = N T := by
    dsimp only [N]
    rw [normSq0S_iterCov_domDomCongr G e T j x b hi]
  have h₁ : N T₁ = N D := hperm e₁ D
  have h₂ : N T₂ = N D := hperm e₂ D
  have h₃ : N T₃ = N Q := hperm e₃ Q
  have hD : N D = Real.sqrt (normSq0S G x (3 + (j + 1)) (iterCov G 3 L (j + 1) x)) := by
    dsimp only [N, D]
    rw [← normSq0S_iterCov_shift G L j x b hi]
  have hQ := htrace U G (Tensor0SField.domDomCongr ∞ e₄ P) x
  rw [normSq0S_iterCov_domDomCongr G e₄ P j x b hi] at hQ
  have hP := iterCov_product_sqrtNormSq_le G x b hi j L L
  have hQ' := hQ.trans (mul_le_mul_of_nonneg_left hP hC.le)
  have ha := jet_sub_le U G ((metricRm04 G + T₁ - T₂) + Q) T₃ j x
  have hb' := jet_add_le U G (metricRm04 G + T₁ - T₂) Q j x
  have hc := jet_sub_le U G (metricRm04 G + T₁) T₂ j x
  have hd := jet_add_le U G (metricRm04 G) T₁ j x
  change N (metricRm04 G + T₁ - T₂ + Q - T₃) ≤ N (metricRm04 G + T₁ - T₂ + Q) + N T₃ at ha
  change N (metricRm04 G + T₁ - T₂ + Q) ≤ N (metricRm04 G + T₁ - T₂) + N Q at hb'
  change N (metricRm04 G + T₁ - T₂) ≤ N (metricRm04 G + T₁) + N T₂ at hc
  change N (metricRm04 G + T₁) ≤ N (metricRm04 G) + N T₁ at hd
  rw [h₁] at hd
  rw [h₂] at hc
  rw [h₃] at ha
  have hout : N (metricRm04 G + T₁ - T₂ + Q - T₃) ≤ N (metricRm04 G) + 2 * N D + 2 * N Q := by
    linarith only [ha, hb', hc, hd]
  rw [he G g]
  change N (metricRm04 G + T₁ - T₂ + Q - T₃) ≤ _
  rw [hD] at hout
  change N Q ≤ _ at hQ'
  dsimp only [N] at hout hQ'
  linarith only [hout, hQ']

theorem exists_iterCov_rm04Section_uniform_bound_on_opens (j : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C > 0, ∀ (U : Opens E) (G g : SmoothRiemannianMetric 𝓘(ℝ, E) U) (x : U),
      Real.sqrt (normSq0S G x (4 + j) (iterCov G 4 (metricRm04 G) j x)) ≤ b →
      (∀ s ≤ j + 1, Real.sqrt (normSq0S G x (3 + s)
        (iterCov G 3 (metricLoweredConnectionDifferenceField G g) s x)) ≤ a) →
      Real.sqrt (normSq0S G x (4 + j)
        (iterCov G 4 (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)) j x)) ≤ C := by
  obtain ⟨K, hK, he⟩ := exists_iterCov_rm04Section_connection_bound_on_opens (E := E) j
  let F : ℝ := ∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ)
  refine ⟨1 + b + 2 * a + 2 * K * (F * a ^ 2), by dsimp only [F]; positivity, ?_⟩
  intro U G g x hR hL
  have h := he U G g x
  dsimp only at h
  let L := metricLoweredConnectionDifferenceField G g
  have hs : (∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) *
      Real.sqrt (normSq0S G x (3 + c) (iterCov G 3 L c x)) *
      Real.sqrt (normSq0S G x (3 + (j - c)) (iterCov G 3 L (j - c) x))) ≤ F * a ^ 2 := by
    calc
      _ ≤ ∑ c ∈ Finset.range (j + 1), (j.choose c : ℝ) * a ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        have hcj : c ≤ j + 1 := (Finset.mem_range.mp hc).le
        have hc' := hL c hcj
        have hd' := hL (j - c) (by omega)
        calc
          _ ≤ (j.choose c : ℝ) * a * a := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg _)) hd'
              (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ha)
          _ = (j.choose c : ℝ) * a ^ 2 := by ring
      _ = F * a ^ 2 := by rw [Finset.sum_mul]
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * K)
  have ht := hL (j + 1) le_rfl
  linarith only [h, hR, ht, hs']
end DifferentialGeometry.Geometry.Curvature
