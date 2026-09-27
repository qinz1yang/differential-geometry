import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciFromJets
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology ENNReal

namespace DifferentialGeometry.Geometry.Curvature

section Trace
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem ricciTensor_nonnegative_of_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (q : M)
    (hRm : metricAlgebraicCurvatureTensorAt g q ∈
      algebraicCurvatureOperatorNonnegativeCone)
    (v : TangentSpace I q) : 0 ≤ ricciTensor g q v v := by
  classical
  have hsec (u w : TangentSpace I q) : 0 ≤ metricRm04StandardAt g q u w w u := by
    have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp hRm)
      1 (fun _ => 1) (fun _ => u) (fun _ => w)
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one,
      one_mul, metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using h
  obtain ⟨B, hB⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g q
  rw [ricciTensor_eq_orthonormal_trace g q v v B hB]
  apply Finset.sum_nonneg
  intro i _
  rw [g.symm q _ _, ← metricRm04StandardAt_eq_inner_riemannOp]
  exact hsec (B i) v

end Trace

section Closure
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem ricciTensor_nonnegative_of_local_metric_jet_convergence
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (g R : SmoothRiemannianMetric I M) (q : M) (v : TangentSpace I q)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∀ a : ℕ, a ≤ 2 → metricDerivNorm a (gSeq k) g R q < ε)
    (hnonneg : ∀ᶠ k in atTop, 0 ≤ ricciTensor (gSeq k) q v v) :
    0 ≤ ricciTensor g q v v := by
  classical
  by_contra hn
  have hneg : ricciTensor g q v v < 0 := lt_of_not_ge hn
  obtain ⟨c, hc, hlow⟩ := metric_lower_on (I := I) (K := ({q} : Set M))
    isCompact_singleton g R
  let B : ℝ := (∑ a ∈ Finset.range 3, metricCovDerivNorm a g R q) + 1
  have hnorm (a : ℕ) : 0 ≤ metricCovDerivNorm a g R q := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) zero_le_one
  have hself (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a g R q ≤ B - 1 := by
    dsimp only [B]
    simp only [add_sub_cancel_right]
    exact Finset.single_le_sum (fun i _ => hnorm i)
      (Finset.mem_range.mpr (show a < 3 by omega))
  obtain ⟨C, hC, hRic⟩ := ricciSub_le_dNorm R q (c / 2) B (by positivity) hB v v
  let ε : ℝ := min (c / 2) (min 1 (-ricciTensor g q v v / (6 * C)))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (by positivity) (lt_min one_pos
      (div_pos (neg_pos.mpr hneg) (mul_pos (by norm_num) hC)))
  have hεc : ε ≤ c / 2 := min_le_left _ _
  have hεone : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεRic : ε * (6 * C) ≤ -ricciTensor g q v v := by
    apply (le_div_iff₀ (by positivity : 0 < 6 * C)).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨kc, hkc⟩ := hconv ε hε
  obtain ⟨kn, hkn⟩ := eventually_atTop.1 hnonneg
  let k := max kc kn
  have hsmall (a : ℕ) (ha : a ≤ 2) : metricDerivNorm a (gSeq k) g R q ≤ ε :=
    (hkc k (le_max_left _ _) a ha).le
  have hRnn (w : TangentSpace I q) : 0 ≤ R.inner q w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (R.pos q w hw).le
  have hlowG (w : TangentSpace I q) : (c / 2) * R.inner q w w ≤ g.inner q w w := by
    have hh := hlow q (mem_singleton q) w
    nlinarith [hRnn w]
  have hlowSeq (w : TangentSpace I q) :
      (c / 2) * R.inner q w w ≤ (gSeq k).inner q w w := by
    have hd := metricDifference_abs_le (gSeq k) g R q w w
    rw [mul_assoc, Real.mul_self_sqrt (hRnn w)] at hd
    have herr := mul_le_mul_of_nonneg_right
      ((hsmall 0 (by omega)).trans hεc) (hRnn w)
    have hlo := (abs_le.mp hd).1
    have hh := hlow q (mem_singleton q) w
    linarith
  have hbSeq (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a (gSeq k) R q ≤ B := by
    have hh := covNorm_le_add a (gSeq k) g R q
    have hs := hself a ha
    have he := (hsmall a ha).trans hεone
    linarith
  have hbG (a : ℕ) (ha : a ≤ 2) : metricCovDerivNorm a g R q ≤ B := by
    linarith [hself a ha]
  have hsum : (∑ a ∈ Finset.range 3, metricDerivNorm a (gSeq k) g R q) ≤ 3 * ε := by
    calc
      _ ≤ ∑ _a ∈ Finset.range 3, ε := Finset.sum_le_sum (fun a ha =>
        hsmall a (by have := Finset.mem_range.mp ha; omega))
      _ = _ := by simp
  have hdiff := hRic (gSeq k) g hlowSeq hlowG hbSeq hbG
  have hu := (abs_le.mp hdiff).2
  have hsumC := mul_le_mul_of_nonneg_left hsum hC.le
  have hpos := hkn k (le_max_right _ _)
  nlinarith

end Closure
end DifferentialGeometry.Geometry.Curvature

end
