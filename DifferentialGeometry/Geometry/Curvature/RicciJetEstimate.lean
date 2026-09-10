import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciFromJets
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

noncomputable section
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

namespace Poincare.Geometry.Curvature

theorem exists_ricci_tensor_difference_bound_of_metric_derivative_bounds
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (gRef : SmoothRiemannianMetric I M) (x : M) (ell B : ℝ)
    (hell : 0 < ell) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ g h : SmoothRiemannianMetric I M,
      (∀ v : TangentSpace I x, ell * gRef.inner x v v ≤ g.inner x v v) →
      (∀ v : TangentSpace I x, ell * gRef.inner x v v ≤ h.inner x v v) →
      (∀ k : ℕ, k ≤ 2 → metricCovDerivNorm (I := I) k g gRef x ≤ B) →
      (∀ k : ℕ, k ≤ 2 → metricCovDerivNorm (I := I) k h gRef x ≤ B) →
      Real.sqrt (normSq0S (I := I) gRef x 2 (metricRicci g x - metricRicci h x)) ≤
        C * ∑ k ∈ Finset.range 3, metricDerivNorm (I := I) k g h gRef x := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis gRef x
  let J := Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))
  choose K hK hcomp using (fun j : J ↦
    ricciSub_le_dNorm gRef x ell B hell hB (basis (j 0)) (basis (j 1)))
  let C := Real.sqrt (∑ j : J, K j ^ 2) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro g h hglow hhlow hgb hhb
  let S := ∑ k ∈ Finset.range 3, metricDerivNorm (I := I) k g h gRef x
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ Real.sqrt_nonneg _)
  have hinv : MetricInverseInBasis (I := I) gRef x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal gRef basis hON
  have hentry (j : J) :
      |component0S (I := I) basis (metricRicci g x - metricRicci h x) j| ≤ K j * S := by
    have heq : component0S (I := I) basis (metricRicci g x - metricRicci h x) j =
        ricciTensor g x (basis (j 0)) (basis (j 1)) -
          ricciTensor h x (basis (j 0)) (basis (j 1)) := by
      rw [component0S_apply, Tensor0SSpace.sub_apply]
      have hj : (fun a : Fin 2 ↦ basis (j a)) = vec2 (basis (j 0)) (basis (j 1)) := by
        funext a
        fin_cases a <;> rfl
      rw [hj]
      change metricRicciAt g x (vec2 (basis (j 0)) (basis (j 1))) -
        metricRicciAt h x (vec2 (basis (j 0)) (basis (j 1))) = _
      rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    rw [heq]
    exact hcomp j g h hglow hhlow hgb hhb
  have hsq : normSq0S (I := I) gRef x 2 (metricRicci g x - metricRicci h x) ≤
      (∑ j : J, K j ^ 2) * S ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq gRef x 2 basis hinv, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have he := hentry j
    have hn : 0 ≤ K j * S := mul_nonneg (hK j).le hS
    have hb : (component0S (I := I) basis (metricRicci g x - metricRicci h x) j) ^ 2 ≤
        (K j * S) ^ 2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hn).mpr he
    nlinarith [hb]
  have hsum : 0 ≤ ∑ j : J, K j ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  calc
    _ ≤ Real.sqrt ((∑ j : J, K j ^ 2) * S ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ j : J, K j ^ 2) * S := by
      rw [Real.sqrt_mul hsum, Real.sqrt_sq hS]
    _ ≤ C * S := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hS

theorem exists_ricci_tensor_difference_bound_of_small_metric_derivatives
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (gRef : SmoothRiemannianMetric I M) (x : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric I M) (ε : ℝ), ε ≤ 1 / 2 →
      (∀ k : ℕ, k ≤ 2 → metricDerivNorm (I := I) k g gRef gRef x ≤ ε) →
      Real.sqrt (normSq0S (I := I) gRef x 2 (metricRicci g x - metricRicci gRef x)) ≤ C * ε := by
  let R := ∑ k ∈ Finset.range 3, metricCovDerivNorm (I := I) k gRef gRef x
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ ↦ Real.sqrt_nonneg _)
  have hself (k : ℕ) (hk : k ≤ 2) : metricCovDerivNorm (I := I) k gRef gRef x ≤ R := by
    exact Finset.single_le_sum (f := fun j ↦ metricCovDerivNorm (I := I) j gRef gRef x)
      (fun _ _ ↦ Real.sqrt_nonneg _) (Finset.mem_range.mpr (show k < 3 by omega))
  obtain ⟨C, hC, hcompare⟩ := exists_ricci_tensor_difference_bound_of_metric_derivative_bounds
    gRef x (1 / 2) (R + 1) (by norm_num) (by linarith)
  refine ⟨3 * C, by positivity, ?_⟩
  intro g ε hε hsmall
  have hnonneg (v : TangentSpace I x) : 0 ≤ gRef.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (gRef.pos x v hv).le
  have hlow : ∀ v : TangentSpace I x, (1 / 2 : ℝ) * gRef.inner x v v ≤ g.inner x v v := by
    intro v
    have hdiff := metricDifference_abs_le g gRef gRef x v v
    rw [mul_assoc, Real.mul_self_sqrt (hnonneg v)] at hdiff
    have hlo := (abs_le.mp hdiff).1
    have hnorm := hsmall 0 (by norm_num)
    have he := mul_le_mul_of_nonneg_right (hnorm.trans hε) (hnonneg v)
    linarith
  have hlowRef : ∀ v : TangentSpace I x,
      (1 / 2 : ℝ) * gRef.inner x v v ≤ gRef.inner x v v := by
    intro v
    linarith [hnonneg v]
  have hb (k : ℕ) (hk : k ≤ 2) : metricCovDerivNorm (I := I) k g gRef x ≤ R + 1 := by
    have h := covNorm_le_add k g gRef gRef x
    have hs := hself k hk
    have hd := hsmall k hk
    linarith
  have hbRef (k : ℕ) (hk : k ≤ 2) : metricCovDerivNorm (I := I) k gRef gRef x ≤ R + 1 := by
    linarith [hself k hk]
  have hsum : (∑ k ∈ Finset.range 3, metricDerivNorm (I := I) k g gRef gRef x) ≤ 3 * ε := by
    calc
      _ ≤ ∑ _k ∈ Finset.range 3, ε :=
        Finset.sum_le_sum (fun k hk ↦ hsmall k (by have := Finset.mem_range.mp hk; omega))
      _ = _ := by simp
  calc
    _ ≤ C * ∑ k ∈ Finset.range 3, metricDerivNorm (I := I) k g gRef gRef x :=
      hcompare g gRef hlow hlowRef hb hbRef
    _ ≤ C * (3 * ε) := mul_le_mul_of_nonneg_left hsum hC.le
    _ = 3 * C * ε := by ring

end Poincare.Geometry.Curvature
