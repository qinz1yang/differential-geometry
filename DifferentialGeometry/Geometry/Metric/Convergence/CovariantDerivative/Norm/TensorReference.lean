import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.CovariantTwoTensor

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

private theorem tensor02_norm_eq_iterCov
    (A : Tensor0SField (I := I) (M := M) ∞ 2)
    (g : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    tensor02CovDerivNormWith j A g g x =
      Real.sqrt (normSq0S g x (2 + j) (iterCov g 2 A j x)) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  exact tensor02CovDerivNormWith_eq_iterCov A g j b
    (metricInverseInBasis_identity_of_orthonormal g b hb)

theorem exists_uniform_tensor02_covariant_norm_reference_bound
    (p : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : Set M), IsOpen u →
      ∀ (gRef g : SmoothRiemannianMetric I M),
      (∀ x ∈ u, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ C * gRef.inner x v v) →
      (∀ x ∈ u, ∀ j : ℕ, 1 ≤ j → j ≤ p →
        Real.sqrt (normSq0S g x (2 + j)
          (iterCov gRef 2 (metricTensorField g) j x)) ≤ B) →
      ∀ (A : Tensor0SField (I := I) (M := M) ∞ 2), ∀ r : ℕ, r ≤ p → ∀ x ∈ u,
        tensor02CovDerivNormWith r A g g x ≤
          D * ∑ j ∈ Finset.range (p + 1), tensor02CovDerivNormWith j A gRef gRef x := by
  classical
  obtain ⟨Cc, hCc, hcomp⟩ :=
    exists_uniform_iterated_covariant_derivative_norm_comparison (I := I) (M := M)
      2 p hC hB
  let F := Real.sqrt (C ^ (2 + p))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  refine ⟨F * (1 + Cc), mul_nonneg hF (by positivity), ?_⟩
  intro u hu gRef g heq hb A r hr x hx
  let S := ∑ j ∈ Finset.range (p + 1), tensor02CovDerivNormWith j A gRef gRef x
  have hn (j : ℕ) : 0 ≤ tensor02CovDerivNormWith j A gRef gRef x := Real.sqrt_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hn j
  have hsingle : tensor02CovDerivNormWith r A gRef gRef x ≤ S :=
    Finset.single_le_sum (fun j _ => hn j) (Finset.mem_range.mpr (by omega))
  have hsum : (∑ j ∈ Finset.range r, tensor02CovDerivNormWith j A gRef gRef x) ≤ S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro j _ _
      exact hn j
  have hfac : Real.sqrt (C ^ (2 + r)) ≤ F :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ hC (by omega))
  by_cases hr0 : r = 0
  · subst r
    have hzero := sqrt_normSq0S_le_of_metric_equiv gRef g x 2 hC (heq x hx) (A x)
    change tensor02CovDerivNormWith 0 A g g x ≤
      Real.sqrt (C ^ 2) * tensor02CovDerivNormWith 0 A gRef gRef x at hzero
    calc
      _ ≤ Real.sqrt (C ^ 2) * tensor02CovDerivNormWith 0 A gRef gRef x := hzero
      _ ≤ F * S := mul_le_mul hfac hsingle (hn 0) hF
      _ ≤ (F * (1 + Cc)) * S := by nlinarith [mul_nonneg hF (mul_nonneg hCc hS)]
  · have hc := hcomp u hu g gRef heq hb A x hx r (Nat.pos_of_ne_zero hr0) hr
    simp_rw [← tensor02_norm_eq_iterCov] at hc
    calc
      _ ≤ Real.sqrt (C ^ (2 + r)) *
          (tensor02CovDerivNormWith r A gRef gRef x + Cc *
            ∑ j ∈ Finset.range r, tensor02CovDerivNormWith j A gRef gRef x) := hc
      _ ≤ F * (S + Cc * S) :=
        mul_le_mul hfac (add_le_add hsingle (mul_le_mul_of_nonneg_left hsum hCc))
          (add_nonneg (hn r) (mul_nonneg hCc (Finset.sum_nonneg fun j _ => hn j))) hF
      _ = (F * (1 + Cc)) * S := by ring

end DifferentialGeometry.CheegerGromovCompactness
