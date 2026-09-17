import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Mathlib.Topology.Compactness.LocallyCompact
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_open_metric_equivalence_iterCov_bound_of_isCompact
    {K : Set M} (hK : IsCompact K)
    (g R : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ (u : Set M) (C B : ℝ), IsOpen u ∧ K ⊆ u ∧ 1 ≤ C ∧ 0 ≤ B ∧
      (∀ x ∈ u, ∀ v : TangentSpace I x,
        C⁻¹ * R.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * R.inner x v v) ∧
      (∀ x ∈ u, ∀ j : ℕ, j ≤ p →
        Real.sqrt (normSq0S (I := I) g x (2 + j)
          (iterCov (I := I) R 2 (metricTensorField (I := I) g) j x)) ≤ B) := by
  classical
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨C, hC⟩ := equivOn_compact (I := I) hK' R g
  have hbounds : ∀ j : Fin (p + 1), ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K',
      Real.sqrt (normSq0S (I := I) g x (2 + (j : ℕ))
        (iterCov (I := I) R 2 (metricTensorField (I := I) g) j x)) ≤ B := by
    intro j
    exact sqrtNormSq0S_bddOn (I := I) hK' (2 + (j : ℕ)) g
      (iterCov (I := I) R 2 (metricTensorField (I := I) g) j)
  choose B hB_nonneg hB using hbounds
  refine ⟨interior K', C, ∑ j, B j, isOpen_interior, hKK', hC.1,
    Finset.sum_nonneg (fun j _ => hB_nonneg j), ?_, ?_⟩
  · intro x hx v
    exact hC.2 x (interior_subset hx) v
  · intro x hx j hj
    let j' : Fin (p + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hB j' x (interior_subset hx)).trans
      (Finset.single_le_sum (fun q _ => hB_nonneg q) (Finset.mem_univ j'))

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open Bundle Filter Set
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metric_deriv_norm_eq_iterCov
    (A B R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) :
    metricDerivNorm q A B R x =
      Real.sqrt (normSq0S R x (2 + q)
        (iterCov R 2 (metricTensorField A - metricTensorField B) q x)) := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis R x
  exact metricDerivNorm_eq_iterCov A B R q b
    (metricInverseInBasis_identity_of_orthonormal R b hb)

theorem exists_metric_deriv_norm_reference_bound
    {K : Set M} (hK : IsCompact K)
    (gRef g : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (A B : SmoothRiemannianMetric I M),
      ∀ r : ℕ, r ≤ p → ∀ x ∈ K,
        metricDerivNorm r A B g x ≤
          D * ∑ k ∈ Finset.range (p + 1), metricDerivNorm k A B gRef x := by
  classical
  obtain ⟨u, C, B₀, hu, hKu, hC, hB₀, heq, hb⟩ :=
    exists_open_metric_equivalence_iterCov_bound_of_isCompact hK g gRef p
  obtain ⟨Cc, hCc, hcomp⟩ :=
    exists_iterated_covariant_derivative_norm_comparison (q₂ := 2)
      hu g gRef p hC hB₀ heq (fun x hx j _ hj => hb x hx j hj)
  let F := Real.sqrt (C ^ (2 + p))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  refine ⟨F * (1 + Cc), mul_nonneg hF (by positivity), ?_⟩
  intro A B r hr x hx
  let S := ∑ k ∈ Finset.range (p + 1), metricDerivNorm k A B gRef x
  have hn (k : ℕ) : 0 ≤ metricDerivNorm k A B gRef x := Real.sqrt_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hn k
  have hsingle : metricDerivNorm r A B gRef x ≤ S :=
    Finset.single_le_sum (fun k _ => hn k) (Finset.mem_range.mpr (by omega))
  have hsum : (∑ k ∈ Finset.range r, metricDerivNorm k A B gRef x) ≤ S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro k _ _
      exact hn k
  have hfac : Real.sqrt (C ^ (2 + r)) ≤ F :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ hC (by omega))
  by_cases hr0 : r = 0
  · subst r
    have hzero := diffNorm_zero_change A B g gRef x hC (heq x (hKu hx))
    calc
      metricDerivNorm 0 A B g x ≤
          Real.sqrt (C ^ 2) * metricDerivNorm 0 A B gRef x := hzero
      _ ≤ F * S := mul_le_mul hfac hsingle (hn 0) hF
      _ ≤ (F * (1 + Cc)) * S := by nlinarith [mul_nonneg hF (mul_nonneg hCc hS)]
  · have hc := hcomp (metricTensorField A - metricTensorField B)
      x (hKu hx) r (Nat.pos_of_ne_zero hr0) hr
    simp_rw [← metric_deriv_norm_eq_iterCov] at hc
    calc
      metricDerivNorm r A B g x ≤ Real.sqrt (C ^ (2 + r)) *
          (metricDerivNorm r A B gRef x + Cc *
            ∑ k ∈ Finset.range r, metricDerivNorm k A B gRef x) := hc
      _ ≤ F * (S + Cc * S) := by
        exact mul_le_mul hfac
          (add_le_add hsingle (mul_le_mul_of_nonneg_left hsum hCc))
          (add_nonneg (hn r) (mul_nonneg hCc
            (Finset.sum_nonneg fun k _ => hn k))) hF
      _ = (F * (1 + Cc)) * S := by ring

theorem MetricCInfConvergenceOnCompacts.change_reference
    {gSeq : ℕ → SmoothRiemannianMetric I M}
    {gInf gRef : SmoothRiemannianMetric I M}
    (hconv : MetricCInfConvergenceOnCompacts gSeq gInf gRef)
    (g : SmoothRiemannianMetric I M) :
    MetricCInfConvergenceOnCompacts gSeq gInf g := by
  intro K hK p ε hε
  obtain ⟨D, hD, hbound⟩ := exists_metric_deriv_norm_reference_bound hK gRef g p
  let δ := ε / (2 * (D + 1) * ((p : ℝ) + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨N, hN⟩ := hconv K hK p δ hδ
  refine ⟨N, fun k hk => ?_⟩
  apply lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall K p (gSeq k) gInf g (ε / 2)
      (by positivity) ?_) (by linarith)
  intro r hr x hx
  have hpoint (j : ℕ) (hj : j ≤ p) : metricDerivNorm j (gSeq k) gInf gRef x ≤ δ :=
    (derivNorm_le_sup hK hj (gSeq k) gInf gRef hx).trans (hN k hk).le
  have hsum : (∑ j ∈ Finset.range (p + 1), metricDerivNorm j (gSeq k) gInf gRef x) ≤
      ((p : ℝ) + 1) * δ := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p + 1), δ :=
        Finset.sum_le_sum fun j hj => hpoint j (by
          have := Finset.mem_range.mp hj
          omega)
      _ = ((p : ℝ) + 1) * δ := by simp
  calc
    metricDerivNorm r (gSeq k) gInf g x ≤
        D * ∑ j ∈ Finset.range (p + 1), metricDerivNorm j (gSeq k) gInf gRef x :=
      hbound (gSeq k) gInf r hr x hx
    _ ≤ D * (((p : ℝ) + 1) * δ) := mul_le_mul_of_nonneg_left hsum hD
    _ ≤ ε / 2 := by
      dsimp only [δ]
      have hden : 0 < 2 * (D + 1) * ((p : ℝ) + 1) := by positivity
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) by positivity) hε.le]

end DifferentialGeometry.CheegerGromovCompactness

end
