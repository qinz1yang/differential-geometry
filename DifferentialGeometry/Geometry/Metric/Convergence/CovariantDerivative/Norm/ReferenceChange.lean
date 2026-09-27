import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Tensor.Metric.ScaleNorm
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

theorem exists_uniform_metric_deriv_norm_reference_bound
    (p : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : Set M), IsOpen u →
      ∀ (gRef g : SmoothRiemannianMetric I M),
      (∀ x ∈ u, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ C * gRef.inner x v v) →
      (∀ x ∈ u, ∀ j : ℕ, 1 ≤ j → j ≤ p →
        Real.sqrt (normSq0S g x (2 + j)
          (iterCov gRef 2 (metricTensorField g) j x)) ≤ B) →
      ∀ (A B : SmoothRiemannianMetric I M), ∀ r : ℕ, r ≤ p → ∀ x ∈ u,
        metricDerivNorm r A B g x ≤
          D * ∑ k ∈ Finset.range (p + 1), metricDerivNorm k A B gRef x := by
  classical
  obtain ⟨Cc, hCc, hcomp⟩ :=
    exists_uniform_iterated_covariant_derivative_norm_comparison (I := I) (M := M)
      2 p hC hB
  let F := Real.sqrt (C ^ (2 + p))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  refine ⟨F * (1 + Cc), mul_nonneg hF (by positivity), ?_⟩
  intro u hu gRef g heq hb A B r hr x hx
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
    have hzero := diffNorm_zero_change A B g gRef x hC (heq x hx)
    calc
      metricDerivNorm 0 A B g x ≤
          Real.sqrt (C ^ 2) * metricDerivNorm 0 A B gRef x := hzero
      _ ≤ F * S := mul_le_mul hfac hsingle (hn 0) hF
      _ ≤ (F * (1 + Cc)) * S := by nlinarith [mul_nonneg hF (mul_nonneg hCc hS)]
  · have hc := hcomp u hu g gRef heq hb (metricTensorField A - metricTensorField B)
      x hx r (Nat.pos_of_ne_zero hr0) hr
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

theorem exists_metric_deriv_norm_reference_bound
    {K : Set M} (hK : IsCompact K)
    (gRef g : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (A B : SmoothRiemannianMetric I M),
      ∀ r : ℕ, r ≤ p → ∀ x ∈ K,
        metricDerivNorm r A B g x ≤
          D * ∑ k ∈ Finset.range (p + 1), metricDerivNorm k A B gRef x := by
  obtain ⟨u, C, B₀, hu, hKu, hC, hB₀, heq, hb⟩ :=
    exists_open_metric_equivalence_iterCov_bound_of_isCompact hK g gRef p
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_metric_deriv_norm_reference_bound (I := I) (M := M) p hC hB₀
  exact ⟨D, hD, fun A B r hr x hx => hbound u hu gRef g heq
    (fun y hy j _ hj => hb y hy j hj) A B r hr x (hKu hx)⟩

section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  [IsManifold J ∞ P] [T2Space P]

private local instance metricReferenceComplete : CompleteSpace F :=
  FiniteDimensional.complete ℝ F

theorem MetricCPConvergenceOn.change_reference
    {gSeq : ℕ → SmoothRiemannianMetric J P}
    {gInf gRef : SmoothRiemannianMetric J P}
    {K : Set P} {p : ℕ} (hconv : MetricCPConvergenceOn K p gSeq gInf gRef)
    (hK : IsCompact K)
    (g : SmoothRiemannianMetric J P) :
    MetricCPConvergenceOn K p gSeq gInf g := by
  intro ε hε
  obtain ⟨D, hD, hbound⟩ := exists_metric_deriv_norm_reference_bound hK gRef g p
  let δ := ε / (2 * (D + 1) * ((p : ℝ) + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨N, hN⟩ := hconv δ hδ
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

end

theorem MetricCInfConvergenceOnCompacts.change_reference
    {gSeq : ℕ → SmoothRiemannianMetric I M}
    {gInf gRef : SmoothRiemannianMetric I M}
    (hconv : MetricCInfConvergenceOnCompacts gSeq gInf gRef)
    (g : SmoothRiemannianMetric I M) :
    MetricCInfConvergenceOnCompacts gSeq gInf g := by
  intro K hK p
  exact (hconv K hK p).change_reference hK g

private theorem norm_iterCov_metric_eq_metricDerivNorm
    (h g : SmoothRiemannianMetric I M) (j : ℕ) (hj : 1 ≤ j) (x : M) :
    Real.sqrt (normSq0S g x (2 + j) (iterCov g 2 (metricTensorField h) j x)) =
      metricDerivNorm j h g g x := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  rw [metricDerivNorm_eq_iterCov h g g j b
    (metricInverseInBasis_identity_of_orthonormal g b hb)]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [iterCov_sub, iterCov_metric_zero, sub_zero]

theorem iterCov_metricTensorField_bound_of_metric_jets
    {U : Set M} (hU : IsOpen U) (h g : SmoothRiemannianMetric I M) (p : ℕ)
    (hjets : ∀ x ∈ U, ∀ j ≤ p, metricDerivNorm j g h h x ≤ 1 / 4) :
    ∀ x ∈ U, ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (normSq0S h x (2 + j) (iterCov g 2 (metricTensorField h) j x)) ≤
        (2 : ℝ) ^ (2 + p) *
          (1 + metricCovariantDerivativeComparisonConstant (E := E) 2 p * (p : ℝ)) := by
  have heq : ∀ x ∈ U, ∀ v : TangentSpace I x,
      (1 + (1 : ℝ))⁻¹ * h.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + (1 : ℝ)) * h.inner x v v := by
    intro x hx v
    have hb := inner_bounds_of_metricTensorErrorNorm_le g h
      (K := U) (fun y hy => hjets y hy 0 (Nat.zero_le p)) x hx v
    have hnonneg := metric_inner_self_nonneg h x v
    norm_num at hb ⊢
    constructor <;> linarith
  have hCc : 0 ≤ metricCovariantDerivativeComparisonConstant (E := E) 2 p :=
    metric_covariant_derivative_comparison_constant_nonneg _ _
  intro x hx j hj1 hjp
  have hnorm : metricDerivNorm j h g g x ≤
      Real.sqrt ((2 : ℝ) ^ (2 + p)) *
        (1 + metricCovariantDerivativeComparisonConstant (E := E) 2 p * (p : ℝ)) := by
    have hc := metric_deriv_norm_change_le hU h g g h p j 1
      zero_le_one le_rfl heq
      (fun y hy k _ hk => (hjets y hy k hk).trans (by norm_num)) x hx (by omega) hjp
    have hpoint (k : ℕ) (hk : k ≤ p) : metricDerivNorm k h g h x ≤ 1 := by
      rw [metricDerivNorm_symm]
      exact (hjets x hx k hk).trans (by norm_num)
    have hsum : (∑ k ∈ Finset.range j, metricDerivNorm k h g h x) ≤ (p : ℝ) := by
      calc
        _ ≤ ∑ _k ∈ Finset.range j, (1 : ℝ) := Finset.sum_le_sum fun k hk =>
          hpoint k (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hjp)
        _ = (j : ℝ) := by simp
        _ ≤ (p : ℝ) := by exact_mod_cast hjp
    norm_num only [one_add_one_eq_two, one_mul] at hc
    have hfac : Real.sqrt ((2 : ℝ) ^ (2 + j)) ≤ Real.sqrt ((2 : ℝ) ^ (2 + p)) :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (by omega))
    exact hc.trans ((mul_le_mul_of_nonneg_left
      (add_le_add (hpoint j hjp) (mul_le_mul_of_nonneg_left hsum hCc))
      (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hfac (by positivity)))
  have heq' : ∀ v : TangentSpace I x,
      (2 : ℝ)⁻¹ * g.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ 2 * g.inner x v v := by
    intro v
    have hb := heq x hx v
    norm_num at hb ⊢
    constructor <;> linarith
  have hn := sqrt_normSq0S_le_of_metric_equiv g h x (2 + j)
    (by norm_num) heq' (iterCov g 2 (metricTensorField h) j x)
  rw [norm_iterCov_metric_eq_metricDerivNorm h g j hj1 x] at hn
  have hfac : Real.sqrt ((2 : ℝ) ^ (2 + j)) ≤ Real.sqrt ((2 : ℝ) ^ (2 + p)) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (by omega))
  calc
    _ ≤ Real.sqrt ((2 : ℝ) ^ (2 + j)) * metricDerivNorm j h g g x := hn
    _ ≤ Real.sqrt ((2 : ℝ) ^ (2 + p)) *
        (Real.sqrt ((2 : ℝ) ^ (2 + p)) *
          (1 + metricCovariantDerivativeComparisonConstant (E := E) 2 p * (p : ℝ))) :=
      mul_le_mul hfac hnorm (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc, Real.mul_self_sqrt (by positivity)]

theorem exists_uniform_reference_bounds_of_scaled_metric_jets
    (p : ℕ) {qmin qmax : ℝ} (hqmin : 0 < qmin) :
    ∃ C B : ℝ, 1 ≤ C ∧ 0 ≤ B ∧ ∀ (U : Set M), IsOpen U →
      ∀ (g h : SmoothRiemannianMetric I M) (Q : ℝ) (hQ : 0 < Q),
      qmin ≤ Q → Q ≤ qmax →
      (∀ x ∈ U, ∀ j ≤ p, metricDerivNorm j (scaleMetric Q hQ g) h h x ≤ 1 / 4) →
      (∀ x ∈ U, ∀ v : TangentSpace I x,
        C⁻¹ * g.inner x v v ≤ h.inner x v v ∧ h.inner x v v ≤ C * g.inner x v v) ∧
      (∀ x ∈ U, ∀ j : ℕ, 1 ≤ j → j ≤ p →
        Real.sqrt (normSq0S h x (2 + j)
          (iterCov g 2 (metricTensorField h) j x)) ≤ B) := by
  let C := max 1 (max (2 / qmin) (2 * qmax))
  have hC : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hClow : 2 / qmin ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hChigh : 2 * qmax ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, (2 : ℝ) ^ (2 + p) *
    (1 + metricCovariantDerivativeComparisonConstant (E := E) 2 p * (p : ℝ)), hC, ?_, ?_⟩
  · have := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    positivity
  intro U hU g h Q hQ hlower hupper hjets
  constructor
  · intro x hx v
    have hb := inner_bounds_of_metricTensorErrorNorm_le (scaleMetric Q hQ g) h
      (K := U) (fun y hy => hjets y hy 0 (Nat.zero_le p)) x hx v
    rw [scaleMetric_inner] at hb
    have hg0 := metric_inner_self_nonneg g x v
    have hh0 := metric_inner_self_nonneg h x v
    have hratio : g.inner x v v ≤ (2 / qmin) * h.inner x v v := by
      have hq := mul_le_mul_of_nonneg_right hlower hg0
      have hq' : qmin * g.inner x v v ≤ 2 * h.inner x v v := by
        nlinarith [hq, hb.2]
      have hdiv := (le_div_iff₀ hqmin).2 (by simpa only [mul_comm] using hq')
      calc
        g.inner x v v ≤ (2 * h.inner x v v) / qmin := hdiv
        _ = (2 / qmin) * h.inner x v v := by ring
    constructor
    · apply (inv_mul_le_iff₀ hCpos).mpr
      exact hratio.trans (mul_le_mul_of_nonneg_right hClow hh0)
    · have hupper' := mul_le_mul_of_nonneg_right hupper hg0
      have hbound := mul_le_mul_of_nonneg_right hChigh hg0
      nlinarith
  · intro x hx j hj1 hjp
    rw [← DifferentialGeometry.Geometry.Tensor.iterCov_scaleMetric g Q hQ]
    exact iterCov_metricTensorField_bound_of_metric_jets hU h (scaleMetric Q hQ g) p
      hjets x hx j hj1 hjp


end DifferentialGeometry.CheegerGromovCompactness

end
