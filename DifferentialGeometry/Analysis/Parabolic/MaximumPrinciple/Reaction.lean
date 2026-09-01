import DifferentialGeometry.Analysis.Spectral.LowerKyFan
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace NNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

namespace PositiveSystem

def satisfiesNullEigenvectorCondition
    (reaction : (E →L[ℝ] E) → E →L[ℝ] E) : Prop :=
  ∀ A, A.IsPositive → ∀ v, A v = 0 → 0 ≤ ⟪reaction A v, v⟫_ℝ

omit [FiniteDimensional ℝ E] in
theorem kernel_derivatives_mem_and_reaction_inner_eq_zero
    {A B : E →L[ℝ] E} (hA : A.IsPositive)
    {i : Type*} [Fintype i] (D : i → E) (w : E)
    (hB : 0 ≤ ⟪B w, w⟫_ℝ)
    (hidentity :
      2 * ∑ j, ⟪A (D j), D j⟫_ℝ + ⟪B w, w⟫_ℝ = 0) :
    (∀ j, D j ∈ A.ker) ∧ ⟪B w, w⟫_ℝ = 0 := by
  have hterm (j : i) : 0 ≤ ⟪A (D j), D j⟫_ℝ :=
    hA.inner_nonneg_left (D j)
  have hsum_nonneg : 0 ≤ ∑ j, ⟪A (D j), D j⟫_ℝ :=
    Finset.sum_nonneg fun j _ ↦ hterm j
  have hsum_nonpos : ∑ j, ⟪A (D j), D j⟫_ℝ ≤ 0 := by
    nlinarith
  have hsum : ∑ j, ⟪A (D j), D j⟫_ℝ = 0 :=
    le_antisymm hsum_nonpos hsum_nonneg
  constructor
  · intro j
    have hall : (fun j ↦ ⟪A (D j), D j⟫_ℝ) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg hterm).mp hsum
    have hj : ⟪A (D j), D j⟫_ℝ = 0 :=
      congrFun hall j
    exact LinearMap.mem_ker.mpr
      ((hA.toLinearMap.inner_apply_self_eq_zero_iff (D j)).mp hj)
  · nlinarith

theorem sum_inner_reaction_ge_neg_mul_lowerKyFanSum
    {reaction : (E →L[ℝ] E) → E →L[ℝ] E}
    (hreactionNull : satisfiesNullEigenvectorCondition reaction)
    {A : E →L[ℝ] E} (hA : A.IsPositive)
    {R : ℝ} (hR : ‖A‖ ≤ R) {K : ℝ≥0}
    (hreactionLip : LipschitzOnWith K reaction
      {B : E →L[ℝ] E | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {k : ℕ} {e : Fin k → E} {eigenvalue : Fin k → ℝ}
    (he : Orthonormal ℝ e)
    (heigen : ∀ i, A (e i) = eigenvalue i • e i)
    (hsum : ∑ i, eigenvalue i =
      hA.toLinearMap.isSymmetric.lowerKyFanSum k) :
    -(K : ℝ) * hA.toLinearMap.isSymmetric.lowerKyFanSum k ≤
      ∑ i, ⟪reaction A (e i), e i⟫_ℝ := by
  have hpoint (i : Fin k) :
      -(K : ℝ) * eigenvalue i ≤ ⟪reaction A (e i), e i⟫_ℝ := by
    let P : E →L[ℝ] E := InnerProductSpace.rankOne ℝ (e i) (e i)
    let Ai : E →L[ℝ] E := A - eigenvalue i • P
    have heigenvalueNonneg : 0 ≤ eigenvalue i := by
      have h := hA.inner_nonneg_left (e i)
      rw [heigen i, inner_smul_left, starRingEnd_apply, star_trivial,
        real_inner_self_eq_norm_sq, he.norm_eq_one] at h
      simpa using h
    have heigenvalueLe : eigenvalue i ≤ R := by
      have h := A.le_opNorm (e i)
      rw [heigen i, norm_smul, he.norm_eq_one, mul_one] at h
      rw [Real.norm_eq_abs, abs_of_nonneg heigenvalueNonneg] at h
      simp only [mul_one] at h
      exact h.trans hR
    have hAi : Ai.IsPositive := by
      apply (ContinuousLinearMap.isPositive_toLinearMap_iff Ai).mp
      exact hA.toLinearMap.sub_smul_rankOne_of_eigenvector
        (he.norm_eq_one i) (heigen i)
    have hAiNorm : ‖Ai‖ ≤ 2 * R := by
      calc
        ‖Ai‖ ≤ ‖A‖ + ‖eigenvalue i • P‖ :=
          norm_sub_le A (eigenvalue i • P)
        _ = ‖A‖ + eigenvalue i := by
          rw [norm_smul, InnerProductSpace.norm_rankOne]
          simp [he.norm_eq_one i, Real.norm_eq_abs,
            abs_of_nonneg heigenvalueNonneg]
        _ ≤ 2 * R := by linarith
    have hANorm : ‖A‖ ≤ 2 * R := by
      have hnorm : 0 ≤ ‖A‖ := norm_nonneg A
      linarith
    have hAiZero : Ai (e i) = 0 := by
      simp [Ai, P, heigen i, he.norm_eq_one i]
    have hlip := hreactionLip.dist_le_mul A ⟨hA, hANorm⟩ Ai ⟨hAi, hAiNorm⟩
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have hAAi : ‖A - Ai‖ = eigenvalue i := by
      rw [show A - Ai = eigenvalue i • P by simp [Ai]]
      rw [norm_smul, InnerProductSpace.norm_rankOne]
      simp [he.norm_eq_one i, Real.norm_eq_abs,
        abs_of_nonneg heigenvalueNonneg]
    rw [hAAi] at hlip
    have hinner :
        |⟪(reaction A - reaction Ai) (e i), e i⟫_ℝ| ≤
          ‖reaction A - reaction Ai‖ := by
      calc
        |⟪(reaction A - reaction Ai) (e i), e i⟫_ℝ| ≤
            ‖(reaction A - reaction Ai) (e i)‖ * ‖e i‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (‖reaction A - reaction Ai‖ * ‖e i‖) * ‖e i‖ := by
          gcongr
          exact (reaction A - reaction Ai).le_opNorm (e i)
        _ = ‖reaction A - reaction Ai‖ := by
          rw [he.norm_eq_one, mul_one, mul_one]
    have hdiff :
        ⟪(reaction A - reaction Ai) (e i), e i⟫_ℝ =
          ⟪reaction A (e i), e i⟫_ℝ - ⟪reaction Ai (e i), e i⟫_ℝ := by
      simp [inner_sub_left]
    have hnull := hreactionNull Ai hAi (e i) hAiZero
    have hlower := neg_le_of_abs_le hinner
    rw [hdiff] at hlower
    nlinarith
  calc
    -(K : ℝ) * hA.toLinearMap.isSymmetric.lowerKyFanSum k =
        ∑ i, -(K : ℝ) * eigenvalue i := by
      rw [← hsum, Finset.mul_sum]
    _ ≤ ∑ i, ⟪reaction A (e i), e i⟫_ℝ :=
      Finset.sum_le_sum fun i _ ↦ hpoint i

theorem sum_inner_reaction_add_mul_pos_of_lowerKyFanSum_eq
    {reaction : (E →L[ℝ] E) → E →L[ℝ] E}
    (hreactionNull : satisfiesNullEigenvectorCondition reaction)
    {A : E →L[ℝ] E} (hA : A.IsPositive)
    {R : ℝ} (hR : ‖A‖ ≤ R) {K : ℝ≥0}
    (hreactionLip : LipschitzOnWith K reaction
      {B : E →L[ℝ] E | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {k : ℕ} {e : Fin k → E} {eigenvalue : Fin k → ℝ}
    (he : Orthonormal ℝ e)
    (heigen : ∀ i, A (e i) = eigenvalue i • e i)
    (hsum : ∑ i, eigenvalue i =
      hA.toLinearMap.isSymmetric.lowerKyFanSum k)
    {c f q : ℝ} (hk : 0 < k) (hc : (K : ℝ) < c)
    (hf : 0 < f) (hq : 0 < q)
    (hphi : hA.toLinearMap.isSymmetric.lowerKyFanSum k =
      (k : ℝ) * (f - q)) :
    0 < ∑ i, ⟪reaction A (e i), e i⟫_ℝ + (k : ℝ) * c * (q + f) := by
  have htrace := sum_inner_reaction_ge_neg_mul_lowerKyFanSum
    hreactionNull hA hR hreactionLip he heigen hsum
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hcpos : 0 < c := hK.trans_lt hc
  have hmain :
      0 < (k : ℝ) * (((c - (K : ℝ)) * f) + ((c + (K : ℝ)) * q)) := by
    apply mul_pos hkReal
    exact add_pos
      (mul_pos (sub_pos.mpr hc) hf)
      (mul_pos (add_pos_of_pos_of_nonneg hcpos hK) hq)
  rw [hphi] at htrace
  apply hmain.trans_le
  calc
    (k : ℝ) * (((c - (K : ℝ)) * f) + ((c + (K : ℝ)) * q)) =
        -(K : ℝ) * ((k : ℝ) * (f - q)) + (k : ℝ) * c * (q + f) := by
      ring
    _ ≤ ∑ i, ⟪reaction A (e i), e i⟫_ℝ + (k : ℝ) * c * (q + f) :=
      by simpa [add_comm] using add_le_add_right htrace ((k : ℝ) * c * (q + f))

theorem exists_frame_lowerKyFanSum_eq_and_reaction_trace_lower_bound
    {reaction : (E →L[ℝ] E) → E →L[ℝ] E}
    (hreactionNull : satisfiesNullEigenvectorCondition reaction)
    {A : E →L[ℝ] E} (hA : A.IsPositive)
    {R : ℝ} (hR : ‖A‖ ≤ R) {K : ℝ≥0}
    (hreactionLip : LipschitzOnWith K reaction
      {B : E →L[ℝ] E | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    ∃ e : Fin k → E,
      Orthonormal ℝ e ∧
      ∑ i, ⟪A (e i), e i⟫_ℝ =
        hA.toLinearMap.isSymmetric.lowerKyFanSum k ∧
      -(K : ℝ) * hA.toLinearMap.isSymmetric.lowerKyFanSum k ≤
        ∑ i, ⟪reaction A (e i), e i⟫_ℝ := by
  obtain ⟨e, eigenvalue, he, heigen, hsum⟩ :=
    hA.toLinearMap.isSymmetric.exists_eigenframe_lowerKyFanSum_eq hk
  refine ⟨e, he, ?_,
    sum_inner_reaction_ge_neg_mul_lowerKyFanSum
      hreactionNull hA hR hreactionLip he heigen hsum⟩
  calc
    ∑ i, ⟪A (e i), e i⟫_ℝ = ∑ i, eigenvalue i := by
      apply Finset.sum_congr rfl
      intro i hi
      change ⟪A.toLinearMap (e i), e i⟫_ℝ = eigenvalue i
      rw [heigen i, inner_smul_left]
      simp [he.norm_eq_one]
    _ = hA.toLinearMap.isSymmetric.lowerKyFanSum k := hsum

end PositiveSystem
