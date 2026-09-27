import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.LeastEigenvector
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set Metric
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem exists_unit_eigenvector_iInf_rayleigh
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    ∃ w : E, ‖w‖ = 1 ∧
      A w = (⨅ x : {x : E // x ≠ 0}, A.rayleighQuotient x) • w ∧
      ∀ x : E, ‖x‖ = 1 →
        (⨅ y : {y : E // y ≠ 0}, A.rayleighQuotient y) ≤ ⟪A x, x⟫_ℝ := by
  obtain ⟨μ, w, hw, heig, hmin⟩ := exists_unit_least_eigenvector A hA
  have hvalue : A.rayleighQuotient w = μ := by
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, heig, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hw, one_pow, mul_one, div_one, RCLike.re_to_real]
  have hinf : (⨅ x : {x : E // x ≠ 0}, A.rayleighQuotient x) = μ := by
    rw [A.iInf_rayleigh_eq_iInf_rayleigh_sphere (by norm_num : (0 : ℝ) < 1)]
    rw [← hvalue]
    apply IsMinOn.iInf_eq (mem_sphere_zero_iff_norm.mpr hw)
    intro x hx
    rw [hvalue]
    change μ ≤ A.rayleighQuotient x
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, mem_sphere_zero_iff_norm.mp hx,
      one_pow, div_one, RCLike.re_to_real] using hmin x (mem_sphere_zero_iff_norm.mp hx)
  exact ⟨w, hw, hinf.symm ▸ heig, hinf.symm ▸ hmin⟩

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem exists_unit_orthogonal {v : E3} (hv : ‖v‖ = 1) :
    ∃ u : E3, ‖u‖ = 1 ∧ ⟪v, u⟫_ℝ = 0 := by
  have hON : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ : Fin 3 => v)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp only [hij, ↓reduceIte, Set.domRestrict_apply, real_inner_self_eq_norm_sq,
      hv, one_pow]
  obtain ⟨b, hb⟩ := hON.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ E3 = Fintype.card (Fin 3))
  refine ⟨b 1, b.orthonormal.norm_eq_one 1, ?_⟩
  rw [← hb 0 (by simp), b.inner_eq_ite]
  norm_num

theorem exists_unit_least_eigenvector_low_cluster
    (B : E3 →L[ℝ] E3) (hB : IsSelfAdjoint B)
    {v : E3} (hv : ‖v‖ = 1) {ε : ℝ}
    (hclose : ∀ x : E3,
      ‖(B - InnerProductSpace.rankOne ℝ v v) x‖ ≤ ε * ‖x‖) :
    ∃ w : E3, ‖w‖ = 1 ∧
      B w = (⨅ x : {x : E3 // x ≠ 0}, B.rayleighQuotient x) • w ∧
      |⨅ x : {x : E3 // x ≠ 0}, B.rayleighQuotient x| ≤ ε ∧
      ⟪v, w⟫_ℝ ^ 2 ≤ 2 * ε ∧ |⟪v, w⟫_ℝ| ≤ 2 * ε := by
  obtain ⟨w, hw, heig, hmin⟩ := exists_unit_eigenvector_iInf_rayleigh B hB
  let μ := ⨅ x : {x : E3 // x ≠ 0}, B.rayleighQuotient x
  have hquad : ⟪B w, w⟫_ℝ = μ := by
    rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq, hw]
    simp only [one_pow, mul_one, μ]
  have herr (u : E3) (hu : ‖u‖ = 1) :
      |⟪B u, u⟫_ℝ - ⟪v, u⟫_ℝ ^ 2| ≤ ε := by
    calc
      |⟪B u, u⟫_ℝ - ⟪v, u⟫_ℝ ^ 2| =
          |⟪(B - InnerProductSpace.rankOne ℝ v v) u, u⟫_ℝ| := by
        simp only [sub_apply, InnerProductSpace.rankOne_apply,
          inner_sub_left, real_inner_smul_left, pow_two]
      _ ≤ ‖(B - InnerProductSpace.rankOne ℝ v v) u‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ ε := by simpa only [hu, mul_one] using hclose u
  obtain ⟨u, hu, huv⟩ := exists_unit_orthogonal hv
  have hupper : μ ≤ ε := by
    have h := (abs_le.mp (herr u hu)).2
    rw [huv, zero_pow (by decide : 2 ≠ 0), sub_zero] at h
    exact (hmin u hu).trans h
  have herrw := abs_le.mp (herr w hw)
  rw [hquad] at herrw
  have habs : |μ| ≤ ε := abs_le.mpr ⟨by nlinarith [sq_nonneg ⟪v, w⟫_ℝ], hupper⟩
  have hsq : ⟪v, w⟫_ℝ ^ 2 ≤ 2 * ε := by linarith [herrw.1]
  refine ⟨w, hw, heig, habs, hsq, ?_⟩
  calc
    |⟪v, w⟫_ℝ| = ‖InnerProductSpace.rankOne ℝ v v w‖ := by
      simp only [InnerProductSpace.rankOne_apply, norm_smul, Real.norm_eq_abs, hv, mul_one]
    _ = ‖B w - (B - InnerProductSpace.rankOne ℝ v v) w‖ := by
      rw [sub_apply, sub_sub_cancel]
    _ ≤ ‖B w‖ + ‖(B - InnerProductSpace.rankOne ℝ v v) w‖ := norm_sub_le _ _
    _ ≤ ε + ε := add_le_add (by
        simpa only [heig, norm_smul, Real.norm_eq_abs, hw, mul_one] using habs)
      (by simpa only [hw, mul_one] using hclose w)
    _ = 2 * ε := by ring

theorem iInf_rayleigh_ge_relative_low_cluster
    (A B : E3 →L[ℝ] E3) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {v : E3} (hv : ‖v‖ = 1) {ε : ℝ}
    (hclose : ∀ x : E3,
      ‖(B - InnerProductSpace.rankOne ℝ v v) x‖ ≤ ε * ‖x‖)
    {t α η : ℝ} (ht : 0 ≤ t) (hα : 0 ≤ α)
    (hincrement : ∀ x : E3,
      α * (‖x‖ ^ 2 - ⟪v, x⟫_ℝ ^ 2) - η * ‖x‖ ^ 2 ≤ ⟪(B - t • A) x, x⟫_ℝ) :
    t * (⨅ x : {x : E3 // x ≠ 0}, A.rayleighQuotient x) + α * (1 - 2 * ε) - η ≤
      (⨅ x : {x : E3 // x ≠ 0}, B.rayleighQuotient x) := by
  obtain ⟨w, hw, heig, _, hsq, _⟩ :=
    exists_unit_least_eigenvector_low_cluster B hB hv hclose
  obtain ⟨_, _, _, hminA⟩ := exists_unit_eigenvector_iInf_rayleigh A hA
  have hAw := mul_le_mul_of_nonneg_left (hminA w hw) ht
  have htilt := mul_le_mul_of_nonneg_left hsq hα
  have hinc := hincrement w
  simp only [sub_apply, smul_apply,
    inner_sub_left, real_inner_smul_left, hw, one_pow, mul_one] at hinc
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq, hw, one_pow, mul_one] at hinc
  nlinarith

end DifferentialGeometry.Analysis
