import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis.Calculus

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_iteratedFDeriv_succ_le_of_fderiv_eq_clm_apply_add
    {U : Set E} (hU : IsOpen U) {u : E → F}
    {A : E → F →L[𝕜] E →L[𝕜] F} {b : E → E →L[𝕜] F} (n : ℕ)
    (hu : ContDiffOn 𝕜 n u U) (hA : ContDiffOn 𝕜 n A U)
    (hb : ContDiffOn 𝕜 n b U)
    (heq : Set.EqOn (fderiv 𝕜 u) (fun x => A x (u x) + b x) U)
    {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv 𝕜 (n + 1) u x‖ ≤
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ‖iteratedFDeriv 𝕜 j A x‖ * ‖iteratedFDeriv 𝕜 (n - j) u x‖) +
        ‖iteratedFDeriv 𝕜 n b x‖ := by
  have hprod := norm_iteratedFDerivWithin_clm_apply hA hu hU.uniqueDiffOn hx le_rfl
  rw [← norm_iteratedFDeriv_fderiv,
    ← iteratedFDerivWithin_of_isOpen n hU hx,
    iteratedFDerivWithin_congr heq hx n,
    fun_iteratedFDerivWithin_add_apply ((hA.clm_apply hu) x hx) (hb x hx)
      hU.uniqueDiffOn hx]
  refine (norm_add_le _ _).trans ((add_le_add hprod (le_refl _)).trans ?_)
  apply le_of_eq
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hU hx,
      iteratedFDerivWithin_of_isOpen (n - j) hU hx]
  · rw [iteratedFDerivWithin_of_isOpen n hU hx]

theorem exists_iteratedFDeriv_bound_le_of_fderiv_eq_clm_apply_add
    {ι : Type*} {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    (u : ι → E → F) (A : ι → E → F →L[𝕜] E →L[𝕜] F)
    (b : ι → E → E →L[𝕜] F) (n : ℕ)
    (hu : ∀ i, ContDiffOn 𝕜 n (u i) U)
    (hA : ∀ i, ContDiffOn 𝕜 n (A i) U)
    (hb : ∀ i, ContDiffOn 𝕜 n (b i) U)
    (heq : ∀ i, Set.EqOn (fderiv 𝕜 (u i))
      (fun x => A i x (u i x) + b i x) U)
    (hu0 : ∃ C : ℝ, ∀ i, ∀ x ∈ K, ‖u i x‖ ≤ C)
    (hAbdd : ∀ r ≤ n, ∃ C : ℝ, ∀ i, ∀ x ∈ K,
      ‖iteratedFDeriv 𝕜 r (A i) x‖ ≤ C)
    (hbbdd : ∀ r ≤ n, ∃ C : ℝ, ∀ i, ∀ x ∈ K,
      ‖iteratedFDeriv 𝕜 r (b i) x‖ ≤ C) :
    ∀ r ≤ n + 1, ∃ C : ℝ, ∀ i, ∀ x ∈ K,
      ‖iteratedFDeriv 𝕜 r (u i) x‖ ≤ C := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    cases r with
    | zero =>
      simpa only [norm_iteratedFDeriv_zero] using hu0
    | succ r =>
      have hrn : r ≤ n := Nat.le_of_succ_le_succ hr
      have hlow : ∀ j : Fin (r + 1), ∃ C : ℝ, ∀ i, ∀ x ∈ K,
          ‖iteratedFDeriv 𝕜 (r - j.val) (u i) x‖ ≤ C := by
        intro j
        exact ih (r - j.val) (by omega) (by omega)
      have hcoeff : ∀ j : Fin (r + 1), ∃ C : ℝ, ∀ i, ∀ x ∈ K,
          ‖iteratedFDeriv 𝕜 j.val (A i) x‖ ≤ C := by
        intro j
        exact hAbdd j.val (by omega)
      choose Cu hCu using hlow
      choose CA hCA using hcoeff
      obtain ⟨B, hB⟩ := hbbdd r hrn
      refine ⟨(∑ j : Fin (r + 1), (r.choose j.val : ℝ) *
        max 0 (CA j) * max 0 (Cu j)) + B, ?_⟩
      intro i x hx
      have hstep := norm_iteratedFDeriv_succ_le_of_fderiv_eq_clm_apply_add hU r
        ((hu i).of_le (by exact_mod_cast hrn))
        ((hA i).of_le (by exact_mod_cast hrn))
        ((hb i).of_le (by exact_mod_cast hrn)) (heq i) (hKU hx)
      refine hstep.trans (add_le_add ?_ (hB i x hx))
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left ((hCA j i x hx).trans (le_max_right _ _))
          (Nat.cast_nonneg _))
        ((hCu j i x hx).trans (le_max_right _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _))

theorem exists_iteratedFDeriv_bound_of_fderiv_eq_clm_apply_add
    {ι : Type*} {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    (u : ι → E → F) (A : ι → E → F →L[𝕜] E →L[𝕜] F)
    (b : ι → E → E →L[𝕜] F)
    (hu : ∀ i, ContDiffOn 𝕜 ∞ (u i) U)
    (hA : ∀ i, ContDiffOn 𝕜 ∞ (A i) U)
    (hb : ∀ i, ContDiffOn 𝕜 ∞ (b i) U)
    (heq : ∀ i, Set.EqOn (fderiv 𝕜 (u i))
      (fun x => A i x (u i x) + b i x) U)
    (hu0 : ∃ C : ℝ, ∀ i, ∀ x ∈ K, ‖u i x‖ ≤ C)
    (hAbdd : ∀ r : ℕ, ∃ C : ℝ, ∀ i, ∀ x ∈ K,
      ‖iteratedFDeriv 𝕜 r (A i) x‖ ≤ C)
    (hbbdd : ∀ r : ℕ, ∃ C : ℝ, ∀ i, ∀ x ∈ K,
      ‖iteratedFDeriv 𝕜 r (b i) x‖ ≤ C) :
    ∀ r : ℕ, ∃ C : ℝ, ∀ i, ∀ x ∈ K,
      ‖iteratedFDeriv 𝕜 r (u i) x‖ ≤ C := by
  intro r
  exact exists_iteratedFDeriv_bound_le_of_fderiv_eq_clm_apply_add hU hKU u A b r
    (fun i => (hu i).of_le (by exact_mod_cast le_top))
    (fun i => (hA i).of_le (by exact_mod_cast le_top))
    (fun i => (hb i).of_le (by exact_mod_cast le_top)) heq hu0
    (fun j _ => hAbdd j) (fun j _ => hbbdd j) r (Nat.le_succ r)

end DifferentialGeometry.Analysis.Calculus
