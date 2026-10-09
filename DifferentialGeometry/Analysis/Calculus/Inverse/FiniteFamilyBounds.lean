import DifferentialGeometry.Analysis.Calculus.Inverse.RingBounds

set_option autoImplicit false

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [HasSummableGeomSeries R]
variable {ι : Type*}

theorem uniform_iteratedFDeriv_ringInverse_bound (K : ℕ) (Λ D : ℝ)
    (A : ι → P → R) (U : Set P) (hU : IsOpen U)
    (hA : ∀ i, ContDiffOn 𝕜 K (A i) U)
    (hunit : ∀ i x, x ∈ U → IsUnit (A i x))
    (hinv : ∀ i x, x ∈ U → ‖Ring.inverse (A i x)‖ ≤ Λ)
    (hderiv : ∀ i n, 1 ≤ n → n ≤ K → ∀ x ∈ U,
      ‖iteratedFDeriv 𝕜 n (A i) x‖ ≤ D) :
    (∀ i, ContDiffOn 𝕜 K (fun x => Ring.inverse (A i x)) U) ∧
      ∀ i n, n ≤ K → ∀ x ∈ U,
        ‖iteratedFDeriv 𝕜 n (fun y => Ring.inverse (A i y)) x‖ ≤
          (K.factorial : ℝ) * ((K.factorial : ℝ) * max Λ 1 ^ (K + 1)) *
            max D 1 ^ K := by
  have hregular := DifferentialGeometry.Analysis.contDiffOn_ringInverse (𝕜 := 𝕜)
    (R := R) (K : ℕ∞ω)
  refine ⟨fun i => hregular.comp (hA i) (fun x hx => hunit i x hx), ?_⟩
  intro i n hn x hx
  obtain ⟨u, hu⟩ := hunit i x hx
  have huinv : ‖(↑u⁻¹ : R)‖ ≤ max Λ 1 := by
    rw [← Ring.inverse_unit, hu]
    exact (hinv i x hx).trans (le_max_left _ _)
  have houter : ∀ j, j ≤ n →
      ‖iteratedFDerivWithin 𝕜 j Ring.inverse {y : R | IsUnit y} (A i x)‖ ≤
        (K.factorial : ℝ) * max Λ 1 ^ (K + 1) := by
    intro j hj
    have hbound := DifferentialGeometry.Analysis.norm_iteratedFDerivWithin_ringInverse_le
      (𝕜 := 𝕜) j u
    rw [hu] at hbound
    refine hbound.trans (mul_le_mul ?_ ?_ (by positivity) (by positivity))
    · exact_mod_cast Nat.factorial_le (hj.trans hn)
    · exact (pow_le_pow_left₀ (norm_nonneg _) huinv _).trans
        (pow_le_pow_right₀ (le_max_right Λ 1) (Nat.add_le_add_right (hj.trans hn) 1))
  have hinner : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDerivWithin 𝕜 j (A i) U x‖ ≤ max D 1 ^ j := by
    intro j hj hjn
    rw [iteratedFDerivWithin_of_isOpen j hU hx]
    exact (hderiv i j hj (hjn.trans hn) x hx).trans
      ((le_max_left D 1).trans (le_self_pow₀ (le_max_right D 1) (by omega)))
  have hcomp := norm_iteratedFDerivWithin_comp_le hregular (hA i)
    (Nat.cast_le.mpr hn) Units.isOpen.uniqueDiffOn hU.uniqueDiffOn
    (fun y hy => hunit i y hy) hx houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hU hx] at hcomp
  refine hcomp.trans (mul_le_mul ?_ ?_ (by positivity) (by positivity))
  · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.factorial_le hn))
      (by positivity)
  · exact pow_le_pow_right₀ (le_max_right D 1) hn

theorem exists_uniform_iteratedFDeriv_ringInverse_bound (K : ℕ) (Λ : ℝ)
    (A : ι → P → R) (U : Set P) (hU : IsOpen U)
    (hA : ∀ i, ContDiffOn 𝕜 K (A i) U)
    (hunit : ∀ i x, x ∈ U → IsUnit (A i x))
    (hinv : ∀ i x, x ∈ U → ‖Ring.inverse (A i x)‖ ≤ Λ)
    (hderiv : ∀ n, 1 ≤ n → n ≤ K → ∃ D : ℝ, ∀ i x, x ∈ U →
      ‖iteratedFDeriv 𝕜 n (A i) x‖ ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      (∀ i, ContDiffOn 𝕜 K (fun x => Ring.inverse (A i x)) U) ∧
      ∀ i n, n ≤ K → ∀ x ∈ U,
        ‖iteratedFDeriv 𝕜 n (fun y => Ring.inverse (A i y)) x‖ ≤ C := by
  have hfinite : ∀ n : Fin (K + 1), ∃ D : ℝ, ∀ i x, x ∈ U → 1 ≤ (n : ℕ) →
      ‖iteratedFDeriv 𝕜 (n : ℕ) (A i) x‖ ≤ D := by
    intro n
    by_cases hn : 1 ≤ (n : ℕ)
    · obtain ⟨D, hD⟩ := hderiv n hn (by omega)
      exact ⟨D, fun i x hx _ => hD i x hx⟩
    · exact ⟨0, fun _ _ _ hn' => (hn hn').elim⟩
  choose b hb using hfinite
  let D : ℝ := ∑ n : Fin (K + 1), max (b n) 0
  have hD : ∀ i n, 1 ≤ n → n ≤ K → ∀ x ∈ U,
      ‖iteratedFDeriv 𝕜 n (A i) x‖ ≤ D := by
    intro i n hn hnK x hx
    let j : Fin (K + 1) := ⟨n, by omega⟩
    refine (hb j i x hx hn).trans ((le_max_left (b j) 0).trans ?_)
    exact Finset.single_le_sum (fun k _ => le_max_right (b k) 0) (Finset.mem_univ j)
  obtain ⟨hreg, hbound⟩ :=
    uniform_iteratedFDeriv_ringInverse_bound K Λ D A U hU hA hunit hinv hD
  exact ⟨_, by positivity, hreg, hbound⟩

end DifferentialGeometry.Analysis
