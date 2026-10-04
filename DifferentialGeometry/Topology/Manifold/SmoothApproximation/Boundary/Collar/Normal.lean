import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.NormalDerivative
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Normal speed of a collar curve under a diffeomorphism

`pos_derivWithin_comp_of_collar_curve`: if `γ : [0, a] → A` starts at a boundary point and is a
unit-speed curve for a defining function `rA` of `∂A` (`rA (γ t) = t`), then for every
`C^k` diffeomorphism `h : A → B` (`1 ≤ k`) and every `C¹` defining function `rB` of `∂B`, the
one-sided derivative of `t ↦ rB (h (γ t))` at `0` is positive. This uses W-2b's A3-b
(`pos_mfderiv_comp_of_diffeomorph`): both `d rA` and `d (rB ∘ h)` at the boundary point are positive
multiples of the inward normal coordinate (`mfderiv_eq_mul_of_pos`).
`mfderiv_ne_zero_of_collar_curve`: a unit-speed collar curve shows `d rA ≠ 0` on the boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

/-- A functional positive on the open half-space `{w 0 > 0}` is a positive multiple of `w ↦ w 0`. -/
theorem eq_mul_of_pos_on_halfSpace {n : ℕ} {Λ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ}
    (hΛ : ∀ w : EuclideanSpace ℝ (Fin (n + 1)), 0 < w 0 → 0 < Λ w) :
    0 < Λ (EuclideanSpace.single 0 1) ∧
      ∀ w : EuclideanSpace ℝ (Fin (n + 1)), Λ w = w 0 * Λ (EuclideanSpace.single 0 1) := by
  set e₀ : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1 with he₀
  have he₀0 : e₀ 0 = 1 := by simp [he₀]
  have hpos : 0 < Λ e₀ := hΛ e₀ (by rw [he₀0]; exact one_pos)
  refine ⟨hpos, fun w => ?_⟩
  set u := w - w 0 • e₀ with hu
  have hu0 : u 0 = 0 := by simp [hu, he₀0]
  have hΛu : Λ u = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos'
    · -- `Λ u < 0`: test `u + ε e₀`
      set ε := -Λ u / (Λ e₀ + 1) with hε
      have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
      have h1 := hΛ (u + ε • e₀) (by simp [hu0, he₀0, hε0])
      rw [map_add, map_smul, smul_eq_mul] at h1
      have h2 : ε * Λ e₀ < -Λ u := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    · set ε := Λ u / (Λ e₀ + 1) with hε
      have hε0 : 0 < ε := div_pos hpos' (by linarith)
      have h1 := hΛ (-u + ε • e₀) (by simp [hu0, he₀0, hε0])
      rw [map_add, map_neg, map_smul, smul_eq_mul] at h1
      have h2 : ε * Λ e₀ < Λ u := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
  have hw : w = u + w 0 • e₀ := by rw [hu]; abel
  rw [hw, map_add, hΛu, map_smul, smul_eq_mul, zero_add]
  simp [hu0, he₀0]

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]

/-- Chain rule along a curve: the one-sided derivative of `r ∘ γ` is `d r` applied to the
velocity of `γ`. -/
theorem derivWithin_comp_eq_mfderiv {a : ℝ} (ha : 0 < a) {γ : ℝ → A}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ (Icc 0 a) 0) {r : A → ℝ}
    (hr : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r (γ 0)) :
    derivWithin (fun t => r (γ t)) (Icc 0 a) 0 =
      mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r (γ 0)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ (Icc 0 a) 0 (1 : ℝ)) := by
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc 0 a) (0 : ℝ) :=
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt).mpr
      (uniqueDiffOn_Icc ha 0 (left_mem_Icc.2 ha.le))
  have hc := mfderiv_comp_mfderivWithin (0 : ℝ) hr hγ hu
  have h1 : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (r ∘ γ) (Icc 0 a) 0 (1 : ℝ) =
      mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r (γ 0)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ (Icc 0 a) 0 (1 : ℝ)) := by
    rw [hc]
    rfl
  rw [← h1, mfderivWithin_eq_fderivWithin]
  rfl

/-- A unit-speed collar curve shows that a defining function has nonzero differential at the
start point. -/
theorem mfderiv_ne_zero_of_collar_curve {a : ℝ} (ha : 0 < a) {γ : ℝ → A}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ (Icc 0 a) 0) {r : A → ℝ}
    (hr : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r (γ 0))
    (hrγ : ∀ t ∈ Icc 0 a, r (γ t) = t) :
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r (γ 0) ≠ 0 := by
  intro h0
  have h1 := derivWithin_comp_eq_mfderiv ha hγ hr
  rw [h0, zero_apply] at h1
  have h2 : derivWithin (fun t => r (γ t)) (Icc 0 a) 0 = 1 := by
    rw [derivWithin_congr (f := id) (fun t ht => hrγ t ht) (hrγ 0 (left_mem_Icc.2 ha.le))]
    exact derivWithin_id _ _ (uniqueDiffOn_Icc ha 0 (left_mem_Icc.2 ha.le))
  rw [h2] at h1
  have h3 : (1 : ℝ) = 0 := h1
  exact one_ne_zero h3

/-- **Positive normal speed.** -/
theorem pos_derivWithin_comp_of_collar_curve {k : ℕ∞ω} (hk : 1 ≤ k)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) {a : ℝ} (ha : 0 < a) {γ : ℝ → A}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ (Icc 0 a) 0)
    (hγ0 : (𝓡∂ (n + 1)).IsBoundaryPoint (γ 0))
    {rA : A → ℝ} (hrA : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) 1 rA) (hrAn : ∀ x, 0 ≤ rA x)
    (hrA0 : ∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x → rA x = 0)
    (hrAd : ∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x → mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) rA x ≠ 0)
    (hrγ : ∀ t ∈ Icc 0 a, rA (γ t) = t)
    {rB : B → ℝ} (hrB : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) 1 rB) (hrBn : ∀ y, 0 ≤ rB y)
    (hrB0 : ∀ y, (𝓡∂ (n + 1)).IsBoundaryPoint y → rB y = 0)
    (hrBd : ∀ y, (𝓡∂ (n + 1)).IsBoundaryPoint y → mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) rB y ≠ 0) :
    0 < derivWithin (fun t => rB (h (γ t))) (Icc 0 a) 0 := by
  have hk0 : k ≠ 0 := (lt_of_lt_of_le zero_lt_one hk).ne'
  set v : EuclideanSpace ℝ (Fin (n + 1)) :=
    mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ (Icc 0 a) 0 (1 : ℝ) with hv
  -- `d rA` and `d (rB ∘ h)` are positive multiples of the normal coordinate
  have hposA : ∀ w : EuclideanSpace ℝ (Fin (n + 1)), 0 < w 0 →
      (0 : ℝ) < (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) rA (γ 0) :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) w :=
    fun w hw => pos_mfderiv_comp_of_diffeomorph (k := ∞) (by exact_mod_cast le_top)
      (Diffeomorph.refl (𝓡∂ (n + 1)) A ∞) hrA hrAn hrA0 hrAd hγ0 w (by simpa using hw)
  have hposB : ∀ w : EuclideanSpace ℝ (Fin (n + 1)), 0 < w 0 →
      (0 : ℝ) < (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (rB ∘ h) (γ 0) :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) w :=
    fun w hw => pos_mfderiv_comp_of_diffeomorph hk h hrB hrBn hrB0 hrBd hγ0 w (by simpa using hw)
  obtain ⟨hμA, hdecA⟩ := eq_mul_of_pos_on_halfSpace hposA
  obtain ⟨hμB, hdecB⟩ := eq_mul_of_pos_on_halfSpace hposB
  have hdA := derivWithin_comp_eq_mfderiv ha hγ (hrA.mdifferentiableAt one_ne_zero)
  have hdB := derivWithin_comp_eq_mfderiv (r := rB ∘ h) ha hγ
    ((hrB.mdifferentiableAt one_ne_zero).comp _ (h.contMDiff.mdifferentiableAt hk0))
  have h1 : derivWithin (fun t => rA (γ t)) (Icc 0 a) 0 = 1 := by
    rw [derivWithin_congr (f := id) (fun t ht => hrγ t ht) (hrγ 0 (left_mem_Icc.2 ha.le))]
    exact derivWithin_id _ _ (uniqueDiffOn_Icc ha 0 (left_mem_Icc.2 ha.le))
  rw [h1] at hdA
  have hvA := hdecA v
  have hvpos : 0 < v 0 := by
    have : (1 : ℝ) = v 0 * _ := hdA.trans hvA
    by_contra hle
    rw [not_lt] at hle
    nlinarith
  change 0 < derivWithin (fun t => (rB ∘ h) (γ t)) (Icc 0 a) 0
  rw [hdB]
  change (0 : ℝ) < (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (rB ∘ h) (γ 0) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) v
  have hB := hdecB v
  have h2 := mul_pos hvpos hμB
  rw [← hB] at h2
  exact h2

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
