import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Acute four-point configurations: the cone case (review 75, section C.3, S-X144 group G5)

Dimension-free half of the planar four-point exclusion. Four points `P 0, ..., P 3` of a real inner
product space such that every angle of every triangle among them is strictly acute
(`0 < ⟪P j - P i, P k - P i⟫` for pairwise distinct `i, j, k`) satisfy:

* `all_same_sign_SMR`: no relation `α (P i - P l) + β (P j - P l) + γ (P k - P l) = 0` with
  `α, β, γ ≥ 0` not all zero (the point `P l` is not in the convex hull of the others);
* `cone_of_relation_SMR`: no such relation with `α, β ≥ 0` and `γ < 0` (a vector of the pencil at
  `P l` lies in the cone spanned by two others): either the point lies inside the triangle
  (`λ + μ ≤ 1`, three acute angles around it) or the four points are a convex quadrilateral
  whose four angles are all acute (`λ + μ > 1`), both impossible.
The planar existence of the relation is in `PlanarFourPoints.lean`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

section Cone

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The core algebra of the cone case with the apex at the origin: `w = λ u + μ v`,
`λ, μ ≥ 0`, and the seven acute conditions that are used. -/
theorem cone_vectors_SMR {u v w : V} {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hw : w = lam • u + mu • v)
    (h1 : 0 < inner ℝ u v) (h2 : 0 < inner ℝ u w)
    (h3 : 0 < inner ℝ (-w) (u - w)) (h4 : 0 < inner ℝ (-w) (v - w))
    (h5 : 0 < inner ℝ (-u) (w - u)) (h6 : 0 < inner ℝ (-v) (w - v))
    (h7 : 0 < inner ℝ (u - w) (v - w)) : False := by
  have hww := real_inner_self_nonneg (x := w)
  have hvu : inner ℝ v u = inner ℝ u v := real_inner_comm u v
  have hvv := real_inner_self_nonneg (x := v)
  have huu := real_inner_self_nonneg (x := u)
  subst hw
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    inner_smul_left, inner_smul_right, hvu,
    RCLike.conj_to_real] at h2 h3 h4 h5 h6 h7 hww
  generalize inner ℝ u u = g11 at *
  generalize inner ℝ u v = g12 at *
  generalize inner ℝ v v = g22 at *
  rcases le_or_gt (lam + mu) 1 with hs | hs
  · have hpos : 0 < lam ∨ 0 < mu := by
      by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      have e1 : lam = 0 := le_antisymm hcon.1 hlam
      have e2 : mu = 0 := le_antisymm hcon.2 hmu
      subst e1
      subst e2
      simp at h2
    have key := mul_nonneg (sub_nonneg.2 hs) hww
    rcases hpos with hp | hp
    · nlinarith [mul_pos hp h3, mul_nonneg hmu h4.le]
    · nlinarith [mul_pos hp h4, mul_nonneg hlam h3.le]
  · nlinarith [mul_nonneg hlam h5.le, mul_nonneg hmu h6.le, mul_pos (sub_pos.2 hs) h1]

/-- **The cone case**: no `α (P i - P l) + β (P j - P l) + γ (P k - P l) = 0` with
`α, β ≥ 0`, `γ < 0` among four points all of whose angles are strictly acute. -/
theorem cone_of_relation_SMR (P : Fin 4 → V)
    (hP : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < inner ℝ (P j - P i) (P k - P i))
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : γ < 0)
    (hrel : α • (P i - P l) + β • (P j - P l) + γ • (P k - P l) = 0) : False := by
  have hγ0 : γ ≠ 0 := hγ.ne
  have hg : γ • (P k - P l) = -(α • (P i - P l) + β • (P j - P l)) :=
    eq_neg_of_add_eq_zero_right hrel
  have hw : P k - P l = (-α / γ) • (P i - P l) + (-β / γ) • (P j - P l) := by
    calc P k - P l = γ⁻¹ • (γ • (P k - P l)) := by rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]
      _ = (-α / γ) • (P i - P l) + (-β / γ) • (P j - P l) := by rw [hg]; module
  refine cone_vectors_SMR (u := P i - P l) (v := P j - P l) (w := P k - P l)
    (div_nonneg_of_nonpos (by linarith) hγ.le) (div_nonneg_of_nonpos (by linarith) hγ.le) hw
    (hP l i j hil.symm hjl.symm hij) (hP l i k hil.symm hkl.symm hik) ?_ ?_ ?_ ?_ ?_
  · simpa only [neg_sub, sub_sub_sub_cancel_right] using hP k l i hkl hik.symm hil.symm
  · simpa only [neg_sub, sub_sub_sub_cancel_right] using hP k l j hkl hjk.symm hjl.symm
  · simpa only [neg_sub, sub_sub_sub_cancel_right] using hP i l k hil hik hkl.symm
  · simpa only [neg_sub, sub_sub_sub_cancel_right] using hP j l k hjl hjk hkl.symm
  · simpa only [neg_sub, sub_sub_sub_cancel_right] using hP k i j hik.symm hjk.symm hij

/-- **The convex-hull case**: no `α (P i - P l) + β (P j - P l) + γ (P k - P l) = 0` with
`α, β, γ ≥ 0` not all zero among four points all of whose angles are strictly acute. -/
theorem all_same_sign_SMR (P : Fin 4 → V)
    (hP : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < inner ℝ (P j - P i) (P k - P i))
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hne : 0 < α ∨ 0 < β ∨ 0 < γ)
    (hrel : α • (P i - P l) + β • (P j - P l) + γ • (P k - P l) = 0) : False := by
  have h12 := hP l i j hil.symm hjl.symm hij
  have h13 := hP l i k hil.symm hkl.symm hik
  have h23 := hP l j k hjl.symm hkl.symm hjk
  generalize hu : P i - P l = u at *
  generalize hv : P j - P l = v at *
  generalize hw : P k - P l = w at *
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at h12
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at h12
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at h13
  have hu1 : 0 < inner ℝ u u := real_inner_self_pos.2 hu0
  have hv1 : 0 < inner ℝ v v := real_inner_self_pos.2 hv0
  have hw1 : 0 < inner ℝ w w := real_inner_self_pos.2 hw0
  have hvu : inner ℝ v u = inner ℝ u v := real_inner_comm u v
  have hwu : inner ℝ w u = inner ℝ u w := real_inner_comm u w
  have hwv : inner ℝ w v = inner ℝ v w := real_inner_comm v w
  have h0 : inner ℝ (α • u + β • v + γ • w) (α • u + β • v + γ • w) = 0 := by
    rw [hrel, inner_zero_left]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hvu, hwu, hwv,
    RCLike.conj_to_real] at h0
  generalize inner ℝ u u = a at *
  generalize inner ℝ v v = b at *
  generalize inner ℝ w w = c at *
  generalize inner ℝ u v = p at *
  generalize inner ℝ u w = q at *
  generalize inner ℝ v w = r at *
  rcases hne with h | h | h
  · nlinarith [mul_pos (mul_pos h h) hu1, mul_nonneg (mul_nonneg hβ hβ) hv1.le,
      mul_nonneg (mul_nonneg hγ hγ) hw1.le, mul_nonneg (mul_nonneg hα hβ) h12.le,
      mul_nonneg (mul_nonneg hα hγ) h13.le, mul_nonneg (mul_nonneg hβ hγ) h23.le]
  · nlinarith [mul_nonneg (mul_nonneg hα hα) hu1.le, mul_pos (mul_pos h h) hv1,
      mul_nonneg (mul_nonneg hγ hγ) hw1.le, mul_nonneg (mul_nonneg hα hβ) h12.le,
      mul_nonneg (mul_nonneg hα hγ) h13.le, mul_nonneg (mul_nonneg hβ hγ) h23.le]
  · nlinarith [mul_nonneg (mul_nonneg hα hα) hu1.le, mul_nonneg (mul_nonneg hβ hβ) hv1.le,
      mul_pos (mul_pos h h) hw1, mul_nonneg (mul_nonneg hα hβ) h12.le,
      mul_nonneg (mul_nonneg hα hγ) h13.le, mul_nonneg (mul_nonneg hβ hγ) h23.le]

end Cone

end GC.MetricGeometry
