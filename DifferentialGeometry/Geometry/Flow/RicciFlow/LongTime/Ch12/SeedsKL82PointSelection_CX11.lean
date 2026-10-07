import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option autoImplicit false

noncomputable section

open Set

namespace GC.LongTime.Ch12

/-- A bounded weighted-curvature selection, valid without a compactness or
maximum-attainment assumption. This is the radial part of KL (45.5)--(45.6).
The available curvature-scale radius is retained in the last inequality. -/
theorem exists_radial_curvature_selection_CX11
    {X : Type*} (S : Set X) (Q d : X → ℝ) {r Λ : ℝ}
    (hΛ : 0 < Λ) (hQ : BddAbove (Q '' S))
    (hgeom : ∀ x ∈ S, 0 < Q x ∧ 0 ≤ d x ∧ d x < r)
    (hseed : ∃ x ∈ S, Λ ≤ Q x * (r - d x) ^ 2) :
    ∃ x ∈ S, Λ / 2 < Q x * (r - d x) ^ 2 ∧
      (∀ y ∈ S, d y ≤ d x + (r - d x) / 4 → Q y ≤ 4 * Q x) ∧
      Real.sqrt (Λ / 2) < Real.sqrt (Q x) * (r - d x) := by
  obtain ⟨x₀, hx₀, hseed₀⟩ := hseed
  have hne : S.Nonempty := ⟨x₀, hx₀⟩
  let score : X → ℝ := fun x => Q x * (r - d x) ^ 2
  obtain ⟨K, hK⟩ := hQ
  have hKpos : 0 < K := (hgeom x₀ hx₀).1.trans_le (hK ⟨x₀, hx₀, rfl⟩)
  have hbdd : BddAbove (score '' S) := by
    refine ⟨K * r ^ 2, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    have hxg := hgeom x hx
    exact mul_le_mul (hK ⟨x, hx, rfl⟩)
      (pow_le_pow_left₀ (sub_pos.mpr hxg.2.2).le (by linarith [hxg.2.1]) 2)
      (sq_nonneg _) hKpos.le
  have hΛsup : Λ ≤ sSup (score '' S) :=
    hseed₀.trans (le_csSup hbdd ⟨x₀, hx₀, rfl⟩)
  have hsup : 0 < sSup (score '' S) := hΛ.trans_le hΛsup
  obtain ⟨v, hv, hvgt⟩ := exists_lt_of_lt_csSup (hne.image score)
    (show sSup (score '' S) / 2 < sSup (score '' S) by linarith)
  obtain ⟨x, hx, rfl⟩ := hv
  have hscore : Λ / 2 < score x := by linarith
  have hxg := hgeom x hx
  have hmargin : 0 < r - d x := sub_pos.mpr hxg.2.2
  have hscoreBound (y : X) (hy : y ∈ S) : score y < 2 * score x :=
    (le_csSup hbdd ⟨y, hy, rfl⟩).trans_lt (by linarith)
  refine ⟨x, hx, hscore, ?_, ?_⟩
  · intro y hy hdy
    have hyg := hgeom y hy
    have hbuffer : 3 * (r - d x) / 4 ≤ r - d y := by linarith
    have hbuffer2 : 9 * (r - d x) ^ 2 / 16 ≤ (r - d y) ^ 2 := by
      convert pow_le_pow_left₀ (by positivity : 0 ≤ 3 * (r - d x) / 4) hbuffer 2 using 1
      ring
    have hh := mul_le_mul_of_nonneg_left hbuffer2 hyg.1.le
    have hb := hscoreBound y hy
    dsimp only [score] at hb
    have hsquare : 0 < (r - d x) ^ 2 := sq_pos_of_pos hmargin
    by_contra hn
    have hlarge : 4 * Q x < Q y := lt_of_not_ge hn
    have hprod := mul_pos (sub_pos.mpr hlarge) hsquare
    nlinarith
  · dsimp only [score] at hscore
    have hh := Real.sqrt_lt_sqrt (by positivity : 0 ≤ Λ / 2) hscore
    rwa [Real.sqrt_mul hxg.1.le, Real.sqrt_sq hmargin.le] at hh

/-- Points outside the age cutoff in (45.5) have scalar curvature at most twice
the selected value on the selected backward time window. -/
theorem scalar_le_two_of_age_cutoff_CX11 {a t s α Q R : ℝ}
    (hα : 0 < α) (hQ : 0 < Q) (hage : α ≤ Q * (t - a))
    (hwindow : t - α / (2 * Q) ≤ s) (hcutoff : R * (s - a) ≤ α) :
    R ≤ 2 * Q := by
  have hδ : 0 < α / (2 * Q) := by positivity
  have he : (2 * Q) * (α / (2 * Q)) = α := by field_simp
  have hage' : α / (2 * Q) ≤ s - a := by
    have hh := mul_le_mul_of_nonneg_left hwindow hQ.le
    nlinarith
  by_contra hn
  have hR : 2 * Q < R := lt_of_not_ge hn
  have hp := mul_pos (sub_pos.mpr hR) hδ
  have hh := mul_nonneg (show 0 ≤ R by linarith) (sub_nonneg.mpr hage')
  nlinarith

end GC.LongTime.Ch12
