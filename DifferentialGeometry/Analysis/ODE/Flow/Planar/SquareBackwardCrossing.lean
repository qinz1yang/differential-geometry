import DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareFlowExit

open Set
open scoped ContDiff

namespace Poincare.Analysis

theorem exists_neg_leftEdge_crossing
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    (hfixed : ∀ z : ℂ, z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v z = 1)
    {z : ℂ} (hzre : z.re ∈ Ioc 0 1) (hzim : z.im ∈ Icc 0 1) :
    ∃ t < 0, (φ t z).re = 0 := by
  let c : ℂ := 1 + Complex.I
  let w : ℂ → ℂ := fun x ↦ v (c - x)
  let ψ : _root_.Flow ℝ ℂ := {
    toFun := fun t x ↦ c - φ (-t) (c - x)
    cont' := continuous_const.sub
      (φ.continuous continuous_fst.neg (continuous_const.sub continuous_snd))
    map_add' := fun t s x ↦ by simp only [neg_add, φ.map_add, sub_sub_cancel]
    map_zero' := fun x ↦ by simp only [neg_zero, φ.map_zero_apply, sub_sub_cancel] }
  have hw : ContDiff ℝ ∞ w := hv.comp (contDiff_const.sub contDiff_id)
  have hwderiv (x : ℂ) (t : ℝ) : HasDerivAt (fun s ↦ ψ s x) (w (ψ t x)) t := by
    convert (hasDerivAt_const t c).sub
      ((hderiv (c - x) (-t)).scomp t (hasDerivAt_neg t)) using 1 <;>
      first
      | rfl
      | simp only [ψ, w, neg_one_smul, zero_sub, neg_neg, sub_sub_cancel]
  have hre (x : ℂ) : (c - x).re = 1 - x.re := by simp [c]
  have him (x : ℂ) : (c - x).im = 1 - x.im := by simp [c]
  have hwfixed (x : ℂ)
      (hx : x.re ≤ 0 ∨ 1 ≤ x.re ∨ x.im ≤ 0 ∨ 1 ≤ x.im) : w x = 1 := by
    apply hfixed
    rcases hx with hx | hx | hx | hx
    · exact Or.inr (Or.inl (by rw [hre]; linarith))
    · exact Or.inl (by rw [hre]; linarith)
    · exact Or.inr (Or.inr (Or.inr (by rw [him]; linarith)))
    · exact Or.inr (Or.inr (Or.inl (by rw [him]; linarith)))
  obtain ⟨t, ht, hcross⟩ := exists_pos_rightEdge_crossing ψ hw (fun x ↦ hnz (c - x))
    hwderiv hwfixed (z := c - z)
    (by rw [hre]; constructor <;> linarith [hzre.1, hzre.2])
    (by rw [him]; constructor <;> linarith [hzim.1, hzim.2])
  change (c - φ (-t) (c - (c - z))).re = 1 at hcross
  rw [sub_sub_cancel, hre] at hcross
  exact ⟨-t, neg_neg_of_pos ht, by linarith⟩

end Poincare.Analysis
