import DifferentialGeometry.Topology.LoopSpace.PrimitiveCircleLift
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

private theorem map_add_int_of_integer_shift {F : ℝ → ℝ} {n : ℤ}
    (hshift : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) (k : ℤ) (t : ℝ) :
    F (t + (k : ℝ)) = F t + (k : ℝ) * (n : ℝ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
      push_cast at ih ⊢
      rw [show t + ((k : ℝ) + 1) = (t + (k : ℝ)) + 1 by ring, hshift, ih]
      ring
  | pred k ih =>
      push_cast at ih ⊢
      have h := hshift (t + (-(k : ℝ) - 1))
      rw [show t + (-(k : ℝ) - 1) + 1 = t + -(k : ℝ) by ring, ih] at h
      linarith

private theorem integer_shift_eq_one_or_neg_one_of_weaklyMonotoneOnce
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (F : C(ℝ, ℝ)) (n : ℤ)
    (hlift : ∀ t : ℝ, (F t : loopCircle) = σ (t : loopCircle))
    (hshift : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) : n = 1 ∨ n = -1 := by
  obtain ⟨ψ, hψc, hψlift, hψdir⟩ := hσ
  have heq : (F : ℝ → ℝ) = fun t => ψ t + (F 0 - ψ 0) :=
    circleQuotientCovering.isCoveringMap.eq_of_comp_eq F.continuous
      (hψc.add continuous_const) (by
        funext t
        change (F t : loopCircle) = ((ψ t + (F 0 - ψ 0) : ℝ) : loopCircle)
        simp only [AddCircle.coe_add, AddCircle.coe_sub, hlift, hψlift, sub_self, add_zero])
      0 (by ring)
  have hF := hshift 0
  have h1 := congrFun heq 1
  rw [zero_add] at hF
  rcases hψdir with ⟨_, hp⟩ | ⟨_, hp⟩
  · have hψ := hp 0
    rw [zero_add] at hψ
    left
    exact_mod_cast (show (n : ℝ) = 1 by linarith)
  · have hψ := hp 0
    rw [zero_add] at hψ
    right
    exact_mod_cast (show (n : ℝ) = -1 by linarith)

theorem IsWeaklyMonotoneOnce.integer_shift_eq_one_or_neg_one_of_comp
    {τ ρ : C(loopCircle, loopCircle)} (h : IsWeaklyMonotoneOnce (τ.comp ρ))
    (F : C(ℝ, ℝ)) (n : ℤ)
    (hlift : ∀ t : ℝ, (F t : loopCircle) = ρ (t : loopCircle))
    (hshift : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) : n = 1 ∨ n = -1 := by
  obtain ⟨G, m, hGlift, hGshift⟩ := exists_real_lift_with_integer_shift τ
  have hcompLift : ∀ t : ℝ, ((G.comp F) t : loopCircle) = (τ.comp ρ) (t : loopCircle) := by
    intro t
    change (G (F t) : loopCircle) = τ (ρ (t : loopCircle))
    rw [hGlift, hlift]
  have hcompShift : ∀ t : ℝ, (G.comp F) (t + 1) = (G.comp F) t + ((n * m : ℤ) : ℝ) := by
    intro t
    change G (F (t + 1)) = G (F t) + ((n * m : ℤ) : ℝ)
    rw [hshift, map_add_int_of_integer_shift hGshift n, Int.cast_mul]
  rcases integer_shift_eq_one_or_neg_one_of_weaklyMonotoneOnce h (G.comp F) (n * m)
      hcompLift hcompShift with hprod | hprod
  · rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with ⟨hn, _⟩ | ⟨hn, _⟩
    · exact Or.inl hn
    · exact Or.inr hn
  · have hprod' : n * (-m) = 1 := by rw [mul_neg, hprod]; norm_num
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod' with ⟨hn, _⟩ | ⟨hn, _⟩
    · exact Or.inl hn
    · exact Or.inr hn

end DifferentialGeometry.Geometry
