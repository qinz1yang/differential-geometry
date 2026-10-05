import DifferentialGeometry.Geometry.Exponential.Flat.UnitPoleOrbitData

/-!
The actual pole signatures restrict the cardinal of a whole free oriented lattice holonomy
group to one, two, three, four, six, eight, twelve or twenty-four. The finite orbit equations
and stabilizer orders are constructed internally; no group-cardinality classification is assumed.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem pole_three_first_two (n f0 f1 f2 d1 d2 : ℕ) (hn : 0 < n)
    (hs : f0 + f1 + f2 + 2 * (n - 1) = 3 * n)
    (hd1 : d1 = 2 ∨ d1 = 3 ∨ d1 = 4 ∨ d1 = 6)
    (hd2 : d2 = 2 ∨ d2 = 3 ∨ d2 = 4 ∨ d2 = 6)
    (hp0 : f0 * 2 = n) (hp1 : f1 * d1 = n) (hp2 : f2 * d2 = n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 24 := by
  have hs' : f0 + f1 + f2 = n + 2 := by
    clear hd1 hd2 hp0 hp1 hp2
    omega
  rcases hd1 with h1 | h1 | h1 | h1
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      have he : n = 4 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inl he)))
    · rw [h2] at hp2
      have he : n = 6 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
    · rw [h2] at hp2
      have he : n = 8 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
    · rw [h2] at hp2
      have he : n = 12 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      have he : n = 6 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
    · rw [h2] at hp2
      have he : n = 12 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))
    · rw [h2] at hp2
      have he : n = 24 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (he)))))))
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      have he : n = 8 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
    · rw [h2] at hp2
      have he : n = 24 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (he)))))))
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      have he : n = 12 := by nlinarith only [hs', hp0, hp1, hp2]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]

private theorem pole_three_first_three (n f0 f1 f2 d1 d2 : ℕ) (hn : 0 < n)
    (hs : f0 + f1 + f2 + 2 * (n - 1) = 3 * n)
    (hd1 : d1 = 2 ∨ d1 = 3 ∨ d1 = 4 ∨ d1 = 6)
    (hd2 : d2 = 2 ∨ d2 = 3 ∨ d2 = 4 ∨ d2 = 6)
    (hp0 : f0 * 3 = n) (hp1 : f1 * d1 = n) (hp2 : f2 * d2 = n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 24 := by
  have hs' : f0 + f1 + f2 = n + 2 := by
    clear hd1 hd2 hp0 hp1 hp2
    omega
  rcases hd1 with h1 | h1 | h1 | h1
  · rw [h1] at hp1
    exact pole_three_first_two n f1 f0 f2 3 d2 hn
      (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
      (Or.inr (Or.inl rfl)) hd2 hp1 hp0 hp2
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 3 3 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 3 4 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 3 6 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr (rfl)))) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]

private theorem pole_three_first_four (n f0 f1 f2 d1 d2 : ℕ) (hn : 0 < n)
    (hs : f0 + f1 + f2 + 2 * (n - 1) = 3 * n)
    (hd1 : d1 = 2 ∨ d1 = 3 ∨ d1 = 4 ∨ d1 = 6)
    (hd2 : d2 = 2 ∨ d2 = 3 ∨ d2 = 4 ∨ d2 = 6)
    (hp0 : f0 * 4 = n) (hp1 : f1 * d1 = n) (hp2 : f2 * d2 = n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 24 := by
  have hs' : f0 + f1 + f2 = n + 2 := by
    clear hd1 hd2 hp0 hp1 hp2
    omega
  rcases hd1 with h1 | h1 | h1 | h1
  · rw [h1] at hp1
    exact pole_three_first_two n f1 f0 f2 4 d2 hn
      (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
      (Or.inr (Or.inr (Or.inl rfl))) hd2 hp1 hp0 hp2
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 4 3 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 4 4 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl rfl))) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 4 6 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr (rfl)))) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]

private theorem pole_three_first_six (n f0 f1 f2 d1 d2 : ℕ) (hn : 0 < n)
    (hs : f0 + f1 + f2 + 2 * (n - 1) = 3 * n)
    (hd1 : d1 = 2 ∨ d1 = 3 ∨ d1 = 4 ∨ d1 = 6)
    (hd2 : d2 = 2 ∨ d2 = 3 ∨ d2 = 4 ∨ d2 = 6)
    (hp0 : f0 * 6 = n) (hp1 : f1 * d1 = n) (hp2 : f2 * d2 = n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 24 := by
  have hs' : f0 + f1 + f2 = n + 2 := by
    clear hd1 hd2 hp0 hp1 hp2
    omega
  rcases hd1 with h1 | h1 | h1 | h1
  · rw [h1] at hp1
    exact pole_three_first_two n f1 f0 f2 6 d2 hn
      (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
      (Or.inr (Or.inr (Or.inr (rfl)))) hd2 hp1 hp0 hp2
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 6 3 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inr (Or.inr (rfl)))) (Or.inr (Or.inl rfl)) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 6 4 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inr (Or.inr (rfl)))) (Or.inr (Or.inr (Or.inl rfl))) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
  · rw [h1] at hp1
    rcases hd2 with h2 | h2 | h2 | h2
    · rw [h2] at hp2
      exact pole_three_first_two n f2 f0 f1 6 6 hn
        (by simpa only [add_assoc, add_comm, add_left_comm] using hs)
        (Or.inr (Or.inr (Or.inr (rfl)))) (Or.inr (Or.inr (Or.inr (rfl)))) hp2 hp0 hp1
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]
    · rw [h2] at hp2
      exfalso
      nlinarith only [hs', hp0, hp1, hp2, Nat.zero_le n]

theorem pole_card_signature_cases (n k : ℕ) (hn : 0 < n) (hk : k ≤ 3) (f d : Fin k → ℕ)
    (hs : (∑ i : Fin k, f i) + 2 * (n - 1) = k * n)
    (hd : ∀ i : Fin k, d i = 2 ∨ d i = 3 ∨ d i = 4 ∨ d i = 6)
    (hp : ∀ i : Fin k, f i * d i = n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 24 := by
  interval_cases k
  · norm_num at hs
    omega
  · simp only [Fin.sum_univ_one, one_mul] at hs
    have hd0 := hd 0
    have hp0 := hp 0
    rcases hd0 with h0 | h0 | h0 | h0 <;> rw [h0] at hp0 <;> omega
  · simp only [Fin.sum_univ_two] at hs
    have hd0 := hd 0
    have hd1 := hd 1
    have hp0 := hp 0
    have hp1 := hp 1
    rcases hd0 with h0 | h0 | h0 | h0 <;>
      rcases hd1 with h1 | h1 | h1 | h1 <;> rw [h0] at hp0 <;> rw [h1] at hp1 <;> omega
  · simp only [Fin.sum_univ_three] at hs
    have hd0 := hd 0
    have hd1 := hd 1
    have hd2 := hd 2
    have hp0 := hp 0
    have hp1 := hp 1
    have hp2 := hp 2
    rcases hd0 with h0 | h0 | h0 | h0
    · rw [h0] at hp0
      exact pole_three_first_two n (f 0) (f 1) (f 2) (d 1) (d 2) hn hs hd1 hd2 hp0 hp1 hp2
    · rw [h0] at hp0
      exact pole_three_first_three n (f 0) (f 1) (f 2) (d 1) (d 2) hn hs hd1 hd2 hp0 hp1 hp2
    · rw [h0] at hp0
      exact pole_three_first_four n (f 0) (f 1) (f 2) (d 1) (d 2) hn hs hd1 hd2 hp0 hp1 hp2
    · rw [h0] at hp0
      exact pole_three_first_six n (f 0) (f 1) (f 2) (d 1) (d 2) hn hs hd1 hd2 hp0 hp1 hp2

theorem affineFree_holonomy_card_cases (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap) :
    let n := Nat.card (affineLinearHom.comp G.subtype).range
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 12 ∨ n = 24 := by
  obtain ⟨k, hk, e, hs, hdata⟩ := affineFree_unitPole_orbit_data G b hb hfree hpos
  let H := (affineLinearHom.comp G.subtype).range
  let f (i : Fin k) := Nat.card (MulAction.orbit H (e i).out)
  let d (i : Fin k) := Nat.card (MulAction.stabilizer H (e i).out)
  have hd (i : Fin k) : d i = 2 ∨ d i = 3 ∨ d i = 4 ∨ d i = 6 := (hdata i).1
  have hp (i : Fin k) : f i * d i = Nat.card H := (hdata i).2
  exact pole_card_signature_cases (Nat.card H) k Nat.card_pos hk f d hs hd hp

end DifferentialGeometry.Geometry.FlatSurface
