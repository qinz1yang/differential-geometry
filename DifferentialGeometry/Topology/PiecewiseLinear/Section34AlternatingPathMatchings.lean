import DifferentialGeometry.Topology.PiecewiseLinear.Section34AlternatingBandAdjacency

namespace Fin

def alternatingNeighbor {n : ℕ} (c : Fin 2) (i : Fin n) : Fin n :=
  if i.val % 2 = c.val then
    if hi : i.val + 1 < n then ⟨i.val + 1, hi⟩ else i
  else
    if hi : 0 < i.val then ⟨i.val - 1, by omega⟩ else i

theorem alternatingNeighbor_fixed_iff {n : ℕ} (c : Fin 2) (i : Fin n) :
    alternatingNeighbor c i = i ↔
      (i.val = 0 ∧ c.val = 1) ∨ (i.val + 1 = n ∧ i.val % 2 = c.val) := by
  have hi := i.isLt
  have hc := c.isLt
  simp only [alternatingNeighbor, Fin.ext_iff]
  split_ifs <;> (try dsimp) <;> omega

theorem alternatingNeighbor_eq_or_adjacent {n : ℕ} (c : Fin 2) (i : Fin n) :
    alternatingNeighbor c i = i ∨ (alternatingNeighbor c i).val = i.val + 1 ∨
      i.val = (alternatingNeighbor c i).val + 1 := by
  simp only [alternatingNeighbor, Fin.ext_iff]
  split_ifs <;> (try dsimp) <;> omega

theorem involutive_alternatingNeighbor {n : ℕ} (c : Fin 2) :
    Function.Involutive (alternatingNeighbor (n := n) c) := by
  intro i
  apply Fin.ext
  simp only [alternatingNeighbor]
  split_ifs <;> dsimp at * <;> omega

theorem alternatingNeighbor_eq_and_ne_iff {n : ℕ} (c : Fin 2) (i j : Fin n) :
    alternatingNeighbor c i = j ∧ i ≠ j ↔
      (i.val % 2 = c.val ∧ i.val + 1 = j.val) ∨
        (j.val % 2 = c.val ∧ j.val + 1 = i.val) := by
  have hi := i.isLt
  have hj := j.isLt
  have hc := c.isLt
  simp only [alternatingNeighbor, Fin.ext_iff, ne_eq]
  split_ifs <;> (try dsimp) <;> omega

theorem exists_common_adjacent_pair_of_noncrossing_alternation {n : ℕ}
    (hn : 1 < n) (p : Fin n ≃ Fin n)
    (hnc : ∀ (c : Fin 2) (a b : Fin n), a < b →
      b < p (alternatingNeighbor c (p.symm a)) →
      p (alternatingNeighbor c (p.symm a)) <
        p (alternatingNeighbor c (p.symm b)) → False) :
    ∃ i j : Fin n, i.val + 1 = j.val ∧
      ((p i).val + 1 = (p j).val ∨ (p j).val + 1 = (p i).val) := by
  let f (c : Fin 2) (a : Fin n) := p (alternatingNeighbor c (p.symm a))
  have hinv (c : Fin 2) : Function.Involutive (f c) := by
    intro a
    dsimp only [f]
    rw [p.symm_apply_apply, involutive_alternatingNeighbor c, p.apply_symm_apply]
  have hfinish (c : Fin 2) (a : Fin n) (ha : (f c a).val = a.val + 1) :
      ∃ i j : Fin n, i.val + 1 = j.val ∧
        ((p i).val + 1 = (p j).val ∨ (p j).val + 1 = (p i).val) := by
    let i := p.symm a
    let j := alternatingNeighbor c i
    have hij : (p j).val = (p i).val + 1 := by
      simpa only [i, j, f, p.apply_symm_apply] using ha
    rcases alternatingNeighbor_eq_or_adjacent c i with h | h | h
    · have hpi := congrArg (fun z => (p z).val) h
      change (p j).val = (p i).val at hpi
      omega
    · exact ⟨i, j, h.symm, Or.inl hij.symm⟩
    · exact ⟨j, i, h.symm, Or.inr hij.symm⟩
  by_cases heven : n % 2 = 0
  · have hfree (a : Fin n) : f 0 a ≠ a := by
      intro ha
      have h := congrArg p.symm ha
      dsimp only [f] at h
      rw [p.symm_apply_apply] at h
      have hfixed := (alternatingNeighbor_fixed_iff 0 (p.symm a)).mp h
      have hi := (p.symm a).isLt
      simp only [Fin.val_zero] at hfixed
      omega
    obtain ⟨a, ha⟩ := exists_adjacent_pair_of_fixed_point_free_noncrossing_involution
      (by omega) (hinv 0) (hnc 0) hfree
    exact hfinish 0 a ha
  have hodd : n % 2 = 1 := by omega
  have hfix₀ (a : Fin n) (ha : f 0 a = a) : (p.symm a).val + 1 = n := by
    have h := congrArg p.symm ha
    dsimp only [f] at h
    rw [p.symm_apply_apply] at h
    have hfixed := (alternatingNeighbor_fixed_iff 0 (p.symm a)).mp h
    simp only [Fin.val_zero] at hfixed
    omega
  have hfix₁ (a : Fin n) (ha : f 1 a = a) : (p.symm a).val = 0 := by
    have h := congrArg p.symm ha
    dsimp only [f] at h
    rw [p.symm_apply_apply] at h
    have hfixed := (alternatingNeighbor_fixed_iff 1 (p.symm a)).mp h
    change ((p.symm a).val = 0 ∧ 1 = 1) ∨
      ((p.symm a).val + 1 = n ∧ (p.symm a).val % 2 = 1) at hfixed
    omega
  have huniq₀ (a b : Fin n) (ha : f 0 a = a) (hb : f 0 b = b) : a = b := by
    apply p.symm.injective
    apply Fin.ext
    have h₀ := hfix₀ a ha
    have h₁ := hfix₀ b hb
    omega
  have huniq₁ (a b : Fin n) (ha : f 1 a = a) (hb : f 1 b = b) : a = b := by
    apply p.symm.injective
    apply Fin.ext
    rw [hfix₁ a ha, hfix₁ b hb]
  have hne : f 0 ≠ f 1 := by
    intro h
    let z : Fin n := ⟨0, by omega⟩
    have hz : alternatingNeighbor 1 z = z :=
      (alternatingNeighbor_fixed_iff 1 z).mpr (Or.inl ⟨rfl, rfl⟩)
    have h₁ : f 1 (p z) = p z := by
      dsimp only [f]
      rw [p.symm_apply_apply, hz]
    have h₀ : f 0 (p z) = p z := h ▸ h₁
    have hh := hfix₀ (p z) h₀
    rw [p.symm_apply_apply] at hh
    change 0 + 1 = n at hh
    omega
  obtain ⟨a, ha | ha⟩ := exists_adjacent_pair_of_distinct_noncrossing_involutions
    (hinv 0) (hinv 1) (hnc 0) (hnc 1) huniq₀ huniq₁ hne
  · exact hfinish 0 a ha
  · exact hfinish 1 a ha

end Fin
