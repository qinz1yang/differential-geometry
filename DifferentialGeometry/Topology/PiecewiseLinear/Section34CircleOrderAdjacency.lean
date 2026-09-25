import DifferentialGeometry.Topology.PiecewiseLinear.Section34AlternatingPathMatchings

namespace Fin

theorem exists_common_adjacent_pair_of_same_parity_noninterleaving {n : ℕ}
    (hn : 1 < n) (p : Fin n ≃ Fin n)
    (hnc : ∀ i j k l : Fin n, i.val + 1 = j.val → k.val + 1 = l.val →
      i.val % 2 = k.val % 2 →
      ¬ (min (p i) (p j) < min (p k) (p l) ∧
        min (p k) (p l) < max (p i) (p j) ∧
        max (p i) (p j) < max (p k) (p l))) :
    ∃ i j : Fin n, i.val + 1 = j.val ∧
      ((p i).val + 1 = (p j).val ∨ (p j).val + 1 = (p i).val) := by
  apply exists_common_adjacent_pair_of_noncrossing_alternation hn p
  intro c a b hab hba hab'
  let x := p.symm a
  let y := alternatingNeighbor c x
  let z := p.symm b
  let w := alternatingNeighbor c z
  have hxy : p x < p y := by
    simpa only [x, y, p.apply_symm_apply] using hab.trans hba
  have hzw : p z < p w := by
    simpa only [z, w, p.apply_symm_apply] using hba.trans hab'
  have hnx : x ≠ y := fun h => hxy.ne (congrArg p h)
  have hnz : z ≠ w := fun h => hzw.ne (congrArg p h)
  have hcross : min (p x) (p y) < min (p z) (p w) ∧
      min (p z) (p w) < max (p x) (p y) ∧
      max (p x) (p y) < max (p z) (p w) := by
    rw [min_eq_left hxy.le, max_eq_right hxy.le, min_eq_left hzw.le, max_eq_right hzw.le]
    simpa only [x, y, z, w, p.apply_symm_apply] using And.intro hab (And.intro hba hab')
  rcases (alternatingNeighbor_eq_and_ne_iff c x y).mp ⟨rfl, hnx⟩ with
    ⟨hcx, hxy⟩ | ⟨hcy, hyx⟩
  · rcases (alternatingNeighbor_eq_and_ne_iff c z w).mp ⟨rfl, hnz⟩ with
      ⟨hcz, hzw⟩ | ⟨hcw, hwz⟩
    · exact hnc x y z w hxy hzw (hcx.trans hcz.symm) hcross
    · apply hnc x y w z hxy hwz (hcx.trans hcw.symm)
      simpa only [min_comm, max_comm] using hcross
  · rcases (alternatingNeighbor_eq_and_ne_iff c z w).mp ⟨rfl, hnz⟩ with
      ⟨hcz, hzw⟩ | ⟨hcw, hwz⟩
    · apply hnc y x z w hyx hzw (hcy.trans hcz.symm)
      simpa only [min_comm, max_comm] using hcross
    · apply hnc y x w z hyx hwz (hcy.trans hcw.symm)
      simpa only [min_comm, max_comm] using hcross

end Fin

namespace Equiv

theorem exists_common_adjacent_labels_of_same_parity_noninterleaving
    {α : Type*} {n : ℕ} (hn : 1 < n) (σA σB : Fin n ≃ α)
    (hnc : ∀ i j k l : Fin n, i.val + 1 = j.val → k.val + 1 = l.val →
      i.val % 2 = k.val % 2 →
      ¬ (min (σA.symm (σB i)) (σA.symm (σB j)) <
          min (σA.symm (σB k)) (σA.symm (σB l)) ∧
        min (σA.symm (σB k)) (σA.symm (σB l)) <
          max (σA.symm (σB i)) (σA.symm (σB j)) ∧
        max (σA.symm (σB i)) (σA.symm (σB j)) <
          max (σA.symm (σB k)) (σA.symm (σB l)))) :
    ∃ a₀ a₁ b₀ b₁ : Fin n, a₀.val + 1 = a₁.val ∧ b₀.val + 1 = b₁.val ∧
      ((σA a₀ = σB b₀ ∧ σA a₁ = σB b₁) ∨
        (σA a₀ = σB b₁ ∧ σA a₁ = σB b₀)) := by
  let p := σB.trans σA.symm
  obtain ⟨b₀, b₁, hb, ha | ha⟩ :=
    Fin.exists_common_adjacent_pair_of_same_parity_noninterleaving hn p hnc
  · exact ⟨p b₀, p b₁, b₀, b₁, ha, hb,
      Or.inl ⟨σA.apply_symm_apply (σB b₀), σA.apply_symm_apply (σB b₁)⟩⟩
  · exact ⟨p b₁, p b₀, b₀, b₁, ha, hb,
      Or.inr ⟨σA.apply_symm_apply (σB b₁), σA.apply_symm_apply (σB b₀)⟩⟩

end Equiv
