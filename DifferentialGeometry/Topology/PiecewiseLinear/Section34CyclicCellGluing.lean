import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCyclicDiagram

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_marked_cylindrical_diagram_of_cyclic_cells
    {G : ℕ → (ℝ × ℝ) × ℝ → E} {B : ℕ → Set E} {m : ℕ} (hm : 2 ≤ m)
    (hG : ∀ k ≤ m, IsPLHomeomorphOn (G k) (spliceSquare ×ˢ Icc (0 : ℝ) 1) (B k))
    (hcap : ∀ k < m, G k '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G (k + 1) '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (harm : ∀ k < m, ∀ i,
      G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G (k + 1) '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)))
    (hpt : ∀ k < m, ∀ i, G k (fourSpokeModelLeaf i, 1) = G (k + 1) (fourSpokeModelLeaf i, 0))
    (hadj : ∀ k < m, B k ∩ B (k + 1) = G k '' (spliceSquare ×ˢ ({1} : Set ℝ)))
    (hadjc : B m ∩ B 0 = G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) → Disjoint (B j) (B k))
    (hclose : G m '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (harmclose : ∀ i,
      G m '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G 0 '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)))
    (hptclose : ∀ i, G m (fourSpokeModelLeaf i, 1) = G 0 (fourSpokeModelLeaf i, 0)) :
    ∃ (φ : (ℝ × ℝ) × ℝ → E) (u : ℝ × ℝ → ℝ × ℝ),
      IsCylindricalDiagram φ spliceSquare (⋃ k ≤ m, B k) ∧
      IsPLHomeomorphOn u spliceSquare spliceSquare ∧
      (∀ x ∈ spliceSquare, φ (x, 0) = φ (u x, 1)) ∧ u 0 = 0 ∧
      (∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf i) ∧
      (∀ i, u '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)) ∧
      (∀ x ∈ spliceSquare, φ (x, 0) = G 0 (x, 0)) ∧
      (∀ i, φ '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m, G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m, G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) := by
  let n := m - 1
  have hn : n + 1 = m := by dsimp [n]; omega
  have hnlt : n < m := by omega
  have hlast : (⋃ k ≤ n, B k) ∩ B (n + 1) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)) ∪
        G n '' (spliceSquare ×ˢ ({1} : Set ℝ)) := by
    rw [hn]
    apply Subset.antisymm
    · rintro x ⟨hx, hxm⟩
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      by_cases hk0 : k = 0
      · exact Or.inl (hadjc.subset ⟨hxm, hk0 ▸ hxk⟩)
      by_cases hkn : k = n
      · apply Or.inr
        have hx : x ∈ B n ∩ B (n + 1) := ⟨hkn ▸ hxk, hn.symm ▸ hxm⟩
        exact (hadj n hnlt).subset hx
      exact False.elim (disjoint_left.mp (hfar k m (by omega) le_rfl (Or.inl hk0)) hxk hxm)
    · intro x hx
      rcases hx with hx | hx
      · have h := hadjc.symm.subset hx
        exact ⟨mem_iUnion₂.mpr ⟨0, Nat.zero_le n, h.2⟩, h.1⟩
      · have h := (hadj n hnlt).symm.subset hx
        exact ⟨mem_iUnion₂.mpr ⟨n, le_rfl, h.1⟩, hn ▸ h.2⟩
  obtain ⟨φ, u, hφ, hu, hφu, hleaves, hspokes, hφ0, -, -, hstrips, hcore⟩ :=
    exists_marked_cylindrical_diagram_of_chain n
      (fun k hk => hG k (hn ▸ hk))
      (fun k hk => hcap k (by omega)) (fun k hk => harm k (by omega))
      (fun k hk => hpt k (by omega)) (fun k hk => hadj k (by omega))
      (fun j k hjk hk => hfar j k hjk (by omega) (Or.inr (by omega)))
      hlast (hn.symm ▸ hclose) (fun i => hn.symm ▸ harmclose i)
      (σ := id) (fun i => hn.symm ▸ hptclose i)
  rw [hn] at hφ hstrips hcore
  exact ⟨φ, u, hφ, hu, hφu, eq_zero_of_image_segment_fourSpokeModelLeaf hspokes,
    hleaves, hspokes, hφ0, hstrips, hcore⟩

end DifferentialGeometry.Topology.PiecewiseLinear
