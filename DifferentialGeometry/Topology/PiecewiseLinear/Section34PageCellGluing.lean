import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellCapTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34UntwistedCircleCellGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_untwisted_diagram_of_cyclic_page_cells
    {G : ℕ → (ℝ × ℝ) × ℝ → E} {B : ℕ → Set E} {P : Fin 4 → Set E} {J : Set E}
    {m : ℕ} (hm : 2 ≤ m)
    (hG : ∀ k ≤ m, IsPLHomeomorphOn (G k) (spliceSquare ×ˢ Icc (0 : ℝ) 1) (B k))
    (hcap : ∀ k < m, G k '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G (k + 1) '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hadj : ∀ k < m, B k ∩ B (k + 1) = G k '' (spliceSquare ×ˢ ({1} : Set ℝ)))
    (hadjc : B m ∩ B 0 = G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) → Disjoint (B j) (B k))
    (hclose : G m '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hpages : ∀ k ≤ m, ∀ i,
      G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) = B k ∩ P i)
    (hcore : ∀ k ≤ m, G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) = B k ∩ J) :
    ∃ f : (ℝ × ℝ) × ℝ → E,
      IsCylindricalDiagram f spliceSquare (⋃ k ≤ m, B k) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = G 0 (x, 0)) ∧
      (∀ i, f '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        (⋃ k ≤ m, B k) ∩ P i) ∧
      f '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) = (⋃ k ≤ m, B k) ∩ J := by
  have hadjdata (k : ℕ) (hk : k < m) :=
    splice_cap_arms_match_of_page_traces (hG k hk.le) (hG (k + 1) hk) (hcap k hk)
      (hpages k hk.le) (hpages (k + 1) hk)
  have hclosedata := splice_cap_arms_match_of_page_traces (hG m le_rfl)
    (hG 0 (Nat.zero_le m)) hclose (hpages m le_rfl) (hpages 0 (Nat.zero_le m))
  obtain ⟨f, hf, hends, hzero, hstrips, haxis⟩ :=
    exists_untwisted_diagram_of_ordered_cyclic_cells hm hG hcap
      (fun k hk => (hadjdata k hk).1) (fun k hk => (hadjdata k hk).2)
      hadj hadjc hfar hclose hclosedata.1 hclosedata.2
  refine ⟨f, hf, hends, hzero, ?_, ?_⟩
  · intro i
    rw [hstrips i]
    simp_rw [iUnion_inter]
    apply iUnion_congr
    intro k
    apply iUnion_congr
    intro hk
    exact hpages k hk i
  · rw [haxis]
    simp_rw [iUnion_inter]
    apply iUnion_congr
    intro k
    apply iUnion_congr
    intro hk
    exact hcore k hk

end DifferentialGeometry.Topology.PiecewiseLinear
