import DifferentialGeometry.Topology.PiecewiseLinear.Section34CyclicCellGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34UntwistedCrossingDiagram

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_untwisted_diagram_of_ordered_cyclic_cells
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
    ∃ f : (ℝ × ℝ) × ℝ → E,
      IsCylindricalDiagram f spliceSquare (⋃ k ≤ m, B k) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = G 0 (x, 0)) ∧
      (∀ i, f '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m, G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1)) ∧
      f '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ k ≤ m, G k '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨g, u, hg, hu, hends, -, hleaves, hspokes, hg0, hgT, hgcore⟩ :=
    exists_marked_cylindrical_diagram_of_cyclic_cells hm hG hcap harm hpt hadj hadjc hfar
      hclose harmclose hptclose
  obtain ⟨f, hf, hfends, hf0, hfT, hfcore, -⟩ :=
    hg.exists_untwisted_four_spoke_diagram hu hends hspokes hleaves
  refine ⟨f, hf, hfends, fun x hx => (hf0 x hx).trans (hg0 x hx),
    fun i => (hfT i).trans (hgT i), ?_⟩
  have heq : EqOn f g (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) := by
    rintro ⟨x, t⟩ ⟨rfl, ht⟩
    exact hfcore t ht
  exact heq.image_eq.trans hgcore

end DifferentialGeometry.Topology.PiecewiseLinear
