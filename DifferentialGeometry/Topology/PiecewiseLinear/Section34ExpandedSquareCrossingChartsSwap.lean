import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExpandedSquareCrossingCharts
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_swapped_axis_charts_of_expanded_square_paths
    {A B : Set (ℝ × ℝ)} {γ : Fin 2 → ℝ → ℝ × ℝ} {c d : ℝ}
    (hc : 0 < c) (hcd : c ≤ 2 * d)
    (hγ : ∀ k, IsPLHomeomorphOn (γ k) (Icc (-d) d) (γ k '' Icc (-d) d))
    (hγbd : ∀ k, γ k '' Icc (-d) d ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hdis : Disjoint (γ 0 '' Icc (-d) d) (γ 1 '' Icc (-d) d))
    (hA : A ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hAB : A ∩ B = {γ 0 0, γ 1 0})
    (hpos : ∀ k, γ k '' Icc 0 d ⊆ A) (hneg : ∀ k, γ k '' Icc (-d) 0 ⊆ B) :
    let ηX := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (-r / 2), r)
    let ηY := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (r / 2), r)
    let X := A ∪ (ηX 0 '' Icc 0 c ∪ ηX 1 '' Icc 0 c)
    let Y := B ∪ (ηY 0 '' Icc 0 c ∪ ηY 1 '' Icc 0 c)
    ∀ k, ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (ε : ℝ),
      0 < ε ∧ IsPLHomeomorphOn e e.source e.target ∧ e (0, 0) = γ k 0 ∧
      Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, e p ∈ X ↔ p.2 = 0) ∧
      ∀ s ∈ Ioo (-ε) ε, e (0, s) ∈ Y := by
  let γ' := fun (k : Fin 2) (t : ℝ) => γ k (-t)
  have hn : IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (-d) d) (Icc (-d) d) := by
    simpa only [neg_one_mul, add_zero] using
      isPLHomeomorphOn_mul_add_Icc_of_neg (m := (-1 : ℝ)) (c := 0)
        (a := -d) (b := d) (a' := -d) (b' := d)
        (by norm_num) (by ring) (by ring)
  have himage (k) : γ' k '' Icc (-d) d = γ k '' Icc (-d) d := by
    change (γ k ∘ fun t => -t) '' Icc (-d) d = _
    rw [image_comp, hn.image_eq]
  have hγ' (k) : IsPLHomeomorphOn (γ' k) (Icc (-d) d) (γ' k '' Icc (-d) d) := by
    rw [himage]
    exact hn.trans (hγ k)
  have hpos' (k) : γ' k '' Icc 0 d ⊆ B := by
    rintro _ ⟨t, ht, rfl⟩
    exact hneg k ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  have hneg' (k) : γ' k '' Icc (-d) 0 ⊆ A := by
    rintro _ ⟨t, ht, rfl⟩
    exact hpos k ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  have h := exists_axis_charts_of_expanded_square_paths hc hcd hγ'
    (fun k => (himage k).symm ▸ hγbd k)
    (by simpa only [himage] using hdis) hA
    (by simpa only [γ', neg_zero, inter_comm] using hAB) hpos' hneg'
  simpa only [γ', neg_zero, neg_div, neg_neg] using h

end DifferentialGeometry.Topology.PiecewiseLinear
