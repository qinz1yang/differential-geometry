import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExteriorCollarCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinderSquare
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PlanarDiskBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_axis_charts_of_expanded_square_paths
    {A B : Set (ℝ × ℝ)} {γ : Fin 2 → ℝ → ℝ × ℝ} {c d : ℝ}
    (hc : 0 < c) (hcd : c ≤ 2 * d)
    (hγ : ∀ k, IsPLHomeomorphOn (γ k) (Icc (-d) d) (γ k '' Icc (-d) d))
    (hγbd : ∀ k, γ k '' Icc (-d) d ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hdis : Disjoint (γ 0 '' Icc (-d) d) (γ 1 '' Icc (-d) d))
    (hB : B ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hAB : A ∩ B = {γ 0 0, γ 1 0})
    (hpos : ∀ k, γ k '' Icc 0 d ⊆ A) (hneg : ∀ k, γ k '' Icc (-d) 0 ⊆ B) :
    let ηX := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (-r / 2), r)
    let ηY := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (r / 2), r)
    let X := A ∪ (ηX 0 '' Icc 0 c ∪ ηX 1 '' Icc 0 c)
    let Y := B ∪ (ηY 0 '' Icc 0 c ∪ ηY 1 '' Icc 0 c)
    ∀ k, ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (ε : ℝ),
      0 < ε ∧ IsPLHomeomorphOn e e.source e.target ∧ e (0, 0) = γ k 0 ∧
      Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, e p ∈ Y ↔ p.2 = 0) ∧
      ∀ s ∈ Ioo (-ε) ε, e (0, s) ∈ X := by
  let P := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let ρ := section34SquareShellFlatten c
  let W := ρ '' (frontier P ×ˢ Icc 0 c)
  have hP : IsPLBall 2 P := isPLBall_unit_square
  obtain ⟨q, hq⟩ := hP
  have hfront : q '' stdSimplexBoundary 2 = frontier P :=
    hq.image_stdSimplexBoundary_eq_frontier_real_prod
  have hBD : frontier P ⊆ P := (isClosed_Icc.prod isClosed_Icc).frontier_subset
  have hf := isPLHomeomorphOn_section34SquareShellFlatten hc
  have hBDpoly : IsPolyhedron (frontier P) := by
    rw [← hfront]
    exact hq.isPLSphere_image_stdSimplexBoundary.isPolyhedron
  have hρ : IsPLHomeomorphOn ρ (frontier P ×ˢ Icc 0 c) W :=
    hf.restrict (hBDpoly.prod isHPolytope_Icc.isPolyhedron) subset_union_right
  have hzero (x) (hx : x ∈ frontier P) : ρ (x, 0) = x :=
    section34_square_shell_flatten_zero hc.le (hBD hx)
  have hWD : W ∩ P = frontier P := by
    apply Subset.antisymm
    · rintro x ⟨⟨⟨p, r⟩, ⟨hp, hr⟩, heq⟩, hx⟩
      have hx0 : (x, (0 : ℝ)) ∈ P ×ˢ {(0 : ℝ)} := ⟨hx, rfl⟩
      have heq' := hf.bijOn.injOn (Or.inr ⟨hp, hr⟩) (Or.inl hx0)
        (heq.trans (section34_square_shell_flatten_zero hc.le hx).symm)
      have hpx : p = x := congrArg Prod.fst heq'
      exact hpx ▸ hp
    · intro x hx
      exact ⟨⟨(x, 0), ⟨hx, le_rfl, hc.le⟩, hzero x hx⟩, hBD hx⟩
  have hpair : Pairwise fun i j => Disjoint (γ i '' Icc (-d) d) (γ j '' Icc (-d) d) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  have h := exists_axis_charts_of_exterior_collar_paths hq hc hcd hγ
    (fun k => hfront.symm ▸ hγbd k) hpair (hfront.symm ▸ hB) hAB hpos hneg
    (hfront.symm ▸ hρ) (fun x hx => hzero x (hfront ▸ hx)) (hWD.trans hfront.symm)
  have hunion (T : Fin 2 → Set (ℝ × ℝ)) : (⋃ k, T k) = T 0 ∪ T 1 := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨k, hk⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr hk
    · rintro (hx | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
  simpa only [hunion, ρ] using h

end DifferentialGeometry.Topology.PiecewiseLinear
