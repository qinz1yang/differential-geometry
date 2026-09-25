import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedLateralStraightening

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_prism_straightening_of_full_arc_family
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {γ : (boundaryComplex 2 D).space → ℝ → E × ℝ}
    (hdis : Pairwise (fun x y => Disjoint (γ x '' Icc 0 1) (γ y '' Icc 0 1)))
    (hcover : (⋃ x, γ x '' Icc 0 1) = (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)
    (hγ : ∀ x, IsPLHomeomorphOn (γ x) (Icc 0 1) (γ x '' Icc 0 1) ∧
      γ x 0 = ((x : E), 0) ∧ γ x 1 = ((x : E), 1) ∧
      γ x '' Icc 0 1 ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
      (γ x '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) =
        {((x : E), 0)} ∧
      (γ x '' Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({1} : Set ℝ)) =
        {((x : E), 1)})
    {x y : (boundaryComplex 2 D).space} (hxy : x ≠ y) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (D.space ×ˢ Icc (0 : ℝ) 1) (D.space ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn Φ id (D.space ×ˢ ({0, 1} : Set ℝ)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, Φ ((x : E), t) = γ x t ∧ Φ ((y : E), t) = γ y t := by
  obtain ⟨r, hr⟩ := hD
  have hbd := hr.image_stdSimplexBoundary_eq_boundaryComplex D rfl
  have hstraight := @exists_lateral_straightening_of_spanning_family E _ _ _ D.space r hr
  rw [hbd] at hstraight
  obtain ⟨H, hH, hfix, hmap⟩ := hstraight
    (fun z => ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn (hγ z).1).isConnected.isPreconnected)
    (fun z => (hγ z).2.2.2.1) (fun z => (hγ z).2.2.2.2.1)
    (fun z => (hγ z).2.2.2.2.2) hdis hcover hxy (hγ x).1 (hγ y).1
    (hγ x).2.1 (hγ x).2.2.1 (hγ y).2.1 (hγ y).2.2.1
  obtain ⟨Φ, hΦ, hΦH, hΦfix⟩ :=
    exists_prism_extension_fixed_caps_of_lateral_map D ⟨r, hr⟩ hH hfix
  exact ⟨Φ, hΦ, hΦfix, fun t ht =>
    ⟨(hΦH ⟨x.2, ht⟩).trans (hmap t ht).1,
      (hΦH ⟨y.2, ht⟩).trans (hmap t ht).2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
