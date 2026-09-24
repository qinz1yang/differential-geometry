import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinderSquare

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_expanded_square_of_outward_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R W : Set E}
    (hf : IsCylindricalDiagram f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f (p, 0) = f (p, 1))
    (hfront : frontier R =
      f '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1))
    {c : ℝ} (hc : 0 < c) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (frontier R ×ˢ Icc 0 c) W)
    (hzero : ∀ y ∈ frontier R, ρ (y, 0) = y) (hWR : W ∩ R = frontier R) :
    IsPLBall 2 (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) ∧
      ∃ G : (ℝ × ℝ) × ℝ → E,
        IsCylindricalDiagram G (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) (R ∪ W) ∧
        (∀ p ∈ Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c), G (p, 0) = G (p, 1)) ∧
        EqOn G f ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) ∧
        (∀ p ∈ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
          ∀ t ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
            G (section34SquareShellFlatten c (p, t), s) = ρ (f (p, s), t)) := by
  classical
  obtain ⟨hD, G, hG, hGends, hGbase, hGside⟩ :=
    hf.exists_enlargement_by_outward_collar isPLBall_unit_square (by simp)
      hends hfront hc hρ hzero hWR
  let P := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let D := P ×ˢ {(0 : ℝ)} ∪ frontier P ×ˢ Icc 0 c
  let σ := section34SquareShellFlatten c
  let τ := Function.invFunOn σ D
  have hσ := isPLHomeomorphOn_section34SquareShellFlatten hc
  have hτ : IsPLHomeomorphOn τ (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) D := hσ.symm
  have hinv {z : (ℝ × ℝ) × ℝ} (hz : z ∈ D) : τ (σ z) = z :=
    hσ.bijOn.invOn_invFunOn.1 hz
  refine ⟨hD.of_isPLHomeomorphOn hσ, G ∘ Prod.map τ id,
    hG.precomp_base_equivalence hτ, ?_, ?_, ?_⟩
  · intro p hp
    exact hGends (τ p) (hτ.bijOn.mapsTo hp)
  · rintro ⟨p, s⟩ ⟨hp, hs⟩
    have hτp : τ p = (p, 0) := by
      have hi := hinv (Or.inl ⟨hp, rfl⟩ : (p, (0 : ℝ)) ∈ D)
      rw [show σ (p, 0) = p from section34_square_shell_flatten_zero hc.le hp] at hi
      exact hi
    change G (τ p, s) = f (p, s)
    rw [hτp]
    exact hGbase p hp s hs
  · intro p hp t ht s hs
    change G (τ (σ (p, t)), s) = ρ (f (p, s), t)
    rw [hinv (Or.inr ⟨hp, ht⟩)]
    exact hGside p hp t ht s hs

end DifferentialGeometry.Topology.PiecewiseLinear
