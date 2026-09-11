import DifferentialGeometry.Topology.Manifold.HalfLine

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Topology.Manifold

variable {E F H G B M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace M]
  [ChartedSpace H B] [ChartedSpace G M]
  {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}

theorem exists_collar_interior_coordinates
    (c : PartialDiffeomorph (J.prod (𝓡∂ 1)) I (B × EuclideanHalfSpace 1) M ∞)
    {K : Set B} {ε : ℝ}
    (hc : c.source = K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε}) :
    ∃ d : PartialDiffeomorph (J.prod 𝓘(ℝ)) I (B × ℝ) M ∞,
      d.source = K ×ˢ Ioo 0 ε ∧
      d.target = c.target ∩ {y : M | 0 < (c.symm y).2.1 0} ∧
      (∀ z, d z = c (z.1, halfSpaceOneLift z.2)) ∧
      ∀ y, d.symm y = ((c.symm y).1, (c.symm y).2.1 0) := by
  let t := halfSpaceOneInteriorDiffeomorph
  let e := (OpenPartialHomeomorph.refl B).prod t.toOpenPartialHomeomorph
  let p : PartialDiffeomorph (J.prod 𝓘(ℝ)) (J.prod (𝓡∂ 1))
      (B × ℝ) (B × EuclideanHalfSpace 1) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_fst.prodMk
        (t.contMDiffOn.comp contMDiffOn_snd (fun _ hz ↦ hz.2))
      contMDiffOn_invFun := contMDiffOn_fst.prodMk
        (t.symm.contMDiffOn.comp contMDiffOn_snd (fun _ hz ↦ hz.2)) }
  let d := p.trans c
  refine ⟨d, ?_, ?_, (fun _ ↦ rfl), (fun _ ↦ rfl)⟩
  · ext z
    change ((z.1 ∈ univ ∧ 0 < z.2) ∧ (z.1, halfSpaceOneLift z.2) ∈ c.source) ↔
      z.1 ∈ K ∧ z.2 ∈ Ioo 0 ε
    rw [hc]
    change ((True ∧ 0 < z.2) ∧ z.1 ∈ K ∧ max z.2 0 < ε) ↔
      z.1 ∈ K ∧ 0 < z.2 ∧ z.2 < ε
    constructor
    · rintro ⟨⟨_, ht⟩, hx, hr⟩
      exact ⟨hx, ht, by simpa only [max_eq_left ht.le] using hr⟩
    · rintro ⟨hx, ht, hr⟩
      exact ⟨⟨trivial, ht⟩, hx, by simpa only [max_eq_left ht.le] using hr⟩
  · ext y
    change (y ∈ c.target ∧ (c.symm y).1 ∈ univ ∧ 0 < (c.symm y).2.1 0) ↔
      y ∈ c.target ∧ 0 < (c.symm y).2.1 0
    simp only [mem_univ, true_and]

end DifferentialGeometry.Geometry.Boundary
