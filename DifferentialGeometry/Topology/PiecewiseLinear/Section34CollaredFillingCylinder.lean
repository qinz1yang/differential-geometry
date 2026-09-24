import DifferentialGeometry.Topology.PiecewiseLinear.CollarGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RegularCircleCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsCylindricalDiagram.prod_collaring_interval
    {f : A × ℝ → E} {P : Set A} {S : Set E}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hends : ∀ p ∈ P, f (p, 0) = f (p, 1)) (a b : ℝ) :
    IsCylindricalDiagram (fun z : (A × ℝ) × ℝ => (f (z.1.1, z.2), z.1.2))
      (P ×ˢ Icc a b) (S ×ˢ Icc a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let L : ((A × ℝ) × ℝ) →ₗ[ℝ] (A × ℝ) × ℝ :=
      { toFun := fun z => ((z.1.1, z.2), z.1.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hpoly : IsPolyhedron ((P ×ˢ Icc a b) ×ˢ Icc (0 : ℝ) 1) :=
      (hP.prod isHPolytope_Icc.isPolyhedron).prod isHPolytope_Icc.isPolyhedron
    have hL := (isPiecewiseAffineOn_of_affine L.toAffineMap isOpen_univ).mono_of_isPolyhedron
      hpoly (subset_univ _)
    have hid := (isHPolytope_Icc (a := a) (b := b)).isPolyhedron.isPLHomeomorphOn_id
    have hcomp := (hf.isPiecewiseAffineOn.prodMap hid.isPiecewiseAffineOn).comp hL
    have hmaps : MapsTo L ((P ×ˢ Icc a b) ×ˢ Icc (0 : ℝ) 1)
        ((P ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc a b) :=
      fun _ hz => ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩
    change IsPiecewiseAffineOn (Prod.map f id ∘ L)
      (((P ×ˢ Icc a b) ×ˢ Icc (0 : ℝ) 1) ∩
        L ⁻¹' ((P ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc a b)) at hcomp
    exact hcomp.mono_of_isPolyhedron hpoly (fun _ hz => ⟨hz, hmaps hz⟩)
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨hf.image_eq ▸ mem_image_of_mem f ⟨hz.1.1, hz.2⟩, hz.1.2⟩
    · rintro ⟨y, t⟩ ⟨hy, ht⟩
      obtain ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩ := hf.image_eq.symm.subset hy
      exact ⟨((p, t), s), ⟨⟨hp, ht⟩, hs⟩, rfl⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨⟨p, t⟩, s⟩, ⟨⟨hp, ht⟩, hs⟩, rfl⟩
      change s = 1 at hs
      subst s
      exact ⟨((p, t), 0), ⟨⟨hp, ht⟩, rfl⟩, Prod.ext (hends p hp) rfl⟩
    · rintro _ ⟨⟨⟨p, t⟩, s⟩, ⟨⟨hp, ht⟩, hs⟩, rfl⟩
      change s = 0 at hs
      subst s
      exact ⟨((p, t), 1), ⟨⟨hp, ht⟩, rfl⟩, Prod.ext (hends p hp).symm rfl⟩
  · intro z hz w hw hzw
    have ht := congrArg Prod.snd hzw
    rcases hf.eq_or_endpoints (z.1.1, z.2) ⟨hz.1.1, hz.2⟩
        (w.1.1, w.2) ⟨hw.1.1, hw.2⟩ (congrArg Prod.fst hzw) with h | h | h
    · have hp := congrArg (fun v : A × ℝ => v.1) h
      have hs := congrArg (fun v : A × ℝ => v.2) h
      exact Or.inl (Prod.ext (Prod.ext hp ht) hs)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem IsPLBall.isPLBall_bottom_union_frontier
    {P : Set A} (hP : IsPLBall 2 P) (hdim : Module.finrank ℝ A = 2)
    {a b : ℝ} (hab : a < b) :
    IsPLBall 2 (P ×ˢ {a} ∪ frontier P ×ˢ Icc a b) := by
  classical
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
  rw [← hKP, frontier_space_eq_boundaryComplex_space_of_finrank (n := 1) hdim K
    hK.isCombinatorialManifoldWithBoundary]
  exact isPLBall_prism_bottom_union_side K hK hab

private theorem cylinder_image_polyhedron [FiniteDimensional ℝ E]
    {f : A × ℝ → E} {P : Set A} {S : Set E}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P) : IsPolyhedron S := by
  have h₀ := hf.isPLHomeomorphOn_strip hP (a := 0) (b := 1 / 2)
    le_rfl (by norm_num) (Or.inr (by norm_num))
  have h₁ := hf.isPLHomeomorphOn_strip hP (a := 1 / 2) (b := 1)
    (by norm_num) le_rfl (Or.inl (by norm_num))
  rw [← hf.image_strip_union (a := 1 / 2) (by norm_num)]
  exact ((hP.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
    h₀.isPiecewiseAffineOn h₀.bijOn.injOn).union
    ((hP.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      h₁.isPiecewiseAffineOn h₁.bijOn.injOn)

theorem IsCylindricalDiagram.exists_enlargement_by_outward_collar [FiniteDimensional ℝ E]
    {f : A × ℝ → E} {P : Set A} {R W : Set E}
    (hf : IsCylindricalDiagram f P R) (hP : IsPLBall 2 P)
    (hdim : Module.finrank ℝ A = 2) (hends : ∀ p ∈ P, f (p, 0) = f (p, 1))
    (hfront : frontier R = f '' (frontier P ×ˢ Icc (0 : ℝ) 1))
    {c : ℝ} (hc : 0 < c) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (frontier R ×ˢ Icc 0 c) W)
    (hzero : ∀ y ∈ frontier R, ρ (y, 0) = y) (hWR : W ∩ R = frontier R) :
    let D := P ×ˢ {(0 : ℝ)} ∪ frontier P ×ˢ Icc 0 c
    IsPLBall 2 D ∧ ∃ G : (A × ℝ) × ℝ → E,
      IsCylindricalDiagram G D (R ∪ W) ∧
      (∀ z ∈ D, G (z, 0) = G (z, 1)) ∧
      (∀ p ∈ P, ∀ s ∈ Icc (0 : ℝ) 1, G ((p, 0), s) = f (p, s)) ∧
      (∀ p ∈ frontier P, ∀ t ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
        G ((p, t), s) = ρ (f (p, s), t)) := by
  classical
  dsimp only
  let D := P ×ˢ {(0 : ℝ)} ∪ frontier P ×ˢ Icc 0 c
  have hD : IsPLBall 2 D := hP.isPLBall_bottom_union_frontier hdim hc
  have hR := cylinder_image_polyhedron hf hP.isPolyhedron
  have hBP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  have hB : IsPolyhedron (frontier P) := by
    obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
    let _ : Finite K.faces := hKfin.to_subtype
    have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
    rw [← hKP, frontier_space_eq_boundaryComplex_space_of_finrank (n := 1) hdim K
      hK.isCombinatorialManifoldWithBoundary]
    exact isPolyhedron_space _
  have hBR : IsPolyhedron (frontier R) := by
    rw [hfront]
    exact cylinder_image_polyhedron (hf.restrict_base_of_eq_ends hB hBP hends) hB
  have hRfront : R ∩ frontier R = frontier R :=
    inter_eq_right.mpr hR.isClosed.frontier_subset
  obtain ⟨H, hH, hHbase, hHside⟩ := exists_isPLHomeomorphOn_bottom_union_collar_sides
    hBR hR Subset.rfl hc hρ hzero hWR
  rw [hRfront, hρ.image_eq] at hH
  rw [hRfront] at hHside
  let m : (A × ℝ) × ℝ → E × ℝ := fun z => (f (z.1.1, z.2), z.1.2)
  have hDP : D ⊆ P ×ˢ Icc (0 : ℝ) c := by
    rintro z (hz | hz)
    · refine ⟨hz.1, ?_⟩
      rw [show z.2 = 0 from hz.2]
      exact ⟨le_rfl, hc.le⟩
    · exact ⟨hBP hz.1, hz.2⟩
  have hm := (hf.prod_collaring_interval hP.isPolyhedron hends 0 c).restrict_base_of_eq_ends
    hD.isPolyhedron hDP (fun z hz => Prod.ext (hends z.1 hz.1) rfl)
  have himage : m '' (D ×ˢ Icc (0 : ℝ) 1) =
      R ×ˢ {(0 : ℝ)} ∪ frontier R ×ˢ Icc 0 c := by
    apply Subset.antisymm
    · rintro _ ⟨⟨⟨p, t⟩, s⟩, ⟨hp | hp, hs⟩, rfl⟩
      · exact Or.inl ⟨hf.image_eq ▸ mem_image_of_mem f ⟨hp.1, hs⟩, hp.2⟩
      · exact Or.inr ⟨hfront ▸ mem_image_of_mem f ⟨hp.1, hs⟩, hp.2⟩
    · rintro ⟨y, t⟩ (hy | hy)
      · obtain ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩ := hf.image_eq.symm.subset hy.1
        exact ⟨((p, t), s), ⟨Or.inl ⟨hp, hy.2⟩, hs⟩, rfl⟩
      · obtain ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩ := hfront.subset hy.1
        exact ⟨((p, t), s), ⟨Or.inr ⟨hp, hy.2⟩, hs⟩, rfl⟩
  change IsCylindricalDiagram m D (m '' (D ×ˢ Icc (0 : ℝ) 1)) at hm
  rw [himage] at hm
  refine ⟨hD, H ∘ m, hm.postcomp_equivalence hH, ?_, ?_, ?_⟩
  · intro z hz
    exact congrArg H (Prod.ext (hends z.1 (hDP hz).1) rfl)
  · intro p hp s hs
    exact hHbase ⟨hf.image_eq ▸ mem_image_of_mem f ⟨hp, hs⟩, rfl⟩
  · intro p hp t ht s hs
    exact hHside ⟨hfront ▸ mem_image_of_mem f ⟨hp, hs⟩, ht⟩

end DifferentialGeometry.Topology.PiecewiseLinear
