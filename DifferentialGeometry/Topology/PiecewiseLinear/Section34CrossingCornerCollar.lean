import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollarModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalAnnuli

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem cylinder_prod_interval
    {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : A × ℝ → E} {P : Set A} {S : Set E}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P)
    (hends : ∀ p ∈ P, f (p, 0) = f (p, 1)) :
    IsCylindricalDiagram (fun z : (A × ℝ) × ℝ => (f (z.1.1, z.2), z.1.2))
      (P ×ˢ Icc (0 : ℝ) 1) (S ×ˢ Icc (0 : ℝ) 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let L : ((A × ℝ) × ℝ) →ₗ[ℝ] (A × ℝ) × ℝ :=
      { toFun := fun z => ((z.1.1, z.2), z.1.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hpoly : IsPolyhedron ((P ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) :=
      (hP.prod isHPolytope_Icc.isPolyhedron).prod isHPolytope_Icc.isPolyhedron
    have hL := (isPiecewiseAffineOn_of_affine L.toAffineMap isOpen_univ).mono_of_isPolyhedron
      hpoly (subset_univ _)
    have hid := (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron.isPLHomeomorphOn_id
    have hcomp := (hf.isPiecewiseAffineOn.prodMap hid.isPiecewiseAffineOn).comp hL
    have hmaps : MapsTo L ((P ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1)
        ((P ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) :=
      fun _ hz => ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩
    change IsPiecewiseAffineOn (Prod.map f id ∘ L)
      (((P ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) ∩
        L ⁻¹' ((P ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1)) at hcomp
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

theorem IsCylindricalDiagram.exists_collar_of_base_embedding
    {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : A × ℝ → E} {P L Q : Set A} {C : Set E} (hf : IsCylindricalDiagram f P C)
    (hends : ∀ p ∈ P, f (p, 0) = f (p, 1)) (hL : IsPolyhedron L) (hLP : L ⊆ P)
    {ψ : A × ℝ → A} (hψ : IsPLHomeomorphOn ψ (L ×ˢ Icc (0 : ℝ) 1) Q)
    (hQP : Q ⊆ P) (hψzero : ∀ p ∈ L, ψ (p, 0) = p) :
    ∃ ρ : E × ℝ → E,
      IsPLHomeomorphOn ρ ((f '' (L ×ˢ Icc (0 : ℝ) 1)) ×ˢ Icc (0 : ℝ) 1)
        (f '' (Q ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ y ∈ f '' (L ×ˢ Icc (0 : ℝ) 1), ρ (y, 0) = y) ∧
      (∀ p ∈ L, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ρ (f (p, s), t) = f (ψ (p, t), s)) ∧
      f '' (Q ×ˢ Icc (0 : ℝ) 1) ⊆ C := by
  have hQ : IsPolyhedron Q := by
    rw [← hψ.image_eq]
    exact (hL.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hψ.isPiecewiseAffineOn hψ.bijOn.injOn
  have hmod := cylinder_prod_interval (hf.restrict_base_of_eq_ends hL hLP hends) hL
    (fun p hp => hends p (hLP hp))
  have hmove := (hf.restrict_base_of_eq_ends hQ hQP hends).precomp_base_equivalence hψ
  obtain ⟨ρ, hρ, hconj⟩ := exists_isPLHomeomorphOn_of_eq_endMap
    (hL.prod isHPolytope_Icc.isPolyhedron) hmod hmove
    (hL.prod isHPolytope_Icc.isPolyhedron).isPLHomeomorphOn_id
    (fun z hz => Prod.ext (hends z.1 (hLP hz.1)) rfl)
    (fun z hz => hends (ψ z) (hQP (hψ.bijOn.mapsTo hz)))
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩
    have h := hconj ((p, 0), s) ⟨⟨hp, by norm_num⟩, hs⟩
    simpa only [Function.comp_apply, Prod.map_apply, id_eq, hψzero p hp] using h
  · intro p hp s hs t ht
    exact hconj ((p, t), s) ⟨⟨hp, ht⟩, hs⟩
  · exact (image_mono (prod_mono_left hQP)).trans hf.image_eq.subset

theorem IsCylindricalDiagram.exists_crossing_corner_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ p ∈ spliceSquare, f (p, 0) = f (p, 1)) (a b : Bool) :
    let L := section34CornerBase a b
    let B := f '' (L ×ˢ Icc (0 : ℝ) 1)
    let Q := section34CornerPush a b '' (L ×ˢ Icc (0 : ℝ) 1)
    ∃ ρ : E × ℝ → E,
      IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) (f '' (Q ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ y ∈ B, ρ (y, 0) = y) ∧
      (∀ p ∈ L, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ρ (f (p, s), t) = f (section34CornerPush a b (p, t), s)) ∧
      f '' (Q ×ˢ Icc (0 : ℝ) 1) ⊆ C := by
  dsimp only
  have hL := section34_corner_base_isPolyhedron a b
  have hLP := (section34_corner_base_subset a b).trans
    (section34_crossing_quadrant_subset_square a b)
  have hpush := section34_corner_push_isPLHomeomorphOn a b
  apply hf.exists_collar_of_base_embedding hends hL hLP hpush
  · rintro _ ⟨z, hz, rfl⟩
    exact section34_crossing_quadrant_subset_square a b (section34_corner_push_mapsTo a b hz)
  · exact fun p _ => section34_corner_push_zero a b p

end DifferentialGeometry.Topology.PiecewiseLinear
