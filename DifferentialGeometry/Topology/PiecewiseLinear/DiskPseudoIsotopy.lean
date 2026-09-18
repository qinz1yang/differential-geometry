import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E E₂ F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def IsPLPseudoIsotopicToId (u : E → E) (P : Set E) : Prop :=
  ∃ Φ : E × ℝ → E × ℝ, IsPLHomeomorphOn Φ (P ×ˢ Icc 0 1) (P ×ˢ Icc 0 1) ∧
    (∀ x ∈ P, Φ (x, 0) = (x, 0)) ∧ ∀ x ∈ P, Φ (x, 1) = (u x, 1)

theorem isPLPseudoIsotopicToId_id {P : Set E} (hP : IsPolyhedron P) :
    IsPLPseudoIsotopicToId (id : E → E) P :=
  ⟨id, (hP.prod isHPolytope_Icc.isPolyhedron).isPLHomeomorphOn_id, fun _ _ => rfl, fun _ _ => rfl⟩

open Classical in
theorem isPLPseudoIsotopicToId_of_eqOn_boundaryComplex [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {u : E → E} (hu : IsPLHomeomorphOn u K.space K.space)
    (hbd : EqOn u id (boundaryComplex 2 K).space) :
    IsPLPseudoIsotopicToId u K.space := by
  classical
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hQ : IsPLBall 3 (K.space ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hK (isPLBall_Icc zero_lt_one)
  obtain ⟨A, hAfin, hAspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hAball : IsPLBall 3 A.space := hAspace ▸ hQ
  have hbdA : (boundaryComplex 3 A).space =
      K.space ×ˢ ({1} : Set ℝ) ∪
        (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
    rw [boundaryComplex_space_prism K hK zero_lt_one A hAspace]
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have hW1poly : IsPolyhedron (K.space ×ˢ ({1} : Set ℝ)) :=
    isPolyhedron_prod_singleton hK.isPolyhedron 1
  have hW0poly : IsPolyhedron
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) :=
    (isPolyhedron_prod_singleton hK.isPolyhedron 0).union
      ((isPolyhedron_space (boundaryComplex 2 K)).prod isHPolytope_Icc.isPolyhedron)
  have hsing : IsPolyhedron ({1} : Set ℝ) := by
    rw [← Icc_self (1 : ℝ)]
    exact isHPolytope_Icc.isPolyhedron
  have hθ1 : IsPLHomeomorphOn (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z)
      (K.space ×ˢ ({1} : Set ℝ)) (K.space ×ˢ ({1} : Set ℝ)) := by
    refine (hu.prodMap hsing.isPLHomeomorphOn_id).congr ?_
    rintro z ⟨-, hz2⟩
    have hz2' : z.2 = 1 := hz2
    simp only [if_pos hz2']
    rfl
  have hθid : EqOn (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z) id
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
    rintro z hz
    by_cases hz2 : z.2 = 1
    · simp only [if_pos hz2]
      rcases hz with ⟨-, hzbot⟩ | ⟨hzb, -⟩
      · have hzbot' : z.2 = 0 := hzbot
        exact absurd (hz2.symm.trans hzbot') (by norm_num)
      · exact Prod.ext (hbd hzb) rfl
    · simp only [if_neg hz2]
      rfl
  have hθ0 : IsPLHomeomorphOn (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z)
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1)
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) :=
    hW0poly.isPLHomeomorphOn_id.congr hθid
  have hmeet : (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z) ''
      (K.space ×ˢ ({1} : Set ℝ) ∩
        (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1)) =
      K.space ×ˢ ({1} : Set ℝ) ∩
        (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) :=
    ((hθid.mono inter_subset_right).image_eq).trans (image_id _)
  have hθ := hθ1.union hθ0 hW1poly hW0poly hmeet
  rw [← hbdA] at hθ
  obtain ⟨Φ, hΦ, hΦbd⟩ :=
    exists_isPLHomeomorphOn_of_boundaryComplex (n := 2) A A hAball hAball hθ
  refine ⟨Φ, hAspace ▸ hΦ, fun x hx => ?_, fun x hx => ?_⟩
  · have hmem : (x, (0 : ℝ)) ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inr (Or.inl ⟨hx, rfl⟩)
    rw [hΦbd hmem]
    exact if_neg (by norm_num)
  · have hmem : (x, (1 : ℝ)) ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inl ⟨hx, rfl⟩
    rw [hΦbd hmem]
    exact if_pos rfl

variable {P : Set E} {P' : Set E₂}

theorem image_prod_singleton_of_map_level {Φ : E₂ × ℝ → E × ℝ} {u : E₂ → E}
    (hu : IsPLHomeomorphOn u P' P) {a : ℝ} (hΦa : ∀ x ∈ P', Φ (x, a) = (u x, a)) :
    Φ '' (P' ×ˢ ({a} : Set ℝ)) = P ×ˢ ({a} : Set ℝ) := by
  apply Subset.antisymm
  · rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have hz2' : z.2 = a := hz2
    rw [show z = (z.1, a) from Prod.ext rfl hz2', hΦa z.1 hz1]
    exact ⟨hu.bijOn.mapsTo hz1, rfl⟩
  · rintro z ⟨hz1, hz2⟩
    have hz2' : z.2 = a := hz2
    obtain ⟨y, hy, hyz⟩ := hu.bijOn.surjOn hz1
    refine ⟨(y, a), ⟨hy, rfl⟩, ?_⟩
    rw [hΦa y hy, hyz]
    exact Prod.ext rfl hz2'.symm

theorem snd_eq_of_map_level {Φ : E₂ × ℝ → E × ℝ}
    (hΦ : IsPLHomeomorphOn Φ (P' ×ˢ Icc 0 1) (P ×ˢ Icc 0 1)) {u : E₂ → E}
    (hu : IsPLHomeomorphOn u P' P) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hΦa : ∀ x ∈ P', Φ (x, a) = (u x, a)) {z : E₂ × ℝ} (hz : z ∈ P' ×ˢ Icc (0 : ℝ) 1)
    (hΦz : (Φ z).2 = a) : z.2 = a := by
  have hmem : Φ z ∈ Φ '' (P' ×ˢ ({a} : Set ℝ)) := by
    rw [image_prod_singleton_of_map_level hu hΦa]
    exact ⟨(hΦ.bijOn.mapsTo hz).1, hΦz⟩
  obtain ⟨w, hw, hwz⟩ := hmem
  have hw2 : w.2 = a := hw.2
  have hwmem : w ∈ P' ×ˢ Icc (0 : ℝ) 1 := ⟨hw.1, hw2.symm ▸ ha⟩
  rw [← hΦ.bijOn.injOn hwmem hz hwz]
  exact hw2

theorem IsCylindricalDiagram.comp_of_ends [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂]
    [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {S : Set F} (h : IsCylindricalDiagram f P S)
    {u₀ u₁ : E₂ → E} (hu₀ : IsPLHomeomorphOn u₀ P' P) (hu₁ : IsPLHomeomorphOn u₁ P' P)
    {Φ : E₂ × ℝ → E × ℝ} (hΦ : IsPLHomeomorphOn Φ (P' ×ˢ Icc 0 1) (P ×ˢ Icc 0 1))
    (hΦ0 : ∀ x ∈ P', Φ (x, 0) = (u₀ x, 0)) (hΦ1 : ∀ x ∈ P', Φ (x, 1) = (u₁ x, 1)) :
    IsCylindricalDiagram (f ∘ Φ) P' S := by
  have hbot : Φ '' (P' ×ˢ ({0} : Set ℝ)) = P ×ˢ ({0} : Set ℝ) :=
    image_prod_singleton_of_map_level hu₀ hΦ0
  have htop : Φ '' (P' ×ˢ ({1} : Set ℝ)) = P ×ˢ ({1} : Set ℝ) :=
    image_prod_singleton_of_map_level hu₁ hΦ1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcomp := h.isPiecewiseAffineOn.comp hΦ.isPiecewiseAffineOn
    have hsub : P' ×ˢ Icc (0 : ℝ) 1 ⊆ Φ ⁻¹' (P ×ˢ Icc (0 : ℝ) 1) := fun x hx => hΦ.bijOn.mapsTo hx
    rwa [inter_eq_left.mpr hsub] at hcomp
  · rw [image_comp, hΦ.image_eq, h.image_eq]
  · rw [image_comp, image_comp, hbot, htop]
    exact h.image_top_eq_bottom
  · intro x hx y hy hxy
    have hxy' : f (Φ x) = f (Φ y) := hxy
    rcases h.eq_or_endpoints (Φ x) (hΦ.bijOn.mapsTo hx) (Φ y) (hΦ.bijOn.mapsTo hy) hxy' with
      heq | hends | hends
    · exact Or.inl (hΦ.bijOn.injOn hx hy heq)
    · exact Or.inr (Or.inl
        ⟨snd_eq_of_map_level hΦ hu₀ (by norm_num) hΦ0 hx hends.1,
          snd_eq_of_map_level hΦ hu₁ (by norm_num) hΦ1 hy hends.2⟩)
    · exact Or.inr (Or.inr
        ⟨snd_eq_of_map_level hΦ hu₁ (by norm_num) hΦ1 hx hends.1,
          snd_eq_of_map_level hΦ hu₀ (by norm_num) hΦ0 hy hends.2⟩)

theorem IsCylindricalDiagram.exists_endMap_id_of_pseudoIsotopicToId
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {S : Set F} (h : IsCylindricalDiagram f P S)
    {u : E → E} (hu : IsPLHomeomorphOn u P P) (hfu : ∀ x ∈ P, f (x, 0) = f (u x, 1))
    (hiso : IsPLPseudoIsotopicToId u P) {w : E₂ → E} (hw : IsPLHomeomorphOn w P' P) :
    ∃ f' : E₂ × ℝ → F, IsCylindricalDiagram f' P' S ∧ ∀ x ∈ P', f' (x, 0) = f' (x, 1) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := hiso
  have hprod : IsPLHomeomorphOn (Prod.map w (id : ℝ → ℝ)) (P' ×ˢ Icc (0 : ℝ) 1)
      (P ×ˢ Icc (0 : ℝ) 1) := hw.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  refine ⟨f ∘ (Φ ∘ Prod.map w id), ?_, fun x hx => ?_⟩
  · exact h.comp_of_ends hw (hw.trans hu) (hprod.trans hΦ)
      (fun y hy => hΦ0 (w y) (hw.bijOn.mapsTo hy))
      (fun y hy => hΦ1 (w y) (hw.bijOn.mapsTo hy))
  · have h0 : Φ (Prod.map w id (x, (0 : ℝ))) = (w x, (0 : ℝ)) := hΦ0 (w x) (hw.bijOn.mapsTo hx)
    have h1 : Φ (Prod.map w id (x, (1 : ℝ))) = (u (w x), (1 : ℝ)) := hΦ1 (w x) (hw.bijOn.mapsTo hx)
    change f (Φ (Prod.map w id (x, 0))) = f (Φ (Prod.map w id (x, 1)))
    rw [h0, h1]
    exact hfu (w x) (hw.bijOn.mapsTo hx)

theorem exists_isPLHomeomorphOn_of_endMaps_pseudoIsotopicToId
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G] {S : Set F} {T : Set G} {f : E × ℝ → F} {g : E₂ × ℝ → G}
    (hf : IsCylindricalDiagram f P S) (hg : IsCylindricalDiagram g P' T)
    (hP' : IsPolyhedron P')
    {uf : E → E} {ug : E₂ → E₂} (huf : IsPLHomeomorphOn uf P P)
    (hug : IsPLHomeomorphOn ug P' P')
    (hfuf : ∀ x ∈ P, f (x, 0) = f (uf x, 1)) (hgug : ∀ x ∈ P', g (x, 0) = g (ug x, 1))
    (hisof : IsPLPseudoIsotopicToId uf P) (hisog : IsPLPseudoIsotopicToId ug P')
    {w : E₂ → E} (hw : IsPLHomeomorphOn w P' P) :
    ∃ H : F → G, IsPLHomeomorphOn H S T := by
  obtain ⟨f', hf', hfid⟩ := hf.exists_endMap_id_of_pseudoIsotopicToId huf hfuf hisof hw
  obtain ⟨g', hg', hgid⟩ :=
    hg.exists_endMap_id_of_pseudoIsotopicToId hug hgug hisog hP'.isPLHomeomorphOn_id
  obtain ⟨H, hH, -⟩ := exists_isPLHomeomorphOn_of_eq_endMap hP' hf' hg'
    hP'.isPLHomeomorphOn_id hfid hgid
  exact ⟨H, hH⟩

end DifferentialGeometry.Topology.PiecewiseLinear
