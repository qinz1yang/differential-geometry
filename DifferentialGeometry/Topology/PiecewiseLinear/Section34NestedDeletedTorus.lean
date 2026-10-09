/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34DeletedFamilyTorus
import DifferentialGeometry.Topology.PiecewiseLinear.FaceRimInteriorDeletedFamily
import DifferentialGeometry.Topology.PiecewiseLinear.SpineNeighborhood
import DifferentialGeometry.Topology.Homeomorph.SubsetImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
  {Sd : Section34SimplexIndex 𝒦 3 → Set E3}

theorem exists_nested_torus_of_deleted_family
    (hsubdiv : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hQsep : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty →
      ∃ e : Section34EdgeIndex 𝒦 𝒦',
        (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∀ s : Section34SimplexIndex 𝒦 3,
      ∃ (S₁ Te : Set E3) (Φ : section34FaceTorus Dv s ≃ₜ Te),
        section34FaceTorus Dv s ⊆ (ct s).source ∧
        (∀ y : section34FaceTorus Dv s, (Φ y : E3) = ct s (y : M₂)) ∧
        (∀ y : section34FaceTorus Dv s, (y : M₂) ∈ h '' simplexRim 𝒦 s.1 ↔
          (Φ y : E3) ∈ ct s '' (h '' simplexRim 𝒦 s.1)) ∧
        IsTopologicalSolidTorus S₁ ∧ IsCombinatorialSolidTorus Te ∧
        S₁ ⊆ interior Te ∧ Te ⊆ interior (Sd s) ∧
        IsToroidalShell (closure (Sd s \ S₁)) (frontier S₁) (frontier (Sd s)) ∧
        IsSpine S₁ (ct s '' (h '' simplexRim 𝒦 s.1)) ∧
        ct s '' (h '' simplexRim 𝒦 s.1) ⊆ Te := by
  intro s
  obtain ⟨hct, hQc⟩ := htor.1 s
  have hTQ : section34FaceTorus Dv s ⊆
      ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := mem_section34FaceTorus_iff.mp hy
    exact mem_iUnion₂.mpr ⟨w, hw, hDvQ w hyw⟩
  have hTc := hTQ.trans hQc
  let Te := ct s '' section34FaceTorus Dv s
  have hTe : IsCombinatorialSolidTorus Te :=
    isCombinatorialSolidTorus_image_face_of_deleted_family hsubdiv hmap hends
      hDv hDd hDmeet hDadj hDddisj s hct hTc
  have hTeSd : Te ⊆ interior (Sd s) := (image_mono hTQ).trans (htor.2.2.2.1 s)
  have hJT : h '' simplexRim 𝒦 s.1 ⊆ interior (section34FaceTorus Dv s) :=
    face_rim_subset_interior_of_deleted_family hQsep hQlf htor hDv hDvQ hDnbhd s
  have hJc : h '' simplexRim 𝒦 s.1 ⊆ (ct s).source :=
    hJT.trans (interior_subset.trans hTc)
  have hJTe : ct s '' (h '' simplexRim 𝒦 s.1) ⊆ interior Te := by
    change ct s '' (h '' simplexRim 𝒦 s.1) ⊆ interior (ct s '' section34FaceTorus Dv s)
    rw [← (ct s).image_interior_of_subset_source hTc]
    exact image_mono hJT
  obtain ⟨S₁, hS₁, hS₁Te, -, hshell, hspine⟩ :=
    (htor.2.2.1 s).2.exists_inner_torus_of_isOpen isOpen_interior hJTe
  let Φ : section34FaceTorus Dv s ≃ₜ Te :=
    (ct s).homeomorphOfImageSubsetSource hTc rfl
  refine ⟨S₁, Te, Φ, hTc, fun _ => rfl, ?_, hS₁, hTe, hS₁Te, hTeSd, hshell, hspine,
    hJTe.trans interior_subset⟩
  intro y
  change (y : M₂) ∈ h '' simplexRim 𝒦 s.1 ↔ ct s y ∈ ct s '' (h '' simplexRim 𝒦 s.1)
  constructor
  · exact fun hy => mem_image_of_mem (ct s) hy
  · rintro ⟨z, hz, hzy⟩
    exact (ct s).injOn (hJc hz) (hTc y.2) hzy ▸ hz

end DifferentialGeometry.Topology.PiecewiseLinear
