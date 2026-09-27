/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem interior_iUnion_subfamily_of_locallyFinite_at
    {ι X : Type*} [TopologicalSpace X] {D Q : ι → Set X} {P : ι → Prop} {x : X}
    (hDclosed : ∀ i, IsClosed (D i)) (hDQ : ∀ i, D i ⊆ Q i)
    (hfinite : ∃ V ∈ 𝓝 x, {i | (Q i ∩ V).Nonempty}.Finite)
    (hnot : ∀ i, ¬ P i → x ∉ D i) (hint : x ∈ interior (⋃ i, D i)) :
    x ∈ interior (⋃ i, ⋃ (_ : P i), D i) := by
  obtain ⟨V, hV, hF⟩ := hfinite
  let F : Set ι := {i | (Q i ∩ V).Nonempty}
  let B : Set ι := {i | i ∈ F ∧ ¬ P i}
  have hB : B.Finite := hF.subset (fun i hi => hi.1)
  have : Finite B := hB.to_subtype
  have hclosed : IsClosed (⋃ i : B, D i.1) :=
    isClosed_iUnion_of_finite fun i => hDclosed i.1
  have hxB : x ∉ ⋃ i : B, D i.1 := by
    intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hnot i.1 i.2.2 hi
  let O : Set X := interior V ∩ (⋃ i : B, D i.1)ᶜ ∩ interior (⋃ i, D i)
  have hOopen : IsOpen O := (isOpen_interior.inter hclosed.isOpen_compl).inter isOpen_interior
  have hxO : x ∈ O := ⟨⟨mem_interior_iff_mem_nhds.mpr hV, hxB⟩, hint⟩
  have hOsub : O ⊆ ⋃ i, ⋃ (_ : P i), D i := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hy.2)
    have hiF : i ∈ F := ⟨y, hDQ i hi, interior_subset hy.1.1⟩
    have hiP : P i := by
      by_contra hpi
      exact hy.1.2 (mem_iUnion.mpr ⟨⟨i, hiF, hpi⟩, hi⟩)
    exact mem_iUnion₂.mpr ⟨i, hiP, hi⟩
  exact interior_maximal hOsub hOopen hxO

private theorem simplexRim_subset_graphSkeletonSpace
    {Ea : Type} {M : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} (𝒦 : LocallyFinitePLPieceIn Ea 3 M U)
    (s : Section34SimplexIndex 𝒦 3) :
    simplexRim 𝒦 s.1 ⊆ graphSkeletonSpace 𝒦 := by
  rintro x hx
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
  change t ⊂ s.1 at ht
  by_cases hne : t.Nonempty
  · have hface : t ∈ 𝒦.complex.faces := 𝒦.complex.down_closed s.2.1 ht.1 hne
    have hcard : t.card ≤ 2 := by
      have hlt := Finset.card_lt_card ht
      omega
    exact mem_iUnion₂.mpr ⟨t, ⟨hface, hcard⟩, hxt⟩
  · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst t
    simp [simplexBody] at hxt

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}

omit [FiniteDimensional ℝ Ea] in
theorem face_rim_subset_interior_of_deleted_family
    (hQsep : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    {Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∀ s : Section34SimplexIndex 𝒦 3,
      h '' simplexRim 𝒦 s.1 ⊆ interior (section34FaceTorus Dv s) := by
  intro s x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzgraph : z ∈ graphSkeletonSpace 𝒦 :=
    simplexRim_subset_graphSkeletonSpace 𝒦 s hz
  have hnear : h z ∈ interior (⋃ w, Dv w) :=
    mem_interior_iff_mem_nhds.mpr
      ((mem_nhdsSet_iff_forall.mp hDnbhd) (h z) ⟨z, hzgraph, rfl⟩)
  have hzbody : h z ∈ h '' simplexBody 𝒦 s.1 := by
    obtain ⟨t, ht, zt⟩ := mem_iUnion₂.mp hz
    change t ⊂ s.1 at ht
    exact ⟨z, image_mono (convexHull_mono (Finset.coe_subset.mpr ht.1)) zt, rfl⟩
  have hQz : h z ∈ ⋃ w, Q w := by
    obtain ⟨-, hrimQ, -, -, -⟩ := htor
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hrimQ s ⟨z, hz, rfl⟩)
    exact mem_iUnion.mpr ⟨w, hzw⟩
  have hnot (w : Section34VertexIndex 𝒦 𝒦')
      (hw : ¬ Section34Incident w.1 s.1) : h z ∉ Dv w := by
    intro hzw
    exact hw (hQsep w s ⟨h z, hDvQ w hzw, hzbody⟩)
  have hincident := interior_iUnion_subfamily_of_locallyFinite_at
    (D := Dv) (Q := Q) (P := fun w => Section34Incident w.1 s.1)
    (fun w => (hDv w).isCompact.isClosed) hDvQ (hQlf (h z) hQz) hnot hnear
  have hfamily : (⋃ w, ⋃ (_ : Section34Incident w.1 s.1), Dv w) =
      section34FaceTorus Dv s := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hyw⟩
    · intro hy
      obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
      have hws : Section34Incident a.1.2.1 s.1 := by
        change a.1.1 = s at ha
        simpa [ha] using a.2
      exact mem_iUnion₂.mpr ⟨a.1.2, hws, hya⟩
  rwa [hfamily] at hincident

end DifferentialGeometry.Topology.PiecewiseLinear
