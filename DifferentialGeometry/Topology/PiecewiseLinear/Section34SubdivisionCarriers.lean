/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSubordinateToCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

theorem section34CarrierSupport_subset_of_subdivision
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {s t : Finset Ea} (ht : t ∈ 𝒦.complex.faces)
    (hst : convexHull ℝ (s : Set Ea) ⊆ convexHull ℝ (t : Set Ea)) :
    Section34CarrierSupport 𝒦' s ⊆ Section34CarrierSupport 𝒦 t := by
  classical
  intro x hx
  obtain ⟨v, hvs, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨r, hr, y, hyr, hyx⟩ := mem_iUnion₂.mp hx
  obtain ⟨q, hq, hrq⟩ := hsub.exists_face_subset hr.1
  have hvt : v ∈ convexHull ℝ (t : Set Ea) := hst (subset_convexHull ℝ _ hvs)
  have hvq : v ∈ convexHull ℝ (q : Set Ea) :=
    hrq (subset_convexHull ℝ _ (Finset.mem_coe.mpr hr.2))
  obtain ⟨a, hat, haq⟩ := convexHull_nonempty_iff.mp
    (show (convexHull ℝ ((t : Set Ea) ∩ (q : Set Ea))).Nonempty from
      ⟨v, 𝒦.complex.inter_subset_convexHull ht hq ⟨hvt, hvq⟩⟩)
  refine mem_iUnion₂.mpr ⟨a, hat, mem_iUnion₂.mpr ⟨q, ⟨hq, haq⟩, y, hrq hyr, ?_⟩⟩
  rw [← hmap]
  exact hyx

theorem finite_subdivision_carrier_fibers {ι : Type*}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (f : ι → 𝒦'.complex.faces) (hf : Function.Injective f) (car : ι → Finset Ea)
    (hcar : ∀ i, car i ∈ 𝒦.complex.faces)
    (hcontain : ∀ i, convexHull ℝ ((f i).1 : Set Ea) ⊆ convexHull ℝ (car i : Set Ea)) :
    ∀ t : Finset Ea, {i | car i = t}.Finite := by
  classical
  intro t
  by_cases ht : t ∈ 𝒦.complex.faces
  · let C : Set 𝒦'.complex.space :=
      (Subtype.val : 𝒦'.complex.space → Ea) ⁻¹' convexHull ℝ (t : Set Ea)
    have hC : IsCompact C := by
      rw [Subtype.isCompact_iff, image_preimage_eq_iff.mpr]
      · exact t.finite_toSet.isCompact_convexHull ℝ
      · intro x hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        rw [hsub.space_eq]
        exact 𝒦.complex.convexHull_subset_space ht hx
    refine ((𝒦'.locallyFinite.finite_nonempty_inter_compact hC).preimage hf.injOn).subset ?_
    intro i hi
    have hcent := (f i).1.centroid_mem_convexHull (R := ℝ)
      (𝒦'.complex.nonempty_of_mem_faces (f i).2)
    refine ⟨⟨(f i).1.centroid ℝ id,
      𝒦'.complex.convexHull_subset_space (f i).2 hcent⟩, hcent, ?_⟩
    change (f i).1.centroid ℝ id ∈ convexHull ℝ (t : Set Ea)
    rw [← hi]
    exact hcontain i hcent
  · have hempty : {i | car i = t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact ht (hi ▸ hcar i)
    rw [hempty]
    exact finite_empty

theorem exists_finite_subdivision_carrier_assignment
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map) :
    ∃ car : 𝒦'.complex.faces → Finset Ea,
      (∀ s, car s ∈ 𝒦.complex.faces) ∧
      (∀ s, convexHull ℝ (s.1 : Set Ea) ⊆ convexHull ℝ (car s : Set Ea)) ∧
      (∀ s, Section34CarrierSupport 𝒦' s.1 ⊆ Section34CarrierSupport 𝒦 (car s)) ∧
      ∀ t : Finset Ea, {s | car s = t}.Finite := by
  classical
  choose car hcar hcontain using fun s : 𝒦'.complex.faces => hsub.exists_face_subset s.2
  exact ⟨car, hcar, hcontain,
    fun s => section34CarrierSupport_subset_of_subdivision hsub hmap (hcar s) (hcontain s),
    finite_subdivision_carrier_fibers hsub id Function.injective_id car hcar hcontain⟩

theorem exists_subdivision_with_finite_carrier_assignment [FiniteDimensional ℝ Ea] [T2Space M₁]
    {ι : Type*} (hU : IsOpen U)
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (O : ι → Set M₁) (hO : ∀ i, IsOpen (O i)) (hcover : U ⊆ ⋃ i, O i) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
      IsCombinatorialManifold 3 𝒦'.complex ∧
      (∀ s ∈ 𝒦'.complex.faces, ∃ i, Section34CarrierSupport 𝒦' s ⊆ O i) ∧
      (∀ w, car w ∈ 𝒦.complex.faces) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ simplexBody 𝒦 (car w)) ∧
      (∀ w, Section34CarrierSupport 𝒦' w.1 ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
      ∀ t : Finset Ea, {w | car w = t}.Finite := by
  classical
  obtain ⟨𝒦', hsub, hmap, hman, hsmall⟩ :=
    exists_isSubdivision_section34CarrierSupport_subset hU 𝒦 h𝒦 O hO hcover
  obtain ⟨car, hcar, hcontain, hsupport, hfinite⟩ :=
    exists_finite_subdivision_carrier_assignment hsub hmap
  let f : Section34VertexIndex 𝒦 𝒦' → 𝒦'.complex.faces := fun w => ⟨w.1, w.2.1⟩
  refine ⟨𝒦', car ∘ f, hsub, hmap, hman, hsmall, fun w => hcar (f w), ?_,
    fun w => hsupport (f w), ?_⟩
  · intro w
    change 𝒦'.map '' convexHull ℝ (w.1 : Set Ea) ⊆
      𝒦.map '' convexHull ℝ (car (f w) : Set Ea)
    rw [hmap]
    exact image_mono (hcontain (f w))
  · intro t
    have hf : Function.Injective f := by
      intro w v h
      exact Subtype.ext (congrArg (fun s : 𝒦'.complex.faces => s.1) h)
    exact (hfinite t).preimage hf.injOn

end DifferentialGeometry.Topology.PiecewiseLinear
