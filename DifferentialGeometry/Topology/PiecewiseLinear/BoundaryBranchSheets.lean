/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchPreimage
import Mathlib.Topology.Separation.Hausdorff

/-!
# Polyhedral source sheets along a boundary branch
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_isPolyhedron_injOn_neighborhood
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Y] [T2Space Y] {f : E → Y} {P A U : Set E}
    (hP : IsPolyhedron P) (hA : IsCompact A) (hAP : A ⊆ P) (hf : ContinuousOn f P)
    (hinj : InjOn f A) (hloc : ∀ x ∈ A, ∃ V ∈ 𝓝[P] x, InjOn f V)
    (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ S : Set E, IsPolyhedron S ∧ A ⊆ S ∧ S ⊆ P ∩ U ∧ InjOn f S ∧
      ∀ x ∈ A, S ∈ 𝓝[P] x := by
  let fP : P → Y := P.domRestrict f
  let A' : Set P := Subtype.val ⁻¹' A
  have hA' : IsCompact A' :=
    hP.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hA
  have hinj' : InjOn fP A' := fun x hx z hz h => Subtype.ext (hinj hx hz h)
  have hloc' : ∀ x ∈ A', ∃ V ∈ 𝓝 x, InjOn fP V := by
    intro x hx
    obtain ⟨V, hV, hinjV⟩ := hloc x hx
    refine ⟨Subtype.val ⁻¹' V, preimage_coe_mem_nhds_subtype.mpr hV, ?_⟩
    exact fun z hz w hw h => Subtype.ext (hinjV hz hw h)
  obtain ⟨V, hV, hA'V, hinjV⟩ :=
    hinj'.exists_isOpen_superset hA' (fun _ _ => hf.domRestrict.continuousAt) hloc'
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  have hAO : A ⊆ O := by
    intro x hx
    have hxV : (⟨x, hAP hx⟩ : P) ∈ V := hA'V hx
    rwa [← hOV] at hxV
  obtain ⟨Q, hQ, hAQ, hQOU⟩ :=
    exists_isPolyhedron_neighborhood hA (hO.inter hU) (subset_inter hAO hAU)
  refine ⟨P ∩ Q, hP.inter hQ, fun x hx => ⟨hAP hx, interior_subset (hAQ hx)⟩,
    fun x hx => ⟨hx.1, (hQOU hx.2).2⟩, ?_, ?_⟩
  · intro x hx z hz hxz
    have hxV : (⟨x, hx.1⟩ : P) ∈ V := by
      rw [← hOV]
      exact (hQOU hx.2).1
    have hzV : (⟨z, hz.1⟩ : P) ∈ V := by
      rw [← hOV]
      exact (hQOU hz.2).1
    exact congrArg Subtype.val (hinjV hxV hzV hxz)
  · intro x hx
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp (hAQ hx)))

namespace NormalSingularCellData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_polyhedral_sheet_neighborhoods_of_boundaryBranch
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C S T : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
        hD.branchPreimage c = A ∪ C ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) A (hD.singularSet.branchComplex c).space ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) C (hD.singularSet.branchComplex c).space ∧
        IsPolyhedron S ∧ IsPolyhedron T ∧ S ⊆ D.domain ∧ T ⊆ D.domain ∧
        A ⊆ S ∧ C ⊆ T ∧ Disjoint S T ∧
        (∀ x ∈ A, S ∈ 𝓝[D.domain] x) ∧ (∀ x ∈ C, T ∈ 𝓝[D.domain] x) ∧
        IsPLOn 2 3 D S ∧ IsPLOn 2 3 D T ∧
        IsEmbedding (S.domRestrict D) ∧ IsEmbedding (T.domRestrict D) ∧
        ∃ W : Set M, IsOpen W ∧ hD.singularSet.branchCarrier c ⊆ W ∧
          (∀ y ∈ W, D.domain ∩ D ⁻¹' {y} ⊆ S ∪ T) ∧
          ∀ y ∈ W, y ∈ doublePointSet D D.domain ↔ y ∈ D '' S ∩ D '' T := by
  obtain ⟨A, C, hA, hC, hAC, hcover, hAcoord, hCcoord⟩ :=
    hD.exists_two_isPLBalls_branchPreimage_of_boundaryBranch_with_coordinate hc
  have hACP : A ∪ C ⊆ D.domain := by
    rw [← hcover]
    exact inter_subset_left
  have hAP : A ⊆ D.domain := subset_union_left.trans hACP
  have hCP : C ⊆ D.domain := subset_union_right.trans hACP
  have hDA : InjOn D A := by
    intro x hx z hz hxz
    apply hAcoord.bijOn.injOn hx hz
    exact congrArg (Function.invFunOn (hD.singularSet.branchPieceIn c).map
      (hD.singularSet.branchPieceIn c).complex.space) hxz
  have hDC : InjOn D C := by
    intro x hx z hz hxz
    apply hCcoord.bijOn.injOn hx hz
    exact congrArg (Function.invFunOn (hD.singularSet.branchPieceIn c).map
      (hD.singularSet.branchPieceIn c).complex.space) hxz
  obtain ⟨U, V, hU, hV, hAU, hCV, hUV⟩ :=
    normal_separation hA.isPolyhedron.isClosed hC.isPolyhedron.isClosed hAC
  obtain ⟨S, hS, hAS, hSPU, hinjS, hSneigh⟩ :=
    exists_isPolyhedron_injOn_neighborhood D.isPLBall_domain.isPolyhedron
      hA.isPolyhedron.isCompact hAP D.continuousOn hDA
      (fun x hx => hD.locallyInjective x (hAP hx)) hU hAU
  obtain ⟨T, hT, hCT, hTPV, hinjT, hTneigh⟩ :=
    exists_isPolyhedron_injOn_neighborhood D.isPLBall_domain.isPolyhedron
      hC.isPolyhedron.isCompact hCP D.continuousOn hDC
      (fun x hx => hD.locallyInjective x (hCP hx)) hV hCV
  have hSP : S ⊆ D.domain := hSPU.trans inter_subset_left
  have hTP : T ⊆ D.domain := hTPV.trans inter_subset_left
  have hST : Disjoint S T :=
    hUV.mono (hSPU.trans inter_subset_right) (hTPV.trans inter_subset_right)
  have hSemb : IsEmbedding (S.domRestrict D) := by
    let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
    exact ((D.continuousOn.mono hSP).domRestrict.isClosedEmbedding
      (Set.injOn_iff_injective.mp hinjS)).isEmbedding
  have hTemb : IsEmbedding (T.domRestrict D) := by
    let _ : CompactSpace T := isCompact_iff_compactSpace.mp hT.isCompact
    exact ((D.continuousOn.mono hTP).domRestrict.isClosedEmbedding
      (Set.injOn_iff_injective.mp hinjT)).isEmbedding
  let f : D.domain → M := D.domain.domRestrict D
  let O : Set D.domain := interior (Subtype.val ⁻¹' S) ∪ interior (Subtype.val ⁻¹' T)
  have hO : IsOpen O := isOpen_interior.union isOpen_interior
  let W : Set M := (f '' Oᶜ)ᶜ
  have hW : IsOpen W := by
    let _ : CompactSpace D.domain :=
      isCompact_iff_compactSpace.mp D.isPLBall_domain.isPolyhedron.isCompact
    exact (D.continuousOn.domRestrict.isClosedMap _ hO.isClosed_compl).isOpen_compl
  have hbranchW : hD.singularSet.branchCarrier c ⊆ W := by
    intro y hy
    rintro ⟨x, hxO, hxy⟩
    have hxbranch : (x : EuclideanSpace ℝ (Fin 2)) ∈ hD.branchPreimage c := by
      refine ⟨x.property, ?_⟩
      change f x ∈ hD.singularSet.branchCarrier c
      rw [hxy]
      exact hy
    rcases hcover.subset hxbranch with hxA | hxC
    · exact hxO (Or.inl (mem_interior_iff_mem_nhds.mpr
        (preimage_coe_mem_nhds_subtype.mpr (hSneigh x hxA))))
    · exact hxO (Or.inr (mem_interior_iff_mem_nhds.mpr
        (preimage_coe_mem_nhds_subtype.mpr (hTneigh x hxC))))
  have hfiber : ∀ y ∈ W, D.domain ∩ D ⁻¹' {y} ⊆ S ∪ T := by
    intro y hy x hx
    have hxO : (⟨x, hx.1⟩ : D.domain) ∈ O := by
      by_contra hxO
      exact hy ⟨⟨x, hx.1⟩, hxO, hx.2⟩
    rcases hxO with hxS | hxT
    · have h := interior_subset hxS
      exact Or.inl h
    · have h := interior_subset hxT
      exact Or.inr h
  exact ⟨A, C, S, T, hA, hC, hAC, hcover, hAcoord, hCcoord, hS, hT, hSP, hTP, hAS,
    hCT, hST, hSneigh, hTneigh, D.isPLOn.mono_of_isPolyhedron hS hSP,
    D.isPLOn.mono_of_isPolyhedron hT hTP, hSemb, hTemb, W, hW, hbranchW, hfiber,
    fun y hy => mem_doublePointSet_iff_mem_image_inter_of_injOn D hSP hTP hST hinjS hinjT
      (hfiber y hy)⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
