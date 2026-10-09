/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodTransport
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem IsNestedCommonAnnularDerivedNeighborhood.image_of_isPLHomeomorphOn
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} {K' : Geometry.SimplicialComplex ℝ F}
    {f : E → F} {A B J S₀ S₁ : Set E}
    (h : IsNestedCommonAnnularDerivedNeighborhood K A B J S₀ S₁)
    (hf : IsPLHomeomorphOn f K.space K'.space) (hJK : J ⊆ K.space)
    (hA : IsCommonAnnularDerivedNeighborhood K' (f '' A) (f '' J)
      (f '' S₀) (f '' S₁))
    (hB : IsCommonAnnularDerivedNeighborhood K' (f '' B) (f '' J)
      (f '' S₀) (f '' S₁)) :
    IsNestedCommonAnnularDerivedNeighborhood K' (f '' A) (f '' B) (f '' J)
      (f '' S₀) (f '' S₁) := by
  obtain ⟨-, hBsource, O, hOopen, hJO, hBO, hOA⟩ := h
  let e : K.space ≃ₜ K'.space := hf.homeomorph
  let W : Set K.space := (Subtype.val : K.space → E) ⁻¹' O
  have hWopen : IsOpen W := hOopen.preimage continuous_subtype_val
  have heWopen : IsOpen (e '' W) := e.isOpenMap W hWopen
  obtain ⟨V, hVopen, hVeW⟩ := isOpen_induced_iff.mp heWopen
  refine ⟨hA, hB, V, hVopen, ?_, ?_, ?_⟩
  · rintro y ⟨x, hxJ, rfl⟩
    have hxK : x ∈ K.space := hJK hxJ
    have hxeW : e ⟨x, hxK⟩ ∈ e '' W :=
      ⟨⟨x, hxK⟩, hJO hxJ, rfl⟩
    have hxeV : e ⟨x, hxK⟩ ∈ (Subtype.val : K'.space → F) ⁻¹' V := by
      rw [hVeW]
      exact hxeW
    exact hxeV
  · rintro y ⟨x, hxB, rfl⟩
    have hxK : x ∈ K.space := hBsource.subset_ambient hxB
    have hxeW : e ⟨x, hxK⟩ ∈ e '' W :=
      ⟨⟨x, hxK⟩, (hBO hxB).1, rfl⟩
    have hxeV : e ⟨x, hxK⟩ ∈ (Subtype.val : K'.space → F) ⁻¹' V := by
      rw [hVeW]
      exact hxeW
    exact ⟨hxeV, hf.bijOn.mapsTo hxK⟩
  · rintro y ⟨hyV, hyK'⟩
    have hyeW : (⟨y, hyK'⟩ : K'.space) ∈ e '' W := by
      rw [← hVeW]
      exact hyV
    obtain ⟨x, hxW, hxy⟩ := hyeW
    refine ⟨x, hOA ⟨hxW, x.2⟩, ?_⟩
    exact congrArg Subtype.val hxy

open Classical in
theorem IsGlueIso.exists_common_annular_derivedNeighborhood_transport
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} {K' : Geometry.SimplicialComplex ℝ F}
    [Finite K.faces] {φ : E → F} {ψ : F → E} (hK : IsGlueIso K K' φ ψ)
    {J S₀ S₁ U : Set E}
    (hJ : IsPLSphere 1 J) (hS₀ : IsPLSphere 2 S₀) (hS₁ : IsPLSphere 2 S₁)
    (hJK : J ⊆ K.space) (hS₀K : S₀ ⊆ K.space) (hS₁K : S₁ ⊆ K.space)
    (hJS₀ : J ⊆ S₀) (hJS₁ : J ⊆ S₁) (hU : IsOpen U) (hJU : J ⊆ U) :
    ∃ N : Set E,
      IsCommonAnnularDerivedNeighborhood K N J S₀ S₁ ∧ N ⊆ U ∧
        IsCommonAnnularDerivedNeighborhood K' (simplicialMap K φ '' N)
          (simplicialMap K φ '' J) (simplicialMap K φ '' S₀)
          (simplicialMap K φ '' S₁) := by
  obtain ⟨N, hN, hNU⟩ := exists_common_annular_derivedNeighborhood K hJ hS₀ hS₁
    hJK hS₀K hS₁K hJS₀ hJS₁ hU hJU
  obtain ⟨R, L, P₀, P₁, hRfin, hLfin, hP₀fin, hP₁fin, hRK, hLspace,
    hP₀space, hP₁space, hP₀R, hP₁R, hLP₀, hLP₁, hRN, hNnhds,
    htrace₀, htrace₁, hH₀, hH₁⟩ := hN
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let _ : Finite P₀.faces := hP₀fin.to_subtype
  let _ : Finite P₁.faces := hP₁fin.to_subtype
  let f := simplicialMap K φ
  let g := simplicialMap K' ψ
  obtain ⟨R', hR'K', hR'fin, hR'R⟩ := hK.symm.exists_isSubdivision R hRK
  let _ : Finite R'.faces := hR'fin.to_subtype
  have hRR' : IsGlueIso R R' f g := hR'R.symm
  have hLR : L.faces ⊆ R.faces := hLP₀.trans hP₀R
  obtain ⟨L', hL'R', hLL'⟩ := hRR'.exists_subcomplex L hLR
  obtain ⟨P₀', hP₀'R', hP₀P₀'⟩ := hRR'.exists_subcomplex P₀ hP₀R
  obtain ⟨P₁', hP₁'R', hP₁P₁'⟩ := hRR'.exists_subcomplex P₁ hP₁R
  have hL'fin : L'.faces.Finite := hR'fin.subset hL'R'
  have hP₀'fin : P₀'.faces.Finite := hR'fin.subset hP₀'R'
  have hP₁'fin : P₁'.faces.Finite := hR'fin.subset hP₁'R'
  let _ : Finite L'.faces := hL'fin.to_subtype
  let _ : Finite P₀'.faces := hP₀'fin.to_subtype
  let _ : Finite P₁'.faces := hP₁'fin.to_subtype
  have hL'P₀' : L'.faces ⊆ P₀'.faces := by
    intro t ht
    have ht' := hP₀P₀'.image₁ (t.image g) (hLP₀ (hLL'.image₂ t ht))
    rwa [hLL'.image_image_right ht] at ht'
  have hL'P₁' : L'.faces ⊆ P₁'.faces := by
    intro t ht
    have ht' := hP₁P₁'.image₁ (t.image g) (hLP₁ (hLL'.image₂ t ht))
    rwa [hLL'.image_image_right ht] at ht'
  have hRmap : EqOn (simplicialMap R f) f R.space :=
    hRK.simplicialMap_simplicialMap_eq φ
  have hsubmap (C : Geometry.SimplicialComplex ℝ E) (hCR : C.faces ⊆ R.faces) :
      EqOn (simplicialMap C f) f C.space :=
    (simplicialMap_eqOn_of_faces_subset R C hCR f).symm.trans
      (hRmap.mono (space_mono_of_faces_subset hCR))
  have hL'space : L'.space = f '' J := by
    calc
      L'.space = simplicialMap L f '' L.space := hLL'.image_left.symm
      _ = f '' L.space := (hsubmap L hLR).image_eq
      _ = f '' J := congrArg (fun A : Set E => f '' A) hLspace
  have hP₀'space : P₀'.space = f '' S₀ := by
    calc
      P₀'.space = simplicialMap P₀ f '' P₀.space := hP₀P₀'.image_left.symm
      _ = f '' P₀.space := (hsubmap P₀ hP₀R).image_eq
      _ = f '' S₀ := congrArg (fun A : Set E => f '' A) hP₀space
  have hP₁'space : P₁'.space = f '' S₁ := by
    calc
      P₁'.space = simplicialMap P₁ f '' P₁.space := hP₁P₁'.image_left.symm
      _ = f '' P₁.space := (hsubmap P₁ hP₁R).image_eq
      _ = f '' S₁ := congrArg (fun A : Set E => f '' A) hP₁space
  let BR := DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision R
  let Φ := simplicialMap BR (simplicialMap R f)
  have hBRmap : EqOn Φ (simplicialMap R f) BR.space :=
    (barycentricSubdivision_isSubdivision R).simplicialMap_simplicialMap_eq f
  have hDNBR :
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood R L).space ⊆
        BR.space := by
    rw [(barycentricSubdivision_isSubdivision R).space_eq]
    exact derivedNeighborhood_space_subset R L
  have hΦ : EqOn Φ f
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood R L).space :=
    (hBRmap.mono hDNBR).trans (hRmap.mono (derivedNeighborhood_space_subset R L))
  have htransport := hRR'.image_derivedNeighborhood hLL' hLR hL'R'
  have hR'N :
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood R' L').space =
        f '' N := by
    calc
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood R' L').space =
          Φ ''
            (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood R L).space :=
        htransport.symm
      _ = f ''
          (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood R L).space :=
        hΦ.image_eq
      _ = f '' N := congrArg (fun A : Set E => f '' A) hRN
  have hN'nhdsPoint : ∀ x ∈ f '' J,
      f '' N ∈ 𝓝[K'.space] x := by
    intro x hx
    rw [← hL'space] at hx
    rw [← hR'N, ← hR'K'.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin hL'R' hx
  have hN'nhds : f '' N ∈ nhdsSetWithin (f '' J) K'.space := by
    choose O hOopen hxO hOsub using fun x : f '' J => mem_nhdsWithin.mp (hN'nhdsPoint x x.2)
    refine mem_nhdsSetWithin.mpr ⟨⋃ x : f '' J, O x, isOpen_iUnion hOopen, ?_, ?_⟩
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩
    · rintro x ⟨hxO, hxK'⟩
      obtain ⟨y, hxy⟩ := mem_iUnion.mp hxO
      exact hOsub y ⟨hxy, hxK'⟩
  have htrace₀' : f '' N ∩ f '' S₀ =
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood P₀' L').space := by
    rw [← hR'N, ← hP₀'space]
    exact derivedNeighborhood_space_inter_subcomplex R' P₀' L' hP₀'R'
  have htrace₁' : f '' N ∩ f '' S₁ =
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood P₁' L').space := by
    rw [← hR'N, ← hP₁'space]
    exact derivedNeighborhood_space_inter_subcomplex R' P₁' L' hP₁'R'
  have hL'sphere : IsPLSphere 1 L'.space :=
    (hLspace.symm ▸ hJ).of_isPLHomeomorphOn hLL'.isPLHomeomorphOn
  have hP₀'sphere : IsPLSphere 2 P₀'.space :=
    (hP₀space.symm ▸ hS₀).of_isPLHomeomorphOn hP₀P₀'.isPLHomeomorphOn
  have hP₁'sphere : IsPLSphere 2 P₁'.space :=
    (hP₁space.symm ▸ hS₁).of_isPLHomeomorphOn hP₁P₁'.isPLHomeomorphOn
  obtain ⟨H₀', hH₀'⟩ := exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle P₀' L'
    hP₀'sphere.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hL'P₀'
    hL'sphere.isCombinatorialManifold hL'sphere.isConnected
    (isOrientable_of_isPLSphere hP₀'sphere)
  obtain ⟨H₁', hH₁'⟩ := exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle P₁' L'
    hP₁'sphere.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hL'P₁'
    hL'sphere.isCombinatorialManifold hL'sphere.isConnected
    (isOrientable_of_isPLSphere hP₁'sphere)
  refine ⟨N, ?_, hNU, ?_⟩
  · exact ⟨R, L, P₀, P₁, hRfin, hLfin, hP₀fin, hP₁fin, hRK, hLspace,
      hP₀space, hP₁space, hP₀R, hP₁R, hLP₀, hLP₁, hRN, hNnhds,
      htrace₀, htrace₁, hH₀, hH₁⟩
  · exact ⟨R', L', P₀', P₁', hR'fin, hL'fin, hP₀'fin, hP₁'fin, hR'K',
      hL'space, hP₀'space, hP₁'space, hP₀'R', hP₁'R', hL'P₀', hL'P₁',
      hR'N, hN'nhds, htrace₀', htrace₁', ⟨H₀', htrace₀' ▸ hH₀'⟩,
      H₁', htrace₁' ▸ hH₁'⟩

open Classical in
theorem IsGlueIso.exists_nested_common_annular_derivedNeighborhood_transport
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} {K' : Geometry.SimplicialComplex ℝ F}
    [Finite K.faces] {φ : E → F} {ψ : F → E} (hK : IsGlueIso K K' φ ψ)
    {J S₀ S₁ U V : Set E}
    (hJ : IsPLSphere 1 J) (hS₀ : IsPLSphere 2 S₀) (hS₁ : IsPLSphere 2 S₁)
    (hJK : J ⊆ K.space) (hS₀K : S₀ ⊆ K.space) (hS₁K : S₁ ⊆ K.space)
    (hJS₀ : J ⊆ S₀) (hJS₁ : J ⊆ S₁)
    (hU : IsOpen U) (hJU : J ⊆ U) (hV : IsOpen V) (hJV : J ⊆ V) :
    ∃ A B : Set E,
      IsNestedCommonAnnularDerivedNeighborhood K A B J S₀ S₁ ∧
        A ⊆ U ∧ B ⊆ V ∧
        IsNestedCommonAnnularDerivedNeighborhood K'
          (simplicialMap K φ '' A) (simplicialMap K φ '' B)
          (simplicialMap K φ '' J) (simplicialMap K φ '' S₀)
          (simplicialMap K φ '' S₁) := by
  obtain ⟨A, hA, hAU, hA'⟩ :=
    hK.exists_common_annular_derivedNeighborhood_transport hJ hS₀ hS₁
      hJK hS₀K hS₁K hJS₀ hJS₁ hU hJU
  obtain ⟨O, hOopen, hJO, hOKA⟩ := mem_nhdsSetWithin.mp hA.mem_nhdsSetWithin
  obtain ⟨B, hB, hBOV, hB'⟩ :=
    hK.exists_common_annular_derivedNeighborhood_transport hJ hS₀ hS₁
      hJK hS₀K hS₁K hJS₀ hJS₁ (hOopen.inter hV) (subset_inter hJO hJV)
  have hBO : B ⊆ O := hBOV.trans inter_subset_left
  have hBV : B ⊆ V := hBOV.trans inter_subset_right
  have hAB : IsNestedCommonAnnularDerivedNeighborhood K A B J S₀ S₁ :=
    ⟨hA, hB, O, hOopen, hJO,
      fun x hx => ⟨hBO hx, hB.subset_ambient hx⟩, hOKA⟩
  have hK'fin : K'.faces.Finite := by
    rw [hK.faces_eq_simplicialImageFaces]
    refine ((Set.toFinite K.faces).image fun s => s.image φ).subset ?_
    rintro t ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  let _ : Finite K'.faces := hK'fin.to_subtype
  exact ⟨A, B, hAB, hAU, hBV,
    hAB.image_of_isPLHomeomorphOn hK.isPLHomeomorphOn hJK hA' hB'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
