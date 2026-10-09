/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteGraphExhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

open Classical in
theorem LocallyFinitePLPieceIn.exists_linearEquiv_transport
    [FiniteDimensional ℝ F] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E n X U) (e : E ≃ₗ[ℝ] F) :
    ∃ T' : LocallyFinitePLPieceIn F n X U,
      IsGlueIso T.complex T'.complex e e.symm ∧ T'.map = T.map ∘ e.symm := by
  have hind : ∀ s ∈ T.complex.faces,
      AffineIndependent ℝ ((↑) : {u // u ∈ s.image e} → F) := fun s hs =>
    affineIndependent_image_of_injOn_convexHull e.toLinearMap.toAffineMap
      (T.complex.indep hs) e.injective.injOn
  have hmap : EqOn (simplicialMap T.complex e) e T.complex.space :=
    simplicialMap_eq_of_forall_affineOn T.complex e fun _ _ =>
      ⟨e.toLinearMap.toAffineMap, fun _ _ => rfl⟩
  have hinj : InjOn (simplicialMap T.complex e) T.complex.space := fun x hx y hy hxy =>
    e.injective ((hmap hx).symm.trans (hxy.trans (hmap hy)))
  let K := simplicialImage T.complex e hind hinj
  have hiso : IsGlueIso T.complex K e e.symm :=
    isGlueIso_of_faces_eq_linearEquiv T.complex K e rfl
  have hspace : K.space = e '' T.complex.space :=
    (simplicialImage_space T.complex e hind hinj).trans hmap.image_eq
  have hinverse (y : F) : e.symm y ∈ T.complex.space ↔ y ∈ K.space := by
    rw [hspace]
    exact ⟨fun hy => ⟨e.symm y, hy, e.apply_symm_apply y⟩,
      fun ⟨x, hx, heq⟩ => by simpa only [← heq, e.symm_apply_apply] using hx⟩
  have hbij : BijOn (T.map ∘ e.symm) K.space U := T.bijOn.comp
    ⟨fun y hy => (hinverse y).mpr hy, e.symm.injective.injOn,
      fun x hx => ⟨e x, (hinverse (e x)).mp (by simpa using hx), e.symm_apply_apply x⟩⟩
  let g : K.space → T.complex.space := fun y => ⟨e.symm y, (hinverse y).mpr y.2⟩
  have hg : Continuous g :=
    (e.symm.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).subtype_mk _
  have hgemb : IsEmbedding g :=
    (e.symm.toContinuousLinearEquiv.toHomeomorph.isEmbedding.comp
      IsEmbedding.subtypeVal).codRestrict T.complex.space (fun y => (hinverse y).mpr y.2)
  let f : K.faces → T.complex.faces := fun s => ⟨s.1.image e.symm, hiso.image₂ s.1 s.2⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    exact (Finset.image_injective e.symm.injective) (congrArg Subtype.val hst)
  have hlocal : LocallyFinite fun s : K.faces =>
      (Subtype.val : K.space → F) ⁻¹' convexHull ℝ (s.1 : Set F) := by
    apply ((T.locallyFinite.comp_injective hf).preimage_continuous hg).subset
    intro s y hy
    change e.symm (y : F) ∈ convexHull ℝ (↑(s.1.image e.symm) : Set E)
    rw [Finset.coe_image]
    exact (e.symm.toLinearMap.image_convexHull (s.1 : Set F)).subset ⟨y, hy, rfl⟩
  let T' : LocallyFinitePLPieceIn F n X U := {
    complex := K
    locallyFinite := hlocal
    map := T.map ∘ e.symm
    bijOn := hbij
    continuousOn := T.continuousOn.comp e.symm.toContinuousLinearEquiv.continuous.continuousOn
      (fun y hy => (hinverse y).mpr hy)
    isEmbedding := T.isEmbedding.comp hgemb
    isPiecewiseAffineOn_chart := by
      intro ct hct
      have h := (T.isPiecewiseAffineOn_chart ct hct).comp
        (isPiecewiseAffineOn_of_affine e.symm.toLinearMap.toAffineMap isOpen_univ)
      change IsPiecewiseAffineOn ((ct ∘ T.map) ∘ e.symm)
        (univ ∩ e.symm ⁻¹' (T.complex.space ∩ T.map ⁻¹' ct.source)) at h
      have hset : univ ∩ e.symm ⁻¹' (T.complex.space ∩ T.map ⁻¹' ct.source) =
          K.space ∩ (T.map ∘ e.symm) ⁻¹' ct.source := by
        ext y
        simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, Function.comp_apply,
          hinverse]
      rw [hset] at h
      exact h.congr fun _ _ => rfl
    isPiecewiseAffineOn_chart_symm := by
      intro ct hct
      have h := (T.isPiecewiseAffineOn_chart_symm ct hct).affine_comp e.toLinearMap.toAffineMap
      refine h.congr fun y hy => ?_
      have h1 : Function.invFunOn (T.map ∘ e.symm) K.space (ct.symm y) ∈ K.space :=
        hbij.surjOn.mapsTo_invFunOn hy.2
      have h2 := hbij.invOn_invFunOn.2 hy.2
      have h3 : Function.invFunOn T.map T.complex.space (ct.symm y) ∈ T.complex.space :=
        T.bijOn.surjOn.mapsTo_invFunOn hy.2
      have h4 := T.bijOn.invOn_invFunOn.2 hy.2
      have h5 : e.symm (Function.invFunOn (T.map ∘ e.symm) K.space (ct.symm y)) =
          Function.invFunOn T.map T.complex.space (ct.symm y) :=
        T.bijOn.injOn ((hinverse _).mpr h1) h3 (h2.trans h4.symm)
      change Function.invFunOn (T.map ∘ e.symm) K.space (ct.symm y) =
        e (Function.invFunOn T.map T.complex.space (ct.symm y))
      rw [← h5, e.apply_symm_apply] }
  exact ⟨T', hiso, rfl⟩

open Classical in
theorem LocallyFinitePLPieceIn.isCombinatorialManifoldWithBoundary_of_isGlueIso
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {d n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E d X U) (T' : LocallyFinitePLPieceIn F d X U)
    {φ : E → F} {ψ : F → E} (h : IsGlueIso T.complex T'.complex φ ψ)
    (hT : IsCombinatorialManifoldWithBoundary (n + 1) T.complex) :
    IsCombinatorialManifoldWithBoundary (n + 1) T'.complex := by
  intro w hw
  have hv : {ψ w} ∈ T.complex.faces := by simpa using h.image₂ {w} hw
  have hvw : φ (ψ w) = w := h.right {w} hw w (Finset.mem_singleton_self w)
  let _ : Finite (SimplicialComplex.geometricLink T.complex {ψ w}).faces :=
    (T.geometricLink_faces_finite hv).to_subtype
  let _ : Finite (SimplicialComplex.geometricLink T'.complex {w}).faces :=
    (T'.geometricLink_faces_finite hw).to_subtype
  have hlink := h.geometricLink hv
  rw [hvw] at hlink
  rcases hT (ψ w) hv with hs | hb
  · exact Or.inl (hs.of_isPLHomeomorphOn hlink.isPLHomeomorphOn)
  · exact Or.inr (hb.of_isPLHomeomorphOn hlink.isPLHomeomorphOn)

open Classical in
theorem IsGlueIso.secondDerived_linearEquiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {K : Geometry.SimplicialComplex ℝ E} {K' : Geometry.SimplicialComplex ℝ F}
    (e : E ≃ₗ[ℝ] F) (h : IsGlueIso K K' e e.symm) :
    IsGlueIso (PiecewiseLinear.secondDerived K) (PiecewiseLinear.secondDerived K') e e.symm := by
  have heq : EqOn (simplicialMap (PiecewiseLinear.barycentricSubdivision K) (simplicialMap K e)) e
      K.space := by
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact ((barycentricSubdivision_isSubdivision K).simplicialMap_simplicialMap_eq e).trans
      ((simplicialMap_eq_of_forall_affineOn K e fun _ _ =>
        ⟨e.toLinearMap.toAffineMap, fun _ _ => rfl⟩).mono
          (barycentricSubdivision_isSubdivision K).space_eq.subset)
  have heq' : EqOn (simplicialMap (PiecewiseLinear.barycentricSubdivision K')
      (simplicialMap K' e.symm))
      e.symm K'.space := by
    rw [← (barycentricSubdivision_isSubdivision K').space_eq]
    exact ((barycentricSubdivision_isSubdivision K').simplicialMap_simplicialMap_eq e.symm).trans
      ((simplicialMap_eq_of_forall_affineOn K' e.symm fun _ _ =>
        ⟨e.symm.toLinearMap.toAffineMap, fun _ _ => rfl⟩).mono
          (barycentricSubdivision_isSubdivision K').space_eq.subset)
  refine ⟨?_, ?_, fun _ _ v _ => e.symm_apply_apply v,
    fun _ _ v _ => e.apply_symm_apply v⟩
  · intro s hs
    have himage := h.secondDerived.image₁ s hs
    have hfin : s.image (simplicialMap (PiecewiseLinear.barycentricSubdivision K)
        (simplicialMap K e)) = s.image e := Finset.image_congr fun v hv => heq
      ((secondDerived_isSubdivision K).space_eq.subset
        ((PiecewiseLinear.secondDerived K).convexHull_subset_space hs (subset_convexHull ℝ _ hv)))
    rwa [hfin] at himage
  · intro s hs
    have himage := h.secondDerived.image₂ s hs
    have hfin : s.image (simplicialMap (PiecewiseLinear.barycentricSubdivision K')
        (simplicialMap K' e.symm)) = s.image e.symm := Finset.image_congr fun v hv => heq'
      ((secondDerived_isSubdivision K').space_eq.subset
        ((PiecewiseLinear.secondDerived K').convexHull_subset_space hs (subset_convexHull ℝ _ hv)))
    rwa [hfin] at himage

open Classical in
theorem IsGlueIso.image_derivedNeighborhood_linearEquiv
    [FiniteDimensional ℝ E]
    {K L : Geometry.SimplicialComplex ℝ E} {K' L' : Geometry.SimplicialComplex ℝ F}
    (e : E ≃ₗ[ℝ] F) (hK : IsGlueIso K K' e e.symm) (hL : IsGlueIso L L' e e.symm)
    (hLK : L.faces ⊆ K.faces) (hL'K' : L'.faces ⊆ K'.faces) :
    e '' (PiecewiseLinear.derivedNeighborhood K L).space =
      (PiecewiseLinear.derivedNeighborhood K' L').space := by
  have heq : EqOn (simplicialMap (PiecewiseLinear.barycentricSubdivision K) (simplicialMap K e)) e
      (PiecewiseLinear.barycentricSubdivision K).space :=
    ((barycentricSubdivision_isSubdivision K).simplicialMap_simplicialMap_eq e).trans
      ((simplicialMap_eq_of_forall_affineOn K e fun _ _ =>
        ⟨e.toLinearMap.toAffineMap, fun _ _ => rfl⟩).mono
          (barycentricSubdivision_isSubdivision K).space_eq.subset)
  have hsub : (PiecewiseLinear.derivedNeighborhood K L).space ⊆
      (PiecewiseLinear.barycentricSubdivision K).space := by
    rw [(barycentricSubdivision_isSubdivision K).space_eq]
    exact derivedNeighborhood_space_subset K L
  exact (heq.mono hsub).image_eq.symm.trans (hK.image_derivedNeighborhood hL hLK hL'K')

open Classical in
theorem LocallyFinitePLPieceIn.isPLDerivedNeighborhoodExhaustion_secondDerived_of_finiteDimensional
    [FiniteDimensional ℝ E] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E 3 X U)
    (hT : IsCombinatorialManifoldWithBoundary 3 T.complex)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ (secondDerived T.complex).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) :
    IsPLDerivedNeighborhoodExhaustion (n := 3)
      (T.map '' (derivedNeighborhood (secondDerived T.complex) L).space)
      (T.map '' L.space) U := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := Classical.decEq _
  let e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  obtain ⟨T', hiso, hmap⟩ := T.exists_linearEquiv_transport e
  have hT' := T.isCombinatorialManifoldWithBoundary_of_isGlueIso T' hiso hT
  have hisoJ := hiso.secondDerived_linearEquiv e
  obtain ⟨L', hL', hisoL⟩ := hisoJ.exists_subcomplex L hL
  have hcard' : ∀ s ∈ L'.faces, s.card ≤ 2 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hisoL.faces_eq_simplicialImageFaces.subset hs
    rw [Finset.card_image_of_injective _ e.injective]
    exact hcard t ht
  have hPL := T'.isPLDerivedNeighborhoodExhaustion_secondDerived hT' L' hL' hcard'
  have hD := hisoJ.image_derivedNeighborhood_linearEquiv e hisoL hL hL'
  have hCore : e '' L.space = L'.space :=
    (simplicialMap_eq_of_forall_affineOn L e fun _ _ =>
      ⟨e.toLinearMap.toAffineMap, fun _ _ => rfl⟩).image_eq.symm.trans hisoL.image_left
  have hNimage : T'.map '' (derivedNeighborhood (secondDerived T'.complex) L').space =
      T.map '' (derivedNeighborhood (secondDerived T.complex) L).space := by
    rw [← hD, hmap, image_image]
    simp only [Function.comp_def, e.symm_apply_apply]
  have hCoreImage : T'.map '' L'.space = T.map '' L.space := by
    rw [← hCore, hmap, image_image]
    simp only [Function.comp_def, e.symm_apply_apply]
  rwa [hNimage, hCoreImage] at hPL

end DifferentialGeometry.Topology.PiecewiseLinear
