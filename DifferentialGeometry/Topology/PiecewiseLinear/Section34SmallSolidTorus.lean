import DifferentialGeometry.Topology.PiecewiseLinear.Section34SmallRegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusOnPolyhedralCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCircleLevels

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLDerivedNeighborhoodExhaustion.exists_solidTorus_regularNeighborhood_with_circle_levels
    {X ι : Type*} [Finite ι] [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) (F : ι → Set X)
    (hF : ∀ i, IsPolyhedralSphere (n := 3) 2 (F i)) (hFU : ∀ i, F i ⊆ U)
    (hCF : ∀ i, C ⊆ F i) :
    ∃ S : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsTopologicalSolidTorus S ∧ S ⊆ O ∩ interior D ∧
      ∀ i, ∃ (φ : (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ≃ₜ ↥(S ∩ F i)) (t : ℝ),
        t ∈ Ioo (0 : ℝ) 1 ∧ Subtype.val '' (φ '' {p | p.1.2 = t}) = C := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨m, T, A, -, hcover, hfin, -, -, hman, -, hmono, -⟩ := h
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  have hCU : C ⊆ U := hCD.trans (interior_subset.trans hDU)
  let Q := T.complex.space ∩ T.map ⁻¹' C
  have hQ : IsPLSphere 1 Q :=
    T.isPLSphere_preimage_of_isPolyhedralSphere A hcover hfin hmono hC hCU
  let P := T.complex.space ∩ T.map ⁻¹' D
  have hP : IsPLBall 3 P :=
    T.isPLBall_preimage_of_isPolyhedralBall A hcover hfin hmono hD hDU
  have hQP : Q ⊆ P := inter_subset_inter_right _ (preimage_mono (hCD.trans interior_subset))
  let F' := fun i => T.complex.space ∩ T.map ⁻¹' F i
  have hF' (i) : IsPLSphere 2 (F' i) :=
    T.isPLSphere_preimage_of_isPolyhedralSphere A hcover hfin hmono (hF i) (hFU i)
  let V : Option (Option ι) → Set (EuclideanSpace ℝ (Fin m)) := fun j =>
    match j with
    | none => P
    | some none => Q
    | some (some i) => F' i
  have hVP (j) : IsPolyhedron (V j) := by
    rcases j with _ | (_ | i)
    · exact hP.isPolyhedron
    · exact hQ.isPolyhedron
    · exact (hF' i).isPolyhedron
  have hVT (j) : V j ⊆ T.complex.space := by
    rcases j with _ | (_ | i) <;> exact inter_subset_left
  obtain ⟨R, hR, hnew, hRV⟩ := T.exists_isSubdivision_restrict_family_finite_change
    A hcover hfin hmono Finset.univ V (fun j _ => hVP j) (fun j _ => hVT j)
  have hRP : (restrict R P).space = P := hRV none (Finset.mem_univ _)
  have hRQ : (restrict R Q).space = Q := hRV (some none) (Finset.mem_univ _)
  have hRF (i) : (restrict R (F' i)).space = F' i :=
    hRV (some (some i)) (Finset.mem_univ _)
  let T₁ := T.subdivide R hR
    (T.locallyFinite_of_isSubdivision_of_finite_new_faces hR hnew)
  have hcardT : ∀ s ∈ T.complex.faces, s.card ≤ 3 + 1 := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ▸ hs)
    have : Finite (A i).faces := (hfin i).to_subtype
    exact (hman i).card_le (A i) hi
  have hCc : IsCompact C := by
    obtain ⟨P, -⟩ := hC
    rw [← P.piece.bijOn.image_eq]
    exact P.piece.isPolyhedron_space.isCompact.image_of_continuousOn P.piece.continuousOn
  let W : Bool → Set X := fun b => if b then O ∩ interior D else Cᶜ
  have hW : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact hCc.isClosed.isOpen_compl
    · exact hO.inter isOpen_interior
  have hUW : U ⊆ ⋃ b, W b := by
    intro x _
    by_cases hxC : x ∈ C
    · exact mem_iUnion.mpr ⟨true, hCO hxC, hCD hxC⟩
    · exact mem_iUnion.mpr ⟨false, hxC⟩
  obtain ⟨S, hS, hSLF, hstar⟩ := T₁.exists_isSubdivision_forall_image_subset
    (fun s hs => hR.card_le hcardT hs) W hW hUW
  have hST : IsSubdivision S T.complex := hS.trans hR
  let T₂ := T.subdivide S hST hSLF
  let G := restrict S Q
  have hGspace : G.space = Q := by
    have he := (hS.restrict (restrict R Q) (restrict_faces_subset R Q)).space_eq
    rwa [hRQ] at he
  have hQS : Q ⊆ S.space := inter_subset_left.trans hST.space_eq.symm.subset
  have hGfin : G.faces.Finite := by
    apply (T₂.finite_faces_inter_of_isCompact hQ.isPolyhedron.isCompact hQS).subset
    rintro s ⟨hs, hsc⟩
    have hx : s.centroid ℝ id ∈ convexHull ℝ (s : Set _) :=
      s.centroid_mem_convexHull (S.nonempty_of_mem_faces hs)
    exact ⟨hs, s.centroid ℝ id, hx, hsc hx⟩
  have : Finite G.faces := hGfin.to_subtype
  have hG : IsPLSphere 1 G.space := hGspace.symm ▸ hQ
  have hcardG : ∀ s ∈ G.faces, s.card ≤ 2 := fun s hs => card_le_of_isPLSphere G hG hs
  have hreg := T.isLocallyFiniteRegularNeighborhoodOf_locallyFinite_subdivision
    hU A hcover hfin hmono hman S hST hSLF G (restrict_faces_subset S Q) hcardG
  have himage : T.map '' G.space = C := by
    rw [hGspace]
    change T.map '' (T.complex.space ∩ T.map ⁻¹' C) = C
    rw [image_inter_preimage, T.bijOn.image_eq, inter_eq_right.mpr hCU]
  have hsmall : T.map '' (derivedNeighborhood S G).space ⊆ O ∩ interior D := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨s, hs, ⟨y, hys, hyG⟩, hzs⟩ := exists_face_meets_of_mem_derivedNeighborhood_space hz
    obtain ⟨b, hb⟩ := hstar s hs
    obtain ⟨v, hv⟩ := S.nonempty_of_mem_faces hs
    have hyW := hb v hv s hs hv (mem_image_of_mem T.map hys)
    have hzW := hb v hv s hs hv (mem_image_of_mem T.map hzs)
    cases b
    · exact (hyW ((hGspace.subset hyG).2)).elim
    · exact hzW
  let B := restrict S P
  have hBspace : B.space = P := by
    have he := (hS.restrict (restrict R P) (restrict_faces_subset R P)).space_eq
    rwa [hRP] at he
  have hPS : P ⊆ S.space := inter_subset_left.trans hST.space_eq.symm.subset
  have hBfin : B.faces.Finite := by
    apply (T₂.finite_faces_inter_of_isCompact hP.isPolyhedron.isCompact hPS).subset
    rintro s ⟨hs, hsc⟩
    have hx : s.centroid ℝ id ∈ convexHull ℝ (s : Set _) :=
      s.centroid_mem_convexHull (S.nonempty_of_mem_faces hs)
    exact ⟨hs, s.centroid ℝ id, hx, hsc hx⟩
  have : Finite B.faces := hBfin.to_subtype
  have hBball : IsPLBall 3 B.space := hBspace.symm ▸ hP
  have hGB : G.faces ⊆ B.faces := fun _ hs => ⟨hs.1, hs.2.trans hQP⟩
  have hNB : (derivedNeighborhood S G).space ⊆ B.space := by
    intro x hx
    apply hBspace.symm.subset
    exact ⟨hST.space_eq.subset (derivedNeighborhood_space_subset S G hx),
      (interior_subset : interior D ⊆ D) (hsmall (mem_image_of_mem T.map hx)).2⟩
  have hNspace : (derivedNeighborhood S G).space = (derivedNeighborhood B G).space := by
    have he := derivedNeighborhood_space_inter_subcomplex S B G (restrict_faces_subset S P)
    rwa [inter_eq_left.mpr hNB] at he
  have hsolid : IsTopologicalSolidTorus (derivedNeighborhood S G).space := by
    rw [hNspace]
    exact (isCombinatorialSolidTorus_derivedNeighborhood_circle B G
      hBball.isCombinatorialManifoldWithBoundary hGB hG.isCombinatorialManifold
      hG.isConnected (isOrientable_of_isPLBall hBball)).1
  have hNT : (derivedNeighborhood S G).space ⊆ T.complex.space :=
    (derivedNeighborhood_space_subset S G).trans hST.space_eq.subset
  let f : (derivedNeighborhood S G).space → X := fun x => T.map x
  have hf : IsEmbedding f := T.isEmbedding.comp (IsEmbedding.inclusion hNT)
  have hrange : range f = T.map '' (derivedNeighborhood S G).space := by
    exact (Set.image_eq_range T.map (derivedNeighborhood S G).space).symm
  obtain ⟨φ⟩ := hsolid
  refine ⟨T.map '' (derivedNeighborhood S G).space, himage ▸ hreg,
    ⟨((hf.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm).trans φ⟩, hsmall, ?_⟩
  intro i
  let H := restrict S (F' i)
  have hHspace : H.space = F' i := by
    have he := (hS.restrict (restrict R (F' i)) (restrict_faces_subset R (F' i))).space_eq
    rwa [hRF i] at he
  have hHS : F' i ⊆ S.space := inter_subset_left.trans hST.space_eq.symm.subset
  have hHfin : H.faces.Finite := by
    apply (T₂.finite_faces_inter_of_isCompact (hF' i).isPolyhedron.isCompact hHS).subset
    rintro t ⟨ht, htc⟩
    have hx : t.centroid ℝ id ∈ convexHull ℝ (t : Set _) :=
      t.centroid_mem_convexHull (S.nonempty_of_mem_faces ht)
    exact ⟨ht, t.centroid ℝ id, hx, htc hx⟩
  have : Finite H.faces := hHfin.to_subtype
  have hHsphere : IsPLSphere 2 H.space := hHspace.symm ▸ hF' i
  have hGH : G.faces ⊆ H.faces := by
    intro t ht
    exact ⟨ht.1, fun x hx => ⟨(ht.2 hx).1, hCF i (ht.2 hx).2⟩⟩
  obtain ⟨ψ, t, hψ, ht, hψG⟩ :=
    exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle_level H G
      hHsphere.isCombinatorialManifold hGH hG (isOrientable_of_isPLSphere hHsphere)
  have htrace : (derivedNeighborhood S G).space ∩ F' i =
      (derivedNeighborhood H G).space := by
    have he := derivedNeighborhood_space_inter_subcomplex S H G
      (restrict_faces_subset S (F' i))
    rwa [hHspace] at he
  have htraceT : (derivedNeighborhood H G).space ⊆ T.complex.space := by
    rw [← htrace]
    exact inter_subset_left.trans hNT
  let g : (derivedNeighborhood H G).space → X := fun x => T.map x
  have hg : IsEmbedding g := T.isEmbedding.comp (IsEmbedding.inclusion htraceT)
  have hgimage : T.map '' (derivedNeighborhood H G).space =
      (T.map '' (derivedNeighborhood S G).space) ∩ F i := by
    rw [← htrace]
    apply Subset.antisymm
    · rintro x ⟨z, ⟨hzN, hzF⟩, rfl⟩
      exact ⟨mem_image_of_mem T.map hzN, hzF.2⟩
    · rintro x ⟨⟨z, hzN, rfl⟩, hzF⟩
      exact ⟨z, ⟨hzN, hNT hzN, hzF⟩, rfl⟩
  have hgrange : range g = (T.map '' (derivedNeighborhood S G).space) ∩ F i :=
    (Set.image_eq_range T.map (derivedNeighborhood H G).space).symm.trans hgimage
  let θ := hψ.homeomorph.trans (hg.toHomeomorph.trans (Homeomorph.setCongr hgrange))
  refine ⟨θ, t, ht, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    change T.map (ψ p.1) ∈ C
    exact (hGspace.subset (hψG.subset ⟨p.1, ⟨p.2.1, hp⟩, rfl⟩)).2
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := himage.symm.subset hx
    obtain ⟨p, hp, hpz⟩ := hψG.symm.subset hz
    have hpI : p.2 ∈ Icc (0 : ℝ) 1 := hp.2 ▸ ⟨ht.1.le, ht.2.le⟩
    let p' : stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨p, hp.1, hpI⟩
    refine ⟨θ p', ⟨p', hp.2, rfl⟩, ?_⟩
    change T.map (ψ p) = x
    rw [hpz]
    exact hzx

theorem IsPLDerivedNeighborhoodExhaustion.exists_solidTorus_regularNeighborhood_with_annular_cores
    {X ι : Type*} [Finite ι] [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) (F : ι → Set X)
    (hF : ∀ i, IsPolyhedralSphere (n := 3) 2 (F i)) (hFU : ∀ i, F i ⊆ U)
    (hCF : ∀ i, C ⊆ F i) :
    ∃ S : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsTopologicalSolidTorus S ∧ S ⊆ O ∩ interior D ∧
      ∀ i, ∃ F₀ F₁ : Set X, IsAnnulusOn (S ∩ F i) F₀ F₁ ∧
        C ⊆ (S ∩ F i) \ (F₀ ∪ F₁) := by
  obtain ⟨S, hS, htS, hSO, hSF⟩ := h.exists_solidTorus_regularNeighborhood_with_circle_levels
    hU hC hD hDU hCD hO hCO F hF hFU hCF
  refine ⟨S, hS, htS, hSO, fun i => ?_⟩
  obtain ⟨φ, t, ht, hlevel⟩ := hSF i
  refine ⟨_, _, isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod φ, ?_⟩
  rw [← hlevel]
  exact annulus_level_subset_sdiff_ends φ ht

theorem IsPLDerivedNeighborhoodExhaustion.exists_solidTorus_regularNeighborhood_with_annular_traces
    {X ι : Type*} [Finite ι] [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) (F : ι → Set X)
    (hF : ∀ i, IsPolyhedralSphere (n := 3) 2 (F i)) (hFU : ∀ i, F i ⊆ U)
    (hCF : ∀ i, C ⊆ F i) :
    ∃ S : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsTopologicalSolidTorus S ∧ S ⊆ O ∩ interior D ∧
      ∀ i, ∃ F₀ F₁ : Set X, IsAnnulusOn (S ∩ F i) F₀ F₁ := by
  obtain ⟨S, hS, htS, hSO, hSF⟩ := h.exists_solidTorus_regularNeighborhood_with_annular_cores
    hU hC hD hDU hCD hO hCO F hF hFU hCF
  refine ⟨S, hS, htS, hSO, fun i => ?_⟩
  obtain ⟨F₀, F₁, hF, -⟩ := hSF i
  exact ⟨F₀, F₁, hF⟩

theorem IsPLDerivedNeighborhoodExhaustion.exists_solidTorus_regularNeighborhood_subset_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ S : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsTopologicalSolidTorus S ∧ S ⊆ O ∩ interior D := by
  obtain ⟨S, hS, htS, hSO, -⟩ := h.exists_solidTorus_regularNeighborhood_with_annular_traces
    hU hC hD hDU hCD hO hCO (fun i : Empty => i.elim)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
  exact ⟨S, hS, htS, hSO⟩

theorem IsPLDerivedNeighborhoodExhaustion.exists_nested_regularNeighborhoods_with_annular_traces
    {X ι : Type*} [Finite ι] [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) (F : ι → Set X)
    (hF : ∀ i, IsPolyhedralSphere (n := 3) 2 (F i)) (hFU : ∀ i, F i ⊆ U)
    (hCF : ∀ i, C ⊆ F i) :
    ∃ S T : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) T C U ∧
      IsTopologicalSolidTorus S ∧ IsTopologicalSolidTorus T ∧
      T ⊆ interior S ∧ S ⊆ O ∩ interior D ∧
      (∀ i, ∃ F₀ F₁ : Set X, IsAnnulusOn (S ∩ F i) F₀ F₁) ∧
      ∀ i, ∃ F₀ F₁ : Set X, IsAnnulusOn (T ∩ F i) F₀ F₁ := by
  obtain ⟨S, hS, htS, hSO, hSF⟩ :=
    h.exists_solidTorus_regularNeighborhood_with_annular_traces
      hU hC hD hDU hCD hO hCO F hF hFU hCF
  have hCS : C ⊆ interior S := subset_interior_iff_mem_nhdsSet.mpr hS.mem_nhdsSet
  obtain ⟨T, hT, htT, hTS, hTF⟩ := h.exists_solidTorus_regularNeighborhood_with_annular_traces
    hU hC hD hDU hCD isOpen_interior hCS F hF hFU hCF
  exact ⟨S, T, hS, hT, htS, htT, hTS.trans inter_subset_left, hSO, hSF, hTF⟩

theorem IsPLDerivedNeighborhoodExhaustion.exists_nested_solidTorus_regularNeighborhoods
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ S T : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) T C U ∧
      IsTopologicalSolidTorus S ∧ IsTopologicalSolidTorus T ∧
      T ⊆ interior S ∧ S ⊆ O ∩ interior D := by
  obtain ⟨S, T, hS, hT, htS, htT, hTS, hSO, -⟩ :=
    h.exists_nested_regularNeighborhoods_with_annular_traces
      hU hC hD hDU hCD hO hCO (fun i : Empty => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
  exact ⟨S, T, hS, hT, htS, htT, hTS, hSO⟩

end DifferentialGeometry.Topology.PiecewiseLinear
