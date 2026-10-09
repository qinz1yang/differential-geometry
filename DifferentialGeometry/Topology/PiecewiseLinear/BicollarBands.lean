/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarComplementCollars
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isCombinatorialManifoldWithBoundary_of_space_eq_prod_Icc
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    {a b : ℝ} (hab : a < b) (T : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite T.faces]
    (hT : T.space = L.space ×ˢ Icc a b) :
    IsCombinatorialManifoldWithBoundary 3 T := by
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods T
  intro p hp
  rw [hT] at hp ⊢
  obtain ⟨D, hD, hDL, hDnhds⟩ :=
    hL.exists_isPLBall_subset_of_mem_nhds hp.1 (U := univ) Filter.univ_mem
  refine ⟨D ×ˢ Icc a b, isPLBall_three_prod hD (isPLBall_Icc hab),
    prod_mono (hDL.trans inter_subset_left) subset_rfl, ?_⟩
  rw [show p = (p.1, p.2) from rfl, nhdsWithin_prod_eq]
  exact Filter.prod_mem_prod hDnhds self_mem_nhdsWithin

open Classical in
theorem boundaryComplex_space_of_space_eq_prod_Icc [d : DecidableEq (E × ℝ)]
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    {a b : ℝ} (hab : a < b) (T : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite T.faces]
    (hT : T.space = L.space ×ˢ Icc a b) :
    (boundaryComplex 3 T).space = L.space ×ˢ {a, b} := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst hd
  let _ : DecidableEq (E × ℝ) := fun x y => Classical.propDecidable (x = y)
  have hTm := isCombinatorialManifoldWithBoundary_of_space_eq_prod_Icc hL hab T hT
  have key : ∀ y ∈ L.space, ∀ t ∈ Icc a b,
      ((y, t) ∈ (boundaryComplex 3 T).space ↔ t = a ∨ t = b) := by
    intro y hy t ht
    obtain ⟨D, hD, hDL, hDnhds⟩ :=
      hL.exists_isPLBall_subset_of_mem_nhds hy (U := univ) Filter.univ_mem
    have hDL' : D ⊆ L.space := hDL.trans inter_subset_left
    have hyD : y ∈ D := mem_of_mem_nhdsWithin hy hDnhds
    obtain ⟨Dc, hDcfin, hDcspace⟩ := hD.isPolyhedron.exists_simplicialComplex
    let _ : Finite Dc.faces := hDcfin.to_subtype
    have hDc : IsPLBall 2 Dc.space := hDcspace.symm ▸ hD
    have hprism : IsPLBall 3 (D ×ˢ Icc a b) := isPLBall_three_prod hD (isPLBall_Icc hab)
    obtain ⟨TD, hTDfin, hTDspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
    let _ : Finite TD.faces := hTDfin.to_subtype
    have hTD : IsCombinatorialManifoldWithBoundary 3 TD :=
      IsPLBall.isCombinatorialManifoldWithBoundary (hTDspace.symm ▸ hprism)
    have hTDT : TD.space ⊆ T.space := by
      rw [hTDspace, hT]
      exact prod_mono hDL' subset_rfl
    have hzTD : (y, t) ∈ TD.space := by
      rw [hTDspace]
      exact ⟨hyD, ht⟩
    have hnhds : TD.space ∈ 𝓝[T.space] (y, t) := by
      rw [hTDspace, hT, nhdsWithin_prod_eq]
      exact Filter.prod_mem_prod hDnhds self_mem_nhdsWithin
    have h1 : (y, t) ∈ (boundaryComplex 3 TD).space ↔ (y, t) ∈ (boundaryComplex 3 T).space :=
      mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin T TD hTm hTD hTDT hzTD hnhds
    have h2 : (boundaryComplex 3 TD).space =
        Dc.space ×ˢ {a, b} ∪ (boundaryComplex 2 Dc).space ×ˢ Icc a b :=
      boundaryComplex_space_prism (d := fun x y => Classical.propDecidable (x = y))
        Dc hDc hab TD (by rw [hTDspace, hDcspace])
    have hDcL : Dc.space ⊆ L.space := by
      rw [hDcspace]
      exact hDL'
    have hyDc : y ∈ Dc.space := by
      rw [hDcspace]
      exact hyD
    have hDcnhds : Dc.space ∈ 𝓝[L.space] y := by
      rw [hDcspace]
      exact hDnhds
    have hyB : y ∉ (boundaryComplex 2 Dc).space := by
      intro hyB
      have h := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin L Dc
        hL.isCombinatorialManifoldWithBoundary hDc.isCombinatorialManifoldWithBoundary hDcL hyDc
        hDcnhds).mp hyB
      obtain ⟨s, hs, _⟩ := (boundaryComplex 2 L).mem_space_iff.mp h
      rw [hL.boundaryComplex_faces_eq_empty L] at hs
      exact hs
    refine h1.symm.trans ?_
    rw [h2]
    constructor
    · rintro (⟨-, hab'⟩ | ⟨hyB', -⟩)
      · exact hab'
      · exact absurd hyB' hyB
    · intro hab'
      exact Or.inl ⟨hyDc, hab'⟩
  ext ⟨y, t⟩
  constructor
  · intro h
    have hz := boundaryComplex_space_subset 3 T h
    rw [hT] at hz
    exact ⟨hz.1, (key y hz.1 t hz.2).mp h⟩
  · rintro ⟨hy, ht⟩
    have htI : t ∈ Icc a b := by
      rcases ht with rfl | rfl
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
    exact (key y hy t htI).mpr ht

open Classical in
theorem IsPLHomeomorphOn.mem_nhdsWithin_of_mem_prod_Ioo
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc a b) W) (hWK : W ⊆ K.space)
    {z : E × ℝ} (hz : z ∈ L.space ×ˢ Ioo a b) :
    W ∈ 𝓝[K.space] ρ z := by
  obtain ⟨T, hTfin, hT⟩ := ((isPolyhedron_space L).prod
    (isHPolytope_Icc (a := a) (b := b)).isPolyhedron).exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hTm := isCombinatorialManifoldWithBoundary_of_space_eq_prod_Icc hL hab T hT
  have hρT : IsPLHomeomorphOn ρ T.space W := by
    rw [hT]
    exact hρ
  have hzT : z ∈ T.space := by
    rw [hT]
    exact ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
  refine hρT.image_mem_nhdsWithin_of_notMem_boundaryComplex T K hTm hK hWK hzT ?_
    self_mem_nhdsWithin
  intro hB
  have h := (boundaryComplex_space_of_space_eq_prod_Icc
    (d := fun x y => Classical.propDecidable (x = y)) hL hab T hT).subset hB
  rcases h.2 with h | h
  · exact hz.2.1.ne' h
  · exact hz.2.2.ne h

open Classical in
theorem IsPLHomeomorphOn.inter_closure_sdiff_eq_image_prod_pair
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    {ρ : E × ℝ → E} {W : Set E} (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space) :
    ∃ A : Geometry.SimplicialComplex ℝ E, ∃ _ : Finite A.faces,
      IsCombinatorialManifoldWithBoundary 3 A ∧ A.space = W ∧
      (boundaryComplex 3 A).space = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) ∧
      W ∩ closure (K.space \ W) = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) := by
  have hab : (-1 : ℝ) < 1 := by norm_num
  obtain ⟨T, hTfin, hT⟩ :=
    ((isPolyhedron_space L).prod
      (isHPolytope_Icc (a := (-1 : ℝ)) (b := 1)).isPolyhedron).exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hTm := isCombinatorialManifoldWithBoundary_of_space_eq_prod_Icc hL hab T hT
  have hWpoly : IsPolyhedron W := by
    rw [← hρ.image_eq]
    exact ((isPolyhedron_space L).prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  obtain ⟨A, hAfin, hA⟩ := hWpoly.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hρTA : IsPLHomeomorphOn ρ T.space A.space := by
    rw [hT, hA]
    exact hρ
  have hAm : IsCombinatorialManifoldWithBoundary 3 A := hTm.of_isPLHomeomorphOn hρTA
  have hbd : (boundaryComplex 3 A).space = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) :=
    (boundaryComplex_space_of_isPLHomeomorphOn T A hTm hρTA).trans
      (congrArg (fun S => ρ '' S) (boundaryComplex_space_of_space_eq_prod_Icc
        (d := fun x y => Classical.propDecidable (x = y)) hL hab T hT))
  have hAK : A.space ⊆ K.space := by
    rw [hA]
    exact hW.trans sdiff_subset
  have hdis : Disjoint A.space (boundaryComplex 3 K).space := by
    rw [hA]
    exact disjoint_left.mpr fun _ hx hxB => (hW hx).2 hxB
  have htrace := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K A hK hAm hAK hdis
  rw [hA] at htrace
  exact ⟨A, inferInstance, hAm, hA, hbd, htrace.trans hbd⟩

open Classical in
theorem boundaryComplex_space_of_closure_sdiff_bicollar
    {K L R : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hR : IsCombinatorialManifoldWithBoundary 3 R) {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space) (hRspace : R.space = closure (K.space \ W)) :
    (boundaryComplex 3 R).space =
      (boundaryComplex 3 K).space ∪ ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) := by
  obtain ⟨A, hAfin, hAm, hA, hbd, -⟩ := hρ.inter_closure_sdiff_eq_image_prod_pair hK hL hW
  let _ : Finite (boundaryComplex 3 K).faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite (boundaryComplex 3 A).faces := (boundaryComplex_faces_finite 3 A).to_subtype
  have hAK : A.space ⊆ K.space := by
    rw [hA]
    exact hW.trans sdiff_subset
  have hbdR := boundaryComplex_space_of_closure_sdiff K A R hK hAm hAK hR
    (by rw [hA]; exact hRspace)
  have hKclosed : IsClosed (boundaryComplex 3 K).space := (isPolyhedron_space _).isClosed
  have hAclosed : IsClosed (boundaryComplex 3 A).space := (isPolyhedron_space _).isClosed
  have h1 : (boundaryComplex 3 K).space \ A.space = (boundaryComplex 3 K).space := by
    rw [hA]
    exact sdiff_eq_left.mpr (disjoint_left.mpr fun _ hx hxW => (hW hxW).2 hx)
  have h2 : (boundaryComplex 3 A).space \ (boundaryComplex 3 K).space =
      (boundaryComplex 3 A).space := by
    refine sdiff_eq_left.mpr (disjoint_left.mpr fun x hx hxK => ?_)
    have hxW : x ∈ W := by
      rw [← hA]
      exact boundaryComplex_space_subset 3 A hx
    exact (hW hxW).2 hxK
  rw [hbdR, h1, h2, hKclosed.closure_eq, hAclosed.closure_eq, hbd]

open Classical in
theorem exists_connectedComponentComplex_boundaryComplex_eq_image_of_bicollar
    {K L R : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hR : IsCombinatorialManifoldWithBoundary 3 R) {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space) (hRspace : R.space = closure (K.space \ W))
    {y : E} (hy : y ∈ L.space) {e : ℝ} (he : e ∈ ({-1, 1} : Set ℝ)) :
    ∃ c : ConnectedComponents (boundaryComplex 3 R).space,
      (connectedComponentComplex (boundaryComplex 3 R) c).space =
        (fun z => ρ (z, e)) '' connectedComponentIn L.space y := by
  have hbdR := boundaryComplex_space_of_closure_sdiff_bicollar hK hL hR hρ hW hRspace
  let _ : Finite (boundaryComplex 3 K).faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hpmI : ∀ t ∈ ({-1, 1} : Set ℝ), t ∈ Icc (-1 : ℝ) 1 := by
    rintro t (rfl | rfl) <;> norm_num
  have hends : ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) ⊆ (boundaryComplex 3 R).space := by
    rw [hbdR]
    exact subset_union_right
  have hb : ρ (y, e) ∈ (boundaryComplex 3 R).space := hends ⟨(y, e), ⟨hy, he⟩, rfl⟩
  refine ⟨ConnectedComponents.mk ⟨ρ (y, e), hb⟩, ?_⟩
  rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
  change connectedComponentIn (boundaryComplex 3 R).space (ρ (y, e)) = _
  have hjc : ContinuousOn (fun z => ρ (z, e)) L.space :=
    hρ.isPiecewiseAffineOn.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      fun z hz => ⟨hz, hpmI e he⟩
  apply Subset.antisymm
  · set C := connectedComponentIn (boundaryComplex 3 R).space (ρ (y, e))
    have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCsub : C ⊆ (boundaryComplex 3 R).space := connectedComponentIn_subset _ _
    have hbC : ρ (y, e) ∈ C := mem_connectedComponentIn hb
    have hEclosed : IsClosed (ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ))) :=
      (((isPolyhedron_space L).isCompact.prod (Set.toFinite _).isCompact).image_of_continuousOn
        (hρ.isPiecewiseAffineOn.continuousOn.mono
          (prod_mono subset_rfl fun t ht => hpmI t ht))).isClosed
    have hdisj : C ∩ ((boundaryComplex 3 K).space ∩ ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ))) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      obtain ⟨z, hz, rfl⟩ := hx.2.2
      exact (hW (hρ.bijOn.mapsTo ⟨hz.1, hpmI z.2 hz.2⟩)).2 hx.2.1
    have hCE : C ⊆ ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hCpre _ _
        (isPolyhedron_space _).isClosed hEclosed (hCsub.trans hbdR.subset) hdisj with h | h
      · exact absurd (h hbC) (hW (hρ.bijOn.mapsTo ⟨hy, hpmI e he⟩)).2
      · exact h
    have hCW : C ⊆ W := hCE.trans (by
      rw [← hρ.image_eq]
      exact image_mono (prod_mono subset_rfl fun t ht => hpmI t ht))
    set ψ := Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1)
    have hψc : ContinuousOn ψ W := hρ.isPiecewiseAffineOn_invFunOn.continuousOn
    have hψinv : ∀ z ∈ L.space ×ˢ Icc (-1 : ℝ) 1, ψ (ρ z) = z := fun z hz =>
      hρ.bijOn.invOn_invFunOn.1 hz
    have hρψ : ∀ w ∈ W, ρ (ψ w) = w := fun w hw => hρ.bijOn.invOn_invFunOn.2 hw
    have hψmem : ∀ w ∈ C, ψ w ∈ L.space ×ˢ ({-1, 1} : Set ℝ) := by
      intro w hw
      obtain ⟨z, hz, hzw⟩ := hCE hw
      rw [← hzw, hψinv z ⟨hz.1, hpmI z.2 hz.2⟩]
      exact hz
    have hψb : ψ (ρ (y, e)) = (y, e) := hψinv _ ⟨hy, hpmI e he⟩
    have h1 : (fun w => (ψ w).1) '' C ⊆ connectedComponentIn L.space y :=
      IsPreconnected.subset_connectedComponentIn
        (hCpre.image _ ((continuous_fst.comp_continuousOn hψc).mono hCW))
        ⟨ρ (y, e), hbC, by change (ψ (ρ (y, e))).1 = y; rw [hψb]⟩
        (by rintro _ ⟨w, hw, rfl⟩; exact (hψmem w hw).1)
    have hoc : ((fun w => (ψ w).2) '' C).OrdConnected :=
      isPreconnected_iff_ordConnected.mp
        (hCpre.image _ ((continuous_snd.comp_continuousOn hψc).mono hCW))
    have he₀ : e ∈ (fun w => (ψ w).2) '' C :=
      ⟨ρ (y, e), hbC, by change (ψ (ρ (y, e))).2 = e; rw [hψb]⟩
    intro w hw
    have h2 : (ψ w).2 = e := by
      have hwimg : (ψ w).2 ∈ (fun w => (ψ w).2) '' C := ⟨w, hw, rfl⟩
      have hw' : (ψ w).2 = -1 ∨ (ψ w).2 = 1 := (hψmem w hw).2
      have he' : e = -1 ∨ e = 1 := he
      by_contra hne
      have h0 : (0 : ℝ) ∈ (fun w => (ψ w).2) '' C := by
        rcases he' with rfl | rfl <;> rcases hw' with h | h
        · exact (hne h).elim
        · exact hoc.out he₀ hwimg ⟨by norm_num, by rw [h]; norm_num⟩
        · exact hoc.out hwimg he₀ ⟨by rw [h]; norm_num, by norm_num⟩
        · exact (hne h).elim
      obtain ⟨w', hw', h0'⟩ := h0
      have h0'' : (ψ w').2 = 0 := h0'
      have h3 : (ψ w').2 = -1 ∨ (ψ w').2 = 1 := (hψmem w' hw').2
      rw [h0''] at h3
      rcases h3 with h3 | h3 <;> norm_num at h3
    refine ⟨(ψ w).1, h1 ⟨w, hw, rfl⟩, ?_⟩
    change ρ ((ψ w).1, e) = w
    rw [← h2]
    exact hρψ w (hCW hw)
  · apply IsPreconnected.subset_connectedComponentIn
    · exact isPreconnected_connectedComponentIn.image _
        (hjc.mono (connectedComponentIn_subset _ _))
    · exact ⟨y, mem_connectedComponentIn hy, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hends ⟨(z, e), ⟨connectedComponentIn_subset _ _ hz, he⟩, rfl⟩

open Classical in
theorem IsPLHomeomorphOn.exists_isOpen_inter_eq_image_prod_Ioo
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    {ρ : E × ℝ → E} {W : Set E} (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hWK : W ⊆ K.space) {s : ℝ} (hs : s ≤ 1) :
    ∃ G : Set E, IsOpen G ∧ G ∩ K.space = ρ '' (L.space ×ˢ Ioo (-s) s) := by
  have hloc : ∀ p ∈ ρ '' (L.space ×ˢ Ioo (-s) s),
      ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ∩ K.space ⊆ ρ '' (L.space ×ˢ Ioo (-s) s) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzI : z ∈ L.space ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hW : W ∈ 𝓝[K.space] ρ z := hρ.mem_nhdsWithin_of_mem_prod_Ioo hK hL (by norm_num) hWK
      ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hS : L.space ×ˢ Ioo (-s) s ∈ 𝓝[L.space ×ˢ Icc (-1 : ℝ) 1] z := by
      rw [show z = (z.1, z.2) from rfl, nhdsWithin_prod_eq]
      exact Filter.prod_mem_prod self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hz.2.1 hz.2.2))
    exact mem_nhdsWithin.mp (nhdsWithin_le_of_mem hW (hρ.image_mem_nhdsWithin hzI hS))
  choose! O hO hpO hOK using hloc
  refine ⟨⋃ p ∈ ρ '' (L.space ×ˢ Ioo (-s) s), O p, isOpen_biUnion hO, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hx, hxK⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    exact hOK p hp ⟨hxp, hxK⟩
  · intro x hx
    refine ⟨mem_iUnion₂.mpr ⟨x, hx, hpO x hx⟩, ?_⟩
    obtain ⟨z, hz, rfl⟩ := hx
    exact hWK (hρ.bijOn.mapsTo ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩)

open Classical in
theorem IsPLHomeomorphOn.exists_continuousOn_push_to_ends
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    {ρ : E × ℝ → E} {W : Set E} (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ Φ : E → E, ContinuousOn Φ K.space ∧ MapsTo Φ K.space K.space ∧
      (∀ w ∈ K.space, w ∉ W → Φ w = w) ∧
      ∀ z ∈ L.space ×ˢ Icc (-1 : ℝ) 1, Φ (ρ z) = ρ (z.1, max (-1) (min 1 (z.2 / s))) := by
  obtain ⟨A, hAfin, -, -, -, htrace⟩ := hρ.inter_closure_sdiff_eq_image_prod_pair hK hL hW
  have hWK : W ⊆ K.space := hW.trans sdiff_subset
  have hcI : ∀ t : ℝ, max (-1) (min 1 (t / s)) ∈ Icc (-1 : ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hψW : ∀ w ∈ W, Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) w ∈
      L.space ×ˢ Icc (-1 : ℝ) 1 := fun w hw => hρ.bijOn.surjOn.mapsTo_invFunOn hw
  have hψρ : ∀ z ∈ L.space ×ˢ Icc (-1 : ℝ) 1,
      Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) (ρ z) = z := fun z hz =>
    hρ.bijOn.invOn_invFunOn.1 hz
  have hWclosed : IsClosed W := by
    rw [← hρ.image_eq]
    exact (((isPolyhedron_space L).isCompact.prod isCompact_Icc).image_of_continuousOn
      hρ.isPiecewiseAffineOn.continuousOn).isClosed
  let g : E → E := fun w => ρ ((Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) w).1,
    max (-1) (min 1 ((Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) w).2 / s)))
  let Φ : E → E := fun w => if w ∈ W then g w else w
  have hgc : ContinuousOn g W := by
    have hψc : ContinuousOn (Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1)) W :=
      hρ.isPiecewiseAffineOn_invFunOn.continuousOn
    have hcc : Continuous fun t : ℝ => max (-1) (min 1 (t / s)) :=
      continuous_const.max (continuous_const.min (continuous_id.div_const s))
    exact hρ.isPiecewiseAffineOn.continuousOn.comp
      ((continuous_fst.comp_continuousOn hψc).prodMk
        (hcc.comp_continuousOn (continuous_snd.comp_continuousOn hψc)))
      fun w hw => ⟨(hψW w hw).1, hcI _⟩
  have hcont1 : ContinuousOn Φ W := hgc.congr fun w hw => ite_eq_left hw
  have hcont2 : ContinuousOn Φ (closure (K.space \ W)) := by
    refine continuousOn_id.congr fun w hw => ?_
    by_cases hwW : w ∈ W
    · obtain ⟨z, hz, rfl⟩ := htrace.subset ⟨hwW, hw⟩
      have hzI : z ∈ L.space ×ˢ Icc (-1 : ℝ) 1 := ⟨hz.1, by
        rcases hz.2 with h | h <;> rw [h] <;> norm_num⟩
      change (if ρ z ∈ W then g (ρ z) else ρ z) = ρ z
      rw [ite_eq_left hwW]
      change ρ ((Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) (ρ z)).1,
        max (-1) (min 1 ((Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) (ρ z)).2 / s))) =
          ρ z
      rw [hψρ z hzI]
      have hs' : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
      rcases hz.2 with h | h
      · rw [h, show max (-1) (min 1 ((-1 : ℝ) / s)) = -1 by
          rw [min_eq_right (by rw [neg_div]; linarith), max_eq_left (by rw [neg_div]; linarith)]]
        rw [← h]
      · rw [show z.2 = 1 from h, show max (-1) (min 1 ((1 : ℝ) / s)) = 1 by
          rw [min_eq_left hs', max_eq_right (by norm_num)]]
        rw [← show z.2 = 1 from h]
    · change (if w ∈ W then g w else w) = w
      rw [ite_eq_right hwW]
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · refine (hcont1.union_of_isClosed hcont2 hWclosed isClosed_closure).mono fun w hw => ?_
    by_cases hwW : w ∈ W
    · exact Or.inl hwW
    · exact Or.inr (subset_closure ⟨hw, hwW⟩)
  · intro w hw
    by_cases hwW : w ∈ W
    · change (if w ∈ W then g w else w) ∈ K.space
      rw [ite_eq_left hwW]
      exact hWK (hρ.bijOn.mapsTo ⟨(hψW w hwW).1, hcI _⟩)
    · change (if w ∈ W then g w else w) ∈ K.space
      rw [ite_eq_right hwW]
      exact hw
  · intro w _ hwW
    change (if w ∈ W then g w else w) = w
    rw [ite_eq_right hwW]
  · intro z hz
    change (if ρ z ∈ W then g (ρ z) else ρ z) = _
    rw [ite_eq_left (hρ.bijOn.mapsTo hz)]
    change ρ ((Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) (ρ z)).1,
      max (-1) (min 1 ((Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) (ρ z)).2 / s))) = _
    rw [hψρ z hz]

theorem IsPLHomeomorphOn.exists_continuousOn_retraction_image_connectedComponentIn
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W) {y₀ : E} (hy₀ : y₀ ∈ L.space)
    {e : ℝ} (he : e ∈ Icc (-1 : ℝ) 1) :
    ∃ r : E → E, ContinuousOn r W ∧
      MapsTo r W ((fun y => ρ (y, e)) '' connectedComponentIn L.space y₀) ∧
      ∀ y ∈ connectedComponentIn L.space y₀, r (ρ (y, e)) = ρ (y, e) := by
  classical
  let _ : LocallyConnectedSpace L.space := locallyConnectedSpace_space L
  let S : Set L.space := connectedComponent (⟨y₀, hy₀⟩ : L.space)
  have hS : IsClopen S := ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  have hSα : ∀ x : L.space, x ∈ S ↔ (x : E) ∈ connectedComponentIn L.space y₀ := by
    intro x
    rw [connectedComponentIn_eq_image hy₀]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨x', hx', hxx'⟩
      rw [Subtype.ext hxx'] at hx'
      exact hx'
  let q : E → E := fun x => if x ∈ connectedComponentIn L.space y₀ then x else y₀
  have hqα : ∀ x, q x ∈ connectedComponentIn L.space y₀ := by
    intro x
    by_cases hx : x ∈ connectedComponentIn L.space y₀
    · simp only [q, ite_eq_left hx]
      exact hx
    · simp only [q, ite_eq_right hx]
      exact mem_connectedComponentIn hy₀
  have hqc : ContinuousOn q L.space := by
    have hc : Continuous fun x : L.space => if x ∈ S then (x : E) else y₀ := by
      apply Continuous.if _ continuous_subtype_val continuous_const
      intro a ha
      simp only [ofPred_mem_eq, hS.frontier_eq, mem_empty_iff_false] at ha
    refine continuousOn_iff_continuous_domRestrict.mpr (hc.congr fun x => ?_)
    change (if x ∈ S then (x : E) else y₀) = q x
    simp only [q, hSα x]
  have hψc : ContinuousOn (Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1)) W :=
    hρ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hψW : ∀ w ∈ W, Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) w ∈
      L.space ×ˢ Icc (-1 : ℝ) 1 := fun w hw => hρ.bijOn.surjOn.mapsTo_invFunOn hw
  refine ⟨fun w => ρ (q (Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) w).1, e), ?_, ?_, ?_⟩
  · exact hρ.isPiecewiseAffineOn.continuousOn.comp
      ((hqc.comp (continuous_fst.comp_continuousOn hψc) fun w hw => (hψW w hw).1).prodMk
        continuousOn_const)
      fun w _ => ⟨connectedComponentIn_subset _ _ (hqα _), he⟩
  · intro w _
    exact ⟨_, hqα _, rfl⟩
  · intro y hy
    change ρ (q (Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) (ρ (y, e))).1, e) = ρ (y, e)
    rw [hρ.bijOn.invOn_invFunOn.1 ⟨connectedComponentIn_subset _ _ hy, he⟩]
    change ρ (q y, e) = ρ (y, e)
    simp only [q, ite_eq_left hy]

end DifferentialGeometry.Topology.PiecewiseLinear
