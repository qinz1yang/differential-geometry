/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitPrismChart
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitAnnulus
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

/-! Local surface traces on one side of a splitting disk. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLHomeomorphOn.isPathConnected_sdiff_of_isPLBall_subset_openSimplex
    {P D : Set E} {p : (Fin 3 → ℝ) → E}
    (hp : IsPLHomeomorphOn p (stdSimplex ℝ (Fin 3)) P)
    (hD : IsPLBall 2 D) (hDP : D ⊆ p '' openSimplex (stdVertices 1)) :
    IsPathConnected (P \ D) := by
  classical
  have hP : IsPLBall 2 P := ⟨p, hp⟩
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hP
  have hboundary : p '' stdSimplexBoundary 2 = (boundaryComplex 2 L).space :=
    hp.image_stdSimplexBoundary_eq_boundaryComplex L hLspace
  have hDP' : D ⊆ P := hDP.trans
    ((image_mono openSimplex_stdVertices_subset_stdSimplex).trans hp.image_eq.subset)
  have hDdis : Disjoint D (boundaryComplex 2 L).space := by
    rw [← hboundary, disjoint_left]
    intro x hxD hxJ
    have hx := hDP hxD
    rw [hp.image_openSimplex_stdVertices] at hx
    exact hx.2 hxJ
  have hprod : IsPLBall 3 (L.space ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hL (isPLBall_Icc zero_lt_one)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 3 R.space := hRspace.symm ▸ hprod
  let S : Set (E × ℝ) := (boundaryComplex 3 R).space
  let D₀ : Set (E × ℝ) := D ×ˢ {(0 : ℝ)}
  let D₁ : Set (E × ℝ) := L.space ×ˢ {(1 : ℝ)}
  have hS : IsPLSphere 2 S := isPLSphere_boundaryComplex_space_of_isPLBall R hR
  have hD₀ : IsPLBall 2 D₀ :=
    hD.of_isPLHomeomorphOn (hD.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hD₁ : IsPLBall 2 D₁ :=
    hL.of_isPLHomeomorphOn (hL.isPolyhedron.isPLHomeomorphOn_prod_const 1)
  have hSspace : S =
      L.space ×ˢ ({(0 : ℝ), 1} : Set ℝ) ∪
        (boundaryComplex 2 L).space ×ˢ Icc 0 1 :=
    boundaryComplex_space_prism L hL zero_lt_one R hRspace
  have hD₀S : D₀ ⊆ S := by
    rw [hSspace]
    rintro ⟨x, t⟩ ⟨hxD, ht⟩
    have ht : t = 0 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact Or.inl ⟨hLspace.symm.subset (hDP' hxD), Or.inl rfl⟩
  have hD₁S : D₁ ⊆ S := by
    rw [hSspace]
    rintro ⟨x, t⟩ ⟨hxL, ht⟩
    have ht : t = 1 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact Or.inl ⟨hxL, Or.inr rfl⟩
  have hdis : Disjoint D₀ D₁ := by
    rw [disjoint_left]
    rintro ⟨x, t⟩ ⟨-, ht₀⟩ ⟨-, ht₁⟩
    have ht₀ : t = 0 := by simpa only [mem_singleton_iff] using ht₀
    have ht₁ : t = 1 := by simpa only [mem_singleton_iff] using ht₁
    norm_num [ht₀] at ht₁
  have hpath := hS.isPathConnected_sdiff_union_of_disjoint_isPLBall_two
    hD₀ hD₀S hD₁ hD₁S hdis
  have himage : Prod.fst '' (S \ (D₀ ∪ D₁)) = L.space \ D := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases z with ⟨x, t⟩
      rw [hSspace] at hz
      change x ∈ L.space \ D
      rcases hz.1 with ⟨hxL, ht⟩ | ⟨hxJ, ht⟩
      · rcases ht with rfl | rfl
        · exact ⟨hxL, fun hxD => hz.2 (Or.inl ⟨hxD, rfl⟩)⟩
        · exact (hz.2 (Or.inr ⟨hxL, rfl⟩)).elim
      · exact ⟨boundaryComplex_space_subset 2 L hxJ,
          fun hxD => disjoint_left.mp hDdis hxD hxJ⟩
    · rintro ⟨hxL, hxD⟩
      refine ⟨(x, 0), ⟨?_, ?_⟩, rfl⟩
      · rw [hSspace]
        exact Or.inl ⟨hxL, Or.inl rfl⟩
      · rintro (⟨hxD', -⟩ | ⟨-, ht⟩)
        · exact hxD hxD'
        · norm_num at ht
  have htarget : IsPathConnected (L.space \ D) := by
    rw [← himage]
    exact hpath.image' continuous_fst.continuousOn
  simpa only [hLspace] using htarget

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem not_mem_closure_sdiff_of_mem_nhdsWithin
    {A B : Set E} {x : E} (hA : A ∈ 𝓝[B] x) : x ∉ closure (B \ A) := by
  intro hx
  obtain ⟨O, hO, hxO, hOA⟩ := mem_nhdsWithin.mp hA
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp hx O hO hxO
  exact hy.2 (hOA ⟨hyO, hy.1⟩)

open Classical in
theorem IsCombinatorialManifold.exists_surface_split_local_traces
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {C Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ)
    {r₁ r₂ : (Fin 3 → ℝ) → E}
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₁ : Δ ⊆ r₁ '' openSimplex (stdVertices 1))
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space)
    (hD₁C : D₁ ⊆ C) (hD₂C : D₂ ⊆ C)
    (hlocal : D₁ ∪ D₂ ∈ 𝓝ˢ[C] Δ) (hU : U ∈ 𝓝ˢ[K.space] Δ) :
    ∃ (N : Set E) (B : Geometry.SimplicialComplex ℝ E)
      (g : (Fin 3 → ℝ) → E) (A₁ Δ₁ C' : Set E),
      B.faces.Finite ∧ IsPLBall 3 N ∧ IsPLBall 3 B.space ∧
      Δ ⊆ N ∧ N ⊆ K.space ∧ N ⊆ U ∧
      (∀ x ∈ Δ, N ∈ 𝓝[K.space] x) ∧ B.space ⊆ N ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (D₂ ∩ N) ∧
      D₂ ∩ N ⊆ (boundaryComplex 3 B).space ∧
      A₁ = N ∩ closure (D₁ \ Δ) ∧ A₁ ⊆ B.space ∧
      IsPLBall 2 Δ₁ ∧ Δ₁ ⊆ (boundaryComplex 3 B).space ∧
      (boundaryComplex 3 B).space = (D₂ ∩ N) ∪ Δ₁ ∧
      (D₂ ∩ N) ∩ Δ₁ = g '' stdSimplexBoundary 2 ∧
      C' = (C \ (A₁ \ ((D₂ ∩ N) ∪ Δ₁))) ∪ Δ₁ ∧
      C ∩ B.space = (D₂ ∩ N) ∪ A₁ ∧
      C' ∩ B.space = (D₂ ∩ N) ∪ Δ₁ ∧
      C' \ B.space = C \ B.space := by
  classical
  let J₁ := r₁ '' stdSimplexBoundary 2
  have hJ₁closed : IsClosed J₁ := hr₁.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isClosed
  have hΔJ₁ : Δ ⊆ J₁ᶜ := by
    intro x hx
    have hx' := hΔintD₁ hx
    rw [hr₁.image_openSimplex_stdVertices] at hx'
    exact hx'.2
  have hJ₁nhds : J₁ᶜ ∈ 𝓝ˢ Δ := mem_nhdsSet_iff_forall.mpr fun x hx =>
    hJ₁closed.isOpen_compl.mem_nhds (hΔJ₁ hx)
  obtain ⟨O, hO, hΔO, hOC⟩ := mem_nhdsSetWithin.mp hlocal
  have hOnhds : O ∈ 𝓝ˢ Δ := mem_nhdsSet_iff_forall.mpr fun x hx => hO.mem_nhds (hΔO hx)
  let V := (U ∩ O) ∩ J₁ᶜ
  have hV : V ∈ 𝓝ˢ[K.space] Δ :=
    Filter.inter_mem (Filter.inter_mem hU (Filter.mem_inf_of_left hOnhds))
      (Filter.mem_inf_of_left hJ₁nhds)
  have hD₁ : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  obtain ⟨R, A, A₁c, A₂c, K₀, K₁, L, φ, ψ, g, ρ,
      hR, hRfin, hAR, hAfin, hAΔ, hA₁R, hA₁fin, hA₁D₁,
      hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
      hLfin, hL, hIso, hN, hΔN, hNK, hNV, hnhds, hmiddleBall, hmiddleTrace,
      hg, hgboundary, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter,
      hmiddleK₀, hmiddleK₁, hρ, hρmid, hρ₀, hρ₁⟩ :=
    hK.exists_isSubdivision_disk_pair_with_centered_prism hΔ hD₁ hr₂ hΔintD₂
      hΔD₁ hΔD₂ hD₁D₂ hD₁K hD₂K hV
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite A₁c.faces := hA₁fin.to_subtype
  let _ : Finite A₂c.faces := hA₂fin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let N := derivedNeighborhood R A
  let Q₁ := derivedNeighborhood A₁c A
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite R A).to_subtype
  let _ : Finite Q₁.faces := (derivedNeighborhood_faces_finite A₁c A).to_subtype
  have hNU : N.space ⊆ U := hNV.trans (inter_subset_left.trans inter_subset_left)
  have hNO : N.space ⊆ O := hNV.trans (inter_subset_left.trans inter_subset_right)
  have hNJ₁ : Disjoint N.space J₁ := by
    apply disjoint_left.mpr
    intro x hxN hxJ
    exact (hNV hxN).2 hxJ
  have hQ₁space : D₁ ∩ N.space = Q₁.space := by
    rw [← hA₁D₁, inter_comm]
    exact derivedNeighborhood_space_inter_subcomplex R A₁c A hA₁R
  have hQ₁N : Q₁.space ⊆ N.space := hQ₁space.symm.subset.trans inter_subset_right
  have hA₁ball : IsPLBall 2 A₁c.space := hA₁D₁.symm ▸ hD₁
  have hQ₁ball : IsPLBall 2 Q₁.space := by
    open IsCombinatorialManifoldWithBoundary in
      exact isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface
        hA₁ball.isCombinatorialManifoldWithBoundary hAA₁ hL hIso
  have hA₁boundary : J₁ = (boundaryComplex 2 A₁c).space :=
    hr₁.image_stdSimplexBoundary_eq_boundaryComplex A₁c hA₁D₁
  have hQ₁dis : Disjoint Q₁.space (boundaryComplex 2 A₁c).space := by
    rw [← hA₁boundary]
    exact hNJ₁.mono_left hQ₁N
  have hQ₁boundary :
      Q₁.space ∩ closure (A₁c.space \ Q₁.space) = (boundaryComplex 2 Q₁).space :=
    inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary A₁c Q₁
      hA₁ball.isCombinatorialManifoldWithBoundary
      hQ₁ball.isCombinatorialManifoldWithBoundary
      (derivedNeighborhood_space_subset A₁c A) hQ₁dis
  obtain ⟨q₁, hq₁⟩ := id hQ₁ball
  have hΔopenQ₁ : Δ ⊆ q₁ '' openSimplex (stdVertices 1) := by
    rw [hq₁.image_openSimplex_stdVertices,
      hq₁.image_stdSimplexBoundary_eq_boundaryComplex Q₁ rfl]
    intro x hxΔ
    have hxA : x ∈ A.space := hAΔ.symm ▸ hxΔ
    have hxA₁ : x ∈ A₁c.space := space_mono_of_faces_subset hAA₁ hxA
    have hxnhds : Q₁.space ∈ 𝓝[A₁c.space] x :=
      derivedNeighborhood_mem_nhdsWithin hAA₁ hxA
    have hxQ₁ : x ∈ Q₁.space := mem_of_mem_nhdsWithin hxA₁ hxnhds
    refine ⟨hxQ₁, fun hxboundary => ?_⟩
    exact not_mem_closure_sdiff_of_mem_nhdsWithin hxnhds
      (hQ₁boundary.symm.subset hxboundary).2
  have hringPath : IsPathConnected (Q₁.space \ Δ) :=
    hq₁.isPathConnected_sdiff_of_isPLBall_subset_openSimplex hΔ hΔopenQ₁
  let T := Q₁.space \ Δ
  let P := stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1
  let θ := Function.invFunOn ρ P
  have hTN : T ⊆ N.space := sdiff_subset.trans hQ₁N
  have hθconn : IsConnected (θ '' T) :=
    hringPath.isConnected.image θ (hρ.isPiecewiseAffineOn_invFunOn.continuousOn.mono hTN)
  have hheightConn : IsConnected (Prod.snd '' (θ '' T)) :=
    hθconn.image Prod.snd continuous_snd.continuousOn
  have hheightCover : Prod.snd '' (θ '' T) ⊆ Iio 0 ∪ Ioi 0 := by
    rintro t ⟨z, ⟨y, hyT, hyz⟩, rfl⟩
    subst z
    have hyN : y ∈ N.space := hTN hyT
    have hzP : θ y ∈ P := hρ.bijOn.surjOn.mapsTo_invFunOn hyN
    have htnonzero : (θ y).2 ≠ 0 := by
      intro ht
      have hρinv : ρ (θ y) = y := hρ.bijOn.invOn_invFunOn.2 hyN
      have hmid : ρ (θ y) = g (θ y).1 := by
        calc
          ρ (θ y) = ρ ((θ y).1, (θ y).2) := congrArg ρ (Prod.eta (θ y)).symm
          _ = ρ ((θ y).1, 0) := by rw [ht]
          _ = g (θ y).1 := hρmid (θ y).1 hzP.1
      have hyg : y = g (θ y).1 := hρinv.symm.trans hmid
      have hymiddle : y ∈ D₂ ∩ N.space := hyg.symm ▸ hg.bijOn.mapsTo hzP.1
      have hyD₁ : y ∈ D₁ := (hQ₁space.symm.subset hyT.1).1
      exact hyT.2 (hD₁D₂.subset ⟨hyD₁, hymiddle.1⟩)
    exact lt_or_gt_of_ne htnonzero
  have hheightSide :
      Prod.snd '' (θ '' T) ⊆ Iio 0 ∨ Prod.snd '' (θ '' T) ⊆ Ioi 0 :=
    IsPreconnected.subset_or_subset isOpen_Iio isOpen_Ioi
      (disjoint_left.mpr fun x hx hy =>
        lt_asymm (show x < 0 from hx) (show 0 < x from hy))
      hheightCover hheightConn.isPreconnected
  have hTside : T ⊆ K₀.space ∨ T ⊆ K₁.space := by
    rcases hheightSide with hneg | hpos
    · left
      intro y hyT
      have hyN : y ∈ N.space := hTN hyT
      have hzP : θ y ∈ P := hρ.bijOn.surjOn.mapsTo_invFunOn hyN
      have hneg' : (θ y).2 < 0 := hneg ⟨θ y, ⟨y, hyT, rfl⟩, rfl⟩
      have hzhalf : θ y ∈ stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0 :=
        ⟨hzP.1, hzP.2.1, hneg'.le⟩
      rw [← hρ₀]
      exact ⟨θ y, hzhalf, hρ.bijOn.invOn_invFunOn.2 hyN⟩
    · right
      intro y hyT
      have hyN : y ∈ N.space := hTN hyT
      have hzP : θ y ∈ P := hρ.bijOn.surjOn.mapsTo_invFunOn hyN
      have hpos' : 0 < (θ y).2 := hpos ⟨θ y, ⟨y, hyT, rfl⟩, rfl⟩
      have hzhalf : θ y ∈ stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 :=
        ⟨hzP.1, hpos'.le, hzP.2.2⟩
      rw [← hρ₁]
      exact ⟨θ y, hzhalf, hρ.bijOn.invOn_invFunOn.2 hyN⟩
  let A₁ : Set E := N.space ∩ closure (D₁ \ Δ)
  have hA₁closure : A₁ ⊆ closure T := by
    intro x hx
    by_cases hxΔ : x ∈ Δ
    · apply mem_closure_iff.mpr
      intro W hW hxW
      obtain ⟨O', hO', hxO', hO'N⟩ := mem_nhdsWithin.mp (hnhds x hxΔ)
      obtain ⟨y, hyWO, hyD₁⟩ :=
        mem_closure_iff.mp hx.2 (W ∩ O') (hW.inter hO') ⟨hxW, hxO'⟩
      refine ⟨y, hyWO.1, ⟨?_, hyD₁.2⟩⟩
      rw [← hQ₁space]
      exact ⟨hyD₁.1, hO'N ⟨hyWO.2, hD₁K hyD₁.1⟩⟩
    · apply subset_closure
      refine ⟨?_, hxΔ⟩
      rw [← hQ₁space]
      exact ⟨closure_minimal sdiff_subset hD₁.isPolyhedron.isClosed hx.2, hx.1⟩
  have hside : A₁ ⊆ K₀.space ∨ A₁ ⊆ K₁.space := by
    rcases hTside with hT₀ | hT₁
    · exact Or.inl (hA₁closure.trans (closure_minimal hT₀ hK₀.isPolyhedron.isClosed))
    · exact Or.inr (hA₁closure.trans (closure_minimal hT₁ hK₁.isPolyhedron.isClosed))
  have finish (B : Geometry.SimplicialComplex ℝ E) (hBfin : B.faces.Finite)
      (hB : IsPLBall 3 B.space) (hBN : B.space ⊆ N.space)
      (hmiddleB : D₂ ∩ N.space ⊆ (boundaryComplex 3 B).space)
      (hA₁B : A₁ ⊆ B.space) :
      ∃ (N' : Set E) (B' : Geometry.SimplicialComplex ℝ E)
        (g' : (Fin 3 → ℝ) → E) (A₁' Δ₁ C' : Set E),
        B'.faces.Finite ∧ IsPLBall 3 N' ∧ IsPLBall 3 B'.space ∧
        Δ ⊆ N' ∧ N' ⊆ K.space ∧ N' ⊆ U ∧
        (∀ x ∈ Δ, N' ∈ 𝓝[K.space] x) ∧ B'.space ⊆ N' ∧
        IsPLHomeomorphOn g' (stdSimplex ℝ (Fin 3)) (D₂ ∩ N') ∧
        D₂ ∩ N' ⊆ (boundaryComplex 3 B').space ∧
        A₁' = N' ∩ closure (D₁ \ Δ) ∧ A₁' ⊆ B'.space ∧
        IsPLBall 2 Δ₁ ∧ Δ₁ ⊆ (boundaryComplex 3 B').space ∧
        (boundaryComplex 3 B').space = (D₂ ∩ N') ∪ Δ₁ ∧
        (D₂ ∩ N') ∩ Δ₁ = g' '' stdSimplexBoundary 2 ∧
        C' = (C \ (A₁' \ ((D₂ ∩ N') ∪ Δ₁))) ∪ Δ₁ ∧
        C ∩ B'.space = (D₂ ∩ N') ∪ A₁' ∧
        C' ∩ B'.space = (D₂ ∩ N') ∪ Δ₁ ∧
        C' \ B'.space = C \ B'.space := by
    let _ : Finite B.faces := hBfin.to_subtype
    let Δ₁ := closure ((boundaryComplex 3 B).space \ (D₂ ∩ N.space))
    have hBboundary : IsPLSphere 2 (boundaryComplex 3 B).space :=
      isPLSphere_boundaryComplex_space_of_isPLBall B hB
    have hΔ₁ : IsPLBall 2 Δ₁ :=
      hBboundary.isPLBall_closure_sdiff hmiddleBall hmiddleB
    have hΔ₁boundary : Δ₁ ⊆ (boundaryComplex 3 B).space :=
      closure_minimal sdiff_subset hBboundary.isPolyhedron.isClosed
    have hboundaryCover : (boundaryComplex 3 B).space = (D₂ ∩ N.space) ∪ Δ₁ := by
      apply Subset.antisymm
      · intro x hx
        by_cases hxm : x ∈ D₂ ∩ N.space
        · exact Or.inl hxm
        · exact Or.inr (subset_closure ⟨hx, hxm⟩)
      · exact union_subset hmiddleB hΔ₁boundary
    have hmiddleMeet : (D₂ ∩ N.space) ∩ Δ₁ = g '' stdSimplexBoundary 2 :=
      hBboundary.inter_closure_sdiff_eq_image_stdSimplexBoundary hg hmiddleB
    have hmiddleSide : D₂ ∩ B.space = D₂ ∩ N.space := by
      apply Subset.antisymm
      · rintro x ⟨hxD₂, hxB⟩
        exact ⟨hxD₂, hBN hxB⟩
      · intro x hx
        exact ⟨hx.1, boundaryComplex_space_subset 3 B (hmiddleB hx)⟩
    have hD₁Side : D₁ ∩ B.space = Δ ∪ A₁ := by
      apply Subset.antisymm
      · rintro x ⟨hxD₁, hxB⟩
        by_cases hxΔ : x ∈ Δ
        · exact Or.inl hxΔ
        · exact Or.inr ⟨hBN hxB, subset_closure ⟨hxD₁, hxΔ⟩⟩
      · rintro x (hxΔ | hxA₁)
        · have hxmiddle : x ∈ D₂ ∩ N.space := ⟨hΔD₂ hxΔ, hΔN hxΔ⟩
          have hxside := hmiddleSide.symm.subset hxmiddle
          exact ⟨hΔD₁ hxΔ, hxside.2⟩
        · exact ⟨closure_minimal sdiff_subset hD₁.isPolyhedron.isClosed hxA₁.2,
            hA₁B hxA₁⟩
    have hCtrace : C ∩ B.space = (D₂ ∩ N.space) ∪ A₁ := by
      ext x
      constructor
      · rintro ⟨hxC, hxB⟩
        have hxO : x ∈ O := hNO (hBN hxB)
        rcases hOC ⟨hxO, hxC⟩ with hxD₁ | hxD₂
        · rcases hD₁Side.subset ⟨hxD₁, hxB⟩ with hxΔ | hxA₁
          · exact Or.inl ⟨hΔD₂ hxΔ, hBN hxB⟩
          · exact Or.inr hxA₁
        · exact Or.inl ⟨hxD₂, hBN hxB⟩
      · rintro (hxmiddle | hxA₁)
        · have hxside := hmiddleSide.symm.subset hxmiddle
          exact ⟨hD₂C hxmiddle.1, hxside.2⟩
        · exact ⟨hD₁C (closure_minimal sdiff_subset hD₁.isPolyhedron.isClosed hxA₁.2),
            hA₁B hxA₁⟩
    let C' := (C \ (A₁ \ ((D₂ ∩ N.space) ∪ Δ₁))) ∪ Δ₁
    have hC'trace : C' ∩ B.space = (D₂ ∩ N.space) ∪ Δ₁ := by
      ext x
      constructor
      · rintro ⟨hxC', hxB⟩
        rcases hxC' with hxC' | hxΔ₁
        · rcases hCtrace.subset ⟨hxC'.1, hxB⟩ with hxmiddle | hxA₁
          · exact Or.inl hxmiddle
          · by_contra hxnot
            exact hxC'.2 ⟨hxA₁, hxnot⟩
        · exact Or.inr hxΔ₁
      · rintro (hxmiddle | hxΔ₁)
        · have hxside := hmiddleSide.symm.subset hxmiddle
          refine ⟨Or.inl ⟨(hCtrace.symm.subset (Or.inl hxmiddle)).1, ?_⟩, hxside.2⟩
          rintro ⟨-, hxnot⟩
          exact hxnot (Or.inl hxmiddle)
        · exact ⟨Or.inr hxΔ₁, boundaryComplex_space_subset 3 B
            (hΔ₁boundary hxΔ₁)⟩
    have houtside : C' \ B.space = C \ B.space := by
      ext x
      constructor
      · rintro ⟨hxC', hxB⟩
        rcases hxC' with hxC' | hxΔ₁
        · exact ⟨hxC'.1, hxB⟩
        · exact (hxB (boundaryComplex_space_subset 3 B
            (hΔ₁boundary hxΔ₁))).elim
      · rintro ⟨hxC, hxB⟩
        refine ⟨Or.inl ⟨hxC, fun hx => hxB (hA₁B hx.1)⟩, hxB⟩
    exact ⟨N.space, B, g, A₁, Δ₁, C', hBfin, hN, hB, hΔN, hNK, hNU,
      hnhds, hBN, hg, hmiddleB, rfl, hA₁B, hΔ₁, hΔ₁boundary, hboundaryCover,
      hmiddleMeet, rfl, hCtrace, hC'trace, houtside⟩
  rcases hside with hA₁K₀ | hA₁K₁
  · exact finish K₀ hK₀fin hK₀ (subset_union_left.trans hcover.subset) hmiddleK₀ hA₁K₀
  · exact finish K₁ hK₁fin hK₁ (subset_union_right.trans hcover.subset) hmiddleK₁ hA₁K₁

end DifferentialGeometry.Topology.PiecewiseLinear
