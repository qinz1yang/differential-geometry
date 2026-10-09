/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem exists_planar_isPLHomeomorphOn_of_isPLSphere_one [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 2))) (f : E → EuclideanSpace ℝ (Fin 2)),
      IsPLSphere 1 C ∧ IsPLHomeomorphOn f S C := by
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (Filter.univ_mem : univ ∈ nhds (0 : EuclideanSpace ℝ (Fin 2)))
  have hC := (isPLBall_convexHull_of_affineIndependent T hT hcard).isPLSphere_frontier
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hC
  exact ⟨_, _, ⟨v, hv⟩, hu.symm.trans hv⟩

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one_of_ambient
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {J : Set E} {J' : Set F} {A : Set E} {A' : Set F}
    (hJ : IsPLSphere 1 J) (hJ' : IsPLSphere 1 J')
    (hA : IsPLBall 1 A) (hAJ : A ⊆ J) {g : E → F}
    (hg : IsPLHomeomorphOn g A A') (hA'J' : A' ⊆ J') :
    ∃ G : E → F, IsPLHomeomorphOn G J J' ∧ EqOn G g A := by
  obtain ⟨C, f, hC, hf⟩ := exists_planar_isPLHomeomorphOn_of_isPLSphere_one hJ
  obtain ⟨C', f', hC', hf'⟩ := exists_planar_isPLHomeomorphOn_of_isPLSphere_one hJ'
  let fi := Function.invFunOn f J
  let fi' := Function.invFunOn f' J'
  let B := f '' A
  let B' := f' '' A'
  let q := f' ∘ g ∘ Function.invFunOn f A
  have hfA : IsPLHomeomorphOn f A B :=
    hf.restrict hA.isPolyhedron hAJ
  have hf'A' : IsPLHomeomorphOn f' A' B' :=
    hf'.restrict (hA.of_isPLHomeomorphOn hg).isPolyhedron hA'J'
  have hB : IsPLBall 1 B := hA.of_isPLHomeomorphOn hfA
  have hq : IsPLHomeomorphOn q B B' := by
    simpa only [q] using (hfA.symm.trans hg).trans hf'A'
  obtain ⟨p, r, hpr⟩ := hB.isArc.exists_isArcBetween
  obtain ⟨Q, hQ, hQq⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one
    hC hC' hpr (by
      rintro _ ⟨x, hx, rfl⟩
      exact hf.bijOn.mapsTo (hAJ hx)) hq (by
      rintro _ ⟨x, hx, rfl⟩
      exact hf'.bijOn.mapsTo (hA'J' hx))
  refine ⟨fi' ∘ Q ∘ f, (hf.trans hQ).trans hf'.symm, ?_⟩
  intro x hx
  have hfxA : f x ∈ B := ⟨x, hx, rfl⟩
  have hfxJ : f x ∈ C := hf.bijOn.mapsTo (hAJ hx)
  have hgxA' : g x ∈ A' := hg.bijOn.mapsTo hx
  change fi' (Q (f x)) = g x
  rw [hQq hfxA]
  simp only [q, Function.comp_apply]
  rw [hfA.bijOn.invOn_invFunOn.1 hx]
  change Function.invFunOn f' J' (f' (g x)) = g x
  exact hf'.bijOn.invOn_invFunOn.1 (hA'J' hgxA')

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {A : Set E} {B : Set F} (hA : IsPLBall 1 A)
    (hAK : A ⊆ (boundaryComplex 2 K).space) {g : E → F}
    (hg : IsPLHomeomorphOn g A B) (hBL : B ⊆ (boundaryComplex 2 L).space) :
    ∃ G : E → F, IsPLHomeomorphOn G K.space L.space ∧ EqOn G g A := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  have hKboundary : IsPLSphere 1 (boundaryComplex 2 K).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall (n := 1) K hK
  have hLboundary : IsPLSphere 1 (boundaryComplex 2 L).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall (n := 1) L hL
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one_of_ambient
    hKboundary hLboundary hA hAK hg hBL
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L hK hL hf
  exact ⟨G, hG, (hGf.mono hAK).trans hfg⟩

open Classical in
theorem isPLBall_union_of_boundary_arc_of_ambient
    [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    (hA : IsPLBall 1 (K.space ∩ L.space))
    (hAK : K.space ∩ L.space ⊆ (boundaryComplex 2 K).space)
    (hAL : K.space ∩ L.space ⊆ (boundaryComplex 2 L).space) :
    IsPLBall 2 (K.space ∪ L.space) := by
  obtain ⟨P, Q, hPfin, hQfin, hP, hQ, hPQ, p, q, hpq, hinter, hBP, hBQ, -⟩ :=
    exists_isPLBall_pair_with_segment_inter_and_finite_frontier_inter
  let _ : Finite P.faces := hPfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hseg : IsPLBall 1 (segment ℝ p q) := isPLBall_segment hpq
  obtain ⟨u, hu⟩ := hA
  have hA : IsPLBall 1 (K.space ∩ L.space) := ⟨u, hu⟩
  obtain ⟨v, hv⟩ := hseg
  let g := v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
  have hg : IsPLHomeomorphOn g (K.space ∩ L.space) (segment ℝ p q) := hu.symm.trans hv
  let d : DecidableEq (EuclideanSpace ℝ (Fin 2)) := inferInstance
  have hd : d = Classical.decEq _ := Subsingleton.elim _ _
  have hBP' : segment ℝ p q ⊆
      (@boundaryComplex _ _ _ (Classical.decEq _) 2 P).space := by
    change segment ℝ p q ⊆ (@boundaryComplex _ _ _ d 2 P).space at hBP
    rwa [hd] at hBP
  have hBQ' : segment ℝ p q ⊆
      (@boundaryComplex _ _ _ (Classical.decEq _) 2 Q).space := by
    change segment ℝ p q ⊆ (@boundaryComplex _ _ _ d 2 Q).space at hBQ
    rwa [hd] at hBQ
  obtain ⟨f₁, hf₁, hf₁g⟩ :=
    exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient K P hK hP hA hAK hg hBP'
  obtain ⟨f₂, hf₂, hf₂g⟩ :=
    exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient L Q hL hQ hA hAL hg hBQ'
  have hfg : EqOn f₁ f₂ (K.space ∩ L.space) := hf₁g.trans hf₂g.symm
  have himage : f₁ '' (K.space ∩ L.space) = P.space ∩ Q.space :=
    hf₁g.image_eq.trans (hg.image_eq.trans hinter.symm)
  have h := hf₁.piecewise hf₂ hK.isPolyhedron hL.isPolyhedron hfg himage
  exact hPQ.of_isPLHomeomorphOn h.symm

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_union_of_inter_isPLBall_one
    [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {C D : Set E}
    (hC : IsPLBall 2 C) (hD : IsPLBall 2 D) (hCK : C ⊆ K.space) (hDK : D ⊆ K.space)
    (hI : IsPLBall 1 (C ∩ D)) : IsPLBall 2 (C ∪ D) := by
  obtain ⟨R, hR, hfin, hcover⟩ := exists_isSubdivision_subcomplexes K
    (fun b : Bool => if b then C else D)
    (fun b => by
      cases b with
      | false => exact hD.isPolyhedron
      | true => exact hC.isPolyhedron)
    (fun b => by
      cases b with
      | false => exact hDK
      | true => exact hCK)
  let _ : Finite R.faces := hfin.to_subtype
  let A := restrict R C
  let B := restrict R D
  let _ : Finite A.faces := (restrict_faces_finite R C).to_subtype
  let _ : Finite B.faces := (restrict_faces_finite R D).to_subtype
  have hA : A.space = C := restrict_space_of_eq_biUnion R C (by simpa using hcover true)
  have hB : B.space = D := restrict_space_of_eq_biUnion R D (by simpa using hcover false)
  have hAB : IsPLBall 1 (A.space ∩ B.space) := by rwa [hA, hB]
  have hboundaryA : A.space ∩ B.space ⊆ (boundaryComplex 2 A).space :=
    _root_.DifferentialGeometry.Topology.PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall
      R A B (hK.of_isSubdivision hR)
      (hA.symm ▸ hC) (hB.symm ▸ hD) (restrict_faces_subset R C)
      (restrict_faces_subset R D) hAB
  have hboundaryB : A.space ∩ B.space ⊆ (boundaryComplex 2 B).space := by
    rw [inter_comm] at hAB ⊢
    exact
      _root_.DifferentialGeometry.Topology.PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall
      R B A (hK.of_isSubdivision hR)
      (hB.symm ▸ hD) (hA.symm ▸ hC) (restrict_faces_subset R D)
      (restrict_faces_subset R C) hAB
  have hU := isPLBall_union_of_boundary_arc_of_ambient A B (hA.symm ▸ hC)
    (hB.symm ▸ hD) hAB hboundaryA hboundaryB
  rwa [hA, hB] at hU

end DifferentialGeometry.Topology.PiecewiseLinear
