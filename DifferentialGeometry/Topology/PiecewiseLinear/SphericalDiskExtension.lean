/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two
    {S D : Set E} {S' D' : Set F} (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    (hD : IsPLBall 2 D) (hDS : D ⊆ S) {g : E → F}
    (hg : IsPLHomeomorphOn g D D') (hD'S' : D' ⊆ S') :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ EqOn G g D := by
  classical
  have hD' := hD.of_isPLHomeomorphOn hg
  let A := closure (S \ D)
  let A' := closure (S' \ D')
  have hA : IsPLBall 2 A := hS.isPLBall_closure_sdiff hD hDS
  have hA' : IsPLBall 2 A' := hS'.isPLBall_closure_sdiff hD' hD'S'
  obtain ⟨q, hq⟩ := hD
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  obtain ⟨a, ha⟩ := hA
  have hA : IsPLBall 2 A := ⟨a, ha⟩
  obtain ⟨a', ha'⟩ := hA'
  have hA' : IsPLBall 2 A' := ⟨a', ha'⟩
  have hmeet : g '' (D ∩ A) = D' ∩ A' := by
    rw [hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS,
      hS'.inter_closure_sdiff_eq_image_stdSimplexBoundary (hq.trans hg) hD'S', image_comp]
  have haB : a '' stdSimplexBoundary 2 = A ∩ D :=
    hS.image_stdSimplexBoundary_complement hD hDS ha
  have ha'B : a' '' stdSimplexBoundary 2 = A' ∩ D' :=
    hS'.image_stdSimplexBoundary_complement hD' hD'S' ha'
  have hgJ : IsPLHomeomorphOn g (a '' stdSimplexBoundary 2) (a' '' stdSimplexBoundary 2) := by
    rw [haB, ha'B, inter_comm A D, inter_comm A' D']
    have h := hg.restrict (hD.isPolyhedron.inter hA.isPolyhedron) inter_subset_left
    rwa [hmeet] at h
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_of_stdSimplexBoundary ha ha' hgJ
  rw [haB] at hfg
  have hgf : EqOn g f (D ∩ A) := fun _ hx => (hfg ⟨hx.2, hx.1⟩).symm
  have hcover : D ∪ A = S := by
    apply Subset.antisymm (union_subset hDS (closure_minimal sdiff_subset hS.isPolyhedron.isClosed))
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hcover' : D' ∪ A' = S' := by
    apply Subset.antisymm (union_subset hD'S' (closure_minimal sdiff_subset
        hS'.isPolyhedron.isClosed))
    intro x hx
    by_cases hxD : x ∈ D'
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have h := hg.piecewise hf hD.isPolyhedron hA.isPolyhedron hgf hmeet
  rw [hcover, hcover'] at h
  exact ⟨_, h, D.piecewise_eqOn g f⟩

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsPLBall 3 K.space) (hL : IsPLBall 3 L.space)
    {D : Set E} {D' : Set F} (hD : IsPLBall 2 D)
    (hDK : D ⊆ (boundaryComplex 3 K).space) {g : E → F}
    (hg : IsPLHomeomorphOn g D D') (hD'L : D' ⊆ (boundaryComplex 3 L).space) :
    ∃ G : E → F, IsPLHomeomorphOn G K.space L.space ∧ EqOn G g D := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two
    (isPLSphere_boundaryComplex_space_of_isPLBall K hK)
    (isPLSphere_boundaryComplex_space_of_isPLBall L hL) hD hDK hg hD'L
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L hK hL hf
  exact ⟨G, hG, (hGf.mono hDK).trans hfg⟩

theorem exists_isPLHomeomorphOn_eqOn_disk_of_eqOn_boundary
    {S D : Set E} (hS : IsPLSphere 2 S)
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDS : D ⊆ S) {g : E → E} (hg : IsPLHomeomorphOn g D D)
    (hfix : EqOn g id (r '' stdSimplexBoundary 2)) :
    ∃ G : E → E, IsPLHomeomorphOn G S S ∧ EqOn G g D ∧
      EqOn G id (closure (S \ D)) := by
  classical
  let A := closure (S \ D)
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hA : IsPLBall 2 A := hS.isPLBall_closure_sdiff hD hDS
  have hAId : IsPLHomeomorphOn (id : E → E) A A :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hA.isPolyhedron
      ((isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron hA.isPolyhedron
        (subset_univ A)) (bijOn_id A)
  have hmeet : D ∩ A = r '' stdSimplexBoundary 2 :=
    hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hDS
  have hfixA : EqOn g id (D ∩ A) := hmeet ▸ hfix
  have himage : g '' (D ∩ A) = D ∩ A := hfixA.image_eq.trans (image_id _)
  have hcover : D ∪ A = S := by
    apply Subset.antisymm
      (union_subset hDS (closure_minimal sdiff_subset hS.isPolyhedron.isClosed))
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hG := hg.piecewise hAId hD.isPolyhedron hA.isPolyhedron hfixA himage
  rw [hcover] at hG
  refine ⟨D.piecewise g id, hG, D.piecewise_eqOn g id, ?_⟩
  intro x hx
  by_cases hxD : x ∈ D
  · rw [D.piecewise_eq_of_mem g id hxD]
    exact hfixA ⟨hxD, hx⟩
  · exact D.piecewise_eq_of_notMem g id hxD

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_boundary_disk_of_eqOn_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 3 K.space) {D : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDK : D ⊆ (boundaryComplex 3 K).space)
    {g : E → E} (hg : IsPLHomeomorphOn g D D)
    (hfix : EqOn g id (r '' stdSimplexBoundary 2)) :
    ∃ G : E → E, IsPLHomeomorphOn G K.space K.space ∧ EqOn G g D ∧
      EqOn G id (closure ((boundaryComplex 3 K).space \ D)) := by
  let _ : DecidableEq E := Classical.decEq _
  have hS := isPLSphere_boundaryComplex_space_of_isPLBall K hK
  obtain ⟨f, hf, hfg, hfid⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_eqOn_boundary hS hr hDK hg hfix
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K K hK hK hf
  exact ⟨G, hG, (hGf.mono hDK).trans hfg,
    (hGf.mono (closure_minimal sdiff_subset hS.isPolyhedron.isClosed)).trans hfid⟩

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_boundary_disk_union
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 3 K.space) {D Q : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDK : D ⊆ (boundaryComplex 3 K).space)
    {g : E → E} (hg : IsPLHomeomorphOn g D D)
    (hfix : EqOn g id (r '' stdSimplexBoundary 2)) (hQ : IsPolyhedron Q)
    (hinter : K.space ∩ Q ⊆ closure ((boundaryComplex 3 K).space \ D)) :
    ∃ G : E → E, IsPLHomeomorphOn G (K.space ∪ Q) (K.space ∪ Q) ∧
      EqOn G g D ∧ EqOn G id Q := by
  let _ : DecidableEq E := Classical.decEq _
  obtain ⟨f, hf, hfg, hfid⟩ :=
    exists_isPLHomeomorphOn_eqOn_boundary_disk_of_eqOn_boundary K hK hr hDK hg hfix
  have hQId : IsPLHomeomorphOn (id : E → E) Q Q :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hQ
      ((isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron hQ (subset_univ Q))
      (bijOn_id Q)
  have hfixQ : EqOn f id (K.space ∩ Q) := hfid.mono hinter
  have himage : f '' (K.space ∩ Q) = K.space ∩ Q :=
    hfixQ.image_eq.trans (image_id _)
  have hDK' : D ⊆ K.space := hDK.trans
    (space_mono_of_faces_subset (boundaryComplex_faces_subset 3 K))
  refine ⟨K.space.piecewise f id,
    hf.piecewise hQId hK.isPolyhedron hQ hfixQ himage,
    ((K.space.piecewise_eqOn f id).mono hDK').trans hfg, ?_⟩
  intro x hx
  by_cases hxK : x ∈ K.space
  · rw [K.space.piecewise_eq_of_mem f id hxK]
    exact hfixQ ⟨hxK, hx⟩
  · exact K.space.piecewise_eq_of_notMem f id hxK

end DifferentialGeometry.Topology.PiecewiseLinear
