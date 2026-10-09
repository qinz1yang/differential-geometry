/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDiskShelling
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleBoundaryDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.DiskDeletionBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_disk_boundary_of_triangular_deletion_sequence
    {D β C : Set E} {subcells : Finset (Set E)}
    {P Q : Geometry.SimplicialComplex ℝ E × Finset (Set E)}
    (hsequence : Relation.ReflTransGen (IsFreeDiskCellDeletion D) P Q)
    (hP : IsPLDiskDecomposition P.1 P.2)
    (htriangles : ∀ F ∈ P.2, ∃ t ∈ P.1.faces, t.card = 3 ∧
      F = convexHull ℝ (t : Set E))
    (hsub : subcells ⊆ P.2) (hDcover : D = ⋃ F ∈ subcells, F)
    (hβP : β ⊆ (boundaryComplex 2 P.1).space) (hβD : β ⊆ D)
    (hC : IsPolyhedron C) (hinside : P.1.space \ β ⊆ interior C) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ e '' C = C ∧
      e '' (boundaryComplex 2 P.1).space = (boundaryComplex 2 Q.1).space := by
  induction hsequence using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨Homeomorph.refl E, ?_, fun _ _ => rfl, fun _ _ => rfl,
        image_id _, image_id _⟩
      exact ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
        (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx =>
          (bijOn_id univ).invOn_invFunOn.1 hx⟩
  | @head P R hstep hsequence ih =>
      let _ : Finite P.1.faces := hP.finite_faces.to_subtype
      obtain ⟨hR, hRtriangles, t, ht, htcard, _, httrace, hRspace⟩ :=
        hstep.triangle_data htriangles
      let _ : Finite R.1.faces := hR.finite_faces.to_subtype
      have hsubR : subcells ⊆ R.2 := by
        obtain ⟨_, F, hF, hnot, _, _, hcells⟩ := hstep
        rw [hcells]
        intro G hG
        refine Finset.mem_erase.mpr ⟨?_, hsub hG⟩
        intro hGF
        apply hnot
        rw [hDcover, ← hGF]
        exact subset_iUnion_of_subset G (subset_iUnion_of_subset hG Subset.rfl)
      have hDR : D ⊆ R.1.space := by
        rw [hDcover]
        exact iUnion₂_subset fun F hF => hR.cell_subset (hsubR hF)
      have hRP : R.1.space ⊆ P.1.space := by
        rw [hRspace]
        exact closure_minimal sdiff_subset hP.isPLBall.isPolyhedron.isClosed
      have hβR : β ⊆ (boundaryComplex 2 R.1).space := fun x hx =>
        inter_boundaryComplex_space_subset_of_subset P.1 R.1
          hP.isPLBall.isCombinatorialManifoldWithBoundary
          hR.isPLBall.isCombinatorialManifoldWithBoundary hRP ⟨hDR (hβD hx), hβP hx⟩
      let A := simplexComplex t (P.1.indep ht)
      let _ : Finite A.faces := (simplexComplex_faces_finite t (P.1.indep ht)).to_subtype
      have hAspace : A.space = convexHull ℝ (t : Set E) :=
        simplexComplex_space t (P.1.indep ht) (P.1.nonempty_of_mem_faces ht)
      have hA : IsPLBall 2 A.space := hAspace.symm ▸
        isPLBall_convexHull_of_affineIndependent t (P.1.indep ht) htcard
      have hAP : A.space ⊆ P.1.space := hAspace.subset.trans (P.1.convexHull_subset_space ht)
      have hbd := boundary_inter_disk_complement_eq P.1 A R.1 hP.isPLBall hA hR.isPLBall hAP
        (hAspace.symm ▸ httrace) (hAspace.symm ▸ hRspace)
      have hβres : β ⊆ closure ((boundaryComplex 2 P.1).space \ convexHull ℝ (t : Set E)) := by
        rw [← hAspace, ← hbd]
        exact fun x hx => ⟨hβP hx, hDR (hβD hx)⟩
      have hmove : convexHull ℝ (t : Set E) \
          closure ((boundaryComplex 2 P.1).space \ convexHull ℝ (t : Set E)) ⊆ interior C := by
        intro x hx
        exact hinside ⟨P.1.convexHull_subset_space ht hx.1, fun hxβ => hx.2 (hβres hxβ)⟩
      obtain ⟨f, hf, hffix, hffront, hfC, hfbd⟩ :=
        exists_isPLHomeomorphOn_disk_boundary_triangle_deletion P.1 R.1 hP.isPLBall hR.isPLBall
          ht htcard (by simpa only [inter_comm] using httrace) hRspace hC hmove
      obtain ⟨g, hg, hgfix, hgfront, hgC, hgbd⟩ :=
        ih hR hRtriangles hsubR hβR (fun x hx => hinside ⟨hRP hx.1, hx.2⟩)
      refine ⟨f.trans g, hf.trans hg, ?_, ?_, ?_, ?_⟩
      · intro x hx
        change g (f x) = x
        rw [hffix hx]
        exact hgfix hx
      · intro x hx
        change g (f x) = x
        rw [hffront hx]
        exact hgfront hx
      · change (g ∘ f) '' C = C
        rw [image_comp, hfC, hgC]
      · change (g ∘ f) '' (boundaryComplex 2 P.1).space = _
        rw [image_comp, hfbd, hgbd]

open Classical in
theorem exists_isPLHomeomorphOn_disk_boundary_to_subdisk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {D β C : Set E} (hD : IsPLBall 2 D) (hDK : D ⊆ K.space)
    (hβK : β ⊆ (boundaryComplex 2 K).space) (hβD : β ⊆ D)
    (hC : IsPolyhedron C) (hinside : K.space \ β ⊆ interior C) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ IsPLBall 2 L.space ∧
      L.space = D ∧ ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
        EqOn e id (frontier C) ∧ e '' C = C ∧
        e '' (boundaryComplex 2 K).space = (boundaryComplex 2 L).space := by
  obtain ⟨R, L, cells, subcells, cs, hRfin, hRK, htriangles, hR,
    hsub, hDcover, hL, hLD, _, _, hsequence⟩ :=
    hK.exists_triangular_deletion_sequence_to_subdisk hD hDK
  let _ : Finite R.faces := hRfin.to_subtype
  have hKR : IsPLHomeomorphOn (id : E → E) K.space R.space := by
    rw [hRK]
    exact hK.isPolyhedron.isPLHomeomorphOn_id
  have hbd : (boundaryComplex 2 R).space = (boundaryComplex 2 K).space := by
    simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn K R
      hK.isCombinatorialManifoldWithBoundary hKR
  obtain ⟨e, he, hfix, hfront, hset, himage⟩ :=
    exists_isPLHomeomorphOn_disk_boundary_of_triangular_deletion_sequence hsequence hR
      htriangles hsub hDcover (hbd.symm ▸ hβK) hβD hC (hRK.symm ▸ hinside)
  exact ⟨L, hL.finite_faces, hL.isPLBall, hLD, e, he, hfix, hfront, hset, hbd ▸ himage⟩

end DifferentialGeometry.Topology.PiecewiseLinear
