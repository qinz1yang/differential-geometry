/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FreeTriangleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section

variable [dE : DecidableEq E] [dP : DecidableEq (EuclideanSpace ℝ (Fin 2))]

open Classical in
private theorem isPLBall_derivedNeighborhood_of_isGlueIso_planar_aux
    (K A : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite A.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hAK : A.faces ⊆ (boundaryComplex 3 K).faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso A L φ ψ)
    {t₀ : Finset E} (ht₀ : t₀ ∈ A.faces) (ht₀card : t₀.card = 3) :
    IsPLBall 3 (derivedNeighborhood K A).space := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdP : dP = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  generalize hn : {u ∈ A.faces | u.card = 3}.ncard = n
  induction n using Nat.strong_induction_on generalizing A L with
  | h n ih =>
    have hA := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
    by_cases heq : A.space = convexHull ℝ (t₀ : Set E)
    · have hAsimplex : A = simplexComplex t₀ (A.indep ht₀) := by
        apply Geometry.SimplicialComplex.ext
        ext s
        change s ∈ A.faces ↔ s.Nonempty ∧ s ⊆ t₀
        constructor
        · intro hs
          have hx := centroid_mem_openSimplex_of_mem_faces A s hs
          have hxt : s.centroid ℝ id ∈ convexHull ℝ (t₀ : Set E) :=
            heq ▸ A.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
          exact ⟨A.nonempty_of_mem_faces hs,
            face_subset_of_mem_openSimplex_of_mem_convexHull A hs ht₀ hx hxt⟩
        · rintro ⟨hsne, hst⟩
          exact A.down_closed ht₀ hst hsne
      rw [hAsimplex]
      exact hK.isPLBall_derivedNeighborhood_simplex (hAK ht₀)
    · obtain ⟨t, s, ht, htcard, htt₀, -, hst, hscard, htrace, hinter, hball⟩ :=
        exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar A L hIso hL ht₀ ht₀card heq
      let A' := eraseTriangleComplex A t
      let L' := eraseTriangleComplex L (t.image φ)
      let _ : Finite A'.faces := (eraseTriangleComplex_faces_finite A t).to_subtype
      let _ : Finite L'.faces := (eraseTriangleComplex_faces_finite L (t.image φ)).to_subtype
      have hA'K : A'.faces ⊆ (boundaryComplex 3 K).faces :=
        (eraseTriangleComplex_faces_subset A t).trans hAK
      have hIso' : IsGlueIso A' L' φ ψ := hIso.eraseTriangleComplex ht
      have hL' : IsPLBall 2 L'.space := hball.of_isPLHomeomorphOn hIso'.isPLHomeomorphOn
      have ht₀' : t₀ ∈ A'.faces :=
        (mem_eraseTriangleComplex_triangle_iff A t
          (fun u hu => card_le_of_isPLBall A hA hu) ht₀card).mpr ⟨ht₀, htt₀.symm⟩
      have hlt : {u ∈ A'.faces | u.card = 3}.ncard < n := by
        rw [← hn]
        exact ncard_triangles_eraseTriangleComplex_lt A t ht htcard
          (fun u hu => card_le_of_isPLBall A hA hu)
      have hprev := ih _ hlt (A := A') (L := L') (hAK := hA'K)
        (hL := hL') (hIso := hIso') (ht₀ := ht₀') rfl
      exact hK.isPLBall_derivedNeighborhood_of_free_triangle hA hAK ht htcard hst
        hscard htrace hinter hprev

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_of_isGlueIso_planar
    {K A : Geometry.SimplicialComplex ℝ E}
    {L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    [Finite K.faces] [Finite A.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hAK : A.faces ⊆ (boundaryComplex 3 K).faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso A L φ ψ) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K A).space := by
  classical
  have hA := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
  obtain ⟨x, hx⟩ := hA.nonempty
  obtain ⟨s, hs, -⟩ := A.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htc⟩ := exists_face_superset_card_eq_of_isPLBall A hA hs
  exact isPLBall_derivedNeighborhood_of_isGlueIso_planar_aux K A L hK hAK hL hIso ht htc

end
open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_boundary_disk
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space) :
    ∃ C : Set E, IsPLBall 3 C ∧ C ⊆ K.space ∧ D ⊆ C := by
  classical
  obtain ⟨R, A, L, φ, ψ, hR, hRfin, hAR, hAfin, hAD, hLfin, hL, hIso, -⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar K hD
      (hDK.trans (boundaryComplex_space_subset 3 K))
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hAK : A.faces ⊆ (boundaryComplex 3 R).faces := by
    intro s hs
    have hx := centroid_mem_openSimplex_of_mem_faces A s hs
    have hxD : s.centroid ℝ id ∈ D :=
      hAD ▸ A.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
    have hxB : s.centroid ℝ id ∈ (boundaryComplex 3 R).space := by
      rw [boundaryComplex_space_of_isSubdivision K R hK hR]
      exact hDK hxD
    exact mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 R)
      (hAR hs) hx hxB
  have hball :=
    (hK.of_isSubdivision hR).isPLBall_derivedNeighborhood_of_isGlueIso_planar hAK hL hIso
  have hsub : A.space ⊆ (PiecewiseLinear.derivedNeighborhood R A).space := by
    rw [← iUnion_derivedNeighborhoodCell_space R A hAR]
    exact space_subset_iUnion_derivedNeighborhoodCell_space R A hAR
  exact ⟨(PiecewiseLinear.derivedNeighborhood R A).space, hball,
    (derivedNeighborhood_space_subset R A).trans hR.space_eq.subset, hAD ▸ hsub⟩

end DifferentialGeometry.Topology.PiecewiseLinear
