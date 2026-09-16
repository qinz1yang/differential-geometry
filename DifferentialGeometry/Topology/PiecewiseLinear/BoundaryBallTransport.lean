import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBall
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLBall_subset_inter_boundaryComplex {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall (n + 1) K.space) {D : Set E} (hD : IsPLBall n D)
    (hDK : D ⊆ (boundaryComplex (n + 1) K).space) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ IsPLBall (n + 1) L.space ∧
      L.space ⊆ K.space ∧ L.space ∩ (boundaryComplex (n + 1) K).space = D ∧
      D ⊆ (boundaryComplex (n + 1) L).space := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := n) (by simp) (0 : EuclideanSpace ℝ (Fin (n + 1))) Filter.univ_mem
  let R := simplexComplex T hT
  let _ : Finite R.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hRspace : R.space = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hR : IsPLBall (n + 1) R.space := hRspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨u, hu⟩ := hR
  obtain ⟨v, hv⟩ := hK
  have hK : IsPLBall (n + 1) K.space := ⟨v, hv⟩
  have hR : IsPLBall (n + 1) R.space := ⟨u, hu⟩
  let f := v ∘ Function.invFunOn u (stdSimplex ℝ (Fin (n + 2)))
  have hf : IsPLHomeomorphOn f R.space K.space := hu.symm.trans hv
  let g := Function.invFunOn f R.space
  have hD0 : IsPLBall n (g '' D) := hD.of_isPLHomeomorphOn
    (hf.symm.restrict hD.isPolyhedron (hDK.trans (boundaryComplex_space_subset (n + 1) K)))
  have hfrontR : frontier R.space = (boundaryComplex (n + 1) R).space :=
    frontier_space_eq_boundaryComplex_space hR.isCombinatorialManifoldWithBoundary
  have hgB : g '' (boundaryComplex (n + 1) K).space = frontier R.space :=
    (boundaryComplex_space_of_isPLHomeomorphOn K R hK.isCombinatorialManifoldWithBoundary
      hf.symm).symm.trans hfrontR.symm
  have hfB : (boundaryComplex (n + 1) K).space = f '' frontier R.space := by
    rw [hfrontR]
    exact boundaryComplex_space_of_isPLHomeomorphOn R K hR.isCombinatorialManifoldWithBoundary hf
  have hD0R : g '' D ⊆ frontier R.space := hgB ▸ image_mono hDK
  obtain ⟨Q, hQ, hQR, hQD, hDQ⟩ := exists_isPLBall_subset_inter_frontier (by simp) hR hD0 hD0R
  have hCQ : IsPLBall (n + 1) (f '' Q) :=
    hQ.of_isPLHomeomorphOn (hf.restrict hQ.isPolyhedron hQR)
  obtain ⟨L, hLfin, hLspace⟩ := hCQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall (n + 1) L.space := hLspace.symm ▸ hCQ
  have hback : f '' (g '' D) = D := by
    rw [image_image]
    have hfix : EqOn (f ∘ g) id D := fun x hx =>
      hf.bijOn.invOn_invFunOn.2 (boundaryComplex_space_subset (n + 1) K (hDK hx))
    exact hfix.image_eq.trans (image_id _)
  have hmeet : L.space ∩ (boundaryComplex (n + 1) K).space = D := by
    rw [hLspace, hfB, ← hf.bijOn.injOn.image_inter hQR hR.isPolyhedron.isClosed.frontier_subset,
      hQD, hback]
  have hLsub : L.space ⊆ K.space := hLspace ▸ (image_mono hQR).trans hf.image_eq.le
  obtain ⟨J, hJfin, hJspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite J.faces := hJfin.to_subtype
  have hJ : IsPLBall (n + 1) J.space := hJspace.symm ▸ hQ
  have hfJL : IsPLHomeomorphOn f J.space L.space := by
    rw [hJspace, hLspace]
    exact hf.restrict hQ.isPolyhedron hQR
  have hLB : (boundaryComplex (n + 1) L).space = f '' frontier Q := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn J L hJ.isCombinatorialManifoldWithBoundary hfJL,
      ← frontier_space_eq_boundaryComplex_space hJ.isCombinatorialManifoldWithBoundary, hJspace]
  refine ⟨L, hLfin, hL, hLsub, hmeet, ?_⟩
  rw [hLB, ← hback]
  exact image_mono hDQ

open Classical in
theorem exists_isPLBall_inter_boundaryComplex_eq_of_subset {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsPLBall (n + 1) A.space) (hAK : A.space ⊆ K.space)
    {D : Set E} (hD : IsPLBall n D) (hDA : D ⊆ A.space)
    (hDK : D ⊆ (boundaryComplex (n + 1) K).space) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ IsPLBall (n + 1) L.space ∧
      L.space ⊆ K.space ∧ L.space ∩ (boundaryComplex (n + 1) K).space = D ∧
      D ⊆ (boundaryComplex (n + 1) L).space := by
  classical
  have hfront := inter_boundaryComplex_space_subset_of_subset K A hK
    hA.isCombinatorialManifoldWithBoundary hAK
  obtain ⟨L, hfin, hL, hLA, hLD, hDL⟩ := exists_isPLBall_subset_inter_boundaryComplex A hA hD
    (fun x hx => hfront ⟨hDA hx, hDK hx⟩)
  refine ⟨L, hfin, hL, hLA.trans hAK, ?_, hDL⟩
  apply Subset.antisymm
  · rintro x ⟨hxL, hxK⟩
    exact hLD ▸ ⟨hxL, hfront ⟨hLA hxL, hxK⟩⟩
  · intro x hx
    exact ⟨(hLD.symm ▸ hx).1, hDK hx⟩
end DifferentialGeometry.Topology.PiecewiseLinear
