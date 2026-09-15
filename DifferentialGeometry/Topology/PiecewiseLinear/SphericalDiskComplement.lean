import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronPush
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexFacetComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_sphere_disk_to_simplex
    {S D : Set E} (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) :
    ∃ (T : Finset (EuclideanSpace ℝ (Fin 3))) (a : EuclideanSpace ℝ (Fin 3))
      (f : E → EuclideanSpace ℝ (Fin 3)),
      AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3)) ∧ T.card = 4 ∧ a ∈ T ∧
      IsPLHomeomorphOn f S (frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      f '' D = convexHull ℝ ((T.erase a : Finset (EuclideanSpace ℝ (Fin 3))) : Set _) := by
  classical
  obtain ⟨T, hT, hTcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 2) (by simp) (0 : EuclideanSpace ℝ (Fin 3)) Filter.univ_mem
  have hspan : affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using hTcard)
    have hrange : range ((↑) : T → EuclideanSpace ℝ (Fin 3)) =
        (T : Set (EuclideanSpace ℝ (Fin 3))) := Subtype.range_coe
    exact (congrArg (affineSpan ℝ) hrange).symm.trans h
  have hboundary : IsPLSphere 2 (frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))) :=
    isPLSphere_frontier_convexHull T hT hspan hTcard
  have hboundaryP := hboundary.isPolyhedron
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hboundary
  let g := v ∘ Function.invFunOn u (stdSimplexBoundary 3)
  have hg : IsPLHomeomorphOn g S (frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))) :=
    hu.symm.trans hv
  have hgD := hg.restrict hD.isPolyhedron hDS
  obtain ⟨a, ha, k, hk, hkC, hkD, -⟩ := exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron
    T hT hTcard (hD.of_isPLHomeomorphOn hgD)
      ((image_mono hDS).trans hg.image_eq.le) isOpen_univ (subset_univ _)
  have hkfront : k '' frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) =
      frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) := by
    rw [k.image_frontier, hkC]
  have hk' := hk.restrict hboundaryP (subset_univ _)
  rw [hkfront] at hk'
  refine ⟨T, a, k ∘ g, hT, hTcard, ha, hg.trans hk', ?_⟩
  change (fun x => k (g x)) '' D = _
  rw [← image_image k g]
  exact hkD

theorem IsPLSphere.isPLBall_closure_sdiff {S D : Set E}
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) :
    IsPLBall 2 (closure (S \ D)) := by
  classical
  obtain ⟨T, a, f, hT, hTcard, ha, hf, hfD⟩ :=
    exists_isPLHomeomorphOn_sphere_disk_to_simplex hS hD hDS
  let B := frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))
  let F : Set (EuclideanSpace ℝ (Fin 3)) := convexHull ℝ (T.erase a : Set (EuclideanSpace ℝ (Fin 3)))
  have hF : IsPLBall 2 F := isPLBall_convexHull_of_affineIndependent (T.erase a)
    (affineIndependent_of_subset hT (Finset.erase_subset a T))
      (by rw [Finset.card_erase_of_mem ha, hTcard])
  have hFB : F ⊆ B := by
    change convexHull ℝ (T.erase a : Set (EuclideanSpace ℝ (Fin 3))) ⊆ B
    rw [← hfD]
    exact (image_mono hDS).trans hf.image_eq.le
  obtain ⟨N, hN, hCN, -⟩ := exists_isPolyhedron_neighborhood
    (T.finite_toSet.isCompact_convexHull ℝ) isOpen_univ (subset_univ _)
  have hFball := hF
  obtain ⟨q, hq⟩ := hF
  obtain ⟨k, hk, hkF, -⟩ := (hasPushProperty_convexHull_simplex T hT hTcard).2 F ⟨q, hq⟩ hFB
    |>.2.2.2 q hq N hN (sdiff_subset.trans hCN)
  have hcomp : IsPLBall 2 (closure (B \ F)) := by
    rw [← hkF]
    exact hFball.of_isPLHomeomorphOn
      (hk.restrict hFball.isPolyhedron (subset_univ F))
  have himg : f '' closure (S \ D) = closure (B \ F) := by
    rw [hf.image_closure hS.isPolyhedron.isCompact sdiff_subset,
      hf.bijOn.injOn.image_sdiff_subset hDS, hf.image_eq, hfD]
  have hsub : closure (S \ D) ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  have hback : Function.invFunOn f S '' closure (B \ F) = closure (S \ D) := by
    rw [← himg, image_image]
    have hInv : EqOn (Function.invFunOn f S ∘ f) id (closure (S \ D)) :=
      fun x hx => hf.bijOn.invOn_invFunOn.1 (hsub hx)
    exact hInv.image_eq.trans (image_id _)
  have hcompB : closure (B \ F) ⊆ B := closure_minimal sdiff_subset isClosed_frontier
  have h := hcomp.of_isPLHomeomorphOn (hf.symm.restrict hcomp.isPolyhedron hcompB)
  rwa [hback] at h

theorem IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary {S D : Set E}
    (hS : IsPLSphere 2 S) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) (hDS : D ⊆ S) :
    D ∩ closure (S \ D) = q '' stdSimplexBoundary 2 := by
  classical
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  obtain ⟨T, a, f, hT, hTcard, ha, hf, hfD⟩ :=
    exists_isPLHomeomorphOn_sphere_disk_to_simplex hS hD hDS
  have hspan : affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using hTcard)
    have hrange : range ((↑) : T → EuclideanSpace ℝ (Fin 3)) =
        (T : Set (EuclideanSpace ℝ (Fin 3))) := Subtype.range_coe
    exact (congrArg (affineSpan ℝ) hrange).symm.trans h
  have hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  have hFcard : (T.erase a).card = 1 + 2 := by rw [Finset.card_erase_of_mem ha, hTcard]
  have hfDpl := hf.restrict hD.isPolyhedron hDS
  rw [hfD] at hfDpl
  have hJimage : f '' (q '' stdSimplexBoundary 2) = (simplexBoundary (T.erase a) hF).space := by
    rw [image_image]
    exact image_stdSimplexBoundary_of_isPLHomeomorphOn_convexHull hF hFcard (hq.trans hfDpl)
  have hcl : closure (S \ D) ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  have hJsub : q '' stdSimplexBoundary 2 ⊆ S := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hDS (hq.bijOn.mapsTo hy.1)
  have himage : f '' (D ∩ closure (S \ D)) = f '' (q '' stdSimplexBoundary 2) := by
    rw [hf.bijOn.injOn.image_inter hDS hcl,
      hf.image_closure hS.isPolyhedron.isCompact sdiff_subset,
      hf.bijOn.injOn.image_sdiff_subset hDS, hf.image_eq, hfD, hJimage]
    exact convexHull_erase_inter_closure_frontier_sdiff T hT hspan ha
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := himage ▸ (show f x ∈ f '' (D ∩ closure (S \ D)) from ⟨x, hx, rfl⟩)
    exact (hf.bijOn.injOn (hJsub hy) (hDS hx.1) hyx) ▸ hy
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := himage.symm ▸ (show f x ∈ f '' (q '' stdSimplexBoundary 2) from ⟨x, hx, rfl⟩)
    exact (hf.bijOn.injOn (hDS hy.1) (hJsub hx) hyx) ▸ hy

end DifferentialGeometry.Topology.PiecewiseLinear
