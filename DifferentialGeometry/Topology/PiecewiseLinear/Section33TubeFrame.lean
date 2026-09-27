/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FineSimplexTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEndPoints
import DifferentialGeometry.Topology.PiecewiseLinear.TubeOfGraphDualCells
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

open Classical in
theorem exists_section33TubeFrame
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite L.faces]
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2) (hedge : ∃ e ∈ L.faces, e.card = 2)
    (hend : ∀ v : L.vertices, ((SimplicialComplex.edgeGraph L).neighborSet v).ncard ≠ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hLU : L.space ⊆ U)
    (hh : Topology.IsEmbedding (U.domRestrict h)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (T L' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
      (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))),
      T.faces.Finite ∧ IsSubdivision L' L ∧ L'.faces ⊆ T.faces ∧
      IsCombinatorialManifoldWithBoundary 3 T ∧
      IsCombinatorialManifoldWithBoundary 3 (derivedNeighborhood T L') ∧
      (derivedNeighborhood T L').space ⊆ U ∧
      (∀ v : L'.vertices, ((SimplicialComplex.edgeGraph L').neighborSet v).ncard ≠ 1) ∧
      IsTube L' (derivedNeighborhood T L').space C D Dbd h
        (h '' (derivedNeighborhood T L').space) ∧
      (∀ v ∈ L'.vertices, C v = (graphDualCell T L' v).space) ∧
      ∀ v ∈ L'.vertices, ∀ x ∈ C v, ∀ y ∈ C v, dist (h x) (h y) < ε / 4 := by
  have hLc : IsCompact L.space := SimplicialComplex.isCompact_geometricSpace L
  obtain ⟨δ, hδ, hthick⟩ := hLc.exists_cthickening_subset_open hU hLU
  have hcont : ContinuousOn h (Metric.cthickening δ L.space) :=
    (continuousOn_iff_continuous_domRestrict.mpr hh.continuous).mono hthick
  obtain ⟨η, hη, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    ((hLc.cthickening (r := δ)).uniformContinuousOn_of_continuous hcont) (ε / 4) (by positivity)
  obtain ⟨T, L', hTfin, hT, hL', hL'T, hLint, hcard', hdiam⟩ :=
    exists_simplex_subdivision_graphDualCell_diam_lt (n := 2) finrank_euclideanSpace_fin L hdim
      (lt_min hδ hη)
  let _ : Finite T.faces := hTfin.to_subtype
  let _ : Finite L'.faces := (hTfin.subset hL'T).to_subtype
  have hvL : ∀ v ∈ L'.vertices, v ∈ L.space := fun v hv => by
    rw [← hL'.space_eq]
    exact L'.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
  have hsmall : ∀ v ∈ L'.vertices, ∀ x ∈ (graphDualCell T L' v).space,
      ∀ y ∈ (graphDualCell T L' v).space, x ∈ Metric.cthickening δ L.space ∧ dist x y < η := by
    intro v hv x hx y hy
    let _ : Finite (graphDualCell T L' v).faces := (graphDualCell_faces_finite T L' v).to_subtype
    have hbdd := (SimplicialComplex.isCompact_geometricSpace (graphDualCell T L' v)).isBounded
    have hvC := mem_graphDualCell_space_of_singleton_mem T L' hL'T hv
    have hxv := (Metric.dist_le_diam_of_mem hbdd hx hvC).trans_lt (hdiam v)
    exact ⟨Metric.mem_cthickening_of_dist_le x v δ L.space (hvL v hv)
        (hxv.le.trans (min_le_left _ _)),
      (Metric.dist_le_diam_of_mem hbdd hx hy).trans_lt ((hdiam v).trans_le (min_le_right _ _))⟩
  have hNU : (⋃ v ∈ L'.vertices, (graphDualCell T L' v).space) ⊆ U :=
    iUnion₂_subset fun v hv x hx => hthick (hsmall v hv x hx x hx).1
  have hh' : IsEmbedding ((⋃ v ∈ L'.vertices, (graphDualCell T L' v).space).domRestrict h) :=
    hh.comp (IsEmbedding.inclusion hNU)
  obtain ⟨C, D, Dbd, htube, hCpin⟩ :
      ∃ (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
        (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))),
      IsTube L' (⋃ v ∈ L'.vertices, (graphDualCell T L' v).space) C D Dbd h
        (h '' ⋃ v ∈ L'.vertices, (graphDualCell T L' v).space) ∧
      ∀ v ∈ L'.vertices, C v = (graphDualCell T L' v).space :=
    ⟨_, _, _, (isTube_graphDualCell hTfin hT hL'T hcard'
      (hL'.exists_mem_faces_card_eq_two hdim hedge) fun v hv => hLint (hvL v hv)).of_isEmbedding
        hh', fun v _ => rfl⟩
  have hNeq : ∀ inst : DecidableEq (EuclideanSpace ℝ (Fin 3)),
      (@derivedNeighborhood _ _ _ inst T L').space =
        ⋃ v ∈ L'.vertices, (graphDualCell T L' v).space := by
    intro inst
    obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
    exact (iUnion_graphDualCell_space T L' hL'T).symm
  have hNman : ∀ inst : DecidableEq (EuclideanSpace ℝ (Fin 3)),
      IsCombinatorialManifoldWithBoundary 3 (@derivedNeighborhood _ _ _ inst T L') := by
    intro inst
    obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
    exact hT.derivedNeighborhood L'
  refine ⟨T, L', C, D, Dbd, hTfin, hL', hL'T, hT, hNman _, ?_,
    hL'.edgeGraph_neighborSet_ncard_ne_one hdim hend, ?_, hCpin, ?_⟩
  · rw [hNeq]
    exact hNU
  · rw [hNeq]
    exact htube
  · intro v hv x hx y hy
    rw [hCpin v hv] at hx hy
    exact hunif x (hsmall v hv x hx y hy).1 y (hsmall v hv y hy x hx).1 (hsmall v hv x hx y hy).2

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
