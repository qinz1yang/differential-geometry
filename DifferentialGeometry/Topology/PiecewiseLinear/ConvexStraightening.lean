import DifferentialGeometry.Topology.PiecewiseLinear.ConeStraightening
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexCone
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalTriangleDeletion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_frontier_of_convex
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : Convex ℝ C) (hball : IsPLBall 3 C) :
    IsSimplyEmbedded (frontier C) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  have hS : IsPLSphere 2 (frontier C) := hball.isPLSphere_frontier
  obtain ⟨K, hKfin, hKspace⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLSphere 2 K.space := hKspace.symm ▸ hS
  obtain ⟨p, hp⟩ := hball.interior_nonempty
  let hpK := isConeBase_of_space_subset_frontier_convex hC hball.isPolyhedron.isClosed hp K hKspace.le
  have hcone : (coneComplex hpK).space = C :=
    coneComplex_space_eq_of_convex hC hball.isPolyhedron.isCompact (interior_subset hp) hpK hKspace
  obtain ⟨x, hx⟩ := hK.nonempty
  obtain ⟨s, hs, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htcard⟩ := exists_face_superset_card_eq_of_isPLSphere K hK hs
  let R := eraseTriangleComplex K t
  let _ : Finite R.faces := (eraseTriangleComplex_faces_finite K t).to_subtype
  have hR : IsPLBall 2 R.space := isPLBall_eraseTriangleComplex_of_isPLSphere_two K hK ht htcard
  let hpR := hpK.of_faces_subset (eraseTriangleComplex_faces_subset K t)
  have hRcone : IsPLBall 3 (coneComplex hpR).space := hpR.isPLBall_of_isPLBall hR
  let _ : Finite (coneComplex hpK).faces := (coneComplex_faces_finite hpK hKfin).to_subtype
  let _ : Finite (coneComplex hpR).faces :=
    (coneComplex_faces_finite hpR (eraseTriangleComplex_faces_finite K t)).to_subtype
  have hsub : (coneComplex hpR).faces ⊆ (coneComplex hpK).faces := by
    rintro u (hu | rfl | ⟨v, hv, rfl⟩)
    · exact Or.inl (eraseTriangleComplex_faces_subset K t hu)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨v, eraseTriangleComplex_faces_subset K t hv, rfl⟩)
  have htop : insert p t ∈ (coneComplex hpK).faces := Or.inr (Or.inr ⟨t, ht, rfl⟩)
  have htopcard : (insert p t).card = 4 := by
    rw [Finset.card_insert_of_notMem (hpK.notMem_face ht), htcard]
  have hdelete : ∀ u ∈ (coneComplex hpK).faces, u.card = 4 →
      (u ∈ (coneComplex hpR).faces ↔ u ≠ insert p t) := by
    intro u hu hucard
    simpa only [hu, true_and] using mem_coneComplex_eraseTriangleComplex_tetrahedron_iff K hpK
      (fun v hv => card_le_of_isPLSphere K hK hv) ht hucard
  have hpatch : frontier (coneComplex hpK).space ∩
      convexHull ℝ ((insert p t : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) =
        convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [hcone, ← hKspace]
    exact hpK.space_inter_convexHull_insert ht
  have hD : IsPLBall 2 (frontier (coneComplex hpK).space ∩
      convexHull ℝ ((insert p t : Finset _) : Set (EuclideanSpace ℝ (Fin 3)))) := by
    rw [hpatch]
    exact isPLBall_convexHull_of_affineIndependent t (K.indep ht) htcard
  have hsimple := isSimplyEmbedded_frontier_coneComplex R hpR hR
  refine ⟨hS, fun W hW hWo hSW => ?_⟩
  have hCW : C ⊆ W := DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_convex_open
    hball.isPolyhedron.isCompact hW hWo hSW
  have hconeW : (coneComplex hpK).space ⊆ W := hcone ▸ hCW
  have hRsub : (coneComplex hpR).space ⊆ (coneComplex hpK).space := space_mono_of_faces_subset hsub
  have hRfrontW : frontier (coneComplex hpR).space ⊆ W :=
    hRcone.isPolyhedron.isClosed.frontier_subset.trans (hRsub.trans hconeW)
  obtain ⟨g, hg, hgC, hgfix⟩ := exists_isPLHomeomorphOn_frontier_of_delete_free_tetrahedron
    (coneComplex hpK) (coneComplex hpR) (hcone.symm ▸ hball) hRcone hsub htop htopcard hdelete
    hD hWo (((coneComplex hpK).convexHull_subset_space htop).trans hconeW)
  obtain ⟨T, H, hT, hTcard, hH, hHC, hHfix⟩ := hsimple.2 W hW hWo hRfrontW
  refine ⟨T, g.trans H, hT, hTcard, hg.trans hH, ?_, ?_⟩
  · change (fun x => H (g x)) '' frontier C = _
    rw [← image_image H g, ← hcone, hgC]
    exact hHC
  · intro x hx
    change H (g x) = x
    rw [hgfix hx, id_eq]
    exact hHfix hx

end DifferentialGeometry.Topology.PiecewiseLinear
