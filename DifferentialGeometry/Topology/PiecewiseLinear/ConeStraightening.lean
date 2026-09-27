/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SimplyEmbedded
import DifferentialGeometry.Analysis.Convex.CompactFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_straighten_cone_of_isGlueIso_planar
    [dE : DecidableEq (EuclideanSpace ℝ (Fin 3))] [dP : DecidableEq (EuclideanSpace ℝ (Fin 2))]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces] [Finite L.faces]
    {p : EuclideanSpace ℝ (Fin 3)} (hp : IsConeBase p K) (hL : IsPLBall 2 L.space)
    {φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)}
    {ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} (hIso : IsGlueIso K L φ ψ)
    {t₀ : Finset (EuclideanSpace ℝ (Fin 3))} (ht₀ : t₀ ∈ K.faces) (ht₀card : t₀.card = 3)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hKU : (coneComplex hp).space ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧ h '' frontier (coneComplex hp).space =
        frontier (convexHull ℝ ((insert p t₀ : Finset _) : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      EqOn h id Uᶜ := by
  cases Subsingleton.elim dE (Classical.decEq _)
  cases Subsingleton.elim dP (Classical.decEq _)
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  have hK : IsPLBall 2 K.space := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
  by_cases heq : K.space = convexHull ℝ (t₀ : Set (EuclideanSpace ℝ (Fin 3)))
  · have hspace : (coneComplex hp).space =
        convexHull ℝ ((insert p t₀ : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) := by
      ext x
      rw [mem_coneComplex_space_iff, heq]
      constructor
      · rintro (rfl | ⟨z, hz, r, hr, hr1, rfl⟩)
        · exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
        · exact mem_convexHull_insert_of_combo hz hr.le hr1
      · exact exists_combo_of_mem_convexHull_insert (hp.notMem_face ht₀)
    refine ⟨Homeomorph.refl _, ?_, ?_, fun _ _ => rfl⟩
    · exact ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
        (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx => (bijOn_id univ).invOn_invFunOn.1 hx⟩
    · change id '' frontier (coneComplex hp).space = _
      rw [image_id, hspace]
  · obtain ⟨t, s, ht, htcard, htt₀, hs, hst, hscard, htrace, -, hball⟩ :=
      exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar K L hIso hL ht₀ ht₀card heq
    have hsne : s ≠ t := by
      intro h
      have hc := congrArg Finset.card h
      omega
    have htU : convexHull ℝ ((insert p t : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) ⊆ U :=
      ((coneComplex hp).convexHull_subset_space (Or.inr (Or.inr ⟨t, ht, rfl⟩))).trans hKU
    obtain ⟨g, hg, hgK, hgfix⟩ := exists_isPLHomeomorphOn_frontier_coneComplex_eraseTriangleComplex
      K hp hK ht htcard (K.nonempty_of_mem_faces hs) hst hsne
      (by simpa only [Finset.coe_erase] using htrace) hball hU (by simpa only [Finset.coe_insert]
          using htU)
    let K' := eraseTriangleComplex K t
    let L' := eraseTriangleComplex L (t.image φ)
    let _ : Finite K'.faces := (eraseTriangleComplex_faces_finite K t).to_subtype
    let _ : Finite L'.faces := (eraseTriangleComplex_faces_finite L (t.image φ)).to_subtype
    let hp' := hp.of_faces_subset (eraseTriangleComplex_faces_subset K t)
    have hIso' : IsGlueIso K' L' φ ψ := hIso.eraseTriangleComplex ht
    have hL' : IsPLBall 2 L'.space := hball.of_isPLHomeomorphOn hIso'.isPLHomeomorphOn
    have ht₀' : t₀ ∈ K'.faces :=
      (mem_eraseTriangleComplex_triangle_iff K t
        (fun u hu => card_le_of_isPLBall K hK hu) ht₀card).mpr ⟨ht₀, htt₀.symm⟩
    have hK'U : (coneComplex hp').space ⊆ U := by
      intro x hx
      apply hKU
      rcases (mem_coneComplex_space_iff hp').mp hx with rfl | ⟨z, hz, r, hr, hr1, rfl⟩
      · exact apex_mem_coneComplex_space hp
      · exact (mem_coneComplex_space_iff hp).mpr (Or.inr ⟨z,
          space_mono_of_faces_subset (eraseTriangleComplex_faces_subset K t) hz, r, hr, hr1, rfl⟩)
    obtain ⟨H, hH, hHK, hHfix⟩ := exists_isPLHomeomorphOn_straighten_cone_of_isGlueIso_planar
      K' L' hp' hL' hIso' ht₀' ht₀card hU hK'U
    refine ⟨g.trans H, hg.trans hH, ?_, ?_⟩
    · change (fun x => H (g x)) '' frontier (coneComplex hp).space = _
      rw [← image_image H g, hgK]
      exact hHK
    · intro x hx
      change H (g x) = x
      rw [hgfix hx, id_eq]
      exact hHfix hx
termination_by {u ∈ K.faces | u.card = 3}.ncard
decreasing_by
  exact ncard_triangles_eraseTriangleComplex_lt K t ht htcard (fun u hu => card_le_of_isPLBall K hK
      hu)

theorem isSimplyEmbedded_frontier_coneComplex [dE : DecidableEq (EuclideanSpace ℝ (Fin 3))]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    {p : EuclideanSpace ℝ (Fin 3)} (hp : IsConeBase p K) (hK : IsPLBall 2 K.space) :
    IsSimplyEmbedded (frontier (coneComplex hp).space) := by
  classical
  cases Subsingleton.elim dE (Classical.decEq _)
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  have hC : IsPLBall 3 (coneComplex hp).space := hp.isPLBall_of_isPLBall hK
  refine ⟨hC.isPLSphere_frontier, fun W hW hWo hCW => ?_⟩
  have hCU : (coneComplex hp).space ⊆ W :=
    DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_convex_open
      hC.isPolyhedron.isCompact hW hWo hCW
  obtain ⟨A, L, φ, ψ, hA, hAfin, hLfin, hL, hIso⟩ := exists_isSubdivision_isGlueIso_planar K hK
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let hpA := hp.of_isSubdivision hA
  have hAC : (coneComplex hpA).space = (coneComplex hp).space := (coneComplex_isSubdivision hp
      hA).space_eq
  have hAball : IsPLBall 2 A.space := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
  obtain ⟨x, hx⟩ := hAball.nonempty
  obtain ⟨s, hs, -⟩ := A.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htcard⟩ := exists_face_superset_card_eq_of_isPLBall A hAball hs
  obtain ⟨h, hh, himage, hfix⟩ := exists_isPLHomeomorphOn_straighten_cone_of_isGlueIso_planar
    A L hpA hL hIso ht htcard hWo (fun x hx => hCU (hAC ▸ hx))
  refine ⟨insert p t, h, ?_, ?_, hh, ?_, hfix⟩
  · have h := hpA.indep t ht
    rwa [← Finset.coe_insert] at h
  · rw [Finset.card_insert_of_notMem (hpA.notMem_face ht), htcard]
  · rwa [hAC] at himage

end DifferentialGeometry.Topology.PiecewiseLinear
