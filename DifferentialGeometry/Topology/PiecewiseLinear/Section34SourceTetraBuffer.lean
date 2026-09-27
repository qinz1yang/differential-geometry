/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceFaceTorusModel

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

open Classical in
theorem isPLBall_section34SourceTetra_union_faceTorus_model
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4)
    (hst : Section34Incident s.1 t.1) :
    IsPLBall 3 (𝒦.complex.space ∩ 𝒦.map ⁻¹'
      (src (.tetraBall t) ∪ section34FaceTorus (fun w => src (.vertexBall w)) s)) := by
  classical
  obtain ⟨n, v, hv, hvinc, hC, hnext, hdis, htriple, hcover⟩ :=
    exists_section34SourceFaceTorus_cycle hcut s
  obtain ⟨-, -, -, hcell, -, -, -, -, hcoverU, -, -, hpatch, hedge, -, -, -, -, -, -, -, -,
    -, hends, -, -⟩ := id hcut
  choose a b hab he hsplit using hends
  let ends := fun e => (a e, b e)
  have hends' : ∀ e, (e.1 : Set Ea) =
      (((ends e).1).1 : Set Ea) ∪ (((ends e).2).1 : Set Ea) := he
  let R := 𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.tetraBall t)
  let C : Fin (n + 3) → Set Ea := fun i =>
    𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.vertexBall (v i))
  have hsrcU (l : Section34CutLabelOf 𝒦 𝒦') : src l ⊆ U := by
    rw [← hcoverU]
    exact subset_iUnion src l
  have hvt (i : Fin (n + 3)) : Section34Incident (v i).1 t.1 :=
    ((hvinc _).mpr ⟨i, rfl⟩).trans (convexHull_min hst (convex_convexHull ℝ _))
  have hR : IsPLBall 3 R := 𝒦.isPLBall_preimage_of_isPLCellOn
    (hcell (.tetraBall t)) (hsrcU (.tetraBall t))
  have hCR (i : Fin (n + 3)) : IsPLBall 2 (C i ∩ R) := by
    let p : Section34PatchIndex 𝒦 𝒦' := ⟨(t, v i), hvt i⟩
    have hP := 𝒦.isPLBall_preimage_of_isPLCellOn (hcell (.patch p)) (hsrcU (.patch p))
    have hPset : C i ∩ R = 𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.patch p) := by
      rw [hpatch p]
      ext x
      simp only [C, R, mem_inter_iff, mem_preimage, p]
      tauto
    exact hPset.symm ▸ hP
  have hCC (i j : Fin (n + 3)) (hne : i ≠ j) (hmeet : (C i ∩ C j).Nonempty) :
      IsPLBall 2 (C i ∩ C j) := by
    apply hnext i j
    by_contra hnot
    obtain ⟨x, hxi, hxj⟩ := hmeet
    exact disjoint_left.mp (hdis i j hne hnot) hxi hxj
  have hCRC (i j : Fin (n + 3)) (hne : i ≠ j) (hmeet : (C i ∩ C j).Nonempty) :
      IsPLBall 1 ((C i ∩ R) ∩ C j) := by
    obtain ⟨x, hxi, hxj⟩ := hmeet
    obtain ⟨e, heij, hend⟩ := exists_section34Edge_of_vertex_inter_nonempty hcut ends hends'
      (fun heq => hne (hv heq)) ⟨𝒦.map x, hxi.2, hxj.2⟩
    have het : Section34Incident e.1 t.1 := by
      change (e.1 : Set Ea) ⊆ convexHull ℝ (t.1 : Set Ea)
      rw [hends' e]
      rcases hend with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [← hi, ← hj]
        exact union_subset (hvt i) (hvt j)
      · rw [← hi, ← hj]
        exact union_subset (hvt j) (hvt i)
    let a : Section34EdgeArcIndex 𝒦 𝒦' := ⟨(t, e), het⟩
    have hA := 𝒦.isPLBall_preimage_of_isPLCellOn (hcell (.edgeArc a))
      (hsrcU (.edgeArc a))
    have hAset : (C i ∩ R) ∩ C j = 𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.edgeArc a) := by
      rw [hedge a, heij]
      ext y
      simp only [C, R, mem_inter_iff, mem_preimage, a]
      tauto
    exact hAset.symm ▸ hA
  have hball := 𝒦.isPLBall_union_iUnion_of_disk_intersections hR Finset.univ C
    inter_subset_left (fun i _ => hC i) (fun _ _ => inter_subset_left)
    (fun i _ => hCR i) (fun i _ j _ hne => hCC i j hne)
    (fun i _ j _ hne => hCRC i j hne)
    (fun i _ j _ k _ hij hik hjk => htriple i j k hij hik hjk)
  have hset : R ∪ ⋃ i ∈ (Finset.univ : Finset (Fin (n + 3))), C i =
      𝒦.complex.space ∩ 𝒦.map ⁻¹'
        (src (.tetraBall t) ∪ section34FaceTorus (fun w => src (.vertexBall w)) s) := by
    simp only [Finset.mem_univ, iUnion_true]
    rw [hcover]
    ext x
    simp only [R, mem_union, mem_inter_iff, mem_preimage]
    tauto
  exact hset ▸ hball

end DifferentialGeometry.Topology.PiecewiseLinear
