/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallImageComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTetraBuffer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem compactExterior_of_ballBuffers
    (K : Geometry.SimplicialComplex ℝ E3) {V : Set E3} (hV : IsOpen V)
    {h : E3 → E3} (hh : ContinuousOn h V) (hinj : InjOn h V) (hKV : K.space ⊆ V)
    (tgtV : Section34CompactVertexIndex K K → Set E3)
    (B : Section34CompactSimplexIndex K 4 → Set E3)
    (hB : ∀ t, IsPLBall 3 (B t)) (hBV : ∀ t, B t ⊆ V)
    (htB : ∀ t, convexHull ℝ (t.1 : Set E3) ⊆ B t)
    (hBF : ∀ t, Disjoint (B t) (K.vertices \ (t.1 : Set E3)))
    (hwB : ∀ t w, Section34Incident w.1 t.1 → tgtV w ⊆ h '' B t) :
    Section34CompactExterior K K h tgtV (fun s => h '' convexHull ℝ (s.1 : Set E3)) := by
  intro t w hwt y hy
  have hobs : section34CompactTetraObstacle tgtV
      (fun s => h '' convexHull ℝ (s.1 : Set E3)) t ⊆ h '' B t := by
    apply union_subset
    · refine iUnion₂_subset fun p hp => ?_
      exact hwB t p.1.2 (hp ▸ p.2)
    · refine iUnion₂_subset fun s hs => image_mono ?_
      exact (convexHull_min hs (convex_convexHull ℝ _)).trans (htB t)
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
  have hvK : v ∈ K.vertices := by
    change {v} ∈ K.faces
    rw [← hv]
    exact w.2.1
  have hvV : v ∈ V := hKV (K.convexHull_subset_space w.2.1
    (subset_convexHull ℝ _ (by rw [hv]; simp)))
  have hvt : v ∉ t.1 := by
    intro hvt
    apply hwt
    change (w.1 : Set E3) ⊆ convexHull ℝ (t.1 : Set E3)
    rw [hv, Finset.coe_singleton, singleton_subset_iff]
    exact subset_convexHull ℝ _ hvt
  have hyv : y = h v := by
    simpa only [hv, Finset.coe_singleton, image_singleton, mem_singleton_iff] using hy
  have hyB : y ∉ h '' B t := by
    rintro ⟨x, hx, hxy⟩
    have hxv : x = v := hinj (hBV t hx) hvV (hxy.trans hyv)
    exact Set.disjoint_left.mp (hBF t) (hxv ▸ hx) ⟨hvK, hvt⟩
  exact (hB t).not_isBounded_connectedComponentIn_compl_of_subset_image
    hV hh hinj (hBV t) hobs hyB

open Classical in
theorem exists_compactExteriorNeighborhoods
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hKint : K.space ⊆ interior M.space) {V : Set E3} (hV : IsOpen V)
    (hMV : M.space ⊆ V) {h : E3 → E3} (hh : ContinuousOn h V) (hinj : InjOn h V) :
    let L := restrict K (section34CompactGraphSkeleton K)
    ∃ W : E3 → Set E3, (∀ v, IsOpen (W v)) ∧
      (∀ v ∈ K.vertices, h '' (graphDualCell M L v).space ⊆ W v) ∧
      ∀ f : E3 → E3, (∀ v ∈ K.vertices, f '' (graphDualCell M L v).space ⊆ W v) →
        Section34CompactExterior K K h
          (section34CompactVertexBallImage (compactDualCutCell M K hKM) f)
          (fun s => h '' convexHull ℝ (s.1 : Set E3)) := by
  let : DecidableEq E3 := Classical.decEq E3
  dsimp only
  let L := restrict K (section34CompactGraphSkeleton K)
  let _ : Finite (Section34CompactSimplexIndex K 4) :=
    finite_section34CompactSimplexIndex ((Set.toFinite M.faces).subset hKM) 4
  choose B hB hBM hAB hBF using
    fun t => exists_compactTetraExteriorBuffer M K hM hKM hKint t
  have hBV (t : Section34CompactSimplexIndex K 4) : B t ⊆ V :=
    (hBM t).trans (interior_subset.trans hMV)
  let W (v : E3) := ⋂ (t : Section34CompactSimplexIndex K 4) (_ : v ∈ t.1),
    interior (h '' B t)
  refine ⟨W, fun v => isOpen_iInter_of_finite fun t =>
    isOpen_iInter_of_finite fun _ => isOpen_interior, ?_, ?_⟩
  · intro v _
    refine subset_iInter fun t => subset_iInter fun hvt => ?_
    rw [interior_image_eq_image_interior hV hh hinj (hBV t)]
    exact image_mono (fun x hx => hAB t (Or.inr (mem_iUnion₂.mpr ⟨v, hvt, hx⟩)))
  · intro f hf
    apply compactExterior_of_ballBuffers K hV hh hinj
      ((space_mono_of_faces_subset hKM).trans hMV) _ B hB hBV
    · intro t
      exact fun x hx => interior_subset (hAB t (Or.inl hx))
    · exact hBF
    · intro t w hwt
      let v := w.1.centroid ℝ id
      have hvK : v ∈ K.vertices := centroid_mem_vertices_compactVertexIndex w
      have hvw : v ∈ w.1 := by
        rw [← singleton_centroid_eq_compactVertexIndex w]
        exact Finset.mem_singleton_self _
      have hvt : v ∈ t.1 :=
        mem_of_mem_convexHull_of_singleton_mem K hvK t.2.1 (hwt hvw)
      change f '' (graphDualCell M L v).space ⊆ h '' B t
      exact (hf v hvK).trans ((iInter_subset_of_subset t
        (iInter_subset_of_subset hvt subset_rfl)).trans interior_subset)

end DifferentialGeometry.Topology.PiecewiseLinear
