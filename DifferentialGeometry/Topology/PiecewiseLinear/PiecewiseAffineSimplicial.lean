/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Star

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPiecewiseAffineOn.exists_isSubdivision_affineOn_faces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {f : E → F}
    (hf : IsPiecewiseAffineOn f K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
  classical
  choose! ι hι C A hCA hnhds using hf
  choose! u hu using fun x (hx : x ∈ K.space) => mem_nhdsWithin.mp (hnhds x hx)
  have hcomp : IsCompact K.space := (isPolyhedron_space K).isCompact
  obtain ⟨t, ht, hcover⟩ := hcomp.elim_nhds_subcover u
    fun x hx => (hu x hx).1.mem_nhds (hu x hx).2.1
  have hfin : ∀ x : t, Finite (ι x) := fun x => hι x (ht x x.2)
  let Q : (Σ x : t, ι x) → Set E := fun p => C p.1 p.2
  have hQ : ∀ p, IsPolyhedron (Q p) := fun p => (hCA p.1 (ht p.1 p.1.2) p.2).1.isPolyhedron
  have hQK : ∀ p, Q p ⊆ K.space := fun p => (hCA p.1 (ht p.1 p.1.2) p.2).2.1
  obtain ⟨K', hK', hfin', hunion⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  refine ⟨K', hK', hfin', fun s hs => ?_⟩
  have hx₀ : s.centroid ℝ id ∈ openSimplex s :=
    centroid_mem_openSimplex (K'.nonempty_of_mem_faces hs)
  have hx₀K : s.centroid ℝ id ∈ K.space :=
    hK'.space_eq ▸ K'.convexHull_subset_space hs (openSimplex_subset_convexHull s hx₀)
  obtain ⟨x, hxt, hx₀u⟩ := mem_iUnion₂.mp (hcover hx₀K)
  have hxK : x ∈ K.space := ht x hxt
  obtain ⟨i, hx₀i⟩ := mem_iUnion.mp ((hu x hxK).2.2 ⟨hx₀u, hx₀K⟩)
  have hx₀Q : s.centroid ℝ id ∈ Q ⟨⟨x, hxt⟩, i⟩ := hx₀i
  rw [hunion ⟨⟨x, hxt⟩, i⟩] at hx₀Q
  obtain ⟨s', ⟨hs', hs'Q⟩, hx₀s'⟩ := mem_iUnion₂.mp hx₀Q
  have hss' : s ⊆ s' := face_subset_of_mem_openSimplex_of_mem_convexHull K' hs hs' hx₀ hx₀s'
  refine ⟨A x i, fun y hy => (hCA x hxK i).2.2 ?_⟩
  exact hs'Q (convexHull_mono (Finset.coe_subset.mpr hss') hy)

open Classical in
theorem exists_isSubdivision_affineOn_faces_finset
    {ι : Type*} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (I : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ I, IsPiecewiseAffineOn (f i) K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ i ∈ I, ∀ s ∈ K'.faces,
        ∃ A : E →ᵃ[ℝ] F, EqOn (f i) A (convexHull ℝ (s : Set E)) := by
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨K, IsSubdivision.refl K, Set.toFinite K.faces, ?_⟩
      simp
  | @insert i I hi ih =>
      have hfI : ∀ j ∈ I, IsPiecewiseAffineOn (f j) K.space :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      obtain ⟨K₁, hK₁, hfin₁, hface₁⟩ := ih hfI
      let _ : Finite K₁.faces := hfin₁.to_subtype
      have hfi : IsPiecewiseAffineOn (f i) K₁.space := by
        rw [hK₁.space_eq]
        exact hf i (Finset.mem_insert_self i I)
      obtain ⟨K₂, hK₂, hfin₂, hface₂⟩ :=
        hfi.exists_isSubdivision_affineOn_faces K₁
      refine ⟨K₂, hK₂.trans hK₁, hfin₂, ?_⟩
      intro j hj s hs
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hface₂ s hs
      · obtain ⟨t, ht, hst⟩ := hK₂.exists_face_subset hs
        obtain ⟨A, hA⟩ := hface₁ j hj t ht
        exact ⟨A, hA.mono hst⟩

open Classical in
theorem exists_isSubdivision_affineOn_faces_finite
    {ι : Type*} [Finite ι] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (f : ι → E → F) (hf : ∀ i, IsPiecewiseAffineOn (f i) K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ i, ∀ s ∈ K'.faces,
        ∃ A : E →ᵃ[ℝ] F, EqOn (f i) A (convexHull ℝ (s : Set E)) := by
  let _ := Fintype.ofFinite ι
  obtain ⟨K', hK', hfin, hface⟩ :=
    exists_isSubdivision_affineOn_faces_finset K Finset.univ f (fun i _ => hf i)
  exact ⟨K', hK', hfin, fun i => hface i (Finset.mem_univ i)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
