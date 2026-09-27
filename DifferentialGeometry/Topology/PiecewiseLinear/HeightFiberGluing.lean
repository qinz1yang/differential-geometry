/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGluing
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleEdgeLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem subsingleton_convexHull_inter_fiber_of_card_le_two
    {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Finset E) (hs : s.card ≤ 2)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ (s : Set E)) (r : ℝ) :
    (convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}).Subsingleton := by
  classical
  by_cases htwo : s.card = 2
  · intro x hx y hy
    exact injOn_linearMap_convexHull_of_card_eq_two s htwo ℓ hinj hx.1 hy.1
      (hx.2.trans hy.2.symm)
  · have hone : s.card ≤ 1 := by omega
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · have heq : s = {v} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hv, fun w hw => (Finset.card_le_one.mp hone) w hw v hv⟩
      rw [heq, Finset.coe_singleton, convexHull_singleton]
      rintro x ⟨hx, -⟩ y ⟨hy, -⟩
      exact hx.trans hy.symm

theorem subsingleton_inter_face_height_fibers
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hsdim : s.card ≤ 3) (htdim : t.card ≤ 3)
    (hne : s ≠ t) (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) (r : ℝ) :
    ((convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}) ∩
      (convexHull ℝ (t : Set E) ∩ {x | ℓ x = r})).Subsingleton := by
  classical
  have hcard : (s ∩ t).card ≤ 2 := by
    by_contra! hbig
    have hsEq : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have htEq : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (hsEq.symm.trans htEq)
  have hverts : ((s ∩ t : Finset E) : Set E) ⊆ K.vertices := by
    intro v hv
    exact K.down_closed hs
      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hv).1) (Finset.singleton_nonempty v)
  have hthin := subsingleton_convexHull_inter_fiber_of_card_le_two (s ∩ t) hcard ℓ
    (hinj.mono hverts) r
  intro x hx y hy
  apply hthin
  · refine ⟨?_, hx.1.2⟩
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull hs ht ⟨hx.1.1, hx.2.1⟩
  · refine ⟨?_, hy.1.2⟩
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull hs ht ⟨hy.1.1, hy.2.1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_height_fiber_of_face_maps
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hdim : ∀ s ∈ K.faces, s.card ≤ 3) (ℓ : E →ₗ[ℝ] ℝ)
    (hinj : InjOn ℓ K.vertices) (r : ℝ) {S : Set E} {f : K.faces → E → E}
    (hf : ∀ s, IsPLHomeomorphOn (f s) (convexHull ℝ (s.val : Set E) ∩ S)
      (convexHull ℝ (s.val : Set E) ∩ {x | ℓ x = r}))
    (hcarrier : ∀ s t : K.faces, ∀ x ∈ convexHull ℝ (s.val : Set E) ∩ S,
      f s x ∈ convexHull ℝ (t.val : Set E) ↔ x ∈ convexHull ℝ (t.val : Set E)) :
    ∃ g : E → E, IsPLHomeomorphOn g (K.space ∩ S) (K.space ∩ {x | ℓ x = r}) ∧
      ∀ s, EqOn g (f s) (convexHull ℝ (s.val : Set E) ∩ S) := by
  have hQ : ∀ s : K.faces, IsPolyhedron (convexHull ℝ (s.val : Set E) ∩ {x | ℓ x = r}) := by
    intro s
    exact ((isHPolytope_convexHull_of_affineIndependent s.val (K.indep s.property)).inter_preimage
        (isHPolytope_singleton r) ℓ.toAffineMap).isPolyhedron
  have hP : ∀ s : K.faces, IsPolyhedron (convexHull ℝ (s.val : Set E) ∩ S) := by
    intro s
    have h := (hf s).isPolyhedron_preimage (hQ s) (Subset.refl _)
    have heq : (convexHull ℝ (s.val : Set E) ∩ S) ∩
        f s ⁻¹' (convexHull ℝ (s.val : Set E) ∩ {x | ℓ x = r}) =
        convexHull ℝ (s.val : Set E) ∩ S :=
      inter_eq_left.mpr (fun _ hx => (hf s).bijOn.mapsTo hx)
    rwa [heq] at h
  have hpair : Pairwise fun s t : K.faces =>
      ((convexHull ℝ (s.val : Set E) ∩ {x | ℓ x = r}) ∩
        (convexHull ℝ (t.val : Set E) ∩ {x | ℓ x = r})).Subsingleton := by
    intro s t hst
    exact subsingleton_inter_face_height_fibers K s.property t.property
      (hdim s.val s.property) (hdim t.val t.property) (fun h => hst (Subtype.ext h)) ℓ hinj r
  obtain ⟨g, hg, hgf⟩ := exists_isPLHomeomorphOn_iUnion_of_subsingleton_inter hP hf hpair (by
    intro s t x hx
    constructor
    · intro hfx
      exact ⟨(hcarrier s t x hx).mp hfx.1, hx.2⟩
    · intro hxt
      exact ⟨(hcarrier s t x hx).mpr hxt.1, ((hf s).bijOn.mapsTo hx).2⟩)
  have hcover : ∀ T : Set E,
      (⋃ s : K.faces, convexHull ℝ (s.val : Set E) ∩ T) = K.space ∩ T := by
    intro T
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hxs, hxT⟩ := mem_iUnion.mp hx
      exact ⟨K.convexHull_subset_space s.property hxs, hxT⟩
    · rintro x ⟨hxK, hxT⟩
      obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hxK
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, hxs, hxT⟩
  rw [hcover, hcover] at hg
  exact ⟨g, hg, hgf⟩

end DifferentialGeometry.Topology.PiecewiseLinear
