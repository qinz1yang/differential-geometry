/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFaceStability
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiberGluing
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldFaces

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eventually_exists_isPLHomeomorphOn_height_fiber_preserving_faces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (ℓ : E →L[ℝ] ℝ)
    (hheight : ∀ x, ℓ (H x) = ℓ x) (hinj : InjOn ℓ K.vertices) {p : E}
    (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ g : E → E,
      IsPLHomeomorphOn g (K.space ∩ {x | f (H x) = f (H p)})
        (K.space ∩ {x | ℓ x = ℓ p}) ∧
      ∀ s ∈ K.faces, ∀ x ∈ K.space ∩ {x | f (H x) = f (H p)},
        g x ∈ convexHull ℝ (s : Set E) ↔ x ∈ convexHull ℝ (s : Set E) := by
  classical
  let ι := {s : K.faces // s.val.card = 3}
  have hvertices : ∀ s ∈ K.faces, (s : Set E) ⊆ K.vertices := by
    intro s hs v hv
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hlocal : ∀ s : ι, ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ g : E → E,
      IsPLHomeomorphOn g
        (convexHull ℝ (s.val.val : Set E) ∩ {x | f (H x) = f (H p)})
        (convexHull ℝ (s.val.val : Set E) ∩ {x | ℓ x = ℓ p}) ∧
      ∀ t ⊆ s.val.val,
        ∀ x ∈ convexHull ℝ (s.val.val : Set E) ∩ {x | f (H x) = f (H p)},
          g x ∈ convexHull ℝ (t : Set E) ↔ x ∈ convexHull ℝ (t : Set E) := by
    intro s
    exact eventually_exists_isPLHomeomorphOn_face_fiber_preserving_subfaces
      (K.indep s.val.property) s.property H hH ℓ hheight
      (hinj.mono (hvertices _ s.val.property))
      (fun v hv => hunique v (hvertices _ s.val.property hv))
  filter_upwards [Filter.eventually_all.mpr hlocal] with f hf
  choose g hg hsub using hf
  let P : ι → Set E := fun s =>
    convexHull ℝ (s.val.val : Set E) ∩ {x | f (H x) = f (H p)}
  let Q : ι → Set E := fun s =>
    convexHull ℝ (s.val.val : Set E) ∩ {x | ℓ x = ℓ p}
  have hcarrier : ∀ s : ι, ∀ t ∈ K.faces, ∀ x ∈ P s,
      g s x ∈ convexHull ℝ (t : Set E) ↔ x ∈ convexHull ℝ (t : Set E) := by
    intro s t ht x hx
    have hgx := (hg s).bijOn.mapsTo hx
    have hsub' := hsub s (s.val.val ∩ t) Finset.inter_subset_left x hx
    constructor
    · intro hgt
      have hgi : g s x ∈ convexHull ℝ ((s.val.val ∩ t : Finset E) : Set E) := by
        simpa only [Finset.coe_inter] using
          K.inter_subset_convexHull s.val.property ht ⟨hgx.1, hgt⟩
      exact convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right) (hsub'.mp hgi)
    · intro hxt
      have hxi : x ∈ convexHull ℝ ((s.val.val ∩ t : Finset E) : Set E) := by
        simpa only [Finset.coe_inter] using
          K.inter_subset_convexHull s.val.property ht ⟨hx.1, hxt⟩
      exact convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right) (hsub'.mpr hxi)
  have hP : ∀ s, IsPolyhedron (P s) := by
    intro s
    have hQ : IsPolyhedron (Q s) :=
      ((isHPolytope_convexHull_of_affineIndependent s.val.val (K.indep
          s.val.property)).inter_preimage
        (isHPolytope_singleton (ℓ p)) ℓ.toLinearMap.toAffineMap).isPolyhedron
    have hpoly := (hg s).isPolyhedron_preimage hQ (Subset.refl _)
    have heq : P s ∩ g s ⁻¹' Q s = P s := inter_eq_left.mpr (hg s).bijOn.mapsTo
    rwa [heq] at hpoly
  have hpair : Pairwise fun s t : ι => (Q s ∩ Q t).Subsingleton := by
    intro s t hne
    apply subsingleton_inter_face_height_fibers K s.val.property t.val.property
      (by omega) (by omega) ?_ ℓ.toLinearMap hinj (ℓ p)
    intro hst
    exact hne (Subtype.ext (Subtype.ext hst))
  obtain ⟨g', hg', hgg⟩ := exists_isPLHomeomorphOn_iUnion_of_subsingleton_inter hP hg hpair (by
    intro s t x hx
    constructor
    · intro hxt
      exact ⟨(hcarrier s t.val.val t.val.property x hx).mp hxt.1, hx.2⟩
    · intro hxt
      exact ⟨(hcarrier s t.val.val t.val.property x hx).mpr hxt.1,
        ((hg s).bijOn.mapsTo hx).2⟩)
  have hcover : ∀ S : Set E,
      (⋃ s : ι, convexHull ℝ (s.val.val : Set E) ∩ S) = K.space ∩ S := by
    intro S
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hxs, hxS⟩ := mem_iUnion.mp hx
      exact ⟨K.convexHull_subset_space s.val.property hxs, hxS⟩
    · rintro x ⟨hxK, hxS⟩
      obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hxK
      obtain ⟨t, ht, hst, hcard⟩ := hpure s hs
      exact mem_iUnion.mpr ⟨⟨⟨t, ht⟩, hcard⟩,
        convexHull_mono (Finset.coe_subset.mpr hst) hxs, hxS⟩
  refine ⟨g', ?_, ?_⟩
  · simpa only [P, Q, hcover] using hg'
  · intro t ht x hx
    obtain ⟨s, hxs⟩ := mem_iUnion.mp ((hcover {x | f (H x) = f (H p)}).symm.subset hx)
    rw [hgg s hxs]
    exact hcarrier s t ht x hxs

theorem IsCombinatorialManifoldWithBoundary.eventually_exists_isPLHomeomorphOn_height_fiber
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (ℓ : E →L[ℝ] ℝ)
    (hheight : ∀ x, ℓ (H x) = ℓ x) (hinj : InjOn ℓ K.vertices) {p : E}
    (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ g : E → E,
      IsPLHomeomorphOn g (K.space ∩ {x | f (H x) = f (H p)})
        (K.space ∩ {x | ℓ x = ℓ p}) ∧
      ∀ s ∈ K.faces, ∀ x ∈ K.space ∩ {x | f (H x) = f (H p)},
        g x ∈ convexHull ℝ (s : Set E) ↔ x ∈ convexHull ℝ (s : Set E) :=
  eventually_exists_isPLHomeomorphOn_height_fiber_preserving_faces K
    (fun _ hs => hK.exists_face_superset_card_eq hs) H hH ℓ hheight hinj hunique

end DifferentialGeometry.Topology.PiecewiseLinear
