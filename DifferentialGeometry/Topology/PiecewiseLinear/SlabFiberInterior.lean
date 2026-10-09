/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSlabInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem interior_convexHull_inter_slab_nonempty_of_lt_of_lt
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = Module.finrank ℝ E + 1) (ℓ : E →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (hbelow : ∃ x ∈ convexHull ℝ (T : Set E), ℓ x < b)
    (habove : ∃ x ∈ convexHull ℝ (T : Set E), a < ℓ x) :
    (interior (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' Icc a b)).Nonempty := by
  have hinter : (interior (convexHull ℝ (T : Set E))).Nonempty := by
    rw [interior_convexHull_eq_openSimplex hT hcard]
    exact ⟨T.centroid ℝ id, centroid_mem_openSimplex (Finset.card_pos.mp (by omega))⟩
  obtain ⟨x, hx, hxab⟩ := Topology.exists_mem_interior_preimage_Ioo_of_convex
    (convex_convexHull ℝ (T : Set E)) hinter ℓ.continuous_of_finiteDimensional hab hbelow habove
  refine ⟨x, ?_⟩
  rw [interior_inter]
  exact ⟨hx, interior_maximal (preimage_mono Ioo_subset_Icc_self)
    (isOpen_Ioo.preimage ℓ.continuous_of_finiteDimensional) hxab⟩

theorem closure_interior_space_inter_slab_of_isPLBall_fiber {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hreg : closure (interior K.space) = K.space) (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices)
    {p : E} {a b : ℝ} (hab : a < b) (hpheight : ℓ p ∈ Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    (hD : IsPLBall (n + 1) (K.space ∩ {x | ℓ x = ℓ p})) :
    closure (interior (K.space ∩ ℓ ⁻¹' Icc a b)) = K.space ∩ ℓ ⁻¹' Icc a b := by
  let Z := closure (interior (K.space ∩ ℓ ⁻¹' Icc a b))
  have hclosed : IsClosed (K.space ∩ ℓ ⁻¹' Icc a b) :=
    (isPolyhedron_space K).isClosed.inter (isClosed_Icc.preimage ℓ.continuous_of_finiteDimensional)
  have hnonvertex : (K.space ∩ ℓ ⁻¹' Icc a b) \ K.vertices ⊆ Z := by
    rintro x ⟨⟨hxK, hxab⟩, hxnot⟩
    obtain ⟨T, hT, hcard, hxT⟩ := exists_face_card_eq_finrank_succ_of_mem_closure K
      isOpen_interior interior_subset (hreg.symm.subset hxK)
    have hverts : (T : Set E) ⊆ K.vertices := fun v hv =>
      K.down_closed hT (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hcross : (∃ v ∈ T, ℓ v < ℓ x) ∧ ∃ w ∈ T, ℓ x < ℓ w := by
      rcases convexHull_inter_fiber_eq_singleton_or_exists_lt_and_gt T (K.indep hT)
        ℓ (hinj.mono hverts) ⟨x, hxT, rfl⟩ with ⟨v, hv, heq⟩ | hcross
      · have hxv : x = v := heq.subset ⟨hxT, rfl⟩
        exact (hxnot (hxv.symm ▸ hverts hv)).elim
      · exact hcross
    have hlow : ∃ v ∈ convexHull ℝ (T : Set E), ℓ v < b := by
      obtain ⟨v, hv, hvx⟩ := hcross.1
      exact ⟨v, subset_convexHull ℝ _ hv, hvx.trans_le hxab.2⟩
    have hhigh : ∃ v ∈ convexHull ℝ (T : Set E), a < ℓ v := by
      obtain ⟨v, hv, hxv⟩ := hcross.2
      exact ⟨v, subset_convexHull ℝ _ hv, hxab.1.trans_lt hxv⟩
    have hpoly : IsHPolytope (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' Icc a b) :=
      (isHPolytope_convexHull_of_affineIndependent T (K.indep hT)).inter_preimage isHPolytope_Icc
          ℓ.toAffineMap
    have hTreg := (hpoly.convex.closure_interior_eq_closure_of_nonempty_interior
      (interior_convexHull_inter_slab_nonempty_of_lt_of_lt T (K.indep hT) hcard ℓ.toAffineMap hab
          hlow hhigh)).trans
      hpoly.isClosed.closure_eq
    exact closure_mono (interior_mono (inter_subset_inter_left _ (K.convexHull_subset_space hT)))
      (hTreg.symm.subset ⟨hxT, hxab⟩)
  have hvertsFin : K.vertices.Finite :=
    (Set.toFinite K.faces).preimage Finset.singleton_injective.injOn
  have hDZ : K.space ∩ {x | ℓ x = ℓ p} ⊆ Z := by
    rw [← hD.closure_sdiff_of_finite hvertsFin]
    apply closure_minimal _ isClosed_closure
    rintro x ⟨⟨hxK, hxp⟩, hxnot⟩
    exact hnonvertex ⟨⟨hxK, by change a ≤ ℓ x ∧ ℓ x ≤ b; rw [hxp]; exact hpheight⟩, hxnot⟩
  apply Subset.antisymm (closure_minimal interior_subset hclosed)
  rintro x ⟨hxK, hxab⟩
  by_cases hxv : x ∈ K.vertices
  · have hxp : x = p := by
      by_contra hne
      rcases hgap x hxv hne with hlow | hhigh
      · exact hlow.not_ge hxab.1
      · exact hhigh.not_ge hxab.2
    exact hDZ ⟨hxK, congrArg ℓ hxp⟩
  · exact hnonvertex ⟨⟨hxK, hxab⟩, hxv⟩

end DifferentialGeometry.Topology.PiecewiseLinear
