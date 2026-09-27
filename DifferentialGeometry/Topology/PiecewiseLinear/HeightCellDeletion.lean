/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSlabDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSectionDecomposition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem fiber_subcomplexGeneratedBy_eq_closure_sdiff
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hdim : Module.finrank ℝ E = 3) (hreg : closure (interior K.space) = K.space)
    {T : Finset E} (hT : T ∈ K.faces) (hTcard : T.card = 4)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) {r : ℝ} (havoid : ∀ v ∈ T, ℓ v ≠ r) :
    (subcomplexGeneratedBy K {s | ¬s ⊆ T}).space ∩ {x | ℓ x = r} =
      closure ((K.space ∩ {x | ℓ x = r}) \ (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r})) := by
  let R := subcomplexGeneratedBy K {s | ¬s ⊆ T}
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite K _).to_subtype
  have hRK : R.faces ⊆ K.faces := subcomplexGeneratedBy_faces_subset K _
  have hRspace : R.space = closure (K.space \ convexHull ℝ (T : Set E)) :=
    (closure_space_sdiff_convexHull_eq_subcomplexGeneratedBy K K Subset.rfl hT).symm
  have hRreg : closure (interior R.space) = R.space := by
    rw [hRspace]
    exact Topology.closure_interior_closure_sdiff hreg (T.finite_toSet.isCompact_convexHull
        ℝ).isClosed
  apply Subset.antisymm
  · rintro x ⟨hxR, hxr⟩
    by_cases hxT : x ∈ convexHull ℝ (T : Set E)
    · have hxnot : x ∉ K.vertices := by
        intro hxv
        exact havoid x (mem_of_mem_convexHull_of_singleton_mem K hxv hT hxT) hxr
      obtain ⟨U, hU, hUcard, hxU⟩ := exists_face_card_eq_finrank_succ_of_mem_closure R
        isOpen_interior interior_subset (hRreg.symm.subset hxR)
      have hUcard' : U.card = 4 := by simpa only [hdim] using hUcard
      have hUT : U ≠ T := by
        intro heq
        obtain ⟨V, ⟨hV, hVT⟩, hUV, -⟩ := hU
        have hVcard := card_le_finrank_succ_of_mem_faces K hV
        have hUVeq : U = V := Finset.eq_of_subset_of_card_le hUV (by omega)
        exact hVT (hUVeq.symm.trans heq).subset
      have hverts : (U : Set E) ⊆ K.vertices := fun v hv =>
        K.down_closed (hRK hU) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have hcross : (∃ v ∈ U, ℓ v < r) ∧ ∃ w ∈ U, r < ℓ w := by
        rcases convexHull_inter_fiber_eq_singleton_or_exists_lt_and_gt U (R.indep hU)
          ℓ (hinj.mono hverts) ⟨x, hxU, hxr⟩ with ⟨v, hv, heq⟩ | hcross
        · have hxv : x = v := heq.subset ⟨hxU, hxr⟩
          exact (hxnot (hxv.symm ▸ hverts hv)).elim
        · exact hcross
      let D := convexHull ℝ (U : Set E) ∩ {y | ℓ y = r}
      let C := convexHull ℝ (T : Set E) ∩ {y | ℓ y = r}
      have hD : IsPLBall 2 D := isPLBall_convexHull_inter_fiber_of_affineIndependent
        U (R.indep hU) hUcard' ℓ.toAffineMap hcross.1 hcross.2
      have hdiff : D \ (D ∩ C) = D \ C := by
        ext y
        simp only [mem_sdiff, mem_inter_iff]
        tauto
      have hdense : closure (D \ C) = D := by
        rcases isPLBall_zero_or_one_inter_face_fibers K (hRK hU) hT hUcard'.le hTcard.le hUT
          ℓ hinj r ⟨x, ⟨hxU, hxr⟩, hxT, hxr⟩ with hI | hI
        · change IsPLBall 0 (D ∩ C) at hI
          simpa only [hdiff] using hD.closure_sdiff_eq_of_isPLBall hI inter_subset_left (by decide)
        · change IsPLBall 1 (D ∩ C) at hI
          simpa only [hdiff] using hD.closure_sdiff_eq_of_isPLBall hI inter_subset_left (by decide)
      exact closure_mono (sdiff_subset_sdiff_left
        (inter_subset_inter_left _ (K.convexHull_subset_space (hRK hU)))) (hdense.symm.subset ⟨hxU,
            hxr⟩)
    · exact subset_closure ⟨⟨space_mono_of_faces_subset hRK hxR, hxr⟩, fun hx => hxT hx.1⟩
  · apply closure_minimal _ ((isPolyhedron_space R).isClosed.inter
      (isClosed_eq ℓ.continuous_of_finiteDimensional continuous_const))
    rintro x ⟨⟨hxK, hxr⟩, hxT⟩
    exact ⟨hRspace.symm.subset (subset_closure ⟨hxK, fun hx => hxT ⟨hx, hxr⟩⟩), hxr⟩

omit [FiniteDimensional ℝ E] in
open Classical in
theorem heightSectionCells_erase_subset_subcomplexGeneratedBy {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {T : Finset E}
    (hTcard : T.card = n + 2) (ℓ : E →ₗ[ℝ] ℝ) (r : ℝ) :
    (heightSectionCells n K ℓ r).erase (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) ⊆
      @heightSectionCells E _ _ n (subcomplexGeneratedBy K {s | ¬s ⊆ T})
        (subcomplexGeneratedBy_faces_finite K _).to_subtype ℓ r := by
  let _ : Finite (subcomplexGeneratedBy K {s | ¬s ⊆ T}).faces :=
    (subcomplexGeneratedBy_faces_finite K _).to_subtype
  intro C hC
  obtain ⟨hneq, hCmem⟩ := Finset.mem_erase.mp hC
  obtain ⟨U, hU, hUcard, hlow, hhigh, hCeq⟩ := mem_heightSectionCells_iff.mp hCmem
  apply mem_heightSectionCells_iff.mpr
  refine ⟨U, ⟨U, ⟨hU, ?_⟩, Finset.Subset.rfl, K.nonempty_of_mem_faces hU⟩, hUcard, hlow, hhigh,
      hCeq⟩
  intro hUT
  have heq : U = T := Finset.eq_of_subset_of_card_le hUT (by omega)
  exact hneq (hCeq.trans (congrArg (fun V : Finset E => convexHull ℝ (V : Set E) ∩ {x | ℓ x = r})
      heq))

end DifferentialGeometry.Topology.PiecewiseLinear
