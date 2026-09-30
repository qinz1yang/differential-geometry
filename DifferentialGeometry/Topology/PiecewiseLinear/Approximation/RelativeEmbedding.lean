import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.EnclosingSimplex

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry
open scoped _root_.Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_finite_convex_complex_containing_bounded
    (S : SimplicialComplex ℝ F) (hS : S.faces.Finite) (B : Set F)
    (hB : Bornology.IsBounded B) :
    ∃ K J : SimplicialComplex ℝ F,
      K.faces.Finite ∧ Convex ℝ K.space ∧ S.space ∪ B ⊆ interior K.space ∧
      J.faces.Finite ∧ J.faces ⊆ K.faces ∧ J.space = S.space ∧ simplicialRefines J S := by
  classical
  have hcompact : IsCompact S.space :=
    hS.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  obtain ⟨b, hb⟩ := exists_bounded_subset_interior_simplex (hcompact.isBounded.union hB)
  let K₀ : SimplicialComplex ℝ F := barycentricComplex b b.ind
  have hK₀ : K₀.faces.Finite := barycentricComplex_finite_faces b b.ind
  have hspace₀ : K₀.space = convexHull ℝ (range b) := barycentricComplex_space_eq b b.ind
  have hdim₀ : ∀ s ∈ K₀.faces, s.card ≤ Module.finrank ℝ F + 1 := by
    intro s hs
    simpa only [Fintype.card_coe] using (K₀.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hSK : S.space ⊆ K₀.space := by
    rw [hspace₀]
    exact (subset_union_left.trans hb).trans interior_subset
  obtain ⟨K, J, hK, hspace, -, -, hJ, hJK, hJspace, hJref⟩ :=
    exists_subdivision_containing_complex K₀ S hK₀ hS hSK hdim₀
  refine ⟨K, J, hK, ?_, ?_, hJ, hJK, hJspace, hJref⟩
  · rw [hspace, hspace₀]
    exact convex_convexHull ℝ _
  · rwa [hspace, hspace₀]

theorem exists_embedding_perturbation_constant
    (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : InjOn f K.space)
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite) (hconv : Convex ℝ T.space)
    (J : SimplicialComplex ℝ F) (hJT : J.faces ⊆ T.faces)
    (hJspace : J.space = f '' K.space)
    (hJref : ∀ t ∈ J.faces, ∃ s ∈ K.faces,
      convexHull ℝ (t : Set F) ⊆ f '' convexHull ℝ (s : Set E))
    (hinterior : f '' K.space ⊆ interior T.space) :
    ∃ C : ℝ≥0, ∀ δ : ℝ≥0, δ * C < 1 → ∀ u : E → F,
      (∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn u A (convexHull ℝ (s : Set E))) →
      (∀ x ∈ K.space, ‖u x - f x‖ ≤ δ) →
      ∃ (H : F ≃ₜ F) (W : F → F),
        (∀ x ∈ K.space, H (f x) = u x) ∧
        (∀ x : T.space, H x = interpolateVertices T hT W x) ∧
        (∀ x ∉ interior T.space, H x = x) ∧ H '' T.space = T.space ∧
        (∀ x, ‖H x - x‖ ≤ δ) ∧ (∀ x, ‖H.symm x - x‖ ≤ δ) := by
  classical
  obtain ⟨C, hC⟩ := exists_vertex_perturbation_constant T hT hconv
  refine ⟨C, fun δ hδ u hu hnear => ?_⟩
  let r : F → E := fun y => if hy : y ∈ f '' K.space then hy.choose else 0
  have hr (x : E) (hx : x ∈ K.space) : r (f x) = x := by
    have hfx : f x ∈ f '' K.space := mem_image_of_mem f hx
    change (if hy : f x ∈ f '' K.space then hy.choose else 0) = x
    rw [dite_eq_left hfx]
    exact hinj hfx.choose_spec.1 hx hfx.choose_spec.2
  let W : F → F := fun y => if y ∈ f '' K.space then u (r y) else y
  have hW (x : E) (hx : x ∈ K.space) : W (f x) = u x := by
    simp only [W, ite_eq_left (mem_image_of_mem f hx), hr x hx]
  have hWnorm (y : F) : ‖W y - y‖ ≤ δ := by
    by_cases hy : y ∈ f '' K.space
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [hW x hx]
      exact hnear x hx
    · simp only [W, ite_eq_right hy, sub_self, norm_zero]
      exact δ.coe_nonneg
  have hWfixed (y : F) (_hy : y ∈ T.vertices) (hyf : y ∈ frontier T.space) : W y = y := by
    apply ite_eq_right
    exact fun hy => hyf.2 (hinterior hy)
  have hWaff (t : Finset F) (ht : t ∈ J.faces) :
      ∃ A : F →ᵃ[ℝ] F, EqOn W A (convexHull ℝ (t : Set F)) := by
    obtain ⟨s, hs, hts⟩ := hJref t ht
    obtain ⟨A, hA⟩ := hf s hs
    obtain ⟨B, hB⟩ := hu s hs
    have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
      intro x hx y hy hxy
      exact hinj (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
        ((hA hx).trans (hxy.trans (hA hy).symm))
    obtain ⟨D, hDA, -⟩ := exists_affine_inverse_on_affineSpan (K.nonempty_of_mem_faces hs) A
      (affineIndependent_of_injOn_convexHull (K.indep hs) A hAi)
    refine ⟨B.comp D, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hts hy
    change W (f x) = B (D (f x))
    rw [hW x (K.convexHull_subset_space hs hx), hB hx, hA hx,
      hDA x (convexHull_subset_affineSpan _ hx)]
  obtain ⟨H, hH, hHfix, hHspace, hHnorm, hHinv⟩ := hC δ hδ W
    (fun y _ => hWnorm y) hWfixed
  refine ⟨H, W, ?_, hH, hHfix, hHspace, hHnorm, hHinv⟩
  intro x hx
  have hxJ : f x ∈ J.space := hJspace.symm ▸ mem_image_of_mem f hx
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxJ
  obtain ⟨A, hA⟩ := hWaff t ht
  have hxT := T.convexHull_subset_space (hJT ht) hxt
  calc
    H (f x) = interpolateVertices T hT W ⟨f x, hxT⟩ := hH ⟨f x, hxT⟩
    _ = A (f x) := interpolateVertices_eq_affineMap T hT W ⟨t, hJT ht⟩ A
      (fun a ha => (hA (subset_convexHull ℝ _ ha)).symm) _ hxt
    _ = u x := (hA hxt).symm.trans (hW x hx)

end DifferentialGeometry.Topology.Engulfing
