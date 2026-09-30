import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanMembraneIteration

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M]

def transportSourceMap {K P : SimplicialComplex ℝ E} (hspace : P.space = K.space)
    (f : C(P.space, M)) : C(K.space, M) :=
  f.comp ⟨(Homeomorph.setCongr hspace).symm, (Homeomorph.setCongr hspace).symm.continuous⟩

omit [DecidableEq E] in
@[simp] theorem transportSourceMap_setCongr {K P : SimplicialComplex ℝ E}
    (hspace : P.space = K.space) (f : C(P.space, M)) (x : P.space) :
    transportSourceMap hspace f (Homeomorph.setCongr hspace x) = f x := by
  classical
  simp only [transportSourceMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Homeomorph.symm_apply_apply]

omit [DecidableEq E] in
theorem transportSourceMap_image {K P : SimplicialComplex ℝ E}
    (hspace : P.space = K.space) (f : C(P.space, M)) (A : Set E) :
    transportSourceMap hspace f '' (Subtype.val ⁻¹' A) = f '' (Subtype.val ⁻¹' A) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(Homeomorph.setCongr hspace).symm x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Homeomorph.setCongr hspace x, hx, transportSourceMap_setCongr hspace f x⟩

omit [DecidableEq E] in
theorem exists_map_on_equal_space_of_target_subset
    (K L P J : SimplicialComplex ℝ E) (hspace : P.space = K.space)
    (hJspace : J.space = L.space) (g : C(K.space, M)) (f : C(P.space, M))
    {ε : ℝ} {A B : Set E} {X Y : Set M} (hAB : A ⊆ B)
    (hfix : ∀ x : P.space, x.val ∈ J.space → f x = g (Homeomorph.setCongr hspace x))
    (hnear : ∀ x : P.space, dist (f x) (g (Homeomorph.setCongr hspace x)) < ε)
    (hcover : X ∪ f '' (Subtype.val ⁻¹' B) ⊆ Y) :
    ∃ g' : C(K.space, M),
      (∀ x : K.space, x.val ∈ L.space → g' x = g x) ∧
      (∀ x, dist (g' x) (g x) < ε) ∧
      X ∪ g' '' (Subtype.val ⁻¹' A) ⊆ Y ∧
      (∀ x : P.space, g' (Homeomorph.setCongr hspace x) = f x) := by
  classical
  refine ⟨transportSourceMap hspace f, ?_, ?_, ?_, transportSourceMap_setCongr hspace f⟩
  · intro x hx
    have hxJ : ((Homeomorph.setCongr hspace).symm x).val ∈ J.space := by
      rw [hJspace]
      exact hx
    change f ((Homeomorph.setCongr hspace).symm x) = g x
    simpa only [Homeomorph.apply_symm_apply] using hfix ((Homeomorph.setCongr hspace).symm x) hxJ
  · intro x
    change dist (f ((Homeomorph.setCongr hspace).symm x)) (g x) < ε
    simpa only [Homeomorph.apply_symm_apply] using hnear ((Homeomorph.setCongr hspace).symm x)
  · rw [transportSourceMap_image]
    exact (union_subset_union_right X (image_mono (preimage_mono hAB))).trans hcover

omit [DecidableEq E] in
theorem exists_skeletal_map_on_original_source
    (K L P J : SimplicialComplex ℝ E) (href : simplicialRefines P K)
    (hspace : P.space = K.space) (hJspace : J.space = L.space)
    (g : C(K.space, M)) (f : C(P.space, M))
    (X U : Set M) (H G : M ≃ₜ M) (C : Set E) (V : Finset E) (q : ℕ) {ε : ℝ}
    (hfix : ∀ x : P.space, x.val ∈ J.space → f x = g (Homeomorph.setCongr hspace x))
    (hnear : ∀ x : P.space, dist (f x) (g (Homeomorph.setCongr hspace x)) < ε)
    (hcover : X ∪ f '' (Subtype.val ⁻¹'
      (C ∪ (convexHull ℝ (V : Set E) ∩ (skeleton P q).space))) ⊆ G '' (H '' U)) :
    ∃ g' : C(K.space, M),
      (∀ x : K.space, x.val ∈ L.space → g' x = g x) ∧
      (∀ x, dist (g' x) (g x) < ε) ∧
      X ∪ g' '' (Subtype.val ⁻¹'
        (C ∪ (convexHull ℝ (V : Set E) ∩ (skeleton K q).space))) ⊆ G '' (H '' U) ∧
      (∀ x : P.space, g' (Homeomorph.setCongr hspace x) = f x) := by
  classical
  apply exists_map_on_equal_space_of_target_subset K L P J hspace hJspace g f
    (union_subset_union_right C (inter_subset_inter_right _ (href.old_skeleton_subset hspace q)))
    hfix hnear hcover

end

end DifferentialGeometry.Topology.Engulfing
