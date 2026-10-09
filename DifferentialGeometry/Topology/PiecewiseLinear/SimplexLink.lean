/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkRadial
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem geometricLink_simplexComplex [DecidableEq E] {T t : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (ht : t ⊆ T) :
    SimplicialComplex.geometricLink (simplexComplex T hT) t =
      simplexComplex (T \ t) (affineIndependent_of_subset hT Finset.sdiff_subset) := by
  ext s
  change (s.Nonempty ∧ Disjoint t s ∧ (t ∪ s).Nonempty ∧ t ∪ s ⊆ T) ↔
    s.Nonempty ∧ s ⊆ T \ t
  constructor
  · rintro ⟨hs, hts, -, hsub⟩
    refine ⟨hs, fun x hx => Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_union_right _ hx), ?_⟩⟩
    exact fun hxt => Finset.disjoint_left.mp hts hxt hx
  · rintro ⟨hs, hsub⟩
    refine ⟨hs, Finset.disjoint_left.mpr (fun x hxt hxs =>
      (Finset.mem_sdiff.mp (hsub hxs)).2 hxt), hs.mono Finset.subset_union_right, ?_⟩
    exact Finset.union_subset ht (hsub.trans Finset.sdiff_subset)

variable [FiniteDimensional ℝ E] [DecidableEq E] {T : Finset E}
  (hT : AffineIndependent ℝ ((↑) : T → E))
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

include hT

theorem exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_simplexComplex
    (hK : IsSubdivision K (simplexComplex T hT)) {u : E} (hu : {u} ∈ K.faces) {σ₀ : Finset E}
    (hσ₀T : σ₀ ⊆ T) (huσ : u ∈ openSimplex σ₀) :
    ∃ f : E → E, IsPLHomeomorphOn f (SimplicialComplex.geometricLink K {u}).space
      (simplexAvoiding T hT {σ₀}).space := by
  have hfin := (simplexAvoiding_faces_finite T hT {σ₀}).to_subtype
  have hspace : K.space = convexHull ℝ (T : Set E) := by
    rw [hK.space_eq]
    exact simplexComplex_space T hT ((nonempty_of_mem_openSimplex huσ).mono hσ₀T)
  refine exists_isPLHomeomorphOn_geometricLink_of_isConeBase K hu _
    (isConeBase_simplexAvoiding hT (Finset.mem_singleton_self σ₀) hσ₀T huσ) ?_ ?_
  · intro x hx hxu
    have hxT : x ∈ convexHull ℝ (T : Set E) := hspace ▸ closedStar_subset_space K u hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase_of_mem_openSimplex hT hσ₀T huσ hxT
    refine ⟨T.erase v, ⟨?_, Finset.erase_subset v T, ?_⟩, hxv⟩
    · rcases (T.erase v).eq_empty_or_nonempty with h | h
      · exfalso
        rw [h, Finset.insert_empty, Finset.coe_singleton, convexHull_singleton] at hxv
        exact hxu hxv
      · exact h
    · intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      exact fun h => Finset.notMem_erase v T (h hv)
  · intro y hy t ht0 ht1
    rw [hspace, add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _)
      (convexHull_mono (Finset.coe_subset.mpr hσ₀T) (openSimplex_subset_convexHull _ huσ))
      (simplexAvoiding_space_subset T hT _ hy) (by linarith) ht0.le (by ring)

theorem exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_simplexBoundary
    (hK : IsSubdivision K (simplexBoundary T hT)) {u : E} (hu : {u} ∈ K.faces) {σ₀ : Finset E}
    (hσ₀T : σ₀ ⊆ T) (huσ : u ∈ openSimplex σ₀) :
    ∃ f : E → E, IsPLHomeomorphOn f (SimplicialComplex.geometricLink K {u}).space
      (simplexAvoiding T hT {σ₀, T \ σ₀}).space := by
  have hfin := (simplexAvoiding_faces_finite T hT {σ₀, T \ σ₀}).to_subtype
  have hσ₀A : σ₀ ∈ ({σ₀, T \ σ₀} : Finset (Finset E)) := Finset.mem_insert_self _ _
  have hτ₀A : T \ σ₀ ∈ ({σ₀, T \ σ₀} : Finset (Finset E)) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  refine exists_isPLHomeomorphOn_geometricLink_of_isConeBase K hu _
    (isConeBase_simplexAvoiding hT hσ₀A hσ₀T huσ) ?_ ?_
  · intro x hx hxu
    obtain ⟨t, ⟨ht, hut⟩, hxt⟩ := mem_iUnion₂.mp hx
    obtain ⟨F, hF, hsub⟩ := hK.exists_face_subset ht
    obtain ⟨hFT, -, hFne⟩ := mem_simplexBoundary_faces_iff.mp hF
    have huF : u ∈ convexHull ℝ (F : Set E) := hsub hut
    have hσ₀F : σ₀ ⊆ F := subset_of_mem_openSimplex_of_mem_convexHull hT hσ₀T hFT huσ huF
    have hxF : x ∈ convexHull ℝ (F : Set E) := hsub hxt
    have hF' : AffineIndependent ℝ ((↑) : F → E) := affineIndependent_of_subset hT hFT
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase_of_mem_openSimplex hF' hσ₀F huσ hxF
    refine ⟨F.erase v, ⟨?_, (Finset.erase_subset v F).trans hFT, ?_⟩, hxv⟩
    · rcases (F.erase v).eq_empty_or_nonempty with h | h
      · exfalso
        rw [h, Finset.insert_empty, Finset.coe_singleton, convexHull_singleton] at hxv
        exact hxu hxv
      · exact h
    · intro σ hσ hσsub
      rcases Finset.mem_insert.mp hσ with h | hσ
      · rw [h] at hσsub
        exact Finset.notMem_erase v F (hσsub hv)
      · rw [Finset.mem_singleton] at hσ
        subst hσ
        apply hFne
        refine Finset.Subset.antisymm hFT fun w hw => ?_
        by_cases hwσ : w ∈ σ₀
        · exact hσ₀F hwσ
        · exact Finset.mem_of_mem_erase (hσsub (Finset.mem_sdiff.mpr ⟨hw, hwσ⟩))
  · intro y hy t ht0 ht1
    obtain ⟨s, ⟨hsne, hsT, hA⟩, hys⟩ := (simplexAvoiding T hT _).mem_space_iff.mp hy
    rw [hK.space_eq]
    refine (simplexBoundary T hT).convexHull_subset_space (s := σ₀ ∪ s) ?_ ?_
    · refine mem_simplexBoundary_faces_iff.mpr ⟨Finset.union_subset hσ₀T hsT,
        (nonempty_of_mem_openSimplex huσ).mono Finset.subset_union_left, fun h => ?_⟩
      apply hA (T \ σ₀) hτ₀A
      intro w hw
      obtain ⟨hwT, hwσ⟩ := Finset.mem_sdiff.mp hw
      have hw' : w ∈ σ₀ ∪ s := by
        rw [h]
        exact hwT
      rcases Finset.mem_union.mp hw' with h' | h'
      · exact absurd h' hwσ
      · exact h'
    · rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _)
        (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
          (openSimplex_subset_convexHull _ huσ))
        (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right) hys)
        (by linarith) ht0.le (by ring)

theorem isPLBall_geometricLink_of_isSubdivision_simplexComplex {n : ℕ} (hcard : T.card = n + 2)
    (hK : IsSubdivision K (simplexComplex T hT)) {u : E} (hu : {u} ∈ K.faces) {σ₀ : Finset E}
    (hσ₀T : σ₀ ⊆ T) (huσ : u ∈ openSimplex σ₀) (hne : σ₀ ≠ T) :
    IsPLBall n (SimplicialComplex.geometricLink K {u}).space := by
  obtain ⟨f, hf⟩ :=
    exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_simplexComplex hT hK hu hσ₀T huσ
  exact (isPLBall_simplexAvoiding_singleton hT hcard hσ₀T (nonempty_of_mem_openSimplex huσ)
    hne).of_isPLHomeomorphOn hf.symm

theorem isPLSphere_geometricLink_of_isSubdivision_simplexComplex_of_mem_openSimplex {n : ℕ}
    (hcard : T.card = n + 2) (hK : IsSubdivision K (simplexComplex T hT)) {u : E}
    (hu : {u} ∈ K.faces) (huT : u ∈ openSimplex T) :
    IsPLSphere n (SimplicialComplex.geometricLink K {u}).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_simplexComplex hT hK hu
    (Finset.Subset.refl T) huT
  rw [simplexAvoiding_singleton_self, simplexBoundary_space T hT (by omega)] at hf
  exact (isPLSphere_biUnion_erase T hT hcard).of_isPLHomeomorphOn hf.symm

theorem isPLSphere_geometricLink_of_isSubdivision_simplexBoundary {n : ℕ}
    (hcard : T.card = n + 3) (hK : IsSubdivision K (simplexBoundary T hT)) {u : E}
    (hu : {u} ∈ K.faces) : IsPLSphere n (SimplicialComplex.geometricLink K {u}).space := by
  have huK : u ∈ K.space := K.convexHull_subset_space hu (subset_convexHull ℝ _ (by simp))
  rw [hK.space_eq, simplexBoundary_space T hT (by omega)] at huK
  obtain ⟨w, hw, huw⟩ := mem_iUnion₂.mp huK
  obtain ⟨σ₀, hσ₀w, hσ₀ne, huσ⟩ := exists_openSimplex_of_mem_convexHull huw
  have hσ₀T : σ₀ ⊆ T := hσ₀w.trans (Finset.erase_subset w T)
  have hσ₀ : σ₀ ≠ T := fun h => Finset.notMem_erase w T (hσ₀w (h ▸ hw))
  obtain ⟨f, hf⟩ :=
    exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_simplexBoundary hT hK hu hσ₀T huσ
  exact (isPLSphere_simplexAvoiding_pair hT hcard hσ₀T hσ₀ne hσ₀).of_isPLHomeomorphOn hf.symm

theorem isPLBall_geometricLink_iff_of_isSubdivision_simplexComplex {n : ℕ}
    (hcard : T.card = n + 2) (hK : IsSubdivision K (simplexComplex T hT)) {u : E}
    (hu : {u} ∈ K.faces) :
    IsPLBall n (SimplicialComplex.geometricLink K {u}).space ↔
      u ∈ (simplexBoundary T hT).space := by
  have huK : u ∈ K.space := K.convexHull_subset_space hu (subset_convexHull ℝ _ (by simp))
  rw [hK.space_eq, simplexComplex_space T hT (Finset.card_pos.mp (by omega))] at huK
  obtain ⟨σ₀, hσ₀T, hσ₀ne, huσ⟩ := exists_openSimplex_of_mem_convexHull huK
  rw [simplexBoundary_space T hT (by omega)]
  by_cases hσ₀ : σ₀ = T
  · subst hσ₀
    have hsph := isPLSphere_geometricLink_of_isSubdivision_simplexComplex_of_mem_openSimplex hT
      hcard hK hu huσ
    refine ⟨fun hB => (hB.not_isPLSphere hsph).elim, fun h => ?_⟩
    obtain ⟨w, hw, huw⟩ := mem_iUnion₂.mp h
    exact absurd (subset_of_mem_openSimplex_of_mem_convexHull hT (Finset.Subset.refl _)
      (Finset.erase_subset w _) huσ huw hw) (Finset.notMem_erase w _)
  · refine ⟨fun _ => ?_, fun _ =>
      isPLBall_geometricLink_of_isSubdivision_simplexComplex hT hcard hK hu hσ₀T huσ hσ₀⟩
    obtain ⟨w, hwT, hwσ⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hσ₀T, hσ₀⟩)
    refine mem_iUnion₂.mpr ⟨w, hwT, convexHull_mono (Finset.coe_subset.mpr fun v hv => ?_)
      (openSimplex_subset_convexHull _ huσ)⟩
    exact Finset.mem_erase.mpr ⟨fun h => hwσ (h ▸ hv), hσ₀T hv⟩

theorem isPLSphere_geometricLink_iff_of_isSubdivision_simplexComplex {n : ℕ}
    (hcard : T.card = n + 2) (hK : IsSubdivision K (simplexComplex T hT)) {u : E}
    (hu : {u} ∈ K.faces) :
    IsPLSphere n (SimplicialComplex.geometricLink K {u}).space ↔
      u ∉ (simplexBoundary T hT).space := by
  have huK : u ∈ K.space := K.convexHull_subset_space hu (subset_convexHull ℝ _ (by simp))
  rw [hK.space_eq, simplexComplex_space T hT (Finset.card_pos.mp (by omega))] at huK
  obtain ⟨σ₀, hσ₀T, hσ₀ne, huσ⟩ := exists_openSimplex_of_mem_convexHull huK
  rw [← isPLBall_geometricLink_iff_of_isSubdivision_simplexComplex hT hcard hK hu]
  by_cases hσ₀ : σ₀ = T
  · subst hσ₀
    have hsph := isPLSphere_geometricLink_of_isSubdivision_simplexComplex_of_mem_openSimplex hT
      hcard hK hu huσ
    exact ⟨fun _ hB => hB.not_isPLSphere hsph, fun _ => hsph⟩
  · have hB := isPLBall_geometricLink_of_isSubdivision_simplexComplex hT hcard hK hu hσ₀T huσ hσ₀
    exact ⟨fun hS => (hB.not_isPLSphere hS).elim, fun h => (h hB).elim⟩

end DifferentialGeometry.Topology.PiecewiseLinear
