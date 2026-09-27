/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RadialProjection
import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsSubdivision.singleton_mem {K' K : Geometry.SimplicialComplex ℝ E}
    (h : IsSubdivision K' K) {p : E} (hp : {p} ∈ K.faces) : {p} ∈ K'.faces := by
  have hpK : p ∈ K.space :=
    K.convexHull_subset_space hp (subset_convexHull ℝ _ (by simp))
  have hpK' : p ∈ K'.space := h.space_eq ▸ hpK
  have hσ := carrierFace_mem hpK'
  have hpσ := mem_openSimplex_carrierFace hpK'
  obtain ⟨t, ht, hsub⟩ := h.exists_face_subset hσ
  have hpt : p ∈ t :=
    mem_of_mem_convexHull_of_singleton_mem K hp ht
      (hsub (openSimplex_subset_convexHull _ hpσ))
  have hvert : ((carrierFace K' p : Finset E) : Set E) ⊆ convexHull ℝ (t : Set E) :=
    (subset_convexHull ℝ _).trans hsub
  have hsingle : ((carrierFace K' p : Finset E) : Set E) ⊆
      convexHull ℝ (({p} : Finset E) : Set E) :=
    subset_convexHull_of_mem_openSimplex (K.indep ht) (Finset.singleton_subset_iff.mpr hpt)
      hvert hpσ (subset_convexHull ℝ _ (by simp))
  have heq : carrierFace K' p = {p} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro v hv
      have := hsingle (Finset.mem_coe.mpr hv)
      rw [Finset.coe_singleton, convexHull_singleton] at this
      exact Finset.mem_singleton.mpr this
    · intro v hv
      rw [Finset.mem_singleton] at hv
      subst hv
      obtain ⟨w, hw₀, hw₁, hwp⟩ := hpσ
      by_contra hvσ
      obtain ⟨u, hu⟩ := K'.nonempty_of_mem_faces hσ
      have := hsingle (Finset.mem_coe.mpr hu)
      rw [Finset.coe_singleton, convexHull_singleton] at this
      exact hvσ (this ▸ hu)
  rw [← heq]
  exact hσ

theorem exists_isPLHomeomorphOn_geometricLink_of_isSubdivision [FiniteDimensional ℝ E]
    [DecidableEq E] {K' K : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (h : IsSubdivision K' K) {p : E} (hp : {p} ∈ K.faces) :
    ∃ f : E → E, IsPLHomeomorphOn f (SimplicialComplex.geometricLink K' {p}).space
      (SimplicialComplex.geometricLink K {p}).space := by
  have hp' : {p} ∈ K'.faces := h.singleton_mem hp
  refine exists_isPLHomeomorphOn_of_radial p (SimplicialComplex.geometricLink K {p})
    (SimplicialComplex.geometricLink K' {p}) (isRadiallyInjective_geometricLink K)
    (isConeBase_geometricLink K') ?_ ?_
  · intro σ hσ
    obtain ⟨hσne, hpσ, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K' p σ).mp hσ
    obtain ⟨t, ht, hsub⟩ := h.exists_face_subset hins
    have hpt : p ∈ t := mem_of_mem_convexHull_of_singleton_mem K hp ht
      (hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p σ))))
    refine ⟨t.erase p, ?_, fun w hw => ?_⟩
    · refine (SimplicialComplex.mem_geometricLink_singleton K p _).mpr
        ⟨?_, Finset.notMem_erase p t, by rwa [Finset.insert_erase hpt]⟩
      obtain ⟨w, hw⟩ := hσne
      have hwt : w ∈ convexHull ℝ (t : Set E) :=
        hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hw)))
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, Finset.erase_eq_empty_iff] at hne
      rcases hne with h0 | h0
      · exact (K.nonempty_of_mem_faces ht).ne_empty h0
      · rw [h0, Finset.coe_singleton, convexHull_singleton] at hwt
        exact hpσ (hwt ▸ hw)
    · have hwt : w ∈ convexHull ℝ ((insert p (t.erase p) : Finset E) : Set E) := by
        rw [Finset.insert_erase hpt]
        exact hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hw)))
      exact exists_ray_mem_convexHull_of_mem_convexHull_insert hwt (ne_of_mem_of_not_mem hw hpσ)
  · intro x hx
    have hxp : x ≠ p := ne_of_mem_of_not_mem hx (notMem_geometricLink_space K)
    refine exists_ray_mem_geometricLink_space K' hp' (fun t ht0 ht1 => ?_) hxp
    rw [h.space_eq]
    exact mem_convexHull_insert_of_mem_geometricLink_space K hx ht0.le ht1

theorem isPLSphere_geometricLink_iff_of_isSubdivision [FiniteDimensional ℝ E] [DecidableEq E]
    {K' K : Geometry.SimplicialComplex ℝ E} [Finite K'.faces] (h : IsSubdivision K' K) {p : E}
    (hp : {p} ∈ K.faces) {n : ℕ} :
    IsPLSphere n (SimplicialComplex.geometricLink K' {p}).space ↔
      IsPLSphere n (SimplicialComplex.geometricLink K {p}).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision h hp
  exact ⟨fun hs => hs.of_isPLHomeomorphOn hf, fun hs => hs.of_isPLHomeomorphOn hf.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
