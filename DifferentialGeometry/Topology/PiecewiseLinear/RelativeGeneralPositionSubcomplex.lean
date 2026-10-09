/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem exists_small_simplicialMap_transverse_in_halfSpace_of_subcomplex
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hLK : L.faces ⊆ K.faces) (hdim : Module.finrank ℝ F = 3)
    (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (f : E → F) (hf : IsPiecewiseAffineOn f K.space)
    (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (f x))
    (hzero : ∀ x ∈ K.space, ℓ (f x) = 0 ↔ x ∈ L.space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (φ : E → F), IsSubdivision R K ∧ R.faces.Finite ∧
      IsPiecewiseAffineOn (simplicialMap R φ) K.space ∧
        (∀ x ∈ K.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
            (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (K.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (K.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ x ∈ K.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
                    (∀ x ∈ K.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ L.space) ∧
                      (∀ s ∈ R.faces, AffineIndependent ℝ (fun v : s => φ (v : E))) ∧
                        ∀ s ∈ R.faces, ∀ t ∈ R.faces, Disjoint s t →
                          (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t.image φ : Set
                            F)).Nonempty →
                            vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) =
                              if ((s ∪ t : Finset E) : Set E) ⊆ L.space
                                then LinearMap.ker ℓ else ⊤ := by
  have hLspace : L.space ⊆ K.space := space_mono_of_faces_subset hLK
  have hzeroL : ∀ x ∈ L.space, ℓ (f x) = 0 := fun x hx => (hzero x (hLspace hx)).mpr hx
  obtain ⟨R, δ, hR, hfinite, heq, hδ, hstable⟩ :=
    exists_isSubdivision_stable_fiber_encard_le_two K f hf hloc hcard
  have : Finite R.faces := hfinite.to_subtype
  have hRman : IsCombinatorialManifoldWithBoundary 2 R := hK.of_isSubdivision hR
  have hvertices : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  let V := hvertices.toFinset
  let B := V.filter (fun v => ℓ (f v) = 0)
  have hBV : B ⊆ V := Finset.filter_subset _ _
  have hVK : ∀ v ∈ V, v ∈ K.space := by
    intro v hv
    rw [← hR.space_eq]
    exact R.subset_space (hvertices.mem_toFinset.mp hv) (Finset.mem_singleton_self v)
  have hfaces : ∀ s ∈ R.faces, s ⊆ V := by
    intro s hs v hv
    apply hvertices.mem_toFinset.mpr
    exact R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hB : ∀ v ∈ B, ℓ (f v) = 0 := fun _ hv => (Finset.mem_filter.mp hv).2
  have hV : ∀ v ∈ V \ B, 0 < ℓ (f v) := by
    intro v hv
    obtain ⟨hvV, hvB⟩ := Finset.mem_sdiff.mp hv
    have hne : ℓ (f v) ≠ 0 := fun h => hvB (Finset.mem_filter.mpr ⟨hvV, h⟩)
    exact lt_of_le_of_ne (hnonneg v (hVK v hvV)) hne.symm
  obtain ⟨φ, _, hclose, hzero', hpos, hgood, htrans⟩ :=
    exists_small_vertexMap_transverse_in_halfSpace V B hBV ℓ hℓ f hB hV (lt_min hδ hε)
  have hφnonneg : ∀ v ∈ R.vertices, 0 ≤ ℓ (φ v) := by
    intro v hv
    by_cases hvB : v ∈ B
    · rw [hzero' v hvB]
    · exact (hpos v (Finset.mem_sdiff.mpr ⟨hvertices.mem_toFinset.mpr hv, hvB⟩)).le
  have hfnonneg : ∀ v ∈ R.vertices, 0 ≤ ℓ (f v) :=
    fun v hv => hnonneg v (hVK v (hvertices.mem_toFinset.mpr hv))
  have hzeroiff : ∀ v ∈ R.vertices, ℓ (φ v) = 0 ↔ ℓ (f v) = 0 := by
    intro v hv
    by_cases hvB : v ∈ B
    · simp only [hzero' v hvB, hB v hvB]
    · have hφne := (hpos v (Finset.mem_sdiff.mpr ⟨hvertices.mem_toFinset.mpr hv, hvB⟩)).ne'
      have hfne : ℓ (f v) ≠ 0 := fun h => hvB (Finset.mem_filter.mpr ⟨hvertices.mem_toFinset.mpr
        hv, h⟩)
      simp only [hφne, hfne]
  obtain ⟨hstar, hlocal, hfiber⟩ := hstable φ
    (fun v _ => (hclose v).trans_le (min_le_left δ ε))
  have hkerbound : 2 ≤ Module.finrank ℝ (LinearMap.ker ℓ) := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    have hle := Submodule.finrank_le (LinearMap.range ℓ)
    rw [Module.finrank_self] at hle
    omega
  refine ⟨R, φ, hR, hfinite, ?_, ?_, hstar, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hR.space_eq] using isPiecewiseAffineOn_simplicialMap R φ
  · intro x hx
    rw [← heq hx]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R
      (fun v _ => (hclose v).trans_le (min_le_right δ ε)) (hR.space_eq.symm ▸ hx)
  · rwa [hR.space_eq] at hlocal
  · rwa [hR.space_eq] at hfiber
  · intro x hx
    rw [linearMap_simplicialMap]
    exact simplicialMap_nonneg_of_nonneg_vertices R (ℓ ∘ φ) hφnonneg (hR.space_eq.symm ▸ hx)
  · intro x hx
    have h := simplicialMap_eq_zero_iff_of_eq_zero_on_vertices R (ℓ ∘ φ) (ℓ ∘ f)
      hφnonneg hfnonneg hzeroiff (hR.space_eq.symm ▸ hx)
    rw [← linearMap_simplicialMap R φ ℓ x, ← linearMap_simplicialMap R f ℓ x, heq hx] at h
    exact h.trans (hzero x hx)
  · intro s hs
    have hc := hRman.card_le R hs
    have hbc := Finset.card_le_card (Finset.inter_subset_left (s₁ := s) (s₂ := B))
    exact hgood s (hfaces s hs) (by omega) (by omega)
  · intro s hs t ht hdisj hinter
    have hiff : s ∪ t ⊆ B ↔ ((s ∪ t : Finset E) : Set E) ⊆ L.space := by
      constructor
      · intro h v hv
        exact (hzero v (hVK v (hBV (h hv)))).mp (hB v (h hv))
      · intro h v hv
        have hvV := (Finset.union_subset (hfaces s hs) (hfaces t ht)) hv
        exact Finset.mem_filter.mpr ⟨hvV, hzeroL v (h hv)⟩
    have h := htrans s (hfaces s hs) t (hfaces t ht) hdisj hinter
    simpa only [hiff] using h

end DifferentialGeometry.Topology.PiecewiseLinear
