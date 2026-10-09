/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleRelativeHalfSpaceCollar

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_relative_simplicialMap_transverse_in_halfSpace_with_collar
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (B Z : Finset E) (hZB : Z ⊆ B)
    (L : Geometry.SimplicialComplex ℝ E) (hLR : L.faces ⊆ R.faces)
    (hLB : (L.vertices : Set E) ⊆ B)
    (hB : (B : Set E) ⊆ R.vertices)
    (hcard : ∀ s ∈ R.faces, s.card ≤ Module.finrank ℝ F + 1)
    (f : E → F) (heq : EqOn (simplicialMap R f) f R.space) {δ : ℝ}
    (hstable : ∀ φ : E → F, (∀ v ∈ R.vertices, dist (φ v) (f v) < δ) →
      (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
        (simplicialMap R φ '' (starComplex R v).space)) ∧
        IsLocallyInjective (R.space.domRestrict (simplicialMap R φ)) ∧
          ∀ y : F, (R.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2)
    (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hzero : ∀ v ∈ Z, ℓ (f v) = 0)
    (hpositive : ∀ v ∈ R.vertices \ Z, 0 < ℓ (f v))
    (hfixedAI : ∀ u : Finset E, (u : Set E) ⊆ B →
      u.card ≤ Module.finrank ℝ F + 1 →
        (u ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
          AffineIndependent ℝ (fun v : u => f v))
    (hfixedPair : ∀ s t : Finset E, (s : Set E) ⊆ Z → (t : Set E) ⊆ Z →
      Disjoint s t →
        (convexHull ℝ (s.image f : Set F) ∩
          convexHull ℝ (t.image f : Set F)).Nonempty →
            vectorSpan ℝ (s.image f : Set F) ⊔
              vectorSpan ℝ (t.image f : Set F) = LinearMap.ker ℓ)
    (hfaceGuard : ∀ s ∈ R.faces,
      (s ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    ∃ φ : E → F,
      IsPiecewiseAffineOn (simplicialMap R φ) R.space ∧
        (∀ x ∈ R.space, dist (simplicialMap R φ x) (f x) < ε) ∧
          (∀ v ∈ B, φ v = f v) ∧
            EqOn (simplicialMap R φ) (simplicialMap R f) L.space ∧
            (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ)
              (starComplex R v).space (simplicialMap R φ '' (starComplex R v).space)) ∧
              IsLocallyInjective (R.space.domRestrict (simplicialMap R φ)) ∧
                (∀ y : F, (R.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2) ∧
                  (∀ v ∈ R.vertices, 0 ≤ ℓ (φ v)) ∧
                    (∀ v ∈ R.vertices, ℓ (φ v) = 0 ↔ v ∈ Z) ∧
                      ∀ s ∈ R.faces, AffineIndependent ℝ (fun v : s => φ v) ∧
                        InjOn (simplicialMap R φ) (convexHull ℝ (s : Set E)) ∧
                          ∀ t ∈ R.faces, Disjoint s t →
                            (convexHull ℝ (s.image φ : Set F) ∩
                              convexHull ℝ (t.image φ : Set F)).Nonempty →
                                (((s ∪ t : Finset E) : Set E) ⊆ Z →
                                  vectorSpan ℝ (s.image φ : Set F) ⊔
                                    vectorSpan ℝ (t.image φ : Set F) = LinearMap.ker ℓ) ∧
                                (¬((s ∪ t : Finset E) : Set E) ⊆ B →
                                  vectorSpan ℝ (s.image φ : Set F) ⊔
                                    vectorSpan ℝ (t.image φ : Set F) = ⊤) := by
  have hRvertices : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite R.faces)
  let V := hRvertices.toFinset
  have hVmem : ∀ v ∈ V, v ∈ R.vertices := fun v hv => hRvertices.mem_toFinset.mp hv
  have hfaces : ∀ s ∈ R.faces, s ⊆ V := by
    intro s hs v hv
    exact hRvertices.mem_toFinset.mpr
      (R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have hBV : B ⊆ V := by
    intro v hv
    exact hRvertices.mem_toFinset.mpr (hB hv)
  have hVZ : ∀ v ∈ V \ Z, 0 < ℓ (f v) := by
    intro v hv
    have hv' : v ∈ V \ Z := by simpa using hv
    exact hpositive v ⟨hVmem v (Finset.mem_sdiff.mp hv').1, (Finset.mem_sdiff.mp hv').2⟩
  have hZ : ∀ v ∈ Z, ℓ (f v) = 0 := hzero
  obtain ⟨φ, hfixV, hfixB, hclose, hφzero, hφpos, hgood⟩ :=
    exists_small_affineIndependent_subsets_relative_in_halfSpace_with_collar
      V B Z hZB hBV ℓ hℓ f hZ hVZ hfixedAI hε
  have hvertexClose : ∀ v ∈ R.vertices, dist (φ v) (f v) < δ := by
    intro v hv
    have hvV := hRvertices.mem_toFinset.mpr hv
    exact (hclose v).trans_le hεδ
  obtain ⟨hstar, hlocal, hfiber⟩ := hstable φ hvertexClose
  have hpl : IsPiecewiseAffineOn (simplicialMap R φ) R.space := by
    exact isPiecewiseAffineOn_simplicialMap R φ
  have hmapClose : ∀ x ∈ R.space,
      dist (simplicialMap R φ x) (f x) < ε := by
    intro x hx
    rw [← heq hx]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R (fun v _ => hclose v) hx
  have hφnonneg : ∀ v ∈ R.vertices, 0 ≤ ℓ (φ v) := by
    intro v hv
    by_cases hvZ : v ∈ Z
    · rw [hφzero v hvZ]
    · exact (hφpos v (Finset.mem_sdiff.mpr ⟨hRvertices.mem_toFinset.mpr hv, hvZ⟩)).le
  have hφzeroiff : ∀ v ∈ R.vertices, ℓ (φ v) = 0 ↔ v ∈ Z := by
    intro v hv
    by_cases hvZ : v ∈ Z
    · simp only [hφzero v hvZ, hvZ]
    · have hne := (hφpos v (Finset.mem_sdiff.mpr
          ⟨hRvertices.mem_toFinset.mpr hv, hvZ⟩)).ne'
      simp only [hne, hvZ]
  have hfaceAI : ∀ s ∈ R.faces, AffineIndependent ℝ (fun v : s => φ v) := by
    intro s hs
    exact hgood s (hfaces s hs) (hcard s hs) (hfaceGuard s hs)
  have htrans : ∀ s ∈ R.faces, ∀ t ∈ R.faces, Disjoint s t →
      (convexHull ℝ (s.image φ : Set F) ∩
        convexHull ℝ (t.image φ : Set F)).Nonempty →
          (((s ∪ t : Finset E) : Set E) ⊆ Z →
            vectorSpan ℝ (s.image φ : Set F) ⊔
              vectorSpan ℝ (t.image φ : Set F) = LinearMap.ker ℓ) ∧
          (¬((s ∪ t : Finset E) : Set E) ⊆ B →
            vectorSpan ℝ (s.image φ : Set F) ⊔
              vectorSpan ℝ (t.image φ : Set F) = ⊤) := by
    intro s hs t ht hdisj hinter
    constructor
    · intro hall
      have hsZ : (s : Set E) ⊆ Z := fun v hv => hall (Finset.mem_union_left t hv)
      have htZ : (t : Set E) ⊆ Z := fun v hv => hall (Finset.mem_union_right s hv)
      have hsimage : s.image φ = s.image f := Finset.image_congr (fun v hv => hfixB (hZB
        (by
          have hvZ : v ∈ Z := by simpa using hsZ hv
          exact hvZ)))
      have htimage : t.image φ = t.image f := Finset.image_congr (fun v hv => hfixB (hZB
        (by
          have hvZ : v ∈ Z := by simpa using htZ hv
          exact hvZ)))
      rw [hsimage, htimage] at hinter
      rw [hsimage, htimage]
      exact hfixedPair s t (by simpa using hsZ) (by simpa using htZ) hdisj hinter
    · intro hnotB
      exact vectorSpan_sup_eq_top_of_affineIndependent_subsets_relative_in_halfSpace
        V B ℓ hℓ φ (fun u hu hucard hBcard =>
          hgood u hu hucard hBcard)
        (hfaces s hs) (hfaces t ht) hdisj hnotB hinter
  have hEqL : EqOn (simplicialMap R φ) (simplicialMap R f) L.space :=
    simplicialMap_eqOn_subcomplex_of_eqOn_vertices R L hLR (fun v hv => hfixB (hLB hv))
  refine ⟨φ, hpl, hmapClose, ?_, hEqL, hstar, hlocal, hfiber, hφnonneg, hφzeroiff, ?_⟩
  · intro v hv
    exact hfixB hv
  · intro s hs
    exact ⟨hfaceAI s hs, injOn_simplicialMap_convexHull R φ hs (hfaceAI s hs), htrans s hs⟩

end DifferentialGeometry.Topology.PiecewiseLinear
