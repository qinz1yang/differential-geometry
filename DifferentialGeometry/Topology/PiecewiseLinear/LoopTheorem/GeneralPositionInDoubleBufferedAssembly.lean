/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NormalCrossingTransport
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem assemble_buffered_fibre_and_boundary_invariants
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {G A : SingularTwoCell M} {H C Ostar V BdM : Set M}
    (hdomain : A.domain = G.domain)
    (hEqStar : ∀ z ∈ Ostar,
      (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
        (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z})
    (hEqOff : ∀ z ∉ V,
      (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
        (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z})
    (hGproper : G.domain ∩ G ⁻¹' H = frontier G.domain)
    (hHiff : ∀ x ∈ G.domain, A x ∈ H ↔ G x ∈ H)
    (hfrontEq : EqOn (A : EuclideanSpace ℝ (Fin 2) → M)
      (G : EuclideanSpace ℝ (Fin 2) → M) (frontier G.domain))
    (hGcross : ∀ z ∈ doublePointSet G G.domain ∩ C,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, z ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e z))
    (hOstar : IsOpen Ostar) (hC : C ⊆ Ostar) :
    A.domain ∩ A ⁻¹' H = frontier A.domain ∧
      EqOn (A : EuclideanSpace ℝ (Fin 2) → M)
        (G : EuclideanSpace ℝ (Fin 2) → M) (frontier G.domain) ∧
        (∀ z ∈ Ostar ∪ Vᶜ,
          (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
            (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z}) ∧
          ∀ z ∈ doublePointSet A A.domain ∩ C,
            ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, z ∈ e.source ∧
              HasPLNormalDoubleCrossingAt (e ∘ A)
                (A.domain ∩ A ⁻¹' e.source)
                (e '' (e.source ∩ BdM)) (e z) := by
  have hEqOnUnion : ∀ z ∈ Ostar ∪ Vᶜ,
      (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
        (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} := by
    intro z hz
    rcases hz with hzO | hzV
    · exact hEqStar z hzO
    · exact hEqOff z hzV
  have hproperA : A.domain ∩ A ⁻¹' H = frontier A.domain := by
    have hset : G.domain ∩ A ⁻¹' H = G.domain ∩ G ⁻¹' H := by
      ext x
      constructor
      · rintro ⟨hx, hAx⟩
        exact ⟨hx, (hHiff x hx).mp hAx⟩
      · rintro ⟨hx, hGx⟩
        exact ⟨hx, (hHiff x hx).mpr hGx⟩
    rw [hdomain, hset, hGproper]
  have hAcross : ∀ z ∈ doublePointSet A A.domain ∩ C,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, z ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ A)
          (A.domain ∩ A ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e z) := by
    intro z hz
    have hznot : z ∉ closure Ostarᶜ := by
      rw [hOstar.isClosed_compl.closure_eq]
      exact fun hz' => hz' (hC hz.2)
    have hEqComplement : ∀ z ∉ Ostarᶜ,
        (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
          (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} := by
      intro z hz
      exact hEqStar z (by simpa only [mem_compl_iff, not_not] using hz)
    exact exists_crossing_chart_of_preimage_singleton_eq_off
      (U := C) (V := Ostarᶜ) hdomain hEqComplement hGcross hz.1 hz.2 hznot
  exact ⟨hproperA, hfrontEq, hEqOnUnion, hAcross⟩

end DifferentialGeometry.Topology.PiecewiseLinear
