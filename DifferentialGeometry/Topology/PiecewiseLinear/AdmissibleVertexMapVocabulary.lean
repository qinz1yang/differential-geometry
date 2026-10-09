/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def AdmissibleVertexMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (τ : ℝ) : Prop :=
  (Bv : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices ∧
    (∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space) ∧
    (∀ v ∈ R.vertices, dist (φ v) (ec (D v)) < τ) ∧
    (∀ v ∈ R.vertices, v ∈ Ac.space → φ v = ec (D v)) ∧
    (∀ v ∈ R.vertices, v ∈ Bv → ℓ (φ v) = 0) ∧
    ∀ v ∈ R.vertices, v ∉ Bv → 0 < ℓ (φ v)

theorem AdmissibleVertexMap.mono {D : SingularTwoCell M}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ}
    {Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} {τ τ' : ℝ}
    (h : AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ) (hle : τ ≤ τ') :
    AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ' :=
  ⟨h.1, h.2.1, fun v hv => lt_of_lt_of_le (h.2.2.1 v hv) hle, h.2.2.2⟩

open Classical in
theorem exists_admissibleVertexMap_of_adaptedChart (D : SingularTwoCell M) {BdM C V : Set M}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRsfin : R.faces.Finite) (hsub : IsSubdivision R Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Bv : Finset (EuclideanSpace ℝ (Fin 2)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv (fun v => ec (D v)) τ := by
  classical
  have hvfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hRsfin
  have hvR : ∀ v ∈ R.vertices, v ∈ Rc.space := by
    intro v hv
    rw [← hsub.space_eq]
    exact Geometry.SimplicialComplex.vertices_subset_space hv
  have hsrc : ∀ v ∈ R.vertices, D v ∈ ec.source := fun v hv => hVec (hRV (hvR v hv))
  have hmemBv : ∀ v, v ∈ hvfin.toFinset.filter (fun w => w ∈ Lc.space) ↔
      v ∈ R.vertices ∧ v ∈ Lc.space := by
    intro v
    simp [Finset.mem_filter, hvfin.mem_toFinset]
  refine ⟨hvfin.toFinset.filter fun w => w ∈ Lc.space, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ((hmemBv v).1 (Finset.mem_coe.mp hv)).1
  · exact fun v hv => ⟨fun h => ((hmemBv v).1 h).2, fun h => (hmemBv v).2 ⟨hv, h⟩⟩
  · intro v _
    simpa using hτ
  · exact fun _ _ _ => rfl
  · intro v hv hvB
    have hvL : v ∈ Lc.space := ((hmemBv v).1 hvB).2
    rw [hLspace] at hvL
    have hmem : v ∈ D.domain ∩ ⇑D ⁻¹' BdM := by
      rw [hproper]
      exact hvL.2
    exact (hBdchart (D v) (hsrc v hv)).1 hmem.2
  · intro v hv hvB
    have hvRc : v ∈ Rc.space := hvR v hv
    have hvL : v ∉ Lc.space := fun h => hvB ((hmemBv v).2 ⟨hv, h⟩)
    have hne : ℓ (ec (D v)) ≠ 0 := by
      intro h
      have hBd : D v ∈ BdM := (hBdchart (D v) (hsrc v hv)).2 h
      have hfr : v ∈ frontier D.domain := by
        rw [← hproper]
        exact ⟨hRdom hvRc, hBd⟩
      exact hvL (by rw [hLspace]; exact ⟨hvRc, hfr⟩)
    exact lt_of_le_of_ne ((hCchart (D v) (hsrc v hv)).1 (hmapC (hRdom hvRc))) (Ne.symm hne)

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
