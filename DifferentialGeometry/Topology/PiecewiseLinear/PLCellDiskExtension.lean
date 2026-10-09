/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_isPLHomeomorphOn_extension_of_frontier_disk
    {P Q D D' : Set E3} (hP : IsPLBall 3 P) (hQ : IsPLBall 3 Q)
    (hD : IsPLBall 2 D) (hDP : D ⊆ frontier P)
    {g : E3 → E3} (hg : IsPLHomeomorphOn g D D') (hD'Q : D' ⊆ frontier Q) :
    ∃ F : E3 → E3, IsPLHomeomorphOn F P Q ∧ EqOn F g D := by
  let _ : DecidableEq E3 := Classical.decEq _
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLQ⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 3 K.space := hKP.symm ▸ hP
  have hL : IsPLBall 3 L.space := hLQ.symm ▸ hQ
  have hDK : D ⊆ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space hK.isCombinatorialManifoldWithBoundary, hKP]
    exact hDP
  have hD'L : D' ⊆ (boundaryComplex 3 L).space := by
    rw [← frontier_space_eq_boundaryComplex_space hL.isCombinatorialManifoldWithBoundary, hLQ]
    exact hD'Q
  obtain ⟨F, hF, hFg⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex K L hK hL hD hDK hg hD'L
  exact ⟨F, by rwa [hKP, hLQ] at hF, hFg⟩

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [TopologicalSpace M₂] [ChartedSpace E3 M₂]

theorem exists_isPLHomeomorphInto_extension_of_boundary_disk
    {P PB : Set M₁} {Q QB : Set M₂} {D J : Set M₁}
    (hP : IsPLCellOn 3 P PB) (hQ : IsPLCellOn 3 Q QB)
    (hD : IsPLCellOn 2 D J) (hDP : D ⊆ PB)
    {g : M₁ → M₂} (hg : IsPLHomeomorphInto 3 g D) (hgD : g '' D ⊆ QB) :
    ∃ F : M₁ → M₂, IsPLHomeomorphInto 3 F P ∧ F '' P = Q ∧ EqOn F g D := by
  have hDP' := hDP.trans hP.boundary_subset
  have hgD' := hgD.trans hQ.boundary_subset
  obtain ⟨A, r, u, hr, hu, rfl, rfl⟩ := hP
  obtain ⟨B, s, v, hs, hv, rfl, rfl⟩ := hQ
  let DA := Function.invFunOn u A '' D
  let DB := Function.invFunOn v B '' (g '' D)
  have huinv := hu.injOn.bijOn_image.invOn_invFunOn
  have hvinv := hv.injOn.bijOn_image.invOn_invFunOn
  have hDAA : DA ⊆ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hDP' hx)
  have hDBB : DB ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hv.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hgD' hx)
  have huDA : u '' DA = D := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [huinv.2 (hDP' hx)]
    · intro x hx
      exact ⟨Function.invFunOn u A x, ⟨x, hx, rfl⟩, huinv.2 (hDP' hx)⟩
  have hvDB : v '' DB = g '' D := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hvinv.2 (hgD' hx)]
    · intro x hx
      exact ⟨Function.invFunOn v B x, ⟨x, hx, rfl⟩, hvinv.2 (hgD' hx)⟩
  obtain ⟨a, ha, -⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP'
  obtain ⟨b, hb, -⟩ := (hD.image hg).exists_isPLHomeomorphOn_invFunOn hv hgD'
  have hDA : IsPLBall 2 DA := ⟨a, ha⟩
  have hDB : IsPLBall 2 DB := ⟨b, hb⟩
  have hDAfr : DA ⊆ frontier A := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hDP hx
    have hzA : z ∈ A := by
      obtain ⟨t, ht, rfl⟩ := hz
      exact hr.bijOn.mapsTo ht.1
    rw [huinv.1 hzA]
    exact (IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr) ▸ hz
  have hDBfr : DB ⊆ frontier B := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hgD hx
    have hzB : z ∈ B := by
      obtain ⟨t, ht, rfl⟩ := hz
      exact hs.bijOn.mapsTo ht.1
    rw [hvinv.1 hzB]
    exact (IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hs) ▸ hz
  have hψ : IsPLHomeomorphOn (Function.invFunOn v B ∘ g ∘ u) DA DB :=
    isPLHomeomorphOn_conj hu hv hDA.isPolyhedron hDAA hDA.nonempty
      hDB.isPolyhedron hDBB hg (huDA ▸ Subset.rfl) (by rw [huDA, hvDB])
  obtain ⟨H, hH, hHψ⟩ := exists_isPLHomeomorphOn_extension_of_frontier_disk
    (show IsPLBall 3 A from ⟨r, hr⟩) (show IsPLBall 3 B from ⟨s, hs⟩)
    hDA hDAfr hψ hDBfr
  obtain ⟨hF, hFim⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn hu hv hH
  refine ⟨_, hF, hFim, fun x hx => ?_⟩
  change v (H (Function.invFunOn u A x)) = g x
  rw [hHψ (show Function.invFunOn u A x ∈ DA from ⟨x, hx, rfl⟩)]
  simp only [Function.comp_apply, huinv.2 (hDP' hx)]
  exact hvinv.2 (hgD' ⟨x, hx, rfl⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
