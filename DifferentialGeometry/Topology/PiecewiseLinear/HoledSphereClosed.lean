/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

open Classical in
theorem IsPLSphere.isClosed_holed_disk_family
    {ι : Type*} [Finite ι] {S : Set E} (hS : IsPLSphere 2 S)
    {D : ι → Set E} {q : ι → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDS : ∀ i, D i ⊆ S)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (i₀ : ι) :
    IsClosed (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2)) := by
  classical
  obtain ⟨χ, Δ, hΔ, hχ, -, hχi⟩ := hS.exists_holed_chart hq hDS hdis i₀
  have hcD : ∀ i, q i '' stdSimplexBoundary 2 ⊆ D i := by
    intro i
    rintro _ ⟨x, hx, rfl⟩
    exact (hq i).bijOn.mapsTo hx.1
  have hint : ∀ i, i ≠ i₀ → interior (χ '' D i) =
      χ '' D i \ χ '' (q i '' stdSimplexBoundary 2) := by
    intro i hi
    have hcl : IsClosed (χ '' D i) :=
      (IsPLBall.of_isPLHomeomorphOn ⟨q i, hq i⟩ (hχi i hi).2.2.1).isPolyhedron.isClosed
    rw [(hχi i hi).2.2.2, hcl.frontier_eq, sdiff_sdiff_right_self,
      inter_eq_right.mpr interior_subset]
  obtain ⟨hPeq, hPC⟩ := image_sdiff_iUnion_sdiff_eq (S := S) i₀ hχ.bijOn rfl
    (fun i hi => (hχi i hi).1) hcD hint
  let A : {i // i ≠ i₀} → Set Plane := fun k => χ '' D k.1
  have hA : ∀ k, IsPLBall 2 (A k) := fun k =>
    IsPLBall.of_isPLHomeomorphOn ⟨q k.1, hq k.1⟩ (hχi k.1 k.2).2.2.1
  have hRpoly : IsPolyhedron (Δ \ ⋃ k, interior (A k)) :=
    hΔ.isPolyhedron.sdiff_iUnion_interior_of_isPLBall hA
  have hRcompact : IsCompact (Δ \ ⋃ k, interior (A k)) := hRpoly.isCompact
  have hRsubset : Δ \ ⋃ k, interior (A k) ⊆ Δ := sdiff_subset
  have hRimage : Function.invFunOn χ (S \ (D i₀ \ q i₀ '' stdSimplexBoundary 2)) ''
      (Δ \ ⋃ k, interior (A k)) = S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2) := by
    rw [← hPeq, hχ.bijOn.injOn.invFunOn_image hPC]
  have hR : IsCompact (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2)) := by
    rw [← hRimage]
    exact hRcompact.image_of_continuousOn (hχ.symm.isPiecewiseAffineOn.continuousOn.mono hRsubset)
  exact hR.isClosed

end DifferentialGeometry.Topology.PiecewiseLinear
