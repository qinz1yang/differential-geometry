/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalMarkedProduct
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalPointedUntwisting
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusThickening

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Δ" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "Disk" => Metric.closedBall (0 : E2) 1
local notation "Circle" => Metric.sphere (0 : E2) 1

theorem IsCylindricalDiagram.exists_thickening_marked_stdCenter
    {S U : Set E3} {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsCylindricalDiagram f Δ S)
    (hclosed : f (stdCenter 1, 0) = f (stdCenter 1, 1))
    (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ P : Set E3, P ⊆ U ∧ S ⊆ interior P ∧
      ∃ Φ : (Disk × Circle) ≃ₜ P,
        f '' ({stdCenter 1} ×ˢ Icc (0 : ℝ) 1) =
          Subtype.val '' (Φ '' {z | (z.1 : E2) = 0}) := by
  obtain ⟨g, hg, hends, haxis⟩ :=
    hf.exists_endMap_id_preserving_stdCenter (by simp) hclosed
  obtain ⟨Ψ, hΨ⟩ := hg.exists_homeomorph_closedBall_prod_sphere_of_eq_ends hends
  have haxisimage : g '' ({stdCenter 1} ×ˢ Icc (0 : ℝ) 1) =
      f '' ({stdCenter 1} ×ˢ Icc (0 : ℝ) 1) := by
    apply image_congr
    rintro ⟨x, t⟩ ⟨rfl, ht⟩
    exact haxis t ht
  have hcore : Subtype.val '' (Ψ '' {z | (z.1 : E2) = 0}) =
      f '' ({stdCenter 1} ×ˢ Icc (0 : ℝ) 1) := hΨ.trans haxisimage
  let A := f '' ({stdCenter 1} ×ˢ Icc (0 : ℝ) 1)
  have hp : stdCenter 1 ∈ Δ := by
    rw [← convexHull_stdVertices 1]
    exact openSimplex_subset_convexHull _ (stdCenter_mem_openSimplex 1)
  have hA : IsCompact A :=
    (isCompact_singleton.prod isCompact_Icc).image_of_continuousOn
      (hf.isPiecewiseAffineOn.continuousOn.mono
        (prod_mono (singleton_subset_iff.mpr hp) subset_rfl))
  have hAS : A ⊆ interior S := by
    rw [show A = Subtype.val '' (Ψ '' {z | (z.1 : E2) = 0}) from hcore.symm]
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact mem_interior_of_homeomorph_closedBall_prod_sphere Ψ.symm z.1 z.2
      (by rw [hz]; simp)
  have hsolid := hf.isCombinatorialSolidTorus (isPLBall_stdSimplex 2) (by simp)
  obtain ⟨P, hPU, hSP, e, he⟩ :=
    hsolid.exists_thickening_fixed_on_compact hA hAS hU hSU
  refine ⟨P, hPU, hSP, Ψ.trans e, ?_⟩
  rw [← hcore]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨e (Ψ z), ⟨z, hz, rfl⟩, ?_⟩
    exact he (Ψ z) (hcore.subset ⟨Ψ z, ⟨z, hz, rfl⟩, rfl⟩)
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Ψ z, ⟨z, hz, rfl⟩, ?_⟩
    exact (he (Ψ z) (hcore.subset ⟨Ψ z, ⟨z, hz, rfl⟩, rfl⟩)).symm

end DifferentialGeometry.Topology.PiecewiseLinear
