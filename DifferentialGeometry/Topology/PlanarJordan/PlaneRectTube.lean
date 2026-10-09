/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.StripExtension

open Set Metric

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem exists_planeRect_subset_of_axis_subset {a b : ℝ} {U : Set Plane}
    (hU : IsOpen U) (haxis : ∀ t ∈ Icc a b, Plane.mk t 0 ∈ U) :
    ∃ δ > 0, planeRect a b (-δ) δ ⊆ U := by
  let e : (ℝ × ℝ) ≃L[ℝ] Plane :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).symm
  have he (p : ℝ × ℝ) : e p = Plane.mk p.1 p.2 := rfl
  have hprod : Icc a b ×ˢ ({0} : Set ℝ) ⊆ e ⁻¹' U := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    obtain rfl : y = 0 := hy
    exact haxis t ht
  obtain ⟨A, B, -, hB, hA, h0B, hAB⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton
      (hU.preimage e.continuous) hprod
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds (h0B rfl))
  refine ⟨r / 2, half_pos hr, fun v hv => ?_⟩
  have hvB : v 1 ∈ B := by
    apply hball
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hv.2.2.1], by linarith [hv.2.2.2]⟩
  have h : e (v 0, v 1) ∈ U := hAB ⟨hA ⟨hv.1, hv.2.1⟩, hvB⟩
  have hv' : e (v 0, v 1) = v := by
    rw [he]
    ext i
    fin_cases i <;> rfl
  exact hv' ▸ h

end DifferentialGeometry.Topology.PlanarJordan
