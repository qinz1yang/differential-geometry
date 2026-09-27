/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskChart

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLBall.exists_openPartialHomeomorph_boundary_disk_plane {Y D O : Set E3}
    (hY : IsPLBall 3 Y) (hD : IsPLBall 2 D) (hDY : D ⊆ frontier Y)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ e : OpenPartialHomeomorph E3 (Plane × ℝ),
      D ⊆ e.source ∧ e.source ⊆ O ∧
      IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target ∧
      (∀ x ∈ e.source, x ∈ frontier Y ↔ (e x).2 = 0) ∧
      (∀ x ∈ e.source, x ∈ Y ↔ 0 ≤ (e x).2) := by
  obtain ⟨e, hDe, heO, he, hei, heS, heY⟩ :=
    hY.exists_openPartialHomeomorph_boundary_disk hD hDY hO hDO
  let g : (ℝ × ℝ) ≃ₗ[ℝ] Plane :=
    (LinearEquiv.finTwoArrow ℝ ℝ).symm.trans (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm
  let L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (Plane × ℝ) :=
    (LinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm.trans
      (g.prodCongr (LinearEquiv.refl ℝ ℝ))
  let l := L.toContinuousLinearEquiv.toHomeomorph.toOpenPartialHomeomorph
  let k := e.trans l
  have hks : k.source = e.source := by
    ext x
    simp only [k, OpenPartialHomeomorph.trans_source, l,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  have hki : IsPiecewiseAffineOn k.symm k.target := by
    have hli : IsPiecewiseAffineOn l.symm l.target :=
      isPiecewiseAffineOn_of_affine L.symm.toLinearMap.toAffineMap isOpen_univ
    exact hei.comp hli
  refine ⟨k, hks ▸ hDe, hks ▸ heO, ?_, hki, ?_, ?_⟩
  · have hl : IsPiecewiseAffineOn l l.source :=
      isPiecewiseAffineOn_of_affine L.toLinearMap.toAffineMap isOpen_univ
    exact hl.comp he
  · intro x hx
    exact heS x (hks ▸ hx)
  · intro x hx
    exact heY x (hks ▸ hx)

end DifferentialGeometry.Topology.PiecewiseLinear
