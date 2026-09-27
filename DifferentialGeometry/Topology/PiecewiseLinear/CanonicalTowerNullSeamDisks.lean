/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusFundamentalGroup

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.bounds_disks_of_boundsDisk
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) {G : Set E3}
    (hG : G ∈ traceCircles (T'' i) (T'' (i + 1)))
    (hnull : boundsDiskIn G (T'' i) ∨ boundsDiskIn G (T'' (i + 1))) :
    boundsDiskIn G (T'' i) ∧ boundsDiskIn G (T'' (i + 1)) := by
  rcases htw.seam_generator_or_bounds_disks h314 i hG with hgen | hboth
  · have hnot : ∀ j ∈ ({i, i + 1} : Set ℤ), ¬ boundsDiskIn G (T'' j) := by
      intro j hj hbound
      obtain ⟨Δ, r, hr, hΔT, hGr⟩ := hbound
      have hGΔ : G ⊆ Δ := by
        rw [hGr]
        exact (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
      have hΔS : Δ ⊆ S'' j := hΔT.trans (htw.boundary_subset_solid j)
      have hS : IsCombinatorialSolidTorus (S'' j) := by
        simpa using (htw.config j).isPolyhedralSolidTorus 0
      obtain ⟨x, hxG⟩ := (traceCircles_isPLSphere hG).nonempty
      exact IsPLBall.not_surjective_fundamentalGroup_map_inclusion (⟨r, hr⟩ : IsPLBall 2 Δ)
        hS.1 hGΔ hΔS ⟨x, hxG⟩ (hgen j hj (hGΔ.trans hΔS) ⟨x, hxG⟩)
    rcases hnull with hnull | hnull
    · exact (hnot i (Or.inl rfl) hnull).elim
    · exact (hnot (i + 1) (Or.inr rfl) hnull).elim
  · exact hboth

theorem IsCanonicalTower.boundsDiskIn_iff
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) {G : Set E3}
    (hG : G ∈ traceCircles (T'' i) (T'' (i + 1))) :
    boundsDiskIn G (T'' i) ↔ boundsDiskIn G (T'' (i + 1)) :=
  ⟨fun h => (htw.bounds_disks_of_boundsDisk h314 i hG (Or.inl h)).2,
    fun h => (htw.bounds_disks_of_boundsDisk h314 i hG (Or.inr h)).1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
