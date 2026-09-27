/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarFibers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def collarHalf {X : Type*} (J : Set X) (ρ : X × ℝ → X) (positive : Bool) : Set X :=
  ρ '' (J ×ˢ if positive then Icc (0 : ℝ) 1 else Icc (-1 : ℝ) 0)

namespace NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem mem_collarHalf_iff (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ) {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (positive : Bool) :
    ρ (a, t) ∈ collarHalf J ρ positive ↔ if positive then 0 ≤ t else t ≤ 0 := by
  have hρpl := hρ.2.2.2.2.2.1
  constructor
  · rintro ⟨⟨b, s⟩, ⟨hb, hs⟩, heq⟩
    have hsI : s ∈ Icc (-1 : ℝ) 1 := by
      cases positive
      · exact ⟨hs.1, hs.2.trans zero_le_one⟩
      · exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hs.1, hs.2⟩
    have hst : s = t := congrArg Prod.snd (hρpl.bijOn.injOn ⟨hb, hsI⟩ ⟨ha, ht⟩ heq)
    subst s
    cases positive
    · exact hs.2
    · exact hs.1
  · intro h
    refine ⟨(a, t), ⟨ha, ?_⟩, rfl⟩
    cases positive
    · exact ⟨ht.1, h⟩
    · exact ⟨h, ht.2⟩

theorem subset_collarHalf (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ) (positive : Bool) : J ⊆ collarHalf J ρ positive := by
  intro a ha
  have h := (hD.mem_collarHalf_iff hρ ha (t := 0) (by constructor <;> norm_num) positive).mpr
    (by cases positive <;> exact le_rfl)
  rwa [hρ.2.2.2.2.2.2.1 a ha] at h

theorem mem_collarHalf_iff_coordinate (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ C) {z : ℝ}
    (hzero : z = 0 ↔ D x ∈ hD.singularSet.branchCarrier c)
    (hpos : 0 < z ↔ ∃ s ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, s)) (positive : Bool) :
    x ∈ collarHalf J ρ positive ↔ if positive then 0 ≤ z else z ≤ 0 := by
  have hρpl := hρ.2.2.2.2.2.1
  obtain ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩ := hρpl.bijOn.surjOn hx
  have hz0 : z = 0 ↔ t = 0 := hzero.trans (hD.mem_branchCarrier_collarFiber_iff hρ ha ht)
  have hzt : 0 < z ↔ 0 < t := by
    rw [hpos]
    constructor
    · rintro ⟨s, hs, w, hw, heq⟩
      have hts : t = s := congrArg Prod.snd (hρpl.bijOn.injOn ⟨ha, ht⟩
        ⟨hw, ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hs.1.le, hs.2⟩⟩ heq)
      exact hts.symm ▸ hs.1
    · intro htpos
      exact ⟨t, ⟨htpos, ht.2⟩, a, ha, rfl⟩
  rw [hD.mem_collarHalf_iff hρ ha ht]
  cases positive
  · exact not_lt.symm.trans ((not_congr hzt).symm.trans not_lt)
  · change 0 ≤ t ↔ 0 ≤ z
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
    exact or_congr hzt.symm (by simpa only [eq_comm] using hz0.symm)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
