/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeWindowReduction

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCanonicalBridgeWindowReduction.exists_row_annulus [DecidableEq E3]
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3}
    {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
    {Dimg Dbdimg W I F : Set E3} {P' a b : E3} {rows : Finset ℤ}
    (h : IsCanonicalBridgeWindowReduction X Y (fun j => φ '' S j) S'' T'' I P' a b rows F)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) (hi : i ∈ rows) :
    ∃ J₀ J₁ : Set E3, IsPLAnnulusWithEnds (Y i).space J₀ J₁ ∧ Disjoint J₀ J₁ ∧
      J₀ ∈ traceCircles (Y i).space (T'' (2 * i)) ∧
      J₁ ∈ traceCircles (Y i).space (T'' (2 * (i + 1))) ∧
      ¬ boundsDiskIn J₀ (T'' (2 * i)) ∧ ¬ boundsDiskIn J₁ (T'' (2 * (i + 1))) ∧
      (Y i).space ∩ T'' (2 * i) = J₀ ∧ (Y i).space ∩ T'' (2 * (i + 1)) = J₁ := by
  obtain ⟨c, hc⟩ := Nat.card_eq_one_iff_exists.mp (h.singleComponent i hi)
  have hspace : (connectedComponentComplex (Y i) c).space = (Y i).space := by
    apply Subset.antisymm
    · exact (subset_iUnion (fun q => (connectedComponentComplex (Y i) q).space) c).trans
        (iUnion_connectedComponentComplex_space (Y i)).subset
    · intro x hx
      obtain ⟨q, hq⟩ :=
        mem_iUnion.mp ((iUnion_connectedComponentComplex_space (Y i)).symm.subset hx)
      simpa only [hc q] using hq
  obtain ⟨J₀, J₁, hC, h₀, h₁, hess₀, hess₁⟩ := h.bridgeComponents i hi c
  have hdis : Disjoint J₀ J₁ :=
    (htw.apart (2 * i) (2 * (i + 1)) (by rw [le_abs]; omega)).mono
      (((traceCircles_subset h₀).trans inter_subset_right).trans (htw.boundary_subset_outer _))
      (((traceCircles_subset h₁).trans inter_subset_right).trans (htw.boundary_subset_outer _))
  have hlo : ¬ boundsDiskIn J₀ (T'' (2 * i)) :=
    fun hd => hess₀ ((h.target.surface.lower_component_boundsDiskIn_iff htw h314 i c h₀).mp hd)
  have hhi : ¬ boundsDiskIn J₁ (T'' (2 * (i + 1))) :=
    fun hd => hess₁ ((h.target.surface.upper_component_boundsDiskIn_iff htw h314 i c h₁).mp hd)
  have hmeet := h.target.surface.bridge_component_inter_even htw i c hC h₀ h₁
  exact ⟨J₀, J₁, hspace ▸ hC, hdis, hspace ▸ h₀, hspace ▸ h₁, hlo, hhi,
    hspace ▸ hmeet.1, hspace ▸ hmeet.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
