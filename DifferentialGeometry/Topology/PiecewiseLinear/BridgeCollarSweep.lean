/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeArcShrinking

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsBridgeDisk.exists_isPLHomeomorphOn_to_collar_ribbon
    {C A B W : Set E} {a b : E} (h : IsBridgeDisk C A B a b) (hC : IsPolyhedron C)
    {c : E × ℝ → E} (hc : IsPLHomeomorphOn c (frontier C ×ˢ Icc (0 : ℝ) 2) W)
    (hc0 : ∀ x ∈ frontier C, c (x, 0) = x)
    (htrace : B ∩ W = c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 2)) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ e '' C = C ∧
      IsBridgeDisk C (e '' A) (c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 1)) a b := by
  have hβ := h.isPLBall_inter_frontier
  have hI : IsPLBall 1 (Icc (0 : ℝ) 1) := isPLBall_Icc zero_lt_one
  have hsub : (B ∩ frontier C) ×ˢ Icc (0 : ℝ) 1 ⊆
      frontier C ×ˢ Icc (0 : ℝ) 2 :=
    prod_mono inter_subset_right (fun _ ht => ⟨ht.1, ht.2.trans (by norm_num)⟩)
  have hcR := hc.restrict (hβ.isPolyhedron.prod hI.isPolyhedron) hsub
  have hR : IsPLBall 2 (c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 1)) :=
    (isPLBall_two_prod hβ hI).of_isPLHomeomorphOn hcR
  have hRB : c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 1) ⊆ B := by
    apply Subset.trans _ (htrace.symm.subset.trans inter_subset_left)
    exact image_mono (prod_mono subset_rfl
      (fun _ ht => ⟨ht.1, ht.2.trans (by norm_num)⟩))
  have hβR : B ∩ frontier C ⊆ c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx
    exact ⟨(x, 0), ⟨hx, by norm_num⟩, hc0 x hx.2⟩
  exact h.exists_isPLHomeomorphOn_to_subdisk hC hR hRB hβR

end DifferentialGeometry.Topology.PiecewiseLinear
