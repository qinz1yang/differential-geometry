/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_small_homeomorph_finite_inter
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] {m n : ℕ}
    (hK : ∀ s ∈ K.faces, s.card ≤ m + 1) (hL : ∀ t ∈ L.faces, t.card ≤ n + 1)
    (hdim : m + n ≤ Module.finrank ℝ E)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : E → E, IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧ (h '' K.space ∩ L.space).Finite := by
  obtain ⟨h, G, hh, hsmall, hfix, hGfin, hGspace, hcard⟩ :=
    exists_small_homeomorph_inter_dimension_le K L hK hL hU hKU hε
  have hGfinite : G.space.Finite := by
    apply hGfin.biUnion
    intro s hs
    have hc := hcard s hs
    have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
    have hone : s.card = 1 := by omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hone
    simpa only [Finset.coe_singleton, convexHull_singleton] using finite_singleton x
  exact ⟨h, hh, hsmall, hfix, hGspace ▸ hGfinite⟩

end DifferentialGeometry.Topology.PiecewiseLinear
