/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate

open Set Topology Metric
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPL_homeomorph_moves_point_dist_lt_eqOn
    {n : ℕ} (hn : 0 < n) {X : Type*} [MetricSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [HasGroupoid X (plGroupoid n)]
    {F U : Set X} (hF : IsClosed F) (hU : IsOpen U) {p : X}
    (hpU : p ∈ U) (hpF : p ∉ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ (C : Set X) (h : X ≃ₜ X),
      IsCompact C ∧ C ⊆ U \ F ∧ IsPL n n h ∧ IsPL n n h.symm ∧ h p ≠ p ∧
        EqOn h id Cᶜ ∧ EqOn h id F ∧ EqOn h id Uᶜ ∧
          ∀ x, dist (h x) x < ε := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hep : p ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) p
  have he : e ∈ (plGroupoid n).maximalAtlas X :=
    StructureGroupoid.chart_mem_maximalAtlas (plGroupoid n) p
  let W := U \ F
  have hW : IsOpen W := hU.sdiff hF
  have hpW : p ∈ W := ⟨hpU, hpF⟩
  let V := e '' (e.source ∩ W)
  have hV : IsOpen V := e.isOpen_image_source_inter hW
  have hepV : e p ∈ V := ⟨p, ⟨hep, hpW⟩, rfl⟩
  have hVt : V ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source hx.1
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV (e p) hepV
  let C₀ := Metric.closedBall (e p) (R / 2)
  have hC₀V : C₀ ⊆ V := by
    intro y hy
    apply hRV
    exact Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hy).trans_lt (half_lt_self hR))
  have hC₀t : C₀ ⊆ e.target := hC₀V.trans hVt
  have hC₀ : IsCompact C₀ := isCompact_closedBall _ _
  let C := e.symm '' C₀
  have hC : IsCompact C :=
    hC₀.image_of_continuousOn (e.continuousOn_symm.mono hC₀t)
  have hCW : C ⊆ W := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hC₀V hy
    have heq : e.symm y = z := by
      rw [← hzy, e.left_inv hz.1]
    rw [heq]
    exact hz.2
  obtain ⟨δ, hδ, hδbound⟩ := e.exists_uniform_conjugateMap_radius hC₀ hC₀t hε
  let η := min δ R
  have hη : 0 < η := lt_min hδ hR
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k, hk, hkmove, hkfix, hkclose⟩ :=
    exists_isPLHomeomorphOn_moves_point_dist_lt (p := e p) hη
  have hballC₀ : Metric.ball (e p) (η / 4) ⊆ C₀ := by
    intro y hy
    apply Metric.mem_closedBall.mpr
    have hy' := Metric.mem_ball.mp hy
    have hηR : η ≤ R := min_le_right δ R
    linarith
  have hkC₀ : EqOn k id C₀ᶜ := by
    intro y hy
    apply hkfix
    exact fun hyball => hy (hballC₀ hyball)
  obtain ⟨hkmap, hclose⟩ := hδbound k
    (fun y _ => (hkclose y).trans_le (min_le_left δ R)) hkC₀
  let h := e.conjugateHomeomorph k hC₀ hC₀t hkC₀
  have hh : IsPL n n h :=
    isPL_conjugateHomeomorph e he k hk.isPiecewiseAffineOn hC₀ hC₀t hkC₀
  have hhmove : h p ≠ p := by
    intro hhp
    have hehp := congrArg e hhp
    change e (e.conjugateMap k p) = e p at hehp
    rw [e.conjugateMap_of_mem k hep, e.right_inv (hkmap (e.map_source hep))] at hehp
    exact hkmove hehp
  have hhfixC : EqOn h id Cᶜ := by
    intro x hx
    exact e.conjugateMap_eqOn_compl hkC₀ hx
  refine ⟨C, h, hC, hCW, hh, isPL_symm_of_homeomorph hh, hhmove, hhfixC, ?_, ?_, ?_⟩
  · intro x hxF
    apply hhfixC
    exact fun hxC => (hCW hxC).2 hxF
  · intro x hxU
    apply hhfixC
    exact fun hxC => hxU (hCW hxC).1
  · intro x
    exact hclose x

end DifferentialGeometry.Topology.PiecewiseLinear
