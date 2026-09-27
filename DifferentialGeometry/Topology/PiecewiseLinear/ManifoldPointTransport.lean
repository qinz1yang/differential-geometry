/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_local_supported_point_transport {n : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [HasGroupoid X (plGroupoid n)] {U : Set X} (hU : IsOpen U) {p : X} (hp : p ∈ U) :
    ∃ V C : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ IsCompact C ∧ C ⊆ U ∧
      ∀ q ∈ V, ∃ φ : X ≃ₜ X, IsPL n n φ ∧ EqOn φ id Cᶜ ∧ φ p = q := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hep : p ∈ e.source := mem_chart_source _ p
  have he : e ∈ (plGroupoid n).maximalAtlas X :=
    StructureGroupoid.chart_mem_maximalAtlas _ p
  have hO : IsOpen (e '' (e.source ∩ U)) := e.isOpen_image_source_inter hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO (e p) ⟨p, ⟨hep, hp⟩, rfl⟩
  let C₀ := Metric.closedBall (e p) (r / 2)
  have hC₀ : IsCompact C₀ := isCompact_closedBall _ _
  have hC₀O : C₀ ⊆ e '' (e.source ∩ U) := by
    intro z hz
    exact hball (Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hr)))
  have hC₀t : C₀ ⊆ e.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hC₀O hz
    exact e.map_source hx.1
  let C := e.symm '' C₀
  have hC : IsCompact C := hC₀.image_of_continuousOn (e.continuousOn_symm.mono hC₀t)
  have hCU : C ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hC₀O hz
    rw [e.left_inv hy.1]
    exact hy.2
  obtain ⟨δ, hδ, hmove⟩ := exists_isPLHomeomorphOn_small_point_move (p := e p)
    Metric.isOpen_ball (Metric.mem_ball_self (half_pos hr))
  let V := (e.source ∩ e ⁻¹' Metric.ball (e p) δ) ∩ U
  have hV : IsOpen V := (e.isOpen_inter_preimage Metric.isOpen_ball).inter hU
  refine ⟨V, C, hV, ⟨⟨hep, Metric.mem_ball_self hδ⟩, hp⟩, inter_subset_right, hC, hCU, ?_⟩
  intro q hq
  obtain ⟨k, hk, hkfix, hkp⟩ := hmove (e q) (Metric.mem_ball.mp hq.1.2)
  have hkC₀ : EqOn k id C₀ᶜ := fun z hz => hkfix fun hzb => hz (Metric.ball_subset_closedBall hzb)
  let φ := e.conjugateHomeomorph k hC₀ hC₀t hkC₀
  refine ⟨φ, isPL_conjugateHomeomorph e he k hk.isPiecewiseAffineOn hC₀ hC₀t hkC₀,
    e.conjugateMap_eqOn_compl hkC₀, ?_⟩
  change e.conjugateMap k p = q
  rw [e.conjugateMap_of_mem k hep, hkp, e.left_inv hq.1.1]

theorem exists_isPL_homeomorph_map_point_eqOn_compl {n : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [HasGroupoid X (plGroupoid n)] {U : Set X} (hU : IsOpen U) (hc : IsPreconnected U)
    {p q : X} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ (C : Set X) (φ : X ≃ₜ X), IsCompact C ∧ C ⊆ U ∧ IsPL n n φ ∧
      IsPL n n φ.symm ∧ EqOn φ id Cᶜ ∧ φ p = q := by
  let A : Set X := {x | x ∈ U ∧ ∃ (C : Set X) (φ : X ≃ₜ X),
    IsCompact C ∧ C ⊆ U ∧ IsPL n n φ ∧ EqOn φ id Cᶜ ∧ φ p = x}
  have hA : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hx, C, φ, hC, hCU, hφ, hfix, hφp⟩
    obtain ⟨V, D, hV, hxV, hVU, hD, hDU, hmove⟩ :=
      exists_local_supported_point_transport (n := n) hU hx
    apply Filter.mem_of_superset (hV.mem_nhds hxV)
    intro y hy
    obtain ⟨ψ, hψ, hψfix, hψx⟩ := hmove y hy
    refine ⟨hVU hy, C ∪ D, φ.trans ψ, hC.union hD, union_subset hCU hDU, hψ.comp hφ, ?_, ?_⟩
    · intro z hz
      exact (congrArg ψ (hfix fun hzC => hz (Or.inl hzC))).trans
        (hψfix fun hzD => hz (Or.inr hzD))
    · exact (congrArg ψ hφp).trans hψx
  have hB : IsOpen (U \ A) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hxU, hxA⟩
    obtain ⟨V, D, hV, hxV, hVU, hD, hDU, hmove⟩ :=
      exists_local_supported_point_transport (n := n) hU hxU
    apply Filter.mem_of_superset (hV.mem_nhds hxV)
    intro y hy
    refine ⟨hVU hy, ?_⟩
    rintro ⟨-, C, φ, hC, hCU, hφ, hfix, hφp⟩
    obtain ⟨ψ, hψ, hψfix, hψx⟩ := hmove y hy
    have hψifix : EqOn ψ.symm id Dᶜ := fun z hz => ψ.symm_apply_eq.mpr (hψfix hz).symm
    apply hxA
    refine ⟨hxU, C ∪ D, φ.trans ψ.symm, hC.union hD, union_subset hCU hDU,
      (isPL_symm_of_homeomorph hψ).comp hφ, ?_, ?_⟩
    · intro z hz
      exact (congrArg ψ.symm (hfix fun hzC => hz (Or.inl hzC))).trans
        (hψifix fun hzD => hz (Or.inr hzD))
    · exact (congrArg ψ.symm hφp).trans (ψ.symm_apply_eq.mpr hψx.symm)
  have hpA : p ∈ A :=
    ⟨hp, ∅, Homeomorph.refl X, isCompact_empty, empty_subset U, isPL_id, fun _ _ => rfl, rfl⟩
  have hUA : U ⊆ A := hc.subset_left_of_subset_union hA hB disjoint_sdiff_right
    (fun x hx => by
      by_cases h : x ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩) ⟨p, hp, hpA⟩
  obtain ⟨C, φ, hC, hCU, hφ, hfix, hφp⟩ := (hUA hq).2
  exact ⟨C, φ, hC, hCU, hφ, isPL_symm_of_homeomorph hφ, hfix, hφp⟩

end DifferentialGeometry.Topology.PiecewiseLinear
