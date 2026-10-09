/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

open Set Topology

theorem IsCompact.exists_isOpen_image_neighborhood_dist_lt
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {C : Set X} (hC : IsCompact C) {h : X → Y} (hh : ContinuousOn h C)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ C)
    (hsmall : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, dist (h y) (h z) < ψ x)
    {O : Set Y} (hO : IsOpen O) (hCO : h '' C ⊆ O) :
    ∃ Q : Set Y, IsOpen Q ∧ h '' C ⊆ Q ∧ Q ⊆ O ∧
      ∀ x ∈ C, ∀ y ∈ Q, ∀ z ∈ Q, dist y z < ψ x := by
  by_cases hne : C.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hC.exists_isMinOn hne hψ
    have hK : IsCompact (h '' C) := hC.image_of_continuousOn hh
    have hKne : (h '' C).Nonempty := hne.image h
    obtain ⟨p, hp, hmax⟩ := (hK.prod hK).exists_isMaxOn (hKne.prod hKne)
      (continuous_fst.dist continuous_snd).continuousOn
    obtain ⟨a, ha, hpa⟩ := hp.1
    obtain ⟨b, hb, hpb⟩ := hp.2
    have hgap : dist p.1 p.2 < ψ x₀ := by
      rw [← hpa, ← hpb]
      exact hsmall x₀ hx₀ a ha b hb
    let ε := (ψ x₀ - dist p.1 p.2) / 4
    have hε : 0 < ε := div_pos (sub_pos.mpr hgap) (by norm_num)
    let Q : Set Y := (⋃ a ∈ h '' C, Metric.ball a ε) ∩ O
    refine ⟨Q, (isOpen_biUnion fun _ _ => Metric.isOpen_ball).inter hO, ?_,
      inter_subset_right, ?_⟩
    · intro y hy
      exact ⟨mem_iUnion₂.mpr ⟨y, hy, Metric.mem_ball_self hε⟩, hCO hy⟩
    · intro x hx y hy z hz
      obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy.1
      obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.mp hz.1
      have hab : dist a b ≤ dist p.1 p.2 :=
        hmax (show (a, b) ∈ (h '' C) ×ˢ (h '' C) from ⟨ha, hb⟩)
      have hψx : ψ x₀ ≤ ψ x := hmin hx
      have hya' : dist y a < ε := hya
      have hzb' : dist z b < ε := hzb
      have htri := dist_triangle y a z
      have htri' := dist_triangle a b z
      rw [dist_comm b z] at htri'
      dsimp [ε] at hya' hzb'
      linarith
  · have hCempty : C = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, isOpen_empty, ?_, empty_subset _, ?_⟩
    · simp [hCempty]
    · intro x hx
      simp [hCempty] at hx
