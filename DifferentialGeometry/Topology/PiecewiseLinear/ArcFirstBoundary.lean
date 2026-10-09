/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_initial_subarc_to_frontier
    {γ : ℝ → E} {P D : Set E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) P)
    (hD : IsClosed D) (h0 : γ 0 ∈ interior D) (h1 : γ 1 ∉ interior D) :
    ∃ (R : Set E) (δ : ℝ → E), IsPLHomeomorphOn δ (Icc 0 1) R ∧
      R ⊆ P ∩ D ∧ δ 0 = γ 0 ∧ δ 1 ∈ frontier D ∧
      R ∩ frontier D = {δ 1} := by
  have hc := hγ.isPiecewiseAffineOn.continuousOn
  have hT : IsCompact (Icc (0 : ℝ) 1 ∩ γ ⁻¹' (interior D)ᶜ) :=
    isCompact_Icc.of_isClosed_subset
      (hc.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl)
      inter_subset_left
  obtain ⟨t, ht, hmin⟩ := hT.exists_isLeast ⟨1, by norm_num, h1⟩
  have ht0 : 0 < t := lt_of_le_of_ne ht.1.1 fun heq => ht.2 (heq ▸ h0)
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.1.2
  have hbefore : ∀ u ∈ Ico (0 : ℝ) t, γ u ∈ interior D := by
    intro u hu
    by_contra h
    exact hu.2.not_ge (hmin ⟨⟨hu.1, hu.2.le.trans ht.1.2⟩, h⟩)
  have hclosed : IsClosed (Icc (0 : ℝ) t ∩ γ ⁻¹' D) :=
    (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hD
  have hinside : Icc (0 : ℝ) t ⊆ γ ⁻¹' D := by
    have hcl := closure_minimal
      (show Ico (0 : ℝ) t ⊆ Icc 0 t ∩ γ ⁻¹' D from fun u hu =>
        ⟨⟨hu.1, hu.2.le⟩, show γ u ∈ D from interior_subset (hbefore u hu)⟩) hclosed
    rw [closure_Ico ht0.ne] at hcl
    exact hcl.trans inter_subset_right
  have htfr : γ t ∈ frontier D := by
    rw [hD.frontier_eq]
    exact ⟨hinside ⟨ht0.le, le_rfl⟩, ht.2⟩
  let R := γ '' Icc (0 : ℝ) t
  have hR : IsPLHomeomorphOn γ (Icc 0 t) R :=
    hγ.restrict (isPLBall_Icc ht0).isPolyhedron hsub
  obtain ⟨φ, hφ, hφ0, hφ1⟩ :=
    exists_isPLHomeomorphOn_Icc_map_endpoints zero_lt_one ht0
  refine ⟨R, γ ∘ φ, hφ.trans hR, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨hγ.bijOn.mapsTo (hsub hu), hinside hu⟩
  · simp only [Function.comp_apply, hφ0]
  · simpa only [Function.comp_apply, hφ1] using htfr
  · simp only [Function.comp_apply, hφ1]
    apply Subset.antisymm
    · rintro _ ⟨⟨u, hu, rfl⟩, hufr⟩
      have hut : u = t := by
        by_contra hne
        exact hufr.2 (hbefore u ⟨hu.1, lt_of_le_of_ne hu.2 hne⟩)
      simp only [hut, mem_singleton_iff]
    · rintro _ rfl
      exact ⟨⟨t, ⟨ht0.le, le_rfl⟩, rfl⟩, htfr⟩

end DifferentialGeometry.Topology.PiecewiseLinear
