/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! # Section34Pierced Ball Frontiers -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem frontier_inter_signed_height_balls {E : Type*} [TopologicalSpace E]
    {P : Set E} (hP : IsClosed P) {g : E → ℝ} (hg : Continuous g)
    (hgb : ∀ x ∈ P, |g x| < 1) (hgfront : ∀ x ∈ frontier P, g x < 0) :
    frontier {y : E × ℝ | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1} ∩
      frontier {y : E × ℝ | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1} =
      {x | x ∈ P ∧ g x = 0} ×ˢ {(0 : ℝ)} := by
  let A : Set (E × ℝ) := {y | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1}
  let B : Set (E × ℝ) := {y | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1}
  have hAc : IsClosed A := (hP.preimage continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd (hg.comp continuous_fst)))
  have hBc : IsClosed B := (hP.preimage continuous_fst).inter
    ((isClosed_le (hg.neg.comp continuous_fst) continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))
  have hAo : IsOpen {y : E × ℝ | y.1 ∈ interior P ∧ -1 < y.2 ∧ y.2 < g y.1} :=
    (isOpen_interior.preimage continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd (hg.comp continuous_fst)))
  have hBo : IsOpen {y : E × ℝ | y.1 ∈ interior P ∧ -g y.1 < y.2 ∧ y.2 < 1} :=
    (isOpen_interior.preimage continuous_fst).inter
      ((isOpen_lt (hg.neg.comp continuous_fst) continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hAi : {y : E × ℝ | y.1 ∈ interior P ∧ -1 < y.2 ∧ y.2 < g y.1} ⊆ interior A :=
    interior_maximal (fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩) hAo
  have hBi : {y : E × ℝ | y.1 ∈ interior P ∧ -g y.1 < y.2 ∧ y.2 < 1} ⊆ interior B :=
    interior_maximal (fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩) hBo
  change frontier A ∩ frontier B = _
  ext y
  constructor
  · intro hy
    have hyA := hAc.frontier_subset hy.1
    have hyB := hBc.frontier_subset hy.2
    have hb := (abs_lt.mp (hgb y.1 hyA.1)).2
    have hgpos : 0 ≤ g y.1 := by linarith [hyA.2.2, hyB.2.1]
    have hyP : y.1 ∈ interior P := by
      by_contra hn
      have hneg := hgfront y.1 ⟨subset_closure hyA.1, hn⟩
      linarith
    have htop : y.2 = g y.1 := by
      apply le_antisymm hyA.2.2
      by_contra hn
      have hyint := hAi ⟨hyP, by linarith [hyB.2.1], lt_of_not_ge hn⟩
      exact hy.1.2 hyint
    have hbottom : -g y.1 = y.2 := by
      apply le_antisymm hyB.2.1
      by_contra hn
      have hyint := hBi ⟨hyP, lt_of_not_ge hn, by linarith [hyA.2.2]⟩
      exact hy.2.2 hyint
    exact ⟨⟨hyA.1, by linarith⟩, by change y.2 = 0; linarith⟩
  · rintro ⟨⟨hyP, hyg⟩, hyzero⟩
    have hz : y.2 = 0 := hyzero
    have hv : Continuous (fun t : ℝ => (y.1, t)) := continuous_const.prodMk continuous_id
    have hnotA : y ∉ interior A := by
      intro hyA
      have hn : A ∈ 𝓝 (y.1, (0 : ℝ)) := by
        simpa only [← hz, Prod.eta] using mem_interior_iff_mem_nhds.mp hyA
      have hpre := hv.continuousAt.preimage_mem_nhds hn
      have hI : Iic (0 : ℝ) ∈ 𝓝 (0 : ℝ) := Filter.mem_of_superset hpre fun t ht => by
        change t ≤ 0
        simpa only [hyg] using ht.2.2
      have hm := mem_interior_iff_mem_nhds.mpr hI
      simp only [interior_Iic, mem_Iio, lt_self_iff_false] at hm
    have hnotB : y ∉ interior B := by
      intro hyB
      have hn : B ∈ 𝓝 (y.1, (0 : ℝ)) := by
        simpa only [← hz, Prod.eta] using mem_interior_iff_mem_nhds.mp hyB
      have hpre := hv.continuousAt.preimage_mem_nhds hn
      have hI : Ici (0 : ℝ) ∈ 𝓝 (0 : ℝ) := Filter.mem_of_superset hpre fun t ht => by
        change 0 ≤ t
        simpa only [hyg, neg_zero] using ht.2.1
      have hm := mem_interior_iff_mem_nhds.mpr hI
      simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at hm
    exact ⟨⟨subset_closure ⟨hyP, by linarith, by linarith⟩, hnotA⟩,
      ⟨subset_closure ⟨hyP, by linarith, by linarith⟩, hnotB⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
