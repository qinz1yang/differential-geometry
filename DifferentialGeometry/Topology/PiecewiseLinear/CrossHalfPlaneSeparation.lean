/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfPlaneRectangle

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem crossHalfPlane_inter {i j : Fin 4} (hij : i ≠ j) :
    crossHalfPlane i ∩ crossHalfPlane j = {p : (ℝ × ℝ) × ℝ | p.1 = 0} := by
  ext p
  constructor
  · rintro ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩
    have h := hpa.symm.trans hpb
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have ha0 : a = 0 := by
      rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
        rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
        try exact (hij rfl).elim
      all_goals norm_num [fourSpokeModelLeaf] at h1 h2
      all_goals linarith
    change p.1 = 0
    rw [hpa, ha0, zero_smul]
  · intro hp
    exact ⟨⟨0, le_rfl, by rw [zero_smul]; exact hp⟩,
      ⟨0, le_rfl, by rw [zero_smul]; exact hp⟩⟩

private def transverseCoordinate (i : Fin 4) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  match i with
  | 0 => p.1.2
  | 1 => -p.1.1
  | 2 => -p.1.2
  | 3 => p.1.1

private theorem transverseCoordinate_zero_iff (i : Fin 4) (p : (ℝ × ℝ) × ℝ) :
    transverseCoordinate i p = 0 ↔ p ∈ crossHalfPlane i ∪ crossHalfPlane (i + 2) := by
  constructor
  · intro hzero
    let a : ℝ := (fourSpokeModelLeaf i).1 * p.1.1 + (fourSpokeModelLeaf i).2 * p.1.2
    have hpa : p.1 = a • fourSpokeModelLeaf i := by
      fin_cases i <;> apply Prod.ext <;>
        norm_num [a, transverseCoordinate, Fin.reduceAdd, fourSpokeModelLeaf] at hzero ⊢ <;>
        linarith
    by_cases ha : 0 ≤ a
    · exact Or.inl ⟨a, ha, hpa⟩
    · have hneg : (-a) • fourSpokeModelLeaf (i + 2) = a • fourSpokeModelLeaf i := by
        fin_cases i <;> ext <;> simp [fourSpokeModelLeaf]
      exact Or.inr ⟨-a, neg_nonneg.mpr (not_le.mp ha).le, hpa.trans hneg.symm⟩
  · rintro (⟨a, -, hpa⟩ | ⟨a, -, hpa⟩) <;>
      simp only [transverseCoordinate, hpa] <;> fin_cases i <;> simp [fourSpokeModelLeaf]

private theorem transverseCoordinate_nonneg (i : Fin 4) {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ crossHalfPlane (i + 1)) : 0 ≤ transverseCoordinate i p := by
  obtain ⟨a, ha, hpa⟩ := hp
  simp only [transverseCoordinate, hpa]
  fin_cases i <;> simpa [fourSpokeModelLeaf] using ha

private theorem transverseCoordinate_nonpos (i : Fin 4) {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ crossHalfPlane (i + 3)) : transverseCoordinate i p ≤ 0 := by
  obtain ⟨a, ha, hpa⟩ := hp
  simp only [transverseCoordinate, hpa]
  fin_cases i <;> simpa [fourSpokeModelLeaf] using neg_nonpos.mpr ha

theorem crossHalfPlane_separated (i : Fin 4) {U : Set ((ℝ × ℝ) × ℝ)}
    (hU : U ⊆ (crossHalfPlane i ∪ crossHalfPlane (i + 2))ᶜ)
    (hconn : IsPreconnected U)
    (hpos : (U ∩ crossHalfPlane (i + 1)).Nonempty)
    (hneg : (U ∩ crossHalfPlane (i + 3)).Nonempty) : False := by
  have hcont : Continuous (transverseCoordinate i) := by
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
      unfold transverseCoordinate <;> fun_prop
  have hzero : ∀ p ∈ U, transverseCoordinate i p ≠ 0 :=
    fun p hp h => hU hp ((transverseCoordinate_zero_iff i p).mp h)
  obtain ⟨p, hpU, hp⟩ := hpos
  obtain ⟨q, hqU, hq⟩ := hneg
  have hp0 : 0 < transverseCoordinate i p :=
    lt_of_le_of_ne (transverseCoordinate_nonneg i hp) (hzero p hpU).symm
  have hq0 : transverseCoordinate i q < 0 :=
    lt_of_le_of_ne (transverseCoordinate_nonpos i hq) (hzero q hqU)
  have h0 : (0 : ℝ) ∈ transverseCoordinate i '' U :=
    (hconn.image (transverseCoordinate i) hcont.continuousOn).Icc_subset
      (mem_image_of_mem _ hqU) (mem_image_of_mem _ hpU) ⟨hq0.le, hp0.le⟩
  obtain ⟨z, hz, heq⟩ := h0
  exact hzero z hz heq

end DifferentialGeometry.Topology.PiecewiseLinear
