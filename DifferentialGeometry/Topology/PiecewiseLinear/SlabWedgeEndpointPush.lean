/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgePush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

def bufferedSlabWedgeHat (c ρ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  slabWedgeHat (c + 2 * ρ) (p + (ρ, 0, 0))

def positiveBufferedWedgePush (c ρ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  positiveWedgePush (c + 2 * ρ) (p + (ρ, 0, 0)) - (ρ, 0, 0)

def negativeBufferedWedgePush (c ρ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  negativeWedgePush (c + 2 * ρ) (p + (ρ, 0, 0)) - (ρ, 0, 0)

def bufferedSlabWedgeSupport (c ρ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  (fun p => p - (ρ, 0, 0)) '' slabWedgeSupport (c + 2 * ρ)

theorem bufferedSlabWedgeHat_left_endpoint {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) :
    bufferedSlabWedgeHat c ρ (0, 0, 0) = ρ / 4 := by
  rw [bufferedSlabWedgeHat]
  have hmem : ρ ∈ Icc (0 : ℝ) (c + 2 * ρ) := by constructor <;> linarith
  rw [show ((0 : ℝ), (0 : ℝ), (0 : ℝ)) + (ρ, (0 : ℝ), (0 : ℝ)) =
      (ρ, (0 : ℝ), (0 : ℝ)) by simp, slabWedgeHat_axis _ _ hmem]
  rw [min_eq_left]
  linarith

theorem bufferedSlabWedgeHat_right_endpoint {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) :
    bufferedSlabWedgeHat c ρ (c, 0, 0) = ρ / 4 := by
  rw [bufferedSlabWedgeHat]
  have hmem : c + ρ ∈ Icc (0 : ℝ) (c + 2 * ρ) := by constructor <;> linarith
  rw [show (c, (0 : ℝ), (0 : ℝ)) + (ρ, (0 : ℝ), (0 : ℝ)) =
      (c + ρ, (0 : ℝ), (0 : ℝ)) by simp,
    slabWedgeHat_axis _ _ hmem]
  rw [show c + 2 * ρ - (c + ρ) = ρ by ring, min_eq_right]
  linarith

theorem isCompact_bufferedSlabWedgeSupport (c ρ : ℝ) :
    IsCompact (bufferedSlabWedgeSupport c ρ) := by
  exact (isCompact_slabWedgeSupport (c + 2 * ρ)).image
    (continuous_id.sub continuous_const)

theorem isPLHomeomorphOn_positiveBufferedWedgePush (c ρ : ℝ) :
    IsPLHomeomorphOn (positiveBufferedWedgePush c ρ) univ univ := by
  have h := ((isPLHomeomorphOn_add_const (ρ, (0 : ℝ), (0 : ℝ))).trans
    (isPLHomeomorphOn_positiveWedgePush (c + 2 * ρ))).trans
      (isPLHomeomorphOn_add_const (-(ρ, (0 : ℝ), (0 : ℝ))))
  refine h.congr fun p _ => ?_
  simp only [Function.comp_apply, positiveBufferedWedgePush, sub_eq_add_neg]

theorem isPLHomeomorphOn_negativeBufferedWedgePush (c ρ : ℝ) :
    IsPLHomeomorphOn (negativeBufferedWedgePush c ρ) univ univ := by
  have h := ((isPLHomeomorphOn_add_const (ρ, (0 : ℝ), (0 : ℝ))).trans
    (isPLHomeomorphOn_negativeWedgePush (c + 2 * ρ))).trans
      (isPLHomeomorphOn_add_const (-(ρ, (0 : ℝ), (0 : ℝ))))
  refine h.congr fun p _ => ?_
  simp only [Function.comp_apply, negativeBufferedWedgePush, sub_eq_add_neg]

noncomputable def positiveBufferedWedgePushHomeomorph (c ρ : ℝ) :
    (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
  (Homeomorph.Set.univ _).symm.trans
    ((isPLHomeomorphOn_positiveBufferedWedgePush c ρ).homeomorph.trans
      (Homeomorph.Set.univ _))

noncomputable def negativeBufferedWedgePushHomeomorph (c ρ : ℝ) :
    (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
  (Homeomorph.Set.univ _).symm.trans
    ((isPLHomeomorphOn_negativeBufferedWedgePush c ρ).homeomorph.trans
      (Homeomorph.Set.univ _))

@[simp]
theorem positiveBufferedWedgePushHomeomorph_apply (c ρ : ℝ) (p : ℝ × ℝ × ℝ) :
    positiveBufferedWedgePushHomeomorph c ρ p = positiveBufferedWedgePush c ρ p := rfl

@[simp]
theorem negativeBufferedWedgePushHomeomorph_apply (c ρ : ℝ) (p : ℝ × ℝ × ℝ) :
    negativeBufferedWedgePushHomeomorph c ρ p = negativeBufferedWedgePush c ρ p := rfl

theorem eqOn_positiveBufferedWedgePush_id_compl_support (c ρ : ℝ) :
    EqOn (positiveBufferedWedgePush c ρ) id (bufferedSlabWedgeSupport c ρ)ᶜ := by
  intro p hp
  have hnot : p + (ρ, 0, 0) ∉ slabWedgeSupport (c + 2 * ρ) := by
    intro hmem
    apply hp
    refine ⟨p + (ρ, 0, 0), hmem, ?_⟩
    simp
  rw [positiveBufferedWedgePush,
    eqOn_positiveWedgePush_id_compl_support (c + 2 * ρ) hnot]
  simp

theorem eqOn_negativeBufferedWedgePush_id_compl_support (c ρ : ℝ) :
    EqOn (negativeBufferedWedgePush c ρ) id (bufferedSlabWedgeSupport c ρ)ᶜ := by
  intro p hp
  have hnot : p + (ρ, 0, 0) ∉ slabWedgeSupport (c + 2 * ρ) := by
    intro hmem
    apply hp
    refine ⟨p + (ρ, 0, 0), hmem, ?_⟩
    simp
  rw [negativeBufferedWedgePush,
    eqOn_negativeWedgePush_id_compl_support (c + 2 * ρ) hnot]
  simp

@[simp]
theorem positiveBufferedWedgePush_fst (c ρ : ℝ) (p : ℝ × ℝ × ℝ) :
    (positiveBufferedWedgePush c ρ p).1 = p.1 := by
  simp [positiveBufferedWedgePush]

@[simp]
theorem negativeBufferedWedgePush_fst (c ρ : ℝ) (p : ℝ × ℝ × ℝ) :
    (negativeBufferedWedgePush c ρ p).1 = p.1 := by
  simp [negativeBufferedWedgePush]

theorem image_positiveBufferedWedgePush_fstFiber (c ρ a : ℝ) :
    positiveBufferedWedgePush c ρ '' {p : ℝ × ℝ × ℝ | p.1 = a} =
      {p : ℝ × ℝ × ℝ | p.1 = a} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [mem_ofPred_eq, positiveBufferedWedgePush_fst] using hp
  · intro p hp
    obtain ⟨q, _, hq⟩ :=
      (isPLHomeomorphOn_positiveBufferedWedgePush c ρ).bijOn.surjOn (mem_univ p)
    refine ⟨q, ?_, hq⟩
    have hfst := congrArg (fun z : ℝ × ℝ × ℝ => z.1) hq
    simpa only [mem_ofPred_eq, positiveBufferedWedgePush_fst] using hfst.trans hp

theorem image_negativeBufferedWedgePush_fstFiber (c ρ a : ℝ) :
    negativeBufferedWedgePush c ρ '' {p : ℝ × ℝ × ℝ | p.1 = a} =
      {p : ℝ × ℝ × ℝ | p.1 = a} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [mem_ofPred_eq, negativeBufferedWedgePush_fst] using hp
  · intro p hp
    obtain ⟨q, _, hq⟩ :=
      (isPLHomeomorphOn_negativeBufferedWedgePush c ρ).bijOn.surjOn (mem_univ p)
    refine ⟨q, ?_, hq⟩
    have hfst := congrArg (fun z : ℝ × ℝ × ℝ => z.1) hq
    simpa only [mem_ofPred_eq, negativeBufferedWedgePush_fst] using hfst.trans hp

theorem image_positiveBufferedWedgePush_wedgeSlabBoundary (c ρ : ℝ) :
    positiveBufferedWedgePush c ρ '' wedgeSlabBoundary c = wedgeSlabBoundary c := by
  change positiveBufferedWedgePush c ρ ''
      ({p : ℝ × ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ × ℝ | p.1 = c}) =
    {p : ℝ × ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ × ℝ | p.1 = c}
  rw [image_union]
  exact congrArg₂ (· ∪ ·) (image_positiveBufferedWedgePush_fstFiber c ρ 0)
    (image_positiveBufferedWedgePush_fstFiber c ρ c)

theorem image_negativeBufferedWedgePush_wedgeSlabBoundary (c ρ : ℝ) :
    negativeBufferedWedgePush c ρ '' wedgeSlabBoundary c = wedgeSlabBoundary c := by
  change negativeBufferedWedgePush c ρ ''
      ({p : ℝ × ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ × ℝ | p.1 = c}) =
    {p : ℝ × ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ × ℝ | p.1 = c}
  rw [image_union]
  exact congrArg₂ (· ∪ ·) (image_negativeBufferedWedgePush_fstFiber c ρ 0)
    (image_negativeBufferedWedgePush_fstFiber c ρ c)

theorem disjoint_positive_negative_bufferedWedgePush_on_slabFold {c ρ : ℝ}
    (hρ : 0 < ρ) :
    Disjoint (positiveBufferedWedgePush c ρ '' positiveSlabFold c)
      (negativeBufferedWedgePush c ρ '' negativeSlabFold c) := by
  rw [Set.disjoint_left]
  rintro w ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
  have hp' : p + (ρ, 0, 0) ∈
      positiveSlabFold (c + 2 * ρ) ∩ wedgeSlabInterior (c + 2 * ρ) := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change 0 ≤ (p + (ρ, 0, 0)).1 ∧
          (p + (ρ, 0, 0)).1 ≤ c + 2 * ρ
        change 0 ≤ p.1 + ρ ∧ p.1 + ρ ≤ c + 2 * ρ
        exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      · simpa using hp.2
    · change 0 < (p + (ρ, 0, 0)).1 ∧
        (p + (ρ, 0, 0)).1 < c + 2 * ρ
      change 0 < p.1 + ρ ∧ p.1 + ρ < c + 2 * ρ
      exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  have hq' : q + (ρ, 0, 0) ∈
      negativeSlabFold (c + 2 * ρ) ∩ wedgeSlabInterior (c + 2 * ρ) := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change 0 ≤ (q + (ρ, 0, 0)).1 ∧
          (q + (ρ, 0, 0)).1 ≤ c + 2 * ρ
        change 0 ≤ q.1 + ρ ∧ q.1 + ρ ≤ c + 2 * ρ
        exact ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
      · simpa using hq.2
    · change 0 < (q + (ρ, 0, 0)).1 ∧
        (q + (ρ, 0, 0)).1 < c + 2 * ρ
      change 0 < q.1 + ρ ∧ q.1 + ρ < c + 2 * ρ
      exact ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
  have heq : negativeWedgePush (c + 2 * ρ) (q + (ρ, 0, 0)) =
      positiveWedgePush (c + 2 * ρ) (p + (ρ, 0, 0)) := by
    rw [negativeBufferedWedgePush, positiveBufferedWedgePush] at hqp
    exact sub_left_inj.mp hqp
  exact Set.disjoint_left.mp disjoint_positive_negative_wedge_push_on_slabInterior
    ⟨p + (ρ, 0, 0), hp', rfl⟩
    ⟨q + (ρ, 0, 0), hq', heq⟩

end

end DifferentialGeometry.Topology.PiecewiseLinear
