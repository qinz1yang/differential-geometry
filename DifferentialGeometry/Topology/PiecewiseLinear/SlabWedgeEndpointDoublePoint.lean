/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgeDoublePoint
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgeEndpointPush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

def bufferedSlabWedgeTaggedMap (c ρ : ℝ) (p : Bool × (ℝ × ℝ × ℝ)) :
    ℝ × ℝ × ℝ :=
  if p.1 then positiveBufferedWedgePush c ρ p.2 else negativeBufferedWedgePush c ρ p.2

theorem image_bufferedSlabWedgeTaggedMap_positive (c ρ : ℝ) (A : Set (ℝ × ℝ × ℝ)) :
    bufferedSlabWedgeTaggedMap c ρ '' positiveWedgeTaggedSource A =
      positiveBufferedWedgePush c ρ '' A := by
  ext y
  constructor
  · rintro ⟨⟨b, p⟩, ⟨hb, hp⟩, rfl⟩
    have hb' : b = true := by simpa only [mem_singleton_iff] using hb
    subst b
    exact ⟨p, hp, by simp [bufferedSlabWedgeTaggedMap]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(true, p), ⟨by simp, hp⟩, by simp [bufferedSlabWedgeTaggedMap]⟩

theorem image_bufferedSlabWedgeTaggedMap_negative (c ρ : ℝ) (B : Set (ℝ × ℝ × ℝ)) :
    bufferedSlabWedgeTaggedMap c ρ '' negativeWedgeTaggedSource B =
      negativeBufferedWedgePush c ρ '' B := by
  ext y
  constructor
  · rintro ⟨⟨b, p⟩, ⟨hb, hp⟩, rfl⟩
    have hb' : b = false := by simpa only [mem_singleton_iff] using hb
    subst b
    exact ⟨p, hp, by simp [bufferedSlabWedgeTaggedMap]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(false, p), ⟨by simp, hp⟩, by simp [bufferedSlabWedgeTaggedMap]⟩

theorem injOn_bufferedSlabWedgeTaggedMap_positive (c ρ : ℝ)
    (A : Set (ℝ × ℝ × ℝ)) :
    InjOn (bufferedSlabWedgeTaggedMap c ρ) (positiveWedgeTaggedSource A) := by
  rintro ⟨b, p⟩ hp ⟨d, q⟩ hq heq
  have hb : b = true := by simpa only [mem_singleton_iff] using hp.1
  have hd : d = true := by simpa only [mem_singleton_iff] using hq.1
  subst b
  subst d
  apply Prod.ext
  · rfl
  · apply (positiveBufferedWedgePushHomeomorph c ρ).injective
    simpa [bufferedSlabWedgeTaggedMap] using heq

theorem injOn_bufferedSlabWedgeTaggedMap_negative (c ρ : ℝ)
    (B : Set (ℝ × ℝ × ℝ)) :
    InjOn (bufferedSlabWedgeTaggedMap c ρ) (negativeWedgeTaggedSource B) := by
  rintro ⟨b, p⟩ hp ⟨d, q⟩ hq heq
  have hb : b = false := by simpa only [mem_singleton_iff] using hp.1
  have hd : d = false := by simpa only [mem_singleton_iff] using hq.1
  subst b
  subst d
  apply Prod.ext
  · rfl
  · apply (negativeBufferedWedgePushHomeomorph c ρ).injective
    simpa [bufferedSlabWedgeTaggedMap] using heq

theorem doublePointSet_bufferedSlabWedgeTaggedMap (c ρ : ℝ)
    (A B : Set (ℝ × ℝ × ℝ)) :
    doublePointSet (bufferedSlabWedgeTaggedMap c ρ) (slabWedgeTaggedSource A B) =
      positiveBufferedWedgePush c ρ '' A ∩ negativeBufferedWedgePush c ρ '' B := by
  ext y
  rw [mem_doublePointSet_iff_mem_image_inter_of_injOn
    (P := slabWedgeTaggedSource A B) (A := positiveWedgeTaggedSource A)
    (B := negativeWedgeTaggedSource B)
    (bufferedSlabWedgeTaggedMap c ρ) (by intro p hp; exact Or.inl hp)
    (by intro p hp; exact Or.inr hp)
    (disjoint_positiveWedgeTaggedSource_negativeWedgeTaggedSource A B)
    (injOn_bufferedSlabWedgeTaggedMap_positive c ρ A)
    (injOn_bufferedSlabWedgeTaggedMap_negative c ρ B) (fun _ h => h.1)]
  rw [image_bufferedSlabWedgeTaggedMap_positive,
    image_bufferedSlabWedgeTaggedMap_negative]

theorem doublePointSet_bufferedSlabWedgeTaggedMap_closed {c ρ : ℝ} (hρ : 0 < ρ) :
    doublePointSet (bufferedSlabWedgeTaggedMap c ρ)
        (slabWedgeTaggedSource (positiveSlabFold c) (negativeSlabFold c)) = ∅ := by
  rw [doublePointSet_bufferedSlabWedgeTaggedMap]
  exact Set.disjoint_iff_inter_eq_empty.mp
    (disjoint_positive_negative_bufferedWedgePush_on_slabFold hρ)

end

end DifferentialGeometry.Topology.PiecewiseLinear
