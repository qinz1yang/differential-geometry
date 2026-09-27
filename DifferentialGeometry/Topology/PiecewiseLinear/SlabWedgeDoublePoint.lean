/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgePush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

def positiveWedgeTaggedSource (A : Set (ℝ × ℝ × ℝ)) : Set (Bool × (ℝ × ℝ × ℝ)) :=
  {true} ×ˢ A

def negativeWedgeTaggedSource (B : Set (ℝ × ℝ × ℝ)) : Set (Bool × (ℝ × ℝ × ℝ)) :=
  {false} ×ˢ B

def slabWedgeTaggedSource (A B : Set (ℝ × ℝ × ℝ)) : Set (Bool × (ℝ × ℝ × ℝ)) :=
  positiveWedgeTaggedSource A ∪ negativeWedgeTaggedSource B

def slabWedgeTaggedMap (c : ℝ) (p : Bool × (ℝ × ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  if p.1 then positiveWedgePush c p.2 else negativeWedgePush c p.2

theorem image_slabWedgeTaggedMap_positive (c : ℝ) (A : Set (ℝ × ℝ × ℝ)) :
    slabWedgeTaggedMap c '' positiveWedgeTaggedSource A = positiveWedgePush c '' A := by
  ext y
  constructor
  · rintro ⟨⟨b, p⟩, ⟨hb, hp⟩, rfl⟩
    have hb' : b = true := by simpa only [mem_singleton_iff] using hb
    subst b
    exact ⟨p, hp, by simp [slabWedgeTaggedMap]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(true, p), ⟨by simp, hp⟩,
      by simp [slabWedgeTaggedMap]⟩

theorem image_slabWedgeTaggedMap_negative (c : ℝ) (B : Set (ℝ × ℝ × ℝ)) :
    slabWedgeTaggedMap c '' negativeWedgeTaggedSource B = negativeWedgePush c '' B := by
  ext y
  constructor
  · rintro ⟨⟨b, p⟩, ⟨hb, hp⟩, rfl⟩
    have hb' : b = false := by simpa only [mem_singleton_iff] using hb
    subst b
    exact ⟨p, hp, by simp [slabWedgeTaggedMap]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(false, p), ⟨by simp, hp⟩,
      by simp [slabWedgeTaggedMap]⟩

theorem disjoint_positiveWedgeTaggedSource_negativeWedgeTaggedSource
    (A B : Set (ℝ × ℝ × ℝ)) :
    Disjoint (positiveWedgeTaggedSource A) (negativeWedgeTaggedSource B) := by
  rw [Set.disjoint_left]
  rintro ⟨b, p⟩ hp hn
  have hbt : b = true := by simpa only [mem_singleton_iff] using hp.1
  have hbf : b = false := by simpa only [mem_singleton_iff] using hn.1
  simp_all

theorem injOn_slabWedgeTaggedMap_positive (c : ℝ) (A : Set (ℝ × ℝ × ℝ)) :
    InjOn (slabWedgeTaggedMap c) (positiveWedgeTaggedSource A) := by
  rintro ⟨b, p⟩ hp ⟨d, q⟩ hq heq
  have hb : b = true := by simpa only [mem_singleton_iff] using hp.1
  have hd : d = true := by simpa only [mem_singleton_iff] using hq.1
  subst b
  subst d
  apply Prod.ext
  · rfl
  · apply (positiveWedgePushHomeomorph c).injective
    simpa [slabWedgeTaggedMap] using heq

theorem injOn_slabWedgeTaggedMap_negative (c : ℝ) (B : Set (ℝ × ℝ × ℝ)) :
    InjOn (slabWedgeTaggedMap c) (negativeWedgeTaggedSource B) := by
  rintro ⟨b, p⟩ hp ⟨d, q⟩ hq heq
  have hb : b = false := by simpa only [mem_singleton_iff] using hp.1
  have hd : d = false := by simpa only [mem_singleton_iff] using hq.1
  subst b
  subst d
  apply Prod.ext
  · rfl
  · apply (negativeWedgePushHomeomorph c).injective
    simpa [slabWedgeTaggedMap] using heq

theorem doublePointSet_slabWedgeTaggedMap (c : ℝ) (A B : Set (ℝ × ℝ × ℝ)) :
    doublePointSet (slabWedgeTaggedMap c) (slabWedgeTaggedSource A B) =
      positiveWedgePush c '' A ∩ negativeWedgePush c '' B := by
  ext y
  rw [mem_doublePointSet_iff_mem_image_inter_of_injOn
    (P := slabWedgeTaggedSource A B) (A := positiveWedgeTaggedSource A)
    (B := negativeWedgeTaggedSource B)
    (slabWedgeTaggedMap c) (by intro p hp; exact Or.inl hp) (by intro p hp; exact Or.inr hp)
    (disjoint_positiveWedgeTaggedSource_negativeWedgeTaggedSource A B)
    (injOn_slabWedgeTaggedMap_positive c A) (injOn_slabWedgeTaggedMap_negative c B)
    (fun _ h => h.1)]
  rw [image_slabWedgeTaggedMap_positive, image_slabWedgeTaggedMap_negative]

theorem doublePointSet_slabWedgeTaggedMap_closed {c : ℝ} (hc : 0 ≤ c) :
    doublePointSet (slabWedgeTaggedMap c)
        (slabWedgeTaggedSource (positiveSlabFold c) (negativeSlabFold c)) =
      {(0, 0, 0), (c, 0, 0)} := by
  rw [doublePointSet_slabWedgeTaggedMap, image_positiveSlabFold_inter_image_negativeSlabFold hc]

theorem doublePointSet_slabWedgeTaggedMap_open (c : ℝ) :
    doublePointSet (slabWedgeTaggedMap c)
        (slabWedgeTaggedSource (positiveSlabFold c ∩ wedgeSlabInterior c)
          (negativeSlabFold c ∩ wedgeSlabInterior c)) = ∅ := by
  rw [doublePointSet_slabWedgeTaggedMap]
  exact Set.disjoint_iff_inter_eq_empty.mp disjoint_positive_negative_wedge_push_on_slabInterior

end

end DifferentialGeometry.Topology.PiecewiseLinear
