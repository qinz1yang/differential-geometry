/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProduct
import Mathlib.Geometry.Manifold.Instances.Quotient

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def halfTurnTranslation (n : ℤ) (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  ((p.1.1 + n, (-1 : ℝ) ^ n * p.1.2), (-1 : ℝ) ^ n * (p.2 - 1 / 2) + 1 / 2)

theorem halfTurnTranslation_zero (p : (ℝ × ℝ) × ℝ) : halfTurnTranslation 0 p = p := by
  ext <;> simp [halfTurnTranslation]

theorem halfTurnTranslation_add (m n : ℤ) (p : (ℝ × ℝ) × ℝ) :
    halfTurnTranslation (m + n) p = halfTurnTranslation m (halfTurnTranslation n p) := by
  have hpow : (-1 : ℝ) ^ (m + n) = (-1 : ℝ) ^ m * (-1 : ℝ) ^ n :=
    zpow_add₀ (by norm_num) _ _
  ext <;> simp only [halfTurnTranslation, Int.cast_add, hpow] <;> ring

theorem continuous_halfTurnTranslation (n : ℤ) : Continuous (halfTurnTranslation n) := by
  unfold halfTurnTranslation
  fun_prop

noncomputable def halfTurnTranslationHomeomorph (n : ℤ) :
    ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) where
  toFun := halfTurnTranslation n
  invFun := halfTurnTranslation (-n)
  left_inv p := by rw [← halfTurnTranslation_add, neg_add_cancel, halfTurnTranslation_zero]
  right_inv p := by rw [← halfTurnTranslation_add, add_neg_cancel, halfTurnTranslation_zero]
  continuous_toFun := continuous_halfTurnTranslation n
  continuous_invFun := continuous_halfTurnTranslation (-n)

def halfTurnSetoid : Setoid ((ℝ × ℝ) × ℝ) where
  r p q := ∃ n : ℤ, q = halfTurnTranslation n p
  iseqv := {
    refl := fun p => ⟨0, (halfTurnTranslation_zero p).symm⟩
    symm := by
      rintro p q ⟨n, rfl⟩
      exact ⟨-n, by rw [← halfTurnTranslation_add, neg_add_cancel, halfTurnTranslation_zero]⟩
    trans := by
      rintro p q z ⟨m, rfl⟩ ⟨n, rfl⟩
      exact ⟨n + m, (halfTurnTranslation_add n m p).symm⟩ }

abbrev halfTurnQuotient := Quotient halfTurnSetoid

def halfTurnProjection : ((ℝ × ℝ) × ℝ) → halfTurnQuotient := Quotient.mk halfTurnSetoid

theorem halfTurnProjection_eq_iff {p q : (ℝ × ℝ) × ℝ} :
    halfTurnProjection p = halfTurnProjection q ↔ ∃ n : ℤ, q = halfTurnTranslation n p :=
  Quotient.eq

theorem halfTurnProjection_translation (n : ℤ) (p : (ℝ × ℝ) × ℝ) :
    halfTurnProjection (halfTurnTranslation n p) = halfTurnProjection p :=
  (halfTurnProjection_eq_iff.mpr ⟨n, rfl⟩).symm

theorem continuous_halfTurnProjection : Continuous halfTurnProjection :=
  continuous_quotient_mk'

theorem surjective_halfTurnProjection : Function.Surjective halfTurnProjection :=
  Quotient.mk_surjective

theorem isOpenMap_halfTurnProjection : IsOpenMap halfTurnProjection := by
  intro U hU
  apply (isQuotientMap_quotient_mk' (s := halfTurnSetoid)).isOpen_preimage.mp
  have heq : halfTurnProjection ⁻¹' (halfTurnProjection '' U) =
      ⋃ n : ℤ, halfTurnTranslation n '' U := by
    ext p
    constructor
    · rintro ⟨q, hq, heq⟩
      obtain ⟨n, rfl⟩ := halfTurnProjection_eq_iff.mp heq
      exact mem_iUnion.mpr ⟨n, q, hq, rfl⟩
    · rintro hp
      obtain ⟨n, q, hq, rfl⟩ := mem_iUnion.mp hp
      exact ⟨q, hq, (halfTurnProjection_translation n q).symm⟩
  change IsOpen (halfTurnProjection ⁻¹' (halfTurnProjection '' U))
  rw [heq]
  exact isOpen_iUnion fun n => (halfTurnTranslationHomeomorph n).isOpenMap _ hU

theorem halfTurnProjection_injOn_slab (a : ℝ) :
    InjOn halfTurnProjection {p | p.1.1 ∈ Ioo (a - 1 / 4) (a + 1 / 4)} := by
  intro p hp q hq hpq
  obtain ⟨n, hn⟩ := halfTurnProjection_eq_iff.mp hpq
  have hx := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hn
  change q.1.1 = p.1.1 + (n : ℝ) at hx
  have hnlo : (-1 : ℝ) < n := by linarith [hp.1, hq.2, hp.2, hq.1]
  have hnhi : (n : ℝ) < 1 := by linarith [hp.1, hq.2, hp.2, hq.1]
  have hn0 : n = 0 := by
    have hlo : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have hhi : n < 1 := by exact_mod_cast hnhi
    omega
  rw [hn0, halfTurnTranslation_zero] at hn
  exact hn.symm

theorem isLocalHomeomorph_halfTurnProjection : IsLocalHomeomorph halfTurnProjection := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro p
  let U : Set ((ℝ × ℝ) × ℝ) := {q | q.1.1 ∈ Ioo (p.1.1 - 1 / 4) (p.1.1 + 1 / 4)}
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_fst.comp continuous_fst)
  refine ⟨U, hU.mem_nhds ⟨by linarith, by linarith⟩, ?_⟩
  exact isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨continuous_halfTurnProjection.comp continuous_subtype_val,
      injOn_iff_injective.mp (halfTurnProjection_injOn_slab p.1.1),
      isOpenMap_halfTurnProjection.comp hU.isOpenMap_subtype_val⟩

noncomputable def twistedStripMap (p : ℝ × ℝ) : halfTurnQuotient :=
  halfTurnProjection ((p.1, p.1 - 1 / 2), p.2)

theorem continuous_twistedStripMap : Continuous twistedStripMap :=
  continuous_halfTurnProjection.comp (by fun_prop)

theorem twistedStripMap_seam (t : ℝ) : twistedStripMap (0, t) = twistedStripMap (1, 1 - t) := by
  apply halfTurnProjection_eq_iff.mpr
  refine ⟨1, ?_⟩
  ext <;> norm_num [halfTurnTranslation]
  ring

theorem twistedStripMap_eq_iff {p q : ℝ × ℝ}
    (hp : p.1 ∈ Icc (-1 / 4 : ℝ) (5 / 4))
    (hq : q.1 ∈ Icc (-1 / 4 : ℝ) (5 / 4)) :
    twistedStripMap p = twistedStripMap q ↔ p = q ∨
      (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = 1 - p.2) ∨
      (p.1 = 1 ∧ q.1 = 0 ∧ q.2 = 1 - p.2) := by
  constructor
  · intro heq
    obtain ⟨n, hn⟩ := halfTurnProjection_eq_iff.mp heq
    have hx := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hn
    have hy := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.2) hn
    have hz := congrArg Prod.snd hn
    change q.1 = p.1 + (n : ℝ) at hx
    change q.1 - 1 / 2 = (-1 : ℝ) ^ n * (p.1 - 1 / 2) at hy
    change q.2 = (-1 : ℝ) ^ n * (p.2 - 1 / 2) + 1 / 2 at hz
    have hnlo : (-2 : ℤ) < n := by
      have hh : (-2 : ℝ) < n := by linarith [hp.1, hp.2, hq.1, hq.2]
      exact_mod_cast hh
    have hnhi : n < 2 := by
      have hh : (n : ℝ) < 2 := by linarith [hp.1, hp.2, hq.1, hq.2]
      exact_mod_cast hh
    interval_cases n
    · norm_num at hx hy hz
      exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)
    · norm_num at hx hy hz
      exact Or.inl (Prod.ext hx.symm hz.symm)
    · norm_num at hx hy hz
      exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · rintro (rfl | ⟨hp, hq, hqt⟩ | ⟨hp, hq, hqt⟩)
    · rfl
    · apply halfTurnProjection_eq_iff.mpr
      refine ⟨1, ?_⟩
      ext <;> simp [halfTurnTranslation, hp, hq, hqt] <;> ring
    · apply halfTurnProjection_eq_iff.mpr
      refine ⟨-1, ?_⟩
      ext <;> simp [halfTurnTranslation, hp, hq, hqt] <;> ring

def twistedSourceRect : Set (ℝ × ℝ) := Icc (-1 / 4 : ℝ) (5 / 4) ×ˢ Icc (0 : ℝ) 1

theorem twistedStripMap_fiber_le_two (y : halfTurnQuotient) :
    (twistedSourceRect ∩ twistedStripMap ⁻¹' {y}).encard ≤ 2 := by
  by_cases h : (twistedSourceRect ∩ twistedStripMap ⁻¹' {y}).Nonempty
  · obtain ⟨p, hp⟩ := h
    have hsub : twistedSourceRect ∩ twistedStripMap ⁻¹' {y} ⊆ {p, (1 - p.1, 1 - p.2)} := by
      rintro q ⟨hq, hqy⟩
      rcases (twistedStripMap_eq_iff hp.1.1 hq.1).mp (hp.2.trans hqy.symm) with
        heq | ⟨hp0, hq1, hqt⟩ | ⟨hp1, hq0, hqt⟩
      · exact Or.inl heq.symm
      · exact Or.inr (Prod.ext (by simp [hp0, hq1]) hqt)
      · exact Or.inr (Prod.ext (by simp [hp1, hq0]) hqt)
    apply (Set.encard_le_encard hsub).trans
    by_cases heq : p = (1 - p.1, 1 - p.2)
    · have hpair : ({p, (1 - p.1, 1 - p.2)} : Set (ℝ × ℝ)) = {p} := by
        rw [← heq]
        exact Set.pair_eq_singleton p
      rw [hpair, Set.encard_singleton]
      norm_num
    · exact (Set.encard_pair heq).le
  · simp only [not_nonempty_iff_eq_empty] at h
    simp [h]

theorem twistedStripMap_injOn_slab (s : ℝ) :
    InjOn twistedStripMap (Prod.fst ⁻¹' Ioo (s - 1 / 4) (s + 1 / 4)) := by
  intro p hp q hq heq
  have h := halfTurnProjection_injOn_slab s hp hq heq
  have hx : p.1 = q.1 := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) h
  have ht : p.2 = q.2 := congrArg (fun z : (ℝ × ℝ) × ℝ => z.2) h
  exact Prod.ext hx ht

theorem twistedStripMap_not_injOn : ¬ InjOn twistedStripMap twistedSourceRect := by
  intro hinj
  have h := hinj (x₁ := (0, 0)) (x₂ := (1, 1))
    (by norm_num [twistedSourceRect]) (by norm_num [twistedSourceRect])
    (by simpa using twistedStripMap_seam 0)
  exact (by norm_num : (0 : ℝ) ≠ 1) (congrArg Prod.fst h)

end DifferentialGeometry.Topology.PiecewiseLinear
