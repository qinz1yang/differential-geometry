import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

namespace DifferentialGeometry.Topology

open Set _root_.Topology

noncomputable section

def intervalStretch (a b c d t : ℝ) : ℝ :=
  t + (c - b) * ((max a (min b t) - a) / (b - a) -
    (max b (min d t) - b) / (d - b))

@[simp]
theorem intervalStretch_self (a b d t : ℝ) : intervalStretch a b b d t = t := by
  simp [intervalStretch]

theorem intervalStretch_of_le_left {a b c d t : ℝ} (hab : a < b) (hbd : b < d)
    (ht : t ≤ a) : intervalStretch a b c d t = t := by
  simp [intervalStretch, min_eq_right (ht.trans hab.le),
    min_eq_right (ht.trans (hab.trans hbd).le), max_eq_left ht,
    max_eq_left (ht.trans hab.le)]

theorem intervalStretch_of_right_le {a b c d t : ℝ} (hab : a < b) (hbd : b < d)
    (ht : d ≤ t) : intervalStretch a b c d t = t := by
  simp [intervalStretch, min_eq_left (hbd.le.trans ht), min_eq_left ht,
    max_eq_right hab.le, max_eq_right hbd.le, sub_ne_zero.mpr hab.ne',
    sub_ne_zero.mpr hbd.ne']

theorem intervalStretch_of_mem_left {a b c d t : ℝ} (hab : a < b) (hbd : b < d)
    (ht : t ∈ Icc a b) :
    intervalStretch a b c d t = a + (c - a) / (b - a) * (t - a) := by
  simp only [intervalStretch, min_eq_right ht.2, max_eq_right ht.1,
    min_eq_right (ht.2.trans hbd.le), max_eq_left ht.2, sub_self, zero_div, sub_zero]
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

theorem intervalStretch_of_mem_right {a b c d t : ℝ} (hab : a < b) (hbd : b < d)
    (ht : t ∈ Icc b d) :
    intervalStretch a b c d t = c + (d - c) / (d - b) * (t - b) := by
  simp only [intervalStretch, min_eq_left ht.1, max_eq_right hab.le,
    min_eq_right ht.2, max_eq_right ht.1, div_self (sub_ne_zero.mpr hab.ne')]
  field_simp [sub_ne_zero.mpr hbd.ne']
  ring

@[simp]
theorem intervalStretch_at_left {a b c d : ℝ} (hab : a < b) (hbd : b < d) :
    intervalStretch a b c d a = a := intervalStretch_of_le_left hab hbd le_rfl

@[simp]
theorem intervalStretch_at_middle {a b c d : ℝ} (hab : a < b) (hbd : b < d) :
    intervalStretch a b c d b = c := by
  rw [intervalStretch_of_mem_left hab hbd ⟨hab.le, le_rfl⟩,
    div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
  ring

@[simp]
theorem intervalStretch_at_right {a b c d : ℝ} (hab : a < b) (hbd : b < d) :
    intervalStretch a b c d d = d := intervalStretch_of_right_le hab hbd le_rfl

theorem intervalStretch_mem_left {a b c d t : ℝ}
    (hab : a < b) (hbd : b < d) (hac : a < c) (ht : t ∈ Icc a b) :
    intervalStretch a b c d t ∈ Icc a c := by
  rw [intervalStretch_of_mem_left hab hbd ht]
  have hr : 0 ≤ (c - a) / (b - a) := (div_pos (sub_pos.mpr hac) (sub_pos.mpr hab)).le
  have hbound := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hr
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')] at hbound
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hr (sub_nonneg.mpr ht.1))
  · linarith

theorem intervalStretch_mem_right {a b c d t : ℝ}
    (hab : a < b) (hbd : b < d) (hcd : c < d) (ht : t ∈ Icc b d) :
    intervalStretch a b c d t ∈ Icc c d := by
  rw [intervalStretch_of_mem_right hab hbd ht]
  have hr : 0 ≤ (d - c) / (d - b) := (div_pos (sub_pos.mpr hcd) (sub_pos.mpr hbd)).le
  have hbound := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 b) hr
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hbd.ne')] at hbound
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hr (sub_nonneg.mpr ht.1))
  · linarith

theorem intervalStretch_inverse {a b c d : ℝ}
    (hab : a < b) (hbd : b < d) (hac : a < c) (hcd : c < d) (t : ℝ) :
    intervalStretch a c b d (intervalStretch a b c d t) = t := by
  by_cases hta : t ≤ a
  · rw [intervalStretch_of_le_left hab hbd hta, intervalStretch_of_le_left hac hcd hta]
  by_cases hdt : d ≤ t
  · rw [intervalStretch_of_right_le hab hbd hdt, intervalStretch_of_right_le hac hcd hdt]
  have hat : a ≤ t := le_of_lt (lt_of_not_ge hta)
  have htd : t ≤ d := le_of_lt (lt_of_not_ge hdt)
  rcases le_total t b with htb | hbt
  · rw [intervalStretch_of_mem_left hac hcd (intervalStretch_mem_left hab hbd hac ⟨hat, htb⟩),
      intervalStretch_of_mem_left hab hbd ⟨hat, htb⟩]
    field_simp [sub_ne_zero.mpr hab.ne', sub_ne_zero.mpr hac.ne']
    ring
  · rw [intervalStretch_of_mem_right hac hcd (intervalStretch_mem_right hab hbd hcd ⟨hbt, htd⟩),
      intervalStretch_of_mem_right hab hbd ⟨hbt, htd⟩]
    field_simp [sub_ne_zero.mpr hbd.ne', sub_ne_zero.mpr hcd.ne']
    ring

theorem continuous_intervalStretch {X : Type*} [TopologicalSpace X]
    {a b c d t : X → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) (ht : Continuous t)
    (hab : ∀ x, a x < b x) (hbd : ∀ x, b x < d x) :
    Continuous (fun x => intervalStretch (a x) (b x) (c x) (d x) (t x)) := by
  unfold intervalStretch
  have hleft := ((ha.max (hb.min ht)).sub ha).div (hb.sub ha)
    (fun x => sub_ne_zero.mpr (hab x).ne')
  have hright := ((hb.max (hd.min ht)).sub hb).div (hd.sub hb)
    (fun x => sub_ne_zero.mpr (hbd x).ne')
  exact ht.add ((hc.sub hb).mul (hleft.sub hright))

def intervalStretchHomeomorph {X : Type*} [TopologicalSpace X]
    (a b c d : X → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x < b x) (hbd : ∀ x, b x < d x)
    (hac : ∀ x, a x < c x) (hcd : ∀ x, c x < d x) : (X × ℝ) ≃ₜ (X × ℝ) where
  toFun p := (p.1, intervalStretch (a p.1) (b p.1) (c p.1) (d p.1) p.2)
  invFun p := (p.1, intervalStretch (a p.1) (c p.1) (b p.1) (d p.1) p.2)
  left_inv p := Prod.ext rfl (intervalStretch_inverse (hab p.1) (hbd p.1) (hac p.1) (hcd p.1) p.2)
  right_inv p := Prod.ext rfl (intervalStretch_inverse (hac p.1) (hcd p.1) (hab p.1) (hbd p.1) p.2)
  continuous_toFun := continuous_fst.prodMk (continuous_intervalStretch
    (ha.comp continuous_fst) (hb.comp continuous_fst) (hc.comp continuous_fst)
    (hd.comp continuous_fst) continuous_snd (fun p => hab p.1) (fun p => hbd p.1))
  continuous_invFun := continuous_fst.prodMk (continuous_intervalStretch
    (ha.comp continuous_fst) (hc.comp continuous_fst) (hb.comp continuous_fst)
    (hd.comp continuous_fst) continuous_snd (fun p => hac p.1) (fun p => hcd p.1))

section HomeomorphAPI

variable {X : Type*} [TopologicalSpace X]
    (a b c d : X → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x < b x) (hbd : ∀ x, b x < d x)
    (hac : ∀ x, a x < c x) (hcd : ∀ x, c x < d x)

@[simp]
theorem intervalStretchHomeomorph_fst (p : X × ℝ) :
    (intervalStretchHomeomorph a b c d ha hb hc hd hab hbd hac hcd p).1 = p.1 := rfl

@[simp]
theorem intervalStretchHomeomorph_snd (p : X × ℝ) :
    (intervalStretchHomeomorph a b c d ha hb hc hd hab hbd hac hcd p).2 =
      intervalStretch (a p.1) (b p.1) (c p.1) (d p.1) p.2 := rfl

@[simp]
theorem intervalStretchHomeomorph_symm :
    (intervalStretchHomeomorph a b c d ha hb hc hd hab hbd hac hcd).symm =
      intervalStretchHomeomorph a c b d ha hc hb hd hac hcd hab hbd := rfl

@[simp]
theorem intervalStretchHomeomorph_apply_middle (x : X) :
    intervalStretchHomeomorph a b c d ha hb hc hd hab hbd hac hcd (x, b x) = (x, c x) :=
  Prod.ext rfl (intervalStretch_at_middle (hab x) (hbd x))

theorem intervalStretchHomeomorph_apply_of_not_mem_Ioo (p : X × ℝ)
    (hp : p.2 ∉ Ioo (a p.1) (d p.1)) :
    intervalStretchHomeomorph a b c d ha hb hc hd hab hbd hac hcd p = p := by
  apply Prod.ext
  · rfl
  change intervalStretch (a p.1) (b p.1) (c p.1) (d p.1) p.2 = p.2
  by_cases hpa : p.2 ≤ a p.1
  · exact intervalStretch_of_le_left (hab p.1) (hbd p.1) hpa
  · exact intervalStretch_of_right_le (hab p.1) (hbd p.1)
      (le_of_not_gt (fun hpd => hp ⟨lt_of_not_ge hpa, hpd⟩))

end HomeomorphAPI

def intervalStretchMiddle {X : Type*} (b c : X → ℝ) (s : Icc (0 : ℝ) 1) (x : X) : ℝ :=
  (1 - (s : ℝ)) * b x + (s : ℝ) * c x

theorem intervalStretchMiddle_mem_Ioo {X : Type*} {a b c d : X → ℝ}
    (hab : ∀ x, a x < b x) (hbd : ∀ x, b x < d x)
    (hac : ∀ x, a x < c x) (hcd : ∀ x, c x < d x) (s : Icc (0 : ℝ) 1) (x : X) :
    intervalStretchMiddle b c s x ∈ Ioo (a x) (d x) := by
  exact (convex_Ioo (𝕜 := ℝ) (a x) (d x)) ⟨hab x, hbd x⟩ ⟨hac x, hcd x⟩
    (sub_nonneg.mpr s.2.2) s.2.1 (by ring)

theorem continuous_intervalStretchMiddle {X : Type*} [TopologicalSpace X]
    {b c : X → ℝ} (hb : Continuous b) (hc : Continuous c) (s : Icc (0 : ℝ) 1) :
    Continuous (intervalStretchMiddle b c s) :=
  (continuous_const.mul hb).add (continuous_const.mul hc)

def intervalStretchIsotopy {X : Type*} [TopologicalSpace X]
    (a b c d : X → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x < b x) (hbd : ∀ x, b x < d x)
    (hac : ∀ x, a x < c x) (hcd : ∀ x, c x < d x)
    (s : Icc (0 : ℝ) 1) : (X × ℝ) ≃ₜ (X × ℝ) :=
  intervalStretchHomeomorph a b (intervalStretchMiddle b c s) d ha hb
    (continuous_intervalStretchMiddle hb hc s) hd hab hbd
    (fun x => (intervalStretchMiddle_mem_Ioo hab hbd hac hcd s x).1)
    (fun x => (intervalStretchMiddle_mem_Ioo hab hbd hac hcd s x).2)

section IsotopyAPI

variable {X : Type*} [TopologicalSpace X]
    (a b c d : X → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x < b x) (hbd : ∀ x, b x < d x)
    (hac : ∀ x, a x < c x) (hcd : ∀ x, c x < d x)

@[simp]
theorem intervalStretchIsotopy_zero :
    intervalStretchIsotopy a b c d ha hb hc hd hab hbd hac hcd ⟨0, by norm_num⟩ =
      Homeomorph.refl (X × ℝ) := by
  ext p : 1
  apply Prod.ext
  · rfl
  change intervalStretch (a p.1) (b p.1) (intervalStretchMiddle b c ⟨0, by norm_num⟩ p.1)
    (d p.1) p.2 = p.2
  simp [intervalStretchMiddle]

@[simp]
theorem intervalStretchIsotopy_one :
    intervalStretchIsotopy a b c d ha hb hc hd hab hbd hac hcd ⟨1, by norm_num⟩ =
      intervalStretchHomeomorph a b c d ha hb hc hd hab hbd hac hcd := by
  ext p : 1
  apply Prod.ext
  · rfl
  change intervalStretch (a p.1) (b p.1) (intervalStretchMiddle b c ⟨1, by norm_num⟩ p.1)
    (d p.1) p.2 = intervalStretch (a p.1) (b p.1) (c p.1) (d p.1) p.2
  simp [intervalStretchMiddle]

theorem continuous_intervalStretchIsotopy :
    Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) =>
      intervalStretchIsotopy a b c d ha hb hc hd hab hbd hac hcd p.1 p.2) := by
  have hbase : Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) => p.2.1) :=
    continuous_snd.fst
  have htime : Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hmiddle : Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) =>
      intervalStretchMiddle b c p.1 p.2.1) :=
    ((continuous_const.sub htime).mul (hb.comp hbase)).add (htime.mul (hc.comp hbase))
  exact hbase.prodMk (continuous_intervalStretch (ha.comp hbase) (hb.comp hbase)
    hmiddle (hd.comp hbase) continuous_snd.snd (fun p => hab p.2.1) (fun p => hbd p.2.1))

theorem continuous_intervalStretchIsotopy_symm :
    Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) =>
      (intervalStretchIsotopy a b c d ha hb hc hd hab hbd hac hcd p.1).symm p.2) := by
  have hbase : Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) => p.2.1) :=
    continuous_snd.fst
  have htime : Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hmiddle : Continuous (fun p : Icc (0 : ℝ) 1 × (X × ℝ) =>
      intervalStretchMiddle b c p.1 p.2.1) :=
    ((continuous_const.sub htime).mul (hb.comp hbase)).add (htime.mul (hc.comp hbase))
  exact hbase.prodMk (continuous_intervalStretch (ha.comp hbase) hmiddle (hb.comp hbase)
    (hd.comp hbase) continuous_snd.snd
    (fun p => (intervalStretchMiddle_mem_Ioo hab hbd hac hcd p.1 p.2.1).1)
    (fun p => (intervalStretchMiddle_mem_Ioo hab hbd hac hcd p.1 p.2.1).2))

theorem intervalStretchIsotopy_apply_of_not_mem_Ioo (s : Icc (0 : ℝ) 1) (p : X × ℝ)
    (hp : p.2 ∉ Ioo (a p.1) (d p.1)) :
    intervalStretchIsotopy a b c d ha hb hc hd hab hbd hac hcd s p = p :=
  intervalStretchHomeomorph_apply_of_not_mem_Ioo _ _ _ _ _ _ _ _ _ _ _ _ p hp

end IsotopyAPI

end

end DifferentialGeometry.Topology
