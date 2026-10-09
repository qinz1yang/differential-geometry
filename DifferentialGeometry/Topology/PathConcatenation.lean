/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter Topology

noncomputable def intervalConcatenation {X : Type*} (f : ℕ → ℝ → X) (t : ℝ) : X :=
  f ⌊t⌋₊ (t - ⌊t⌋₊)

theorem intervalConcatenation_eq_of_mem_Icc {X : Type*} {f : ℕ → ℝ → X}
    (hjoin : ∀ n, f n 1 = f (n + 1) 0) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (n : ℝ) (n + 1)) : intervalConcatenation f t = f n (t - n) := by
  by_cases htn : t = n + 1
  · subst t
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast]
    simp only [intervalConcatenation, Nat.floor_natCast, sub_self]
    rw [← hjoin n]
    congr 1
    push_cast
    ring
  · have hfloor : ⌊t⌋₊ = n := Nat.floor_eq_on_Ico n t ⟨ht.1, lt_of_le_of_ne ht.2 htn⟩
    simp only [intervalConcatenation, hfloor]

theorem continuousOn_intervalConcatenation {X : Type*} [TopologicalSpace X]
    {f : ℕ → ℝ → X} (hf : ∀ n, ContinuousOn (f n) (Icc 0 1))
    (hjoin : ∀ n, f n 1 = f (n + 1) 0) :
    ContinuousOn (intervalConcatenation f) (Ici 0) := by
  have hloc : LocallyFinite (fun n : ℕ => Icc (n : ℝ) (n + 1)) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt x
    refine ⟨Iio (N : ℝ), Iio_mem_nhds hN, (finite_Iio N).subset ?_⟩
    rintro n ⟨y, hy, hyN⟩
    exact_mod_cast hy.1.trans_lt hyN
  have hcover : (⋃ n : ℕ, Icc (n : ℝ) (n + 1)) = Ici (0 : ℝ) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact (Nat.cast_nonneg n).trans hn.1
    · intro x hx
      exact mem_iUnion.mpr ⟨⌊x⌋₊, Nat.floor_le hx, (Nat.lt_floor_add_one x).le⟩
  rw [← hcover]
  apply hloc.continuousOn_iUnion (fun _ => isClosed_Icc)
  intro n
  have hmap : MapsTo (fun t : ℝ => t - n) (Icc (n : ℝ) (n + 1)) (Icc 0 1) := by
    intro t ht
    constructor <;> dsimp <;> linarith [ht.1, ht.2]
  exact ((hf n).comp (by fun_prop) hmap).congr
    (fun t ht => intervalConcatenation_eq_of_mem_Icc hjoin n ht)

theorem tendsto_intervalConcatenation {X : Type*} [TopologicalSpace X]
    {f : ℕ → ℝ → X} {x : X}
    (hf : Tendsto (fun n => f n '' Icc 0 1) atTop (𝓝 x).smallSets) :
    Tendsto (intervalConcatenation f) atTop (𝓝 x) := by
  have hfloor : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop :=
    Nat.floor_mono.tendsto_atTop_atTop fun n => ⟨(n : ℝ), by simp⟩
  apply (hf.comp hfloor).of_smallSets
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact mem_image_of_mem (f ⌊t⌋₊) ⟨sub_nonneg.mpr (Nat.floor_le ht), (Nat.self_sub_floor_lt_one
      t).le⟩

theorem ContinuousOn.exists_continuousOn_Icc_of_tendsto_atTop
    {X : Type*} [TopologicalSpace X] {g : ℝ → X} {p : X}
    (hg : ContinuousOn g (Ici 0)) (hlim : Tendsto g atTop (𝓝 p)) :
    ∃ h : ℝ → X, ContinuousOn h (Icc 0 1) ∧ h 0 = p ∧ h 1 = g 0 ∧
      ∀ t ∈ Ioc (0 : ℝ) 1, h t = g (t⁻¹ - 1) := by
  let h (t : ℝ) := if t = 0 then p else g (t⁻¹ - 1)
  have h0 : h 0 = p := by simp only [h, ite_true]
  have heq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : h t = g (t⁻¹ - 1) := by
    simp only [h, ht.1.ne', ite_false]
  have hmap : MapsTo (fun t : ℝ => t⁻¹ - 1) (Ioc 0 1) (Ici 0) :=
    fun t ht => sub_nonneg.mpr ((one_le_inv₀ ht.1).mpr ht.2)
  have hcont : ContinuousOn h (Ioc 0 1) := by
    apply (hg.comp ?_ hmap).congr heq
    exact (continuousOn_id.inv₀ (fun t ht => ht.1.ne')).sub continuousOn_const
  have hinv : Tendsto (fun t : ℝ => t⁻¹ - 1) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-1 : ℝ)
        tendsto_inv_nhdsGT_zero
  have hzero : ContinuousWithinAt h (Ioc 0 1) 0 := by
    rw [ContinuousWithinAt, h0]
    refine ((hlim.comp hinv).mono_left (nhdsWithin_mono 0 Ioc_subset_Ioi_self)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heq t ht).symm
  refine ⟨h, ?_, h0, ?_, heq⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · subst t
      simpa only [Ioc_insert_left (show (0 : ℝ) ≤ 1 by norm_num)] using hzero.insert
    · apply (hcont t ⟨ht0, ht.2⟩).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht0)] with s hs hs0
      exact ⟨hs0, hs.2⟩
  · simpa only [inv_one, sub_self] using heq 1 ⟨zero_lt_one, le_rfl⟩
