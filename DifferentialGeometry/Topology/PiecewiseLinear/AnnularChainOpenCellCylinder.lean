/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCellCoordinates
import Mathlib.Topology.Order.AtTopBotIxx

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {R X : Type*} [TopologicalSpace R] [TopologicalSpace X]

private noncomputable def annulusChartValue {A : ℤ → Set X}
    (e : ∀ i, (R × unitInterval) ≃ₜ A i) (i : ℤ) (p : R × unitInterval) : X :=
  e i p

private noncomputable def annulusCylinderMap {A : ℤ → Set X}
    (e : ∀ i, (R × unitInterval) ≃ₜ A i) (p : R × ℝ) : X :=
  annulusChartValue e ⌊p.2⌋ (p.1, ⟨Int.fract p.2, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)

private theorem annulusCylinderMap_shift {A : ℤ → Set X}
    (e : ∀ i, (R × unitInterval) ≃ₜ A i)
    (hseam : ∀ i x, (e i (x, 1) : X) = e (i + 1) (x, 0))
    (i : ℤ) (x : R) (s : unitInterval) :
    annulusCylinderMap e (x, (i : ℝ) + s) = e i (x, s) := by
  by_cases hs : s = 1
  · subst s
    have hf : ⌊(i : ℝ) + 1⌋ = i + 1 := by
      rw [← Int.cast_one, ← Int.cast_add, Int.floor_intCast]
    have ht : Int.fract ((i : ℝ) + 1) = 0 := by
      rw [← Int.cast_one, ← Int.cast_add, Int.fract_intCast]
    dsimp only [annulusCylinderMap]
    simp only [Set.Icc.coe_one]
    rw [hf]
    simp only [ht]
    exact (hseam i x).symm
  · have hs' : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 (by
      intro heq
      exact hs (Subtype.ext heq))
    have hf : ⌊(i : ℝ) + s⌋ = i := Int.floor_eq_iff.mpr ⟨by
      linarith [s.property.1], by linarith⟩
    have ht : Int.fract ((i : ℝ) + s) = s := by rw [Int.fract, hf]; ring
    dsimp only [annulusCylinderMap]
    rw [hf]
    simp only [ht, Subtype.coe_eta, annulusChartValue]

private theorem annulusCylinderMap_continuous {A : ℤ → Set X}
    (e : ∀ i, (R × unitInterval) ≃ₜ A i)
    (hseam : ∀ i x, (e i (x, 1) : X) = e (i + 1) (x, 0)) :
    Continuous (annulusCylinderMap e) := by
  let T : ℤ → Set (R × ℝ) := fun i => Prod.snd ⁻¹' Icc (i : ℝ) ((i : ℝ) + 1)
  have hlocal₀ : LocallyFinite (fun i : ℤ => Icc (i : ℝ) ((i : ℝ) + 1)) :=
    locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop
      (tendsto_atBot_add_const_right _ 1 (tendsto_intCast_atBot_iff.mpr tendsto_id))
  have hlocal : LocallyFinite T := hlocal₀.preimage_continuous continuous_snd
  have hcover : ⋃ i, T i = univ := by
    apply eq_univ_of_forall
    intro p
    exact mem_iUnion.mpr ⟨⌊p.2⌋, Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  refine hlocal.continuous hcover (fun _ => isClosed_Icc.preimage continuous_snd) ?_
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  let c : T i → R × unitInterval := fun p =>
    (p.1.1, ⟨p.1.2 - i, by constructor <;> linarith [p.property.1, p.property.2]⟩)
  have hc : Continuous c :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (((continuous_snd.comp continuous_subtype_val).sub continuous_const).subtype_mk _)
  have heq : (fun p : T i => annulusCylinderMap e p) = fun p => (e i (c p) : X) := by
    funext p
    have h := annulusCylinderMap_shift e hseam i p.1.1 (c p).2
    have ht : (i : ℝ) + ((c p).2 : ℝ) = p.1.2 := by dsimp [c]; ring
    simpa only [ht, annulusChartValue] using h
  change Continuous (fun p : T i => annulusCylinderMap e p)
  rw [heq]
  exact continuous_subtype_val.comp ((e i).continuous.comp hc)

private theorem annulus_chart_collision {A : ℤ → Set X}
    (e : ∀ i, (R × unitInterval) ≃ₜ A i)
    (hseam : ∀ i x, (e i (x, 1) : X) = e (i + 1) (x, 0))
    (hinter : ∀ i, A i ∩ A (i + 1) = range (fun x => (e i (x, 1) : X)))
    (hdisj : ∀ i j, 2 ≤ |i - j| → Disjoint (A i) (A j))
    {i j : ℤ} {p q : R × unitInterval} (heq : (e i p : X) = e j q) :
    p.1 = q.1 ∧ (i : ℝ) + p.2 = (j : ℝ) + q.2 := by
  have hnear : |i - j| < 2 := by
    by_contra hn
    exact Set.disjoint_left.mp (hdisj i j (not_lt.mp hn)) (e i p).property
      (heq ▸ (e j q).property)
  have hstep {i : ℤ} {p q : R × unitInterval}
      (h : (e i p : X) = e (i + 1) q) : p.1 = q.1 ∧ p.2 = 1 ∧ q.2 = 0 := by
    have hm : (e i p : X) ∈ A i ∩ A (i + 1) :=
      ⟨(e i p).property, h ▸ (e (i + 1) q).property⟩
    rw [hinter] at hm
    obtain ⟨r, hr⟩ := hm
    have hp : p = (r, 1) := (e i).injective (Subtype.ext hr.symm)
    have hq : q = (r, 0) := (e (i + 1)).injective
      (Subtype.ext ((h.symm.trans hr.symm).trans (hseam i r)))
    simp [hp, hq]
  have htrich : i = j ∨ j = i + 1 ∨ i = j + 1 := by
    rw [abs_lt] at hnear
    omega
  rcases htrich with rfl | rfl | rfl
  · have hpq := (e i).injective (Subtype.ext heq)
    exact ⟨congrArg Prod.fst hpq, congrArg (fun p : R × unitInterval => (i : ℝ) + p.2) hpq⟩
  · obtain ⟨hpq, hp, hq⟩ := hstep heq
    simp only [hp, hq, Int.cast_add, Int.cast_one, Set.Icc.coe_one,
      Set.Icc.coe_zero, add_zero]
    exact ⟨hpq, trivial⟩
  · obtain ⟨hqp, hq, hp⟩ := hstep heq.symm
    simp only [hp, hq, Int.cast_add, Int.cast_one, Set.Icc.coe_one,
      Set.Icc.coe_zero, add_zero]
    exact ⟨hqp.symm, trivial⟩

theorem exists_annulus_chain_cylinder_homeomorph [CompactSpace R] [T2Space X]
    {A : ℤ → Set X} (e : ∀ i, (R × unitInterval) ≃ₜ A i)
    (hseam : ∀ i x, (e i (x, 1) : X) = e (i + 1) (x, 0))
    (hinter : ∀ i, A i ∩ A (i + 1) = range (fun x => (e i (x, 1) : X)))
    (hdisj : ∀ i j, 2 ≤ |i - j| → Disjoint (A i) (A j))
    (hlocal : LocallyFinite (fun i =>
      (Subtype.val : (⋃ j, A j) → X) ⁻¹' A i)) :
    ∃ c : (R × ℝ) ≃ₜ (⋃ i, A i),
      ∀ (i : ℤ) (x : R) (s : unitInterval),
        (c (x, (i : ℝ) + s) : X) = e i (x, s) := by
  let f : R × ℝ → (⋃ i, A i) := fun p =>
    ⟨annulusCylinderMap e p, mem_iUnion.mpr ⟨⌊p.2⌋, (e _ _).property⟩⟩
  have hf : Continuous f := (annulusCylinderMap_continuous e hseam).subtype_mk _
  have hfshift (i : ℤ) (x : R) (s : unitInterval) :
      (f (x, (i : ℝ) + s) : X) = e i (x, s) :=
    annulusCylinderMap_shift e hseam i x s
  have hfinj : Function.Injective f := by
    intro p q hpq
    have hpq' : annulusCylinderMap e p = annulusCylinderMap e q :=
      congrArg Subtype.val hpq
    dsimp only [annulusCylinderMap, annulusChartValue] at hpq'
    have h := annulus_chart_collision e hseam hinter hdisj hpq'
    apply Prod.ext
    · exact h.1
    · have heqp : (⌊p.2⌋ : ℝ) + Int.fract p.2 = p.2 := by rw [Int.fract]; ring
      have heqq : (⌊q.2⌋ : ℝ) + Int.fract q.2 = q.2 := by rw [Int.fract]; ring
      exact heqp.symm.trans (h.2.trans heqq)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp y.property
    obtain ⟨⟨x, s⟩, hs⟩ := (e i).surjective ⟨y, hi⟩
    refine ⟨(x, (i : ℝ) + s), Subtype.ext ?_⟩
    exact (hfshift i x s).trans (congrArg Subtype.val hs)
  let T : ℤ → Set (R × ℝ) := fun i => Prod.snd ⁻¹' Icc (i : ℝ) ((i : ℝ) + 1)
  have hTcompact (i : ℤ) : IsCompact (T i) := by
    let shift : R × unitInterval → R × ℝ := fun p => (p.1, (i : ℝ) + p.2)
    have hcont : Continuous shift := continuous_fst.prodMk
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))
    have hT : shift '' univ = T i := by
      ext p
      constructor
      · rintro ⟨⟨x, s⟩, _, rfl⟩
        constructor <;> dsimp [shift] <;> linarith [s.property.1, s.property.2]
      · intro hp
        refine ⟨(p.1, ⟨p.2 - i, by
          constructor <;> linarith [hp.1, hp.2]⟩), mem_univ _, ?_⟩
        apply Prod.ext
        · rfl
        · dsimp [shift]
          ring
    exact hT ▸ isCompact_univ.image hcont
  have hfT (i : ℤ) : f '' T i ⊆ (Subtype.val : (⋃ j, A j) → X) ⁻¹' A i := by
    rintro y ⟨p, hp, rfl⟩
    let s : unitInterval := ⟨p.2 - i, by
      constructor <;> linarith [hp.1, hp.2]⟩
    have hp' : p = (p.1, (i : ℝ) + s) := by
      apply Prod.ext
      · rfl
      · dsimp [s]
        ring
    change (f p : X) ∈ A i
    rw [hp', hfshift]
    exact (e i (p.1, s)).property
  have hfclosed : IsClosedMap f := by
    intro D hD
    have hl : LocallyFinite (fun i => f '' (D ∩ T i)) := hlocal.subset fun i =>
      (image_mono inter_subset_right).trans (hfT i)
    have hcl : IsClosed (⋃ i, f '' (D ∩ T i)) := hl.isClosed_iUnion fun i =>
      ((hTcompact i).inter_left hD).image hf |>.isClosed
    have heq : (⋃ i, f '' (D ∩ T i)) = f '' D := by
      apply Subset.antisymm
      · exact iUnion_subset fun i => image_mono inter_subset_left
      · rintro y ⟨p, hp, rfl⟩
        exact mem_iUnion.mpr ⟨⌊p.2⌋, p, ⟨hp, Int.floor_le _,
          (Int.lt_floor_add_one _).le⟩, rfl⟩
    exact heq ▸ hcl
  let c := (Equiv.ofBijective f ⟨hfinj, hfsurj⟩).toHomeomorphOfContinuousClosed hf hfclosed
  exact ⟨c, hfshift⟩

end DifferentialGeometry.Topology.PiecewiseLinear
