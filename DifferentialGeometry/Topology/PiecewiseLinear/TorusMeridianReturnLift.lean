/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridianReturn

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem finite_circle_lift_inter_compact
    {K : Set loopCircle} (hK : K.Finite) {C : Set ℝ} (hC : IsCompact C) :
    (((↑) : ℝ → loopCircle) ⁻¹' K ∩ C).Finite := by
  have hd : IsDiscrete (((↑) : ℝ → loopCircle) ⁻¹' K) :=
    hK.isDiscrete.preimage' (AddCircle.continuous_mk' 1).continuousOn fun z =>
      ⟨(AddCircle.isCoveringMap_coe (1 : ℝ) z).discreteTopology_fiber⟩
  exact (hC.inter_left (hK.isClosed.preimage (AddCircle.continuous_mk' 1))).finite
    (hd.mono inter_subset_left)

private theorem product_fiber_mem_iff
    {E : Type*} [TopologicalSpace E] {M Q X : Set E}
    (φ : (M × Q) ≃ₜ X) (q : Q) (x : X) :
    (x : E) ∈ range (fun m : M => (φ (m, q) : E)) ↔ (φ.symm x).2 = q := by
  constructor
  · rintro ⟨m, hm⟩
    have hmx : φ (m, q) = x := Subtype.ext hm
    rw [← hmx, φ.symm_apply_apply]
  · intro hx
    refine ⟨(φ.symm x).1, ?_⟩
    have heq : ((φ.symm x).1, q) = φ.symm x := Prod.ext rfl hx.symm
    change (φ ((φ.symm x).1, q) : E) = (x : E)
    rw [heq, φ.apply_symm_apply]

private theorem exists_ordered_lifts_of_same_mark
    (ρ : C(loopCircle, loopCircle)) {K : Set loopCircle}
    (hmore : ∃ x y : loopCircle, x ≠ y ∧ ρ x = ρ y ∧ ρ x ∈ K) :
    ∃ a b : ℝ, a < b ∧ b < a + 1 ∧ ρ (a : loopCircle) = ρ (b : loopCircle) ∧
      ρ (a : loopCircle) ∈ K := by
  obtain ⟨x, y, hxy, hρ, hxK⟩ := hmore
  obtain ⟨a, ha, hax⟩ := exists_lift_mem_Ico x
  obtain ⟨b, hb, hby⟩ := exists_lift_mem_Ico y
  have hab : a ≠ b := fun h =>
    hxy (hax.symm.trans ((congrArg (fun t : ℝ => (t : loopCircle)) h).trans hby))
  rcases lt_or_gt_of_ne hab with hab | hba
  · refine ⟨a, b, hab, by linarith [ha.1, hb.2], ?_, ?_⟩
    · simpa only [hax, hby] using hρ
    · simpa only [hax] using hxK
  · refine ⟨b, a, hba, by linarith [hb.1, ha.2], ?_, ?_⟩
    · simpa only [hax, hby] using hρ.symm
    · simpa only [hby, ← hρ] using hxK

private theorem exists_returning_arc_of_circle_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} {J M Q X : Set E} (hJ : IsPLSphere 1 J)
    (e : loopCircle ≃ₜ J) (φ : (M × Q) ≃ₜ X) (hJX : J ⊆ X) (q : ι → Q)
    {a b : ℝ} (hab : a < b) (hba : b < a + 1) (i : ι)
    (ha : (φ.symm ⟨e (a : loopCircle), hJX (e (a : loopCircle)).property⟩).2 = q i)
    (hb : (φ.symm ⟨e (b : loopCircle), hJX (e (b : loopCircle)).property⟩).2 = q i)
    (havoid : ∀ t ∈ Ioo a b, ∀ k,
      (φ.symm ⟨e (t : loopCircle), hJX (e (t : loopCircle)).property⟩).2 ≠ q k) :
    ∃ (B : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) B ∧ B ⊆ J ∧
      ({γ 0, γ 1} : Set E) ⊆ range (fun m : M => (φ (m, q i) : E)) ∧
      B ∩ (⋃ k, range (fun m : M => (φ (m, q k) : E))) = {γ 0, γ 1} := by
  let g : ℝ → E := fun t => e (t : loopCircle)
  obtain ⟨γ, hγ, hγ0, hγ1⟩ :=
    hJ.exists_isPLHomeomorphOn_Icc_image_circleInterval e hab hba
  have hga : g a ∈ range (fun m : M => (φ (m, q i) : E)) :=
    (product_fiber_mem_iff φ (q i) _).mpr ha
  have hgb : g b ∈ range (fun m : M => (φ (m, q i) : E)) :=
    (product_fiber_mem_iff φ (q i) _).mpr hb
  refine ⟨g '' Icc a b, γ, hγ, ?_, ?_, ?_⟩
  · rintro _ ⟨t, -, rfl⟩
    exact (e _).property
  · intro y hy
    simp only [hγ0, hγ1, mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hga
    · exact hgb
  · rw [hγ0, hγ1]
    apply Subset.antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, htf⟩
      by_cases hta : t = a
      · rw [hta]
        exact mem_insert _ _
      by_cases htb : t = b
      · rw [htb]
        exact mem_insert_of_mem _ rfl
      obtain ⟨k, hk⟩ := mem_iUnion.mp htf
      exact (havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩ k
        ((product_fiber_mem_iff φ (q k) _).mp hk)).elim
    · intro y hy
      rcases mem_insert_iff.mp hy with hy | hy
      · subst y
        exact ⟨⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, mem_iUnion.mpr ⟨i, hga⟩⟩
      · have hy' := mem_singleton_iff.mp hy
        subst y
        exact ⟨⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, mem_iUnion.mpr ⟨i, hgb⟩⟩

theorem exists_returning_arc_of_periodic_longitude_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] {J M Q X : Set E} (hJ : IsPLSphere 1 J)
    (φ : (M × Q) ≃ₜ X) (hJX : J ⊆ X) (q : ι → Q)
    (eJ : loopCircle ≃ₜ J) (eQ : loopCircle ≃ₜ Q) (F : C(ℝ, ℝ))
    (hproj : ∀ t : ℝ, eQ (F t : loopCircle) =
      (φ.symm ⟨eJ (t : loopCircle), hJX (eJ (t : loopCircle)).property⟩).2)
    (hperiod : (∀ t, F (t + 1) = F t + 1) ∨ (∀ t, F (t + 1) = F t - 1))
    (hno : ∀ t i, eQ (F t : loopCircle) = q i → ¬ IsLocalExtr F t)
    (hmore : ∃ i, (J ∩ range (fun m : M => (φ (m, q i) : E))).Nontrivial) :
    ∃ (i : ι) (B : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc 0 1) B ∧ B ⊆ J ∧
      ({γ 0, γ 1} : Set E) ⊆ range (fun m : M => (φ (m, q i) : E)) ∧
      B ∩ (⋃ k, range (fun m : M => (φ (m, q k) : E))) = {γ 0, γ 1} := by
  classical
  let π : C(J, Q) := ContinuousMap.snd.comp ((φ.symm : C(X, M × Q)).comp
    ⟨inclusion hJX, continuous_inclusion hJX⟩)
  let ρ : C(loopCircle, loopCircle) :=
    (eQ.symm : C(Q, loopCircle)).comp (π.comp (eJ : C(loopCircle, J)))
  let K : Set loopCircle := eQ ⁻¹' range q
  let P : Set ℝ := ((↑) : ℝ → loopCircle) ⁻¹' K
  have hK : K.Finite := (finite_range q).preimage eQ.injective.injOn
  have hP : ∀ y : ℝ, y + 1 ∈ P ↔ y ∈ P := by
    intro y
    change eQ ((y + 1 : ℝ) : loopCircle) ∈ range q ↔ eQ (y : loopCircle) ∈ range q
    rw [AddCircle.coe_add_period]
  have hfinite : ∀ a b : ℝ, (P ∩ F '' Icc a b).Finite := fun a b =>
    finite_circle_lift_inter_compact hK (isCompact_Icc.image F.continuous)
  have hlift (t : ℝ) : (F t : loopCircle) = ρ (t : loopCircle) := by
    apply eQ.injective
    exact (hproj t).trans (eQ.apply_symm_apply _).symm
  have hno' : ∀ t : ℝ, F t ∈ P → ¬ IsLocalMax F t ∧ ¬ IsLocalMin F t := by
    intro t ht
    obtain ⟨i, hi⟩ := ht
    exact ⟨fun h => hno t i hi.symm (Or.inr h), fun h => hno t i hi.symm (Or.inl h)⟩
  have hmoreρ : ∃ x y : loopCircle, x ≠ y ∧ ρ x = ρ y ∧ ρ x ∈ K := by
    obtain ⟨i, p, hp, s, hs, hps⟩ := hmore
    let u : J := ⟨p, hp.1⟩
    let v : J := ⟨s, hs.1⟩
    have hu : π u = q i := (product_fiber_mem_iff φ (q i) _).mp hp.2
    have hv : π v = q i := (product_fiber_mem_iff φ (q i) _).mp hs.2
    refine ⟨eJ.symm u, eJ.symm v, ?_, ?_, ?_⟩
    · intro huv
      exact hps (congrArg Subtype.val (eJ.symm.injective huv))
    · change eQ.symm (π (eJ (eJ.symm u))) = eQ.symm (π (eJ (eJ.symm v)))
      rw [eJ.apply_symm_apply, eJ.apply_symm_apply, hu, hv]
    · change eQ (eQ.symm (π (eJ (eJ.symm u)))) ∈ range q
      rw [eJ.apply_symm_apply, eQ.apply_symm_apply, hu]
      exact mem_range_self i
  obtain ⟨a, b, hab, hba, habρ, haK⟩ := exists_ordered_lifts_of_same_mark ρ hmoreρ
  have haP : F a ∈ P := by
    change (F a : loopCircle) ∈ K
    rwa [hlift]
  have hmod : ∃ k : ℤ, F b - F a = (k : ℝ) :=
    (loopCircle_coe_eq_coe_iff _ _).mp (by rw [hlift, hlift, habρ])
  obtain ⟨c, d, hcd, hdc, heq, hcP, havoid⟩ :=
    exists_periodic_marked_excursion F.continuous hperiod hP hfinite hno' hab hba haP hmod
  obtain ⟨i, hi⟩ := hcP
  have hc : π (eJ (c : loopCircle)) = q i := (hproj c).symm.trans hi.symm
  have hd : π (eJ (d : loopCircle)) = q i := by
    change (φ.symm ⟨eJ (d : loopCircle), hJX (eJ (d : loopCircle)).property⟩).2 = q i
    rw [← hproj d, ← heq]
    exact hi.symm
  have hav : ∀ t ∈ Ioo c d, ∀ k, π (eJ (t : loopCircle)) ≠ q k := by
    intro t ht k he
    apply havoid t ht
    exact ⟨k, ((hproj t).trans he).symm⟩
  obtain ⟨B, γ, hγ, hBJ, hend, hinter⟩ :=
    exists_returning_arc_of_circle_interval hJ eJ φ hJX q hcd hdc i hc hd hav
  exact ⟨i, B, γ, hγ, hBJ, hend, hinter⟩

end DifferentialGeometry.Topology.PiecewiseLinear
