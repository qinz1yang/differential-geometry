/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.Submersion
import DifferentialGeometry.Topology.Manifold.RegularSublevelBoundary
import DifferentialGeometry.Topology.Manifold.SmoothSignedClamp
import DifferentialGeometry.Topology.VanKampen.SmoothTwoSidedCollarBridge

set_option autoImplicit false

open Set Topology Manifold
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

open DifferentialGeometry.Topology.Morse

variable
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {S : Type} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type} [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)

noncomputable def finiteTime (x : h.neighborhood) : ℝ :=
  ((h.toDiffeomorph.symm x).2 : ℝ)

theorem contMDiff_finiteTime :
    ContMDiff J (modelWithCornersSelf ℝ ℝ) ∞ h.finiteTime := by
  exact contMDiff_subtype_val.comp (contMDiff_snd.comp h.toDiffeomorph.symm.contMDiff)

noncomputable def collarSignedValue (x : h.neighborhood) : ℝ :=
  smoothSignedClamp h.radius h.radius_pos (h.finiteTime x)

theorem contMDiff_collarSignedValue :
    ContMDiff J (modelWithCornersSelf ℝ ℝ) ∞ h.collarSignedValue := by
  exact (contDiff_smoothSignedClamp h.radius h.radius_pos).contMDiff.comp
    h.contMDiff_finiteTime

noncomputable def finiteNormalVector (x : h.neighborhood) : F :=
  (h.toDiffeomorph.symm.mfderivToContinuousLinearEquiv (by simp) x).symm (0, 1)

theorem mfderiv_finiteTime_apply_finiteNormalVector (x : h.neighborhood) :
    mfderiv J (modelWithCornersSelf ℝ ℝ) h.finiteTime x (h.finiteNormalVector x) = 1 := by
  let q : S × symmetricOpenInterval h.radius := h.toDiffeomorph.symm x
  have hInv :
      mfderiv J (I.prod (modelWithCornersSelf ℝ ℝ))
          (h.toDiffeomorph.symm : h.neighborhood → S × symmetricOpenInterval h.radius)
          x (h.finiteNormalVector x) = (0, 1) := by
    change (h.toDiffeomorph.symm.mfderivToContinuousLinearEquiv (by simp) x)
        ((h.toDiffeomorph.symm.mfderivToContinuousLinearEquiv (by simp) x).symm (0, 1)) =
      (0, 1)
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hSymmDiff :
      MDifferentiableAt J (I.prod (modelWithCornersSelf ℝ ℝ))
        (h.toDiffeomorph.symm : h.neighborhood → S × symmetricOpenInterval h.radius) x :=
    h.toDiffeomorph.symm.mdifferentiable (by simp) x
  have hSndDiff :
      MDifferentiableAt (I.prod (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ ℝ)
        (@Prod.snd S (symmetricOpenInterval h.radius)) q :=
    mdifferentiableAt_snd
  have hValDiff :
      MDifferentiableAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        (Subtype.val : symmetricOpenInterval h.radius → ℝ) q.2 :=
    (contMDiff_subtype_val.contMDiffAt).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hCompSnd := mfderiv_comp x hSndDiff hSymmDiff
  have hCompVal := mfderiv_comp x hValDiff (hSndDiff.comp x hSymmDiff)
  change mfderiv J (modelWithCornersSelf ℝ ℝ)
    ((Subtype.val : symmetricOpenInterval h.radius → ℝ) ∘
      (@Prod.snd S (symmetricOpenInterval h.radius)) ∘ h.toDiffeomorph.toEquiv.symm)
      x (h.finiteNormalVector x) = 1
  erw [hCompVal, hCompSnd]
  change mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
    (Subtype.val : symmetricOpenInterval h.radius → ℝ) q.2
      (mfderiv (I.prod (modelWithCornersSelf ℝ ℝ)) (modelWithCornersSelf ℝ ℝ)
        (@Prod.snd S (symmetricOpenInterval h.radius)) q
          (mfderiv J (I.prod (modelWithCornersSelf ℝ ℝ))
            (h.toDiffeomorph.symm : h.neighborhood → S × symmetricOpenInterval h.radius)
            x (h.finiteNormalVector x))) = 1
  rw [hInv, mfderiv_snd, DifferentialGeometry.mfderiv_subtype_val_apply]
  rfl

theorem not_isCriticalPointAt_finiteTime (x : h.neighborhood) :
    ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt J h.finiteTime x := by
  intro hcrit
  change mfderiv J (modelWithCornersSelf ℝ ℝ) h.finiteTime x = 0 at hcrit
  have hzero :
      mfderiv J (modelWithCornersSelf ℝ ℝ) h.finiteTime x
        (h.finiteNormalVector x) = 0 := by
    rw [hcrit]
    rfl
  rw [h.mfderiv_finiteTime_apply_finiteNormalVector] at hzero
  exact (by norm_num : (1 : ℝ) ≠ 0) hzero

theorem collarSignedValue_eq_zero_iff (x : h.neighborhood) :
    h.collarSignedValue x = 0 ↔ h.finiteTime x = 0 := by
  exact smoothSignedClamp_eq_zero_iff h.radius h.radius_pos (h.finiteTime x)

theorem collarSignedValue_eventuallyEq_finiteTime_of_eq_zero
    (x : h.neighborhood) (hx : h.collarSignedValue x = 0) :
    h.collarSignedValue =ᶠ[nhds x] h.finiteTime := by
  have htime : h.finiteTime x = 0 := (h.collarSignedValue_eq_zero_iff x).mp hx
  have hcontinuous : Continuous h.finiteTime := h.contMDiff_finiteTime.continuous
  have hopen : IsOpen {t : ℝ | |t| < h.radius / 3} :=
    isOpen_lt continuous_abs continuous_const
  have hthird : 0 < h.radius / 3 := by linarith [h.radius_pos]
  have hzero : (0 : ℝ) ∈ {t : ℝ | |t| < h.radius / 3} := by
    simpa only [Set.mem_ofPred_eq, abs_zero] using hthird
  have hmem : h.finiteTime ⁻¹' {t : ℝ | |t| < h.radius / 3} ∈ nhds x := by
    apply (hopen.preimage hcontinuous).mem_nhds
    simpa only [Set.mem_preimage, htime] using hzero
  filter_upwards [hmem] with y hy
  apply smoothSignedClamp_eq_self_of_abs_le_third h.radius h.radius_pos
  exact hy.le

theorem not_isCriticalPointAt_collarSignedValue_of_eq_zero
    (x : h.neighborhood) (hx : h.collarSignedValue x = 0) :
    ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt J h.collarSignedValue x := by
  intro hcrit
  apply h.not_isCriticalPointAt_finiteTime x
  change mfderiv J (modelWithCornersSelf ℝ ℝ) h.collarSignedValue x = 0 at hcrit
  change mfderiv J (modelWithCornersSelf ℝ ℝ) h.finiteTime x = 0
  rw [← (h.collarSignedValue_eventuallyEq_finiteTime_of_eq_zero x hx).mfderiv_eq]
  exact hcrit

noncomputable def rescaledTime (x : h.neighborhood) : ℝ :=
  (ThreeManifold.TwoSidedCollar.realHomeomorphIoo h.radius h.radius_pos).symm
    (h.toDiffeomorph.symm x).2

theorem finiteTime_neg_iff_rescaledTime_neg (x : h.neighborhood) :
    h.finiteTime x < 0 ↔ h.rescaledTime x < 0 := by
  let ψ := ThreeManifold.TwoSidedCollar.realHomeomorphIoo h.radius h.radius_pos
  have happ : ψ (h.rescaledTime x) = (h.toDiffeomorph.symm x).2 := by
    exact ψ.apply_symm_apply _
  have hsign := ThreeManifold.TwoSidedCollar.realHomeomorphIoo_neg_iff
    h.radius h.radius_pos (h.rescaledTime x)
  rw [happ] at hsign
  exact hsign

theorem finiteTime_pos_iff_rescaledTime_pos (x : h.neighborhood) :
    0 < h.finiteTime x ↔ 0 < h.rescaledTime x := by
  let ψ := ThreeManifold.TwoSidedCollar.realHomeomorphIoo h.radius h.radius_pos
  have happ : ψ (h.rescaledTime x) = (h.toDiffeomorph.symm x).2 := by
    exact ψ.apply_symm_apply _
  have hsign := ThreeManifold.TwoSidedCollar.realHomeomorphIoo_pos_iff
    h.radius h.radius_pos (h.rescaledTime x)
  rw [happ] at hsign
  exact hsign

theorem toTwoSidedCollar_toFun_rescaledTime (x : h.neighborhood) :
    h.toTwoSidedCollar.toFun ((h.toDiffeomorph.symm x).1, h.rescaledTime x) = x.1 := by
  rw [h.toTwoSidedCollar_toFun]
  have happ :
      ThreeManifold.TwoSidedCollar.realHomeomorphIoo h.radius h.radius_pos
          (h.rescaledTime x) = (h.toDiffeomorph.symm x).2 := by
    exact (ThreeManifold.TwoSidedCollar.realHomeomorphIoo
      h.radius h.radius_pos).apply_symm_apply _
  rw [happ]
  change (h.toDiffeomorph ((h.toDiffeomorph.symm x).1,
    (h.toDiffeomorph.symm x).2) : M) = x.1
  exact congrArg Subtype.val (h.toDiffeomorph.apply_symm_apply x)

section Sides

variable [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]

theorem finiteTime_neg_iff_mem_negativeSide (x : h.neighborhood) :
    h.finiteTime x < 0 ↔ x.1 ∈ h.toTwoSidedCollar.negativeSide := by
  constructor
  · intro ht
    rw [← h.toTwoSidedCollar_toFun_rescaledTime x]
    exact h.toTwoSidedCollar.toFun_mem_negativeSide_of_neg _
      ((h.finiteTime_neg_iff_rescaledTime_neg x).mp ht)
  · intro hx
    rcases lt_trichotomy (h.finiteTime x) 0 with ht | ht | ht
    · exact ht
    · have hxzero : x.1 ∈ Set.range e := by
        refine ⟨(h.toDiffeomorph.symm x).1, ?_⟩
        rw [← h.toFun_zero]
        have hpair :
            ((h.toDiffeomorph.symm x).1,
              ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) =
            h.toDiffeomorph.symm x := by
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            exact ht.symm
        rw [hpair]
        exact congrArg Subtype.val (h.toDiffeomorph.apply_symm_apply x)
      exact ((h.toTwoSidedCollar.negativeSide_subset_complement hx) hxzero).elim
    · have hxpos : x.1 ∈ h.toTwoSidedCollar.positiveSide := by
        rw [← h.toTwoSidedCollar_toFun_rescaledTime x]
        exact h.toTwoSidedCollar.toFun_mem_positiveSide_of_pos _
          ((h.finiteTime_pos_iff_rescaledTime_pos x).mp ht)
      exact (Set.disjoint_left.mp h.toTwoSidedCollar.disjoint_negativeSide_positiveSide hx hxpos).elim

theorem finiteTime_pos_iff_mem_positiveSide (x : h.neighborhood) :
    0 < h.finiteTime x ↔ x.1 ∈ h.toTwoSidedCollar.positiveSide := by
  constructor
  · intro ht
    rw [← h.toTwoSidedCollar_toFun_rescaledTime x]
    exact h.toTwoSidedCollar.toFun_mem_positiveSide_of_pos _
      ((h.finiteTime_pos_iff_rescaledTime_pos x).mp ht)
  · intro hx
    rcases lt_trichotomy (h.finiteTime x) 0 with ht | ht | ht
    · have hxneg : x.1 ∈ h.toTwoSidedCollar.negativeSide := by
        rw [← h.toTwoSidedCollar_toFun_rescaledTime x]
        exact h.toTwoSidedCollar.toFun_mem_negativeSide_of_neg _
          ((h.finiteTime_neg_iff_rescaledTime_neg x).mp ht)
      exact (Set.disjoint_left.mp h.toTwoSidedCollar.disjoint_negativeSide_positiveSide hxneg hx).elim
    · have hxzero : x.1 ∈ Set.range e := by
        refine ⟨(h.toDiffeomorph.symm x).1, ?_⟩
        rw [← h.toFun_zero]
        have hpair :
            ((h.toDiffeomorph.symm x).1,
              ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) =
            h.toDiffeomorph.symm x := by
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            exact ht.symm
        rw [hpair]
        exact congrArg Subtype.val (h.toDiffeomorph.apply_symm_apply x)
      exact ((h.toTwoSidedCollar.positiveSide_subset_complement hx) hxzero).elim
    · exact ht

end Sides

noncomputable def sideDefiningFunction [Nonempty S] (x : M) : ℝ :=
  by
    classical
    exact if hx : x ∈ h.neighborhood then
      h.collarSignedValue ⟨x, hx⟩
    else if x ∈ h.toTwoSidedCollar.negativeSide then -1 else 1

theorem sideDefiningFunction_of_mem_neighborhood [Nonempty S]
    {x : M} (hx : x ∈ h.neighborhood) :
    h.sideDefiningFunction x = h.collarSignedValue ⟨x, hx⟩ := by
  simp only [sideDefiningFunction, dif_pos hx]

section GlobalClassification

variable [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]

theorem sideDefiningFunction_neg_iff (x : M) :
    h.sideDefiningFunction x < 0 ↔ x ∈ h.toTwoSidedCollar.negativeSide := by
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN,
      collarSignedValue, smoothSignedClamp_neg_iff]
    exact h.finiteTime_neg_iff_mem_negativeSide ⟨x, hxN⟩
  · simp only [sideDefiningFunction, dif_neg hxN]
    by_cases hxneg : x ∈ h.toTwoSidedCollar.negativeSide
    · simp [hxneg]
    · simp [hxneg]

theorem sideDefiningFunction_pos_iff (x : M) :
    0 < h.sideDefiningFunction x ↔ x ∈ h.toTwoSidedCollar.positiveSide := by
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN,
      collarSignedValue, smoothSignedClamp_pos_iff]
    exact h.finiteTime_pos_iff_mem_positiveSide ⟨x, hxN⟩
  · simp only [sideDefiningFunction, dif_neg hxN]
    by_cases hxneg : x ∈ h.toTwoSidedCollar.negativeSide
    · have hxnotpos : x ∉ h.toTwoSidedCollar.positiveSide := fun hxpos =>
        Set.disjoint_left.mp h.toTwoSidedCollar.disjoint_negativeSide_positiveSide hxneg hxpos
      simp [hxneg, hxnotpos]
    · have hxcomp : x ∈ h.toTwoSidedCollar.complement := by
        intro hxrange
        have hxneigh : x ∈ h.neighborhood := by
          rcases hxrange with ⟨s, rfl⟩
          rw [← h.toFun_zero]
          exact (h.toDiffeomorph
            (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩)).2
        exact hxN hxneigh
      have hxpos : x ∈ h.toTwoSidedCollar.positiveSide := by
        rw [h.toTwoSidedCollar.complement_eq_negativeSide_union_positiveSide] at hxcomp
        exact hxcomp.resolve_left hxneg
      simp [hxneg, hxpos]

theorem sideDefiningFunction_eq_zero_iff (x : M) :
    h.sideDefiningFunction x = 0 ↔ x ∈ Set.range e := by
  constructor
  · intro hxzero
    by_contra hxrange
    have hxcomp : x ∈ h.toTwoSidedCollar.complement := hxrange
    rw [h.toTwoSidedCollar.complement_eq_negativeSide_union_positiveSide] at hxcomp
    rcases hxcomp with hxneg | hxpos
    · have := (h.sideDefiningFunction_neg_iff x).mpr hxneg
      linarith
    · have := (h.sideDefiningFunction_pos_iff x).mpr hxpos
      linarith
  · rintro ⟨s, rfl⟩
    let z : symmetricOpenInterval h.radius :=
      ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩
    have hmem : e s ∈ h.neighborhood := by
      rw [← h.toFun_zero]
      exact (h.toDiffeomorph (s, z)).2
    rw [h.sideDefiningFunction_of_mem_neighborhood hmem]
    have heq : (⟨e s, hmem⟩ : h.neighborhood) = h.toDiffeomorph (s, z) := by
      apply Subtype.ext
      exact (h.toFun_zero s).symm
    rw [heq]
    change smoothSignedClamp h.radius h.radius_pos
      ((h.toDiffeomorph.symm (h.toDiffeomorph (s, z))).2 : ℝ) = 0
    rw [h.toDiffeomorph.symm_apply_apply]
    exact (smoothSignedClamp_eq_zero_iff h.radius h.radius_pos z).mpr rfl

theorem sideDefiningFunction_nonpos_set :
    {x : M | h.sideDefiningFunction x ≤ 0} =
      closure h.toTwoSidedCollar.negativeSide := by
  rw [h.toTwoSidedCollar.closure_negativeSide]
  ext x
  constructor
  · intro hx
    change h.sideDefiningFunction x ≤ 0 at hx
    rcases hx.eq_or_lt with hxzero | hxneg
    · exact Or.inr ((h.sideDefiningFunction_eq_zero_iff x).mp hxzero)
    · exact Or.inl ((h.sideDefiningFunction_neg_iff x).mp hxneg)
  · rintro (hxneg | hxzero)
    · exact ((h.sideDefiningFunction_neg_iff x).mpr hxneg).le
    · exact ((h.sideDefiningFunction_eq_zero_iff x).mpr hxzero).le

theorem sideDefiningFunction_nonneg_set :
    {x : M | 0 ≤ h.sideDefiningFunction x} =
      closure h.toTwoSidedCollar.positiveSide := by
  rw [h.toTwoSidedCollar.closure_positiveSide]
  ext x
  constructor
  · intro hx
    change 0 ≤ h.sideDefiningFunction x at hx
    rcases hx.eq_or_lt with hxzero | hxpos
    · exact Or.inr ((h.sideDefiningFunction_eq_zero_iff x).mp hxzero.symm)
    · exact Or.inl ((h.sideDefiningFunction_pos_iff x).mp hxpos)
  · rintro (hxpos | hxzero)
    · exact ((h.sideDefiningFunction_pos_iff x).mpr hxpos).le
    · exact ((h.sideDefiningFunction_eq_zero_iff x).mpr hxzero).ge

end GlobalClassification

noncomputable def neighborhoodLiftAt (x₀ : h.neighborhood) (x : M) : h.neighborhood := by
  classical
  exact if hx : x ∈ h.neighborhood then ⟨x, hx⟩ else x₀

@[simp]
theorem neighborhoodLiftAt_of_mem (x₀ : h.neighborhood) {x : M}
    (hx : x ∈ h.neighborhood) :
    h.neighborhoodLiftAt x₀ x = ⟨x, hx⟩ := by
  simp only [neighborhoodLiftAt, dif_pos hx]

theorem contMDiffAt_neighborhoodLiftAt (x₀ : h.neighborhood) :
    ContMDiffAt J J ∞ (h.neighborhoodLiftAt x₀) x₀.1 := by
  apply (ContMDiffAt.subtypeVal_comp_iff h.neighborhood (h.neighborhoodLiftAt x₀) x₀.1).mp
  have heq :
      (Subtype.val ∘ h.neighborhoodLiftAt x₀) =ᶠ[nhds x₀.1] (id : M → M) := by
    filter_upwards [h.neighborhood.2.mem_nhds x₀.2] with x hx
    simp [Function.comp_apply, h.neighborhoodLiftAt_of_mem x₀ hx]
  exact contMDiffAt_id.congr_of_eventuallyEq heq

noncomputable def ambientCollarSignedValueAt (x₀ : h.neighborhood) (x : M) : ℝ :=
  h.collarSignedValue (h.neighborhoodLiftAt x₀ x)

theorem contMDiffAt_ambientCollarSignedValueAt (x₀ : h.neighborhood) :
    ContMDiffAt J (modelWithCornersSelf ℝ ℝ) ∞
      (h.ambientCollarSignedValueAt x₀) x₀.1 :=
  h.contMDiff_collarSignedValue.contMDiffAt.comp x₀.1
    (h.contMDiffAt_neighborhoodLiftAt x₀)

theorem sideDefiningFunction_eventuallyEq_ambientCollarSignedValueAt
    [Nonempty S] (x₀ : h.neighborhood) :
    h.sideDefiningFunction =ᶠ[nhds x₀.1] h.ambientCollarSignedValueAt x₀ := by
  filter_upwards [h.neighborhood.2.mem_nhds x₀.2] with x hx
  rw [h.sideDefiningFunction_of_mem_neighborhood hx]
  simp only [ambientCollarSignedValueAt, h.neighborhoodLiftAt_of_mem x₀ hx]

theorem contMDiffAt_sideDefiningFunction_of_mem_neighborhood
    [Nonempty S] {x : M} (hx : x ∈ h.neighborhood) :
    ContMDiffAt J (modelWithCornersSelf ℝ ℝ) ∞ h.sideDefiningFunction x := by
  let x₀ : h.neighborhood := ⟨x, hx⟩
  exact (h.contMDiffAt_ambientCollarSignedValueAt x₀).congr_of_eventuallyEq
    (h.sideDefiningFunction_eventuallyEq_ambientCollarSignedValueAt x₀)

theorem mfderiv_collarSignedValue_apply_finiteNormalVector_of_eq_zero
    (x : h.neighborhood) (hx : h.collarSignedValue x = 0) :
    mfderiv J (modelWithCornersSelf ℝ ℝ) h.collarSignedValue x
      (h.finiteNormalVector x) = 1 := by
  rw [(h.collarSignedValue_eventuallyEq_finiteTime_of_eq_zero x hx).mfderiv_eq]
  exact h.mfderiv_finiteTime_apply_finiteNormalVector x

theorem mfderiv_neighborhoodLiftAt_self (x₀ : h.neighborhood) :
    mfderiv J J (h.neighborhoodLiftAt x₀) x₀.1 = ContinuousLinearMap.id ℝ F := by
  have heq :
      (Subtype.val ∘ h.neighborhoodLiftAt x₀) =ᶠ[nhds x₀.1] (id : M → M) := by
    filter_upwards [h.neighborhood.2.mem_nhds x₀.2] with x hx
    simp [Function.comp_apply, h.neighborhoodLiftAt_of_mem x₀ hx]
  have hLiftDiff : MDifferentiableAt J J (h.neighborhoodLiftAt x₀) x₀.1 :=
    (h.contMDiffAt_neighborhoodLiftAt x₀).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hValDiff : MDifferentiableAt J J (Subtype.val : h.neighborhood → M)
      (h.neighborhoodLiftAt x₀ x₀.1) :=
    (contMDiff_subtype_val.contMDiffAt).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x₀.1 hValDiff hLiftDiff
  have heqDeriv := heq.mfderiv_eq (I := J) (I' := J)
  rw [heqDeriv, mfderiv_id,
    DifferentialGeometry.mfderiv_subtype_val] at hcomp
  simpa using! hcomp.symm

theorem mfderiv_ambientCollarSignedValueAt_apply_finiteNormalVector_of_eq_zero
    (x₀ : h.neighborhood) (hx : h.collarSignedValue x₀ = 0) :
    mfderiv J (modelWithCornersSelf ℝ ℝ) (h.ambientCollarSignedValueAt x₀) x₀.1
      (h.finiteNormalVector x₀) = 1 := by
  have hLiftDiff : MDifferentiableAt J J (h.neighborhoodLiftAt x₀) x₀.1 :=
    (h.contMDiffAt_neighborhoodLiftAt x₀).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hValueDiff :
      MDifferentiableAt J (modelWithCornersSelf ℝ ℝ) h.collarSignedValue
        (h.neighborhoodLiftAt x₀ x₀.1) :=
    h.contMDiff_collarSignedValue.contMDiffAt.mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hself : h.neighborhoodLiftAt x₀ x₀.1 = x₀ := by
    exact h.neighborhoodLiftAt_of_mem x₀ x₀.2
  have hcomp := mfderiv_comp x₀.1 hValueDiff hLiftDiff
  change mfderiv J (modelWithCornersSelf ℝ ℝ)
      (h.collarSignedValue ∘ h.neighborhoodLiftAt x₀) x₀.1
        (h.finiteNormalVector x₀) = 1
  rw [hcomp, h.mfderiv_neighborhoodLiftAt_self, hself]
  change mfderiv J (modelWithCornersSelf ℝ ℝ) h.collarSignedValue x₀
    (h.finiteNormalVector x₀) = 1
  exact h.mfderiv_collarSignedValue_apply_finiteNormalVector_of_eq_zero x₀ hx

section GlobalRegularity

variable [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]

omit [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M] in
theorem zeroSlice_subset_neighborhood : Set.range e ⊆ h.neighborhood := by
  rintro _ ⟨s, rfl⟩
  rw [← h.toFun_zero]
  exact (h.toDiffeomorph
    (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩)).2

theorem not_isCriticalPointAt_sideDefiningFunction_of_eq_zero
    (x : M) (hx : h.sideDefiningFunction x = 0) :
    ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt J h.sideDefiningFunction x := by
  let x₀ : h.neighborhood :=
    ⟨x, h.zeroSlice_subset_neighborhood ((h.sideDefiningFunction_eq_zero_iff x).mp hx)⟩
  have hxLocal : h.collarSignedValue x₀ = 0 := by
    rw [← h.sideDefiningFunction_of_mem_neighborhood x₀.2]
    exact hx
  intro hcrit
  change mfderiv J (modelWithCornersSelf ℝ ℝ) h.sideDefiningFunction x = 0 at hcrit
  have heq := (h.sideDefiningFunction_eventuallyEq_ambientCollarSignedValueAt x₀).mfderiv_eq
    (I := J) (I' := modelWithCornersSelf ℝ ℝ)
  have hzero :
      mfderiv J (modelWithCornersSelf ℝ ℝ) (h.ambientCollarSignedValueAt x₀) x
        (h.finiteNormalVector x₀) = 0 := by
    rw [← heq, hcrit]
    rfl
  have hone := h.mfderiv_ambientCollarSignedValueAt_apply_finiteNormalVector_of_eq_zero
    x₀ hxLocal
  change mfderiv J (modelWithCornersSelf ℝ ℝ) (h.ambientCollarSignedValueAt x₀) x
    (h.finiteNormalVector x₀) = 1 at hone
  rw [hone] at hzero
  exact (by norm_num : (1 : ℝ) ≠ 0) hzero

end GlobalRegularity

def centralClosedInterval : Set ℝ :=
  Set.Icc (-(2 * h.radius / 3)) (2 * h.radius / 3)

noncomputable def centralCoreMap (p : S × h.centralClosedInterval) : M :=
  h.toFun (p.1, ⟨p.2, by
    constructor
    · have hp := p.2.2.1
      dsimp [centralClosedInterval] at hp
      nlinarith [h.radius_pos]
    · have hp := p.2.2.2
      dsimp [centralClosedInterval] at hp
      nlinarith [h.radius_pos]⟩)

noncomputable def centralCore : Set M := Set.range h.centralCoreMap

theorem continuous_centralCoreMap : Continuous h.centralCoreMap := by
  apply h.isOpenEmbedding_toFun.continuous.comp
  apply continuous_fst.prodMk
  exact (continuous_subtype_val.comp continuous_snd).subtype_mk _

theorem isCompact_centralCore [CompactSpace S] : IsCompact h.centralCore := by
  let _ : CompactSpace h.centralClosedInterval :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_range h.continuous_centralCoreMap

theorem isClosed_centralCore [CompactSpace S] [T2Space M] : IsClosed h.centralCore :=
  h.isCompact_centralCore.isClosed

theorem centralCore_subset_neighborhood : h.centralCore ⊆ h.neighborhood := by
  rintro _ ⟨p, rfl⟩
  exact (h.toDiffeomorph
    (p.1, ⟨p.2, by
      constructor
      · have hp := p.2.2.1
        dsimp [centralClosedInterval] at hp
        nlinarith [h.radius_pos]
      · have hp := p.2.2.2
        dsimp [centralClosedInterval] at hp
        nlinarith [h.radius_pos]⟩)).2

section ConstantSides

variable [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]

theorem sideDefiningFunction_eq_neg_one_of_mem_negativeSide_diff_centralCore
    {x : M} (hx : x ∈ h.toTwoSidedCollar.negativeSide \ h.centralCore) :
    h.sideDefiningFunction x = -1 := by
  rcases hx with ⟨hxneg, hxcore⟩
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN]
    let q : S × symmetricOpenInterval h.radius := h.toDiffeomorph.symm ⟨x, hxN⟩
    have hqneg : (q.2 : ℝ) < 0 :=
      (h.finiteTime_neg_iff_mem_negativeSide ⟨x, hxN⟩).mpr hxneg
    have hqnot : (q.2 : ℝ) ∉ h.centralClosedInterval := by
      intro hqmem
      apply hxcore
      refine ⟨(q.1, ⟨q.2, hqmem⟩), ?_⟩
      change h.toFun q = x
      exact congrArg Subtype.val (h.toDiffeomorph.apply_symm_apply ⟨x, hxN⟩)
    have hqle : (q.2 : ℝ) ≤ -(2 * h.radius / 3) := by
      rw [centralClosedInterval, Set.mem_Icc, not_and_or] at hqnot
      rcases hqnot with hlow | hhigh
      · exact le_of_not_ge hlow
      · have hupper : 2 * h.radius / 3 < (q.2 : ℝ) := lt_of_not_ge hhigh
        have hupperpos : 0 < 2 * h.radius / 3 := by nlinarith [h.radius_pos]
        exfalso
        linarith
    change smoothSignedClamp h.radius h.radius_pos (h.finiteTime ⟨x, hxN⟩) = -1
    exact smoothSignedClamp_eq_neg_one_of_le_neg_two_thirds
      h.radius h.radius_pos hqle
  · simp [sideDefiningFunction, hxN, hxneg]

theorem sideDefiningFunction_eq_one_of_mem_positiveSide_diff_centralCore
    {x : M} (hx : x ∈ h.toTwoSidedCollar.positiveSide \ h.centralCore) :
    h.sideDefiningFunction x = 1 := by
  rcases hx with ⟨hxpos, hxcore⟩
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN]
    let q : S × symmetricOpenInterval h.radius := h.toDiffeomorph.symm ⟨x, hxN⟩
    have hqpos : 0 < (q.2 : ℝ) :=
      (h.finiteTime_pos_iff_mem_positiveSide ⟨x, hxN⟩).mpr hxpos
    have hqnot : (q.2 : ℝ) ∉ h.centralClosedInterval := by
      intro hqmem
      apply hxcore
      refine ⟨(q.1, ⟨q.2, hqmem⟩), ?_⟩
      change h.toFun q = x
      exact congrArg Subtype.val (h.toDiffeomorph.apply_symm_apply ⟨x, hxN⟩)
    have hqge : 2 * h.radius / 3 ≤ (q.2 : ℝ) := by
      rw [centralClosedInterval, Set.mem_Icc, not_and_or] at hqnot
      rcases hqnot with hlow | hhigh
      · have : ¬ (q.2 : ℝ) ≤ -(2 * h.radius / 3) := by linarith [h.radius_pos]
        exact (this (le_of_not_ge hlow)).elim
      · exact (lt_of_not_ge hhigh).le
    change smoothSignedClamp h.radius h.radius_pos (h.finiteTime ⟨x, hxN⟩) = 1
    exact smoothSignedClamp_eq_one_of_two_thirds_le h.radius h.radius_pos hqge
  · have hxnotneg : x ∉ h.toTwoSidedCollar.negativeSide := fun hxneg =>
      Set.disjoint_left.mp h.toTwoSidedCollar.disjoint_negativeSide_positiveSide hxneg hxpos
    simp [sideDefiningFunction, hxN, hxnotneg]

omit [SimplyConnectedSpace M] in
theorem neighborhood_union_constantSides :
    (h.neighborhood : Set M) ∪
      (h.toTwoSidedCollar.negativeSide \ h.centralCore) ∪
      (h.toTwoSidedCollar.positiveSide \ h.centralCore) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hxN : x ∈ h.neighborhood
  · exact Or.inl (Or.inl hxN)
  · have hxrange : x ∉ Set.range e := fun hxzero =>
      hxN (h.zeroSlice_subset_neighborhood hxzero)
    have hxcomp : x ∈ h.toTwoSidedCollar.complement := hxrange
    rw [h.toTwoSidedCollar.complement_eq_negativeSide_union_positiveSide] at hxcomp
    have hxcore : x ∉ h.centralCore := fun hxcore =>
      hxN (h.centralCore_subset_neighborhood hxcore)
    rcases hxcomp with hxneg | hxpos
    · exact Or.inl (Or.inr ⟨hxneg, hxcore⟩)
    · exact Or.inr ⟨hxpos, hxcore⟩

theorem contMDiff_sideDefiningFunction :
    ContMDiff J (modelWithCornersSelf ℝ ℝ) ∞ h.sideDefiningFunction := by
  apply contMDiff_of_locally_contMDiffOn
  intro x
  have hcover :
      x ∈ (h.neighborhood : Set M) ∪
        (h.toTwoSidedCollar.negativeSide \ h.centralCore) ∪
        (h.toTwoSidedCollar.positiveSide \ h.centralCore) := by
    rw [h.neighborhood_union_constantSides]
    trivial
  rcases hcover with (hxN | hxneg) | hxpos
  · refine ⟨h.neighborhood, h.neighborhood.2, hxN, ?_⟩
    intro y hy
    exact (h.contMDiffAt_sideDefiningFunction_of_mem_neighborhood hy).contMDiffWithinAt
  · let U : Set M := h.toTwoSidedCollar.negativeSide \ h.centralCore
    have hUopen : IsOpen U :=
      h.toTwoSidedCollar.isOpen_negativeSide.sdiff h.isClosed_centralCore
    refine ⟨U, hUopen, hxneg, ?_⟩
    exact contMDiffOn_const.congr (fun y hy =>
      h.sideDefiningFunction_eq_neg_one_of_mem_negativeSide_diff_centralCore hy)
  · let U : Set M := h.toTwoSidedCollar.positiveSide \ h.centralCore
    have hUopen : IsOpen U :=
      h.toTwoSidedCollar.isOpen_positiveSide.sdiff h.isClosed_centralCore
    refine ⟨U, hUopen, hxpos, ?_⟩
    exact contMDiffOn_const.congr (fun y hy =>
      h.sideDefiningFunction_eq_one_of_mem_positiveSide_diff_centralCore hy)

end ConstantSides

noncomputable def oppositeSideDefiningFunction [Nonempty S] (x : M) : ℝ :=
  -h.sideDefiningFunction x

section OppositeSide

variable [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]

theorem contMDiff_oppositeSideDefiningFunction :
    ContMDiff J (modelWithCornersSelf ℝ ℝ) ∞ h.oppositeSideDefiningFunction := by
  change ContMDiff J (modelWithCornersSelf ℝ ℝ) ∞
    (fun x : M => -h.sideDefiningFunction x)
  exact h.contMDiff_sideDefiningFunction.neg

theorem oppositeSideDefiningFunction_eq_zero_iff (x : M) :
    h.oppositeSideDefiningFunction x = 0 ↔ x ∈ Set.range e := by
  rw [oppositeSideDefiningFunction, neg_eq_zero]
  exact h.sideDefiningFunction_eq_zero_iff x

theorem not_isCriticalPointAt_oppositeSideDefiningFunction_of_eq_zero
    (x : M) (hx : h.oppositeSideDefiningFunction x = 0) :
    ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt J
      h.oppositeSideDefiningFunction x := by
  intro hcrit
  apply h.not_isCriticalPointAt_sideDefiningFunction_of_eq_zero x
    ((h.sideDefiningFunction_eq_zero_iff x).mpr
      ((h.oppositeSideDefiningFunction_eq_zero_iff x).mp hx))
  change mfderiv J (modelWithCornersSelf ℝ ℝ) (-h.sideDefiningFunction) x = 0 at hcrit
  rw [mfderiv_neg] at hcrit
  exact neg_eq_zero.mp hcrit

theorem oppositeSideDefiningFunction_nonpos_set :
    {x : M | h.oppositeSideDefiningFunction x ≤ 0} =
      closure h.toTwoSidedCollar.positiveSide := by
  ext x
  change h.oppositeSideDefiningFunction x ≤ 0 ↔
    x ∈ closure h.toTwoSidedCollar.positiveSide
  rw [show h.oppositeSideDefiningFunction x = -h.sideDefiningFunction x by
    rfl, neg_nonpos]
  exact Set.ext_iff.mp h.sideDefiningFunction_nonneg_set x

end OppositeSide

noncomputable abbrev euclideanThreeMorseModelWithCorners :
    ModelWithCorners ℝ (MorseModel 3) (EuclideanSpace ℝ (Fin 3)) :=
  (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).transContinuousLinearEquiv
    (EuclideanSpace.equiv (Fin 3) ℝ)

noncomputable def toMorseThreeModel
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    {H₀ : Type} [TopologicalSpace H₀]
    {I₀ : ModelWithCorners ℝ E₀ H₀}
    {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace H₀ S₀]
    {M₀ : Type} [TopologicalSpace M₀]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₀]
    {e₀ : S₀ → M₀}
    (h₀ : SmoothTwoSidedCollar I₀
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) e₀) :
    SmoothTwoSidedCollar I₀ euclideanThreeMorseModelWithCorners e₀ :=
  h₀.transAmbientModel (EuclideanSpace.equiv (Fin 3) ℝ)

section RegularSublevelBridge

open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Handle

variable [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]
  {J₃ : ModelWithCorners ℝ (MorseModel 3) G}
  [J₃.Boundaryless]
  [IsManifold J₃ (⊤ : WithTop ℕ∞) M]

variable (h₃ : SmoothTwoSidedCollar I J₃ e)

@[reducible]
noncomputable def negativeSideSublevelChartedSpace :
    ChartedSpace (MorseHalfSpace 2) (SublevelSpace h₃.sideDefiningFunction 0) := by
  exact manifoldSublevelChartedSpace (m := 2)
    J₃ h₃.sideDefiningFunction 0
    h₃.contMDiff_sideDefiningFunction
    h₃.not_isCriticalPointAt_sideDefiningFunction_of_eq_zero

theorem negativeSideSublevel_isManifold :
    @IsManifold ℝ _ (MorseModel 3) _ _ (MorseHalfSpace 2) _
      (morseModelWithCornersHalfSpace 2) ∞
      (SublevelSpace h₃.sideDefiningFunction 0) _
      h₃.negativeSideSublevelChartedSpace := by
  exact manifoldSublevelIsManifold (m := 2)
    J₃ h₃.sideDefiningFunction 0
    h₃.contMDiff_sideDefiningFunction
    h₃.not_isCriticalPointAt_sideDefiningFunction_of_eq_zero

theorem negativeSideSublevel_isBoundaryPoint_iff
    (x : SublevelSpace h₃.sideDefiningFunction 0) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (MorseModel 3) _ _
      (MorseHalfSpace 2) _ (morseModelWithCornersHalfSpace 2)
      (SublevelSpace h₃.sideDefiningFunction 0) _
      h₃.negativeSideSublevelChartedSpace x ↔
      x.1 ∈ Set.range e := by
  rw [manifoldSublevelBoundary_iff_mem_levelSet
    J₃ h₃.sideDefiningFunction 0
    h₃.contMDiff_sideDefiningFunction
    h₃.not_isCriticalPointAt_sideDefiningFunction_of_eq_zero]
  exact h₃.sideDefiningFunction_eq_zero_iff x.1

noncomputable def negativeSideClosureHomeomorph :
    {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide} ≃ₜ
      SublevelSpace h₃.sideDefiningFunction 0 := by
  apply Homeomorph.setCongr
  change closure h₃.toTwoSidedCollar.negativeSide =
    {x : M | h₃.sideDefiningFunction x ≤ 0}
  exact h₃.sideDefiningFunction_nonpos_set.symm

@[reducible]
noncomputable def negativeSideClosureChartedSpace :
    ChartedSpace (MorseHalfSpace 2)
      {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide} := by
  let _ : ChartedSpace (MorseHalfSpace 2) (SublevelSpace h₃.sideDefiningFunction 0) :=
    h₃.negativeSideSublevelChartedSpace
  exact chartedSpaceOfHomeomorph h₃.negativeSideClosureHomeomorph

theorem negativeSideClosure_isManifold :
    @IsManifold ℝ _ (MorseModel 3) _ _ (MorseHalfSpace 2) _
      (morseModelWithCornersHalfSpace 2) ∞
      {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide} _
      h₃.negativeSideClosureChartedSpace := by
  let _ : ChartedSpace (MorseHalfSpace 2) (SublevelSpace h₃.sideDefiningFunction 0) :=
    h₃.negativeSideSublevelChartedSpace
  let _ : IsManifold (morseModelWithCornersHalfSpace 2) ∞
      (SublevelSpace h₃.sideDefiningFunction 0) :=
    h₃.negativeSideSublevel_isManifold
  exact isManifoldOfHomeomorph (morseModelWithCornersHalfSpace 2)
    h₃.negativeSideClosureHomeomorph

theorem negativeSideClosure_isBoundaryPoint_iff
    (x : {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide}) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (MorseModel 3) _ _
      (MorseHalfSpace 2) _ (morseModelWithCornersHalfSpace 2)
      {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide} _
      h₃.negativeSideClosureChartedSpace x ↔
      x.1 ∈ Set.range e := by
  let _ : ChartedSpace (MorseHalfSpace 2)
      (SublevelSpace h₃.sideDefiningFunction 0) :=
    h₃.negativeSideSublevelChartedSpace
  let _ : IsManifold (morseModelWithCornersHalfSpace 2) ∞
      (SublevelSpace h₃.sideDefiningFunction 0) :=
    h₃.negativeSideSublevel_isManifold
  let _ : ChartedSpace (MorseHalfSpace 2)
      {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide} :=
    h₃.negativeSideClosureChartedSpace
  let _ : IsManifold (morseModelWithCornersHalfSpace 2) ∞
      {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide} :=
    h₃.negativeSideClosure_isManifold
  let Φ :
      {x : M // x ∈ closure h₃.toTwoSidedCollar.negativeSide} ≃ₘ⟮
          morseModelWithCornersHalfSpace 2, morseModelWithCornersHalfSpace 2⟯
        SublevelSpace h₃.sideDefiningFunction 0 :=
    { toEquiv := h₃.negativeSideClosureHomeomorph.toEquiv
      contMDiff_toFun :=
        contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
          h₃.negativeSideClosureHomeomorph (morseModelWithCornersHalfSpace 2) ∞
      contMDiff_invFun :=
        contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
          h₃.negativeSideClosureHomeomorph (morseModelWithCornersHalfSpace 2) ∞ }
  have hboundary :=
    ((Φ.isLocalDiffeomorph x).isBoundaryPoint_iff
      (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  rw [hboundary]
  have hΦval : (Φ x).1 = x.1 := by
    rfl
  rw [← hΦval]
  exact h₃.negativeSideSublevel_isBoundaryPoint_iff (Φ x)

@[reducible]
noncomputable def positiveSideSublevelChartedSpace :
    ChartedSpace (MorseHalfSpace 2)
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) := by
  exact manifoldSublevelChartedSpace (m := 2)
    J₃ h₃.oppositeSideDefiningFunction 0
    h₃.contMDiff_oppositeSideDefiningFunction
    h₃.not_isCriticalPointAt_oppositeSideDefiningFunction_of_eq_zero

theorem positiveSideSublevel_isManifold :
    @IsManifold ℝ _ (MorseModel 3) _ _ (MorseHalfSpace 2) _
      (morseModelWithCornersHalfSpace 2) ∞
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) _
      h₃.positiveSideSublevelChartedSpace := by
  exact manifoldSublevelIsManifold (m := 2)
    J₃ h₃.oppositeSideDefiningFunction 0
    h₃.contMDiff_oppositeSideDefiningFunction
    h₃.not_isCriticalPointAt_oppositeSideDefiningFunction_of_eq_zero

theorem positiveSideSublevel_isBoundaryPoint_iff
    (x : SublevelSpace h₃.oppositeSideDefiningFunction 0) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (MorseModel 3) _ _
      (MorseHalfSpace 2) _ (morseModelWithCornersHalfSpace 2)
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) _
      h₃.positiveSideSublevelChartedSpace x ↔
      x.1 ∈ Set.range e := by
  rw [manifoldSublevelBoundary_iff_mem_levelSet
    J₃ h₃.oppositeSideDefiningFunction 0
    h₃.contMDiff_oppositeSideDefiningFunction
    h₃.not_isCriticalPointAt_oppositeSideDefiningFunction_of_eq_zero]
  exact h₃.oppositeSideDefiningFunction_eq_zero_iff x.1

noncomputable def positiveSideClosureHomeomorph :
    {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide} ≃ₜ
      SublevelSpace h₃.oppositeSideDefiningFunction 0 := by
  apply Homeomorph.setCongr
  change closure h₃.toTwoSidedCollar.positiveSide =
    {x : M | h₃.oppositeSideDefiningFunction x ≤ 0}
  exact h₃.oppositeSideDefiningFunction_nonpos_set.symm

@[reducible]
noncomputable def positiveSideClosureChartedSpace :
    ChartedSpace (MorseHalfSpace 2)
      {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide} := by
  let _ : ChartedSpace (MorseHalfSpace 2)
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) :=
    h₃.positiveSideSublevelChartedSpace
  exact chartedSpaceOfHomeomorph h₃.positiveSideClosureHomeomorph

theorem positiveSideClosure_isManifold :
    @IsManifold ℝ _ (MorseModel 3) _ _ (MorseHalfSpace 2) _
      (morseModelWithCornersHalfSpace 2) ∞
      {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide} _
      h₃.positiveSideClosureChartedSpace := by
  let _ : ChartedSpace (MorseHalfSpace 2)
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) :=
    h₃.positiveSideSublevelChartedSpace
  let _ : IsManifold (morseModelWithCornersHalfSpace 2) ∞
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) :=
    h₃.positiveSideSublevel_isManifold
  exact isManifoldOfHomeomorph (morseModelWithCornersHalfSpace 2)
    h₃.positiveSideClosureHomeomorph

theorem positiveSideClosure_isBoundaryPoint_iff
    (x : {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide}) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (MorseModel 3) _ _
      (MorseHalfSpace 2) _ (morseModelWithCornersHalfSpace 2)
      {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide} _
      h₃.positiveSideClosureChartedSpace x ↔
      x.1 ∈ Set.range e := by
  let _ : ChartedSpace (MorseHalfSpace 2)
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) :=
    h₃.positiveSideSublevelChartedSpace
  let _ : IsManifold (morseModelWithCornersHalfSpace 2) ∞
      (SublevelSpace h₃.oppositeSideDefiningFunction 0) :=
    h₃.positiveSideSublevel_isManifold
  let _ : ChartedSpace (MorseHalfSpace 2)
      {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide} :=
    h₃.positiveSideClosureChartedSpace
  let _ : IsManifold (morseModelWithCornersHalfSpace 2) ∞
      {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide} :=
    h₃.positiveSideClosure_isManifold
  let Φ :
      {x : M // x ∈ closure h₃.toTwoSidedCollar.positiveSide} ≃ₘ⟮
          morseModelWithCornersHalfSpace 2, morseModelWithCornersHalfSpace 2⟯
        SublevelSpace h₃.oppositeSideDefiningFunction 0 :=
    { toEquiv := h₃.positiveSideClosureHomeomorph.toEquiv
      contMDiff_toFun :=
        contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
          h₃.positiveSideClosureHomeomorph (morseModelWithCornersHalfSpace 2) ∞
      contMDiff_invFun :=
        contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
          h₃.positiveSideClosureHomeomorph (morseModelWithCornersHalfSpace 2) ∞ }
  have hboundary :=
    ((Φ.isLocalDiffeomorph x).isBoundaryPoint_iff
      (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  rw [hboundary]
  have hΦval : (Φ x).1 = x.1 := by
    rfl
  rw [← hΦval]
  exact h₃.positiveSideSublevel_isBoundaryPoint_iff (Φ x)

end RegularSublevelBridge

@[simp]
theorem finiteTime_toFun (p : S × symmetricOpenInterval h.radius) :
    h.finiteTime ⟨h.toFun p, (h.toDiffeomorph p).2⟩ = p.2 := by
  change ((h.toDiffeomorph.symm (h.toDiffeomorph p)).2 : ℝ) = p.2
  rw [h.toDiffeomorph.symm_apply_apply]

@[simp]
theorem collarSignedValue_toFun (p : S × symmetricOpenInterval h.radius) :
    h.collarSignedValue ⟨h.toFun p, (h.toDiffeomorph p).2⟩ =
      smoothSignedClamp h.radius h.radius_pos p.2 := by
  simp [collarSignedValue]

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
