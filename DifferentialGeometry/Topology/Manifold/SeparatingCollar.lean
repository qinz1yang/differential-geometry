import DifferentialGeometry.Topology.Manifold.BicollarComponents
import DifferentialGeometry.Topology.VanKampen.SmoothSideDefiningFunction

set_option autoImplicit false
open Set Topology Manifold
open scoped Manifold ContDiff
noncomputable section

namespace Poincare.Topology.SmoothTwoSidedCollar

variable
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {S : Type} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type} [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)


theorem finiteTime_eq_zero_iff_mem_range (x : h.neighborhood) :
    h.finiteTime x = 0 ↔ x.val ∈ Set.range e := by
  let z : symmetricOpenInterval h.radius :=
    ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩
  constructor
  · intro ht
    let q := h.toDiffeomorph.symm x
    have hq : q.2 = z := Subtype.ext ht
    refine ⟨q.1, ?_⟩
    calc
      e q.1 = h.toFun (q.1, z) := (h.toFun_zero q.1).symm
      _ = h.toFun q := congrArg h.toFun (Prod.ext rfl hq.symm)
      _ = x.val := congrArg Subtype.val (h.toDiffeomorph.apply_symm_apply x)
  · rintro ⟨s, hs⟩
    have heq : x = h.toDiffeomorph (s, z) :=
      Subtype.ext ((h.toFun_zero s).trans hs).symm
    rw [heq]
    simp [finiteTime, z]

theorem sideDefiningFunction_zeroSet [Nonempty S] :
    {x : M | h.sideDefiningFunction x = 0} = Set.range e := by
  ext x
  change h.sideDefiningFunction x = 0 ↔ x ∈ Set.range e
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN, collarSignedValue,
      smoothSignedClamp_eq_zero_iff]
    exact h.finiteTime_eq_zero_iff_mem_range ⟨x, hxN⟩
  · have hr : x ∉ Set.range e := fun hx ↦ hxN (h.zeroSlice_subset_neighborhood hx)
    simp only [sideDefiningFunction, dif_neg hxN, hr, iff_false]
    split_ifs <;> norm_num


theorem exists_mfderiv_sideDefiningFunction_eq_one [Nonempty S]
    {x : M} (hx : h.sideDefiningFunction x = 0) :
    ∃ v : TangentSpace J x,
      mfderiv J 𝓘(ℝ, ℝ) h.sideDefiningFunction x v = 1 := by
  have hxrange : x ∈ Set.range e := (Set.ext_iff.mp h.sideDefiningFunction_zeroSet x).mp hx
  let x₀ : h.neighborhood := ⟨x, h.zeroSlice_subset_neighborhood hxrange⟩
  have hxLocal : h.collarSignedValue x₀ = 0 := by
    rw [← h.sideDefiningFunction_of_mem_neighborhood x₀.2]
    exact hx
  refine ⟨h.finiteNormalVector x₀, ?_⟩
  rw [(h.sideDefiningFunction_eventuallyEq_ambientCollarSignedValueAt x₀).mfderiv_eq]
  exact h.mfderiv_ambientCollarSignedValueAt_apply_finiteNormalVector_of_eq_zero x₀ hxLocal


theorem mfderiv_sideDefiningFunction_ne_zero [Nonempty S]
    {x : M} (hx : h.sideDefiningFunction x = 0) :
    mfderiv J 𝓘(ℝ, ℝ) h.sideDefiningFunction x ≠ 0 := by
  obtain ⟨v, hv⟩ := h.exists_mfderiv_sideDefiningFunction_eq_one hx
  intro hz
  rw [hz] at hv
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hv


theorem sideDefiningFunction_eq_zero_iff_mem_range [Nonempty S] (x : M) :
    h.sideDefiningFunction x = 0 ↔ x ∈ Set.range e :=
  Set.ext_iff.mp h.sideDefiningFunction_zeroSet x

section Separating
variable [CompactSpace S] [ConnectedSpace S] [T2Space M]
  [ConnectedSpace M] [LocallyPathConnectedSpace M]
  (hsep : ¬ IsConnected h.toTwoSidedCollar.complement)

include hsep


theorem finiteTime_neg_iff_mem_negativeSide_of_disconnected (x : h.neighborhood) :
    h.finiteTime x < 0 ↔ x.val ∈ h.toTwoSidedCollar.negativeSide := by
  calc
    h.finiteTime x < 0 ↔ h.rescaledTime x < 0 := h.finiteTime_neg_iff_rescaledTime_neg x
    _ ↔ h.toTwoSidedCollar.toFun ((h.toDiffeomorph.symm x).1, h.rescaledTime x) ∈
        h.toTwoSidedCollar.negativeSide :=
      (h.toTwoSidedCollar.toFun_mem_negativeSide_iff hsep _ _).symm
    _ ↔ x.val ∈ h.toTwoSidedCollar.negativeSide := by
      rw [h.toTwoSidedCollar_toFun_rescaledTime x]


theorem finiteTime_pos_iff_mem_positiveSide_of_disconnected (x : h.neighborhood) :
    0 < h.finiteTime x ↔ x.val ∈ h.toTwoSidedCollar.positiveSide := by
  calc
    0 < h.finiteTime x ↔ 0 < h.rescaledTime x := h.finiteTime_pos_iff_rescaledTime_pos x
    _ ↔ h.toTwoSidedCollar.toFun ((h.toDiffeomorph.symm x).1, h.rescaledTime x) ∈
        h.toTwoSidedCollar.positiveSide :=
      (h.toTwoSidedCollar.toFun_mem_positiveSide_iff hsep _ _).symm
    _ ↔ x.val ∈ h.toTwoSidedCollar.positiveSide := by
      rw [h.toTwoSidedCollar_toFun_rescaledTime x]

theorem sideDefiningFunction_neg_iff_of_disconnected (x : M) :
    h.sideDefiningFunction x < 0 ↔ x ∈ h.toTwoSidedCollar.negativeSide := by
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN,
      collarSignedValue, smoothSignedClamp_neg_iff]
    exact (h.finiteTime_neg_iff_mem_negativeSide_of_disconnected hsep) ⟨x, hxN⟩
  · simp only [sideDefiningFunction, dif_neg hxN]
    by_cases hxneg : x ∈ h.toTwoSidedCollar.negativeSide
    · simp [hxneg]
    · simp [hxneg]

theorem sideDefiningFunction_pos_iff_of_disconnected (x : M) :
    0 < h.sideDefiningFunction x ↔ x ∈ h.toTwoSidedCollar.positiveSide := by
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN,
      collarSignedValue, smoothSignedClamp_pos_iff]
    exact (h.finiteTime_pos_iff_mem_positiveSide_of_disconnected hsep) ⟨x, hxN⟩
  · simp only [sideDefiningFunction, dif_neg hxN]
    by_cases hxneg : x ∈ h.toTwoSidedCollar.negativeSide
    · have hxnotpos : x ∉ h.toTwoSidedCollar.positiveSide := fun hxpos =>
        Set.disjoint_left.mp (h.toTwoSidedCollar.disjoint_negativeSide_positiveSide_of_disconnected hsep) hxneg hxpos
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

theorem sideDefiningFunction_nonpos_set_of_disconnected :
    {x : M | h.sideDefiningFunction x ≤ 0} =
      closure h.toTwoSidedCollar.negativeSide := by
  rw [(h.toTwoSidedCollar.closure_negativeSide_of_disconnected hsep)]
  ext x
  constructor
  · intro hx
    change h.sideDefiningFunction x ≤ 0 at hx
    rcases hx.eq_or_lt with hxzero | hxneg
    · exact Or.inr ((h.sideDefiningFunction_eq_zero_iff_mem_range x).mp hxzero)
    · exact Or.inl (((h.sideDefiningFunction_neg_iff_of_disconnected hsep) x).mp hxneg)
  · rintro (hxneg | hxzero)
    · exact (((h.sideDefiningFunction_neg_iff_of_disconnected hsep) x).mpr hxneg).le
    · exact ((h.sideDefiningFunction_eq_zero_iff_mem_range x).mpr hxzero).le

theorem sideDefiningFunction_nonneg_set_of_disconnected :
    {x : M | 0 ≤ h.sideDefiningFunction x} =
      closure h.toTwoSidedCollar.positiveSide := by
  rw [(h.toTwoSidedCollar.closure_positiveSide_of_disconnected hsep)]
  ext x
  constructor
  · intro hx
    change 0 ≤ h.sideDefiningFunction x at hx
    rcases hx.eq_or_lt with hxzero | hxpos
    · exact Or.inr ((h.sideDefiningFunction_eq_zero_iff_mem_range x).mp hxzero.symm)
    · exact Or.inl (((h.sideDefiningFunction_pos_iff_of_disconnected hsep) x).mp hxpos)
  · rintro (hxpos | hxzero)
    · exact (((h.sideDefiningFunction_pos_iff_of_disconnected hsep) x).mpr hxpos).le
    · exact ((h.sideDefiningFunction_eq_zero_iff_mem_range x).mpr hxzero).ge

theorem sideDefiningFunction_eq_neg_one_of_mem_negativeSide_diff_centralCore_of_disconnected
    {x : M} (hx : x ∈ h.toTwoSidedCollar.negativeSide \ h.centralCore) :
    h.sideDefiningFunction x = -1 := by
  rcases hx with ⟨hxneg, hxcore⟩
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN]
    let q : S × symmetricOpenInterval h.radius := h.toDiffeomorph.symm ⟨x, hxN⟩
    have hqneg : (q.2 : ℝ) < 0 :=
      ((h.finiteTime_neg_iff_mem_negativeSide_of_disconnected hsep) ⟨x, hxN⟩).mpr hxneg
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

theorem sideDefiningFunction_eq_one_of_mem_positiveSide_diff_centralCore_of_disconnected
    {x : M} (hx : x ∈ h.toTwoSidedCollar.positiveSide \ h.centralCore) :
    h.sideDefiningFunction x = 1 := by
  rcases hx with ⟨hxpos, hxcore⟩
  by_cases hxN : x ∈ h.neighborhood
  · rw [h.sideDefiningFunction_of_mem_neighborhood hxN]
    let q : S × symmetricOpenInterval h.radius := h.toDiffeomorph.symm ⟨x, hxN⟩
    have hqpos : 0 < (q.2 : ℝ) :=
      ((h.finiteTime_pos_iff_mem_positiveSide_of_disconnected hsep) ⟨x, hxN⟩).mpr hxpos
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
      Set.disjoint_left.mp (h.toTwoSidedCollar.disjoint_negativeSide_positiveSide_of_disconnected hsep) hxneg hxpos
    simp [sideDefiningFunction, hxN, hxnotneg]

theorem contMDiff_sideDefiningFunction_of_disconnected :
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
      (h.sideDefiningFunction_eq_neg_one_of_mem_negativeSide_diff_centralCore_of_disconnected hsep) hy)
  · let U : Set M := h.toTwoSidedCollar.positiveSide \ h.centralCore
    have hUopen : IsOpen U :=
      h.toTwoSidedCollar.isOpen_positiveSide.sdiff h.isClosed_centralCore
    refine ⟨U, hUopen, hxpos, ?_⟩
    exact contMDiffOn_const.congr (fun y hy =>
      (h.sideDefiningFunction_eq_one_of_mem_positiveSide_diff_centralCore_of_disconnected hsep) hy)


theorem contMDiff_oppositeSideDefiningFunction_of_disconnected :
    ContMDiff J 𝓘(ℝ, ℝ) ∞ h.oppositeSideDefiningFunction :=
  (h.contMDiff_sideDefiningFunction_of_disconnected hsep).neg


theorem oppositeSideDefiningFunction_nonpos_set_of_disconnected :
    {x : M | h.oppositeSideDefiningFunction x ≤ 0} =
      closure h.toTwoSidedCollar.positiveSide := by
  simpa only [oppositeSideDefiningFunction, neg_nonpos] using
    h.sideDefiningFunction_nonneg_set_of_disconnected hsep

end Separating


theorem oppositeSideDefiningFunction_zeroSet [Nonempty S] :
    {x : M | h.oppositeSideDefiningFunction x = 0} = Set.range e := by
  simpa only [oppositeSideDefiningFunction, neg_eq_zero] using h.sideDefiningFunction_zeroSet


theorem mfderiv_oppositeSideDefiningFunction_ne_zero [Nonempty S]
    {x : M} (hx : h.oppositeSideDefiningFunction x = 0) :
    mfderiv J 𝓘(ℝ, ℝ) h.oppositeSideDefiningFunction x ≠ 0 := by
  change mfderiv J 𝓘(ℝ, ℝ) (-h.sideDefiningFunction) x ≠ 0
  rw [mfderiv_neg]
  change -(mfderiv J 𝓘(ℝ, ℝ) h.sideDefiningFunction x : F →L[ℝ] ℝ) ≠ 0
  exact neg_ne_zero.mpr (h.mfderiv_sideDefiningFunction_ne_zero (neg_eq_zero.mp hx))

end Poincare.Topology.SmoothTwoSidedCollar
