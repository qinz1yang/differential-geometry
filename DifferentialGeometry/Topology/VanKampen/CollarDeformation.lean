import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRetraction
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

noncomputable section

open Set Topology Filter
open scoped ContinuousMap unitInterval

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {S : Type*} [TopologicalSpace S] {X : Type*} [TopologicalSpace X] {e : S → X}

noncomputable def collarScale (t τ : ℝ) : ℝ := min τ (max 0 (t * τ))

theorem continuous_collarScale : Continuous fun z : I × ℝ => collarScale (z.1 : ℝ) z.2 := by
  unfold collarScale
  fun_prop

theorem collarScale_zero (τ : ℝ) : collarScale 0 τ = min τ 0 := by
  unfold collarScale
  norm_num

theorem collarScale_one (τ : ℝ) : collarScale 1 τ = τ := by
  unfold collarScale
  rw [one_mul, min_eq_left (le_max_right (0 : ℝ) τ)]

theorem collarScale_zero_fun : collarScale ((0 : I) : ℝ) = fun τ : ℝ => min τ 0 := by
  funext τ
  rw [show ((0 : I) : ℝ) = 0 from rfl, collarScale_zero]

theorem collarScale_one_fun : collarScale ((1 : I) : ℝ) = fun τ : ℝ => τ := by
  funext τ
  rw [show ((1 : I) : ℝ) = 1 from rfl, collarScale_one]

theorem collarScale_lt_one (t : ℝ) {τ : ℝ} (hτ : τ < 1) : collarScale t τ < 1 :=
  lt_of_le_of_lt (min_le_left _ _) hτ

theorem collarScale_eq_self_of_nonpos {t τ : ℝ} (ht : 0 ≤ t) (hτ : τ ≤ 0) :
    collarScale t τ = τ := by
  unfold collarScale
  rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos ht hτ), min_eq_left hτ]

variable (h : TwoSidedCollar e)

include h

noncomputable def negativeHomotopyValue [Nonempty S] (t : I) (x : h.negativeCover) : X := by
  classical
  exact if hx : x.1 ∈ h.collarSlice (Set.Iio 1) then
      let p := h.homeomorphRange.symm ⟨x.1, h.collarSlice_subset_range _ hx⟩
      h.toFun (p.1, collarScale (t : ℝ) p.2)
    else x.1

theorem negativeHomotopyValue_eq_of_mem_negativeSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    (t : I) (x : h.negativeCover) (hxN : x.1 ∈ h.negativeSide) :
    h.negativeHomotopyValue t x = x.1 := by
  by_cases hx : x.1 ∈ h.collarSlice (Set.Iio 1)
  · let p := h.homeomorphRange.symm
      (⟨x.1, h.collarSlice_subset_range _ hx⟩ : h.range)
    have hp : p.2 < 0 := by
      have := h.time_neg_of_mem_negativeSide_range
        (⟨x.1, h.collarSlice_subset_range _ hx⟩ : h.range) hxN
      change p.2 < 0 at this
      exact this
    unfold negativeHomotopyValue
    rw [dif_pos hx]
    change h.toFun (p.1, collarScale (t : ℝ) p.2) = x.1
    rw [collarScale_eq_self_of_nonpos t.2.1 hp.le]
    exact congrArg Subtype.val (h.homeomorphRange.apply_symm_apply _)
  · unfold negativeHomotopyValue
    rw [dif_neg hx]

theorem negativeHomotopyValue_mem_negativeCover
    [Nonempty S] (t : I) (x : h.negativeCover) :
    h.negativeHomotopyValue t x ∈ h.negativeCover := by
  by_cases hx : x.1 ∈ h.collarSlice (Set.Iio 1)
  · unfold negativeHomotopyValue
    rw [dif_pos hx]
    refine Or.inr ?_
    have hmem : (⟨h.toFun
        ((h.homeomorphRange.symm
            ⟨x.1, h.collarSlice_subset_range _ hx⟩).1,
          collarScale (t : ℝ)
            (h.homeomorphRange.symm ⟨x.1, h.collarSlice_subset_range _ hx⟩).2),
        ⟨_, rfl⟩⟩ : h.range).1 ∈ h.collarSlice (Set.Iio 1) := by
      rw [h.mem_collarSlice_iff_time]
      rw [h.time_mk]
      have hτ : (h.homeomorphRange.symm
          ⟨x.1, h.collarSlice_subset_range _ hx⟩).2 < 1 := by
        have := (h.mem_collarSlice_iff_time (Set.Iio 1)
          ⟨x.1, h.collarSlice_subset_range _ hx⟩).mp hx
        change h.time ⟨x.1, h.collarSlice_subset_range _ hx⟩ < 1 at this
        exact this
      exact collarScale_lt_one _ hτ
    exact hmem
  · unfold negativeHomotopyValue
    rw [dif_neg hx]
    exact x.2

theorem continuous_negativeHomotopyValue
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    Continuous fun z : I × h.negativeCover => h.negativeHomotopyValue z.1 z.2 := by
  let A : Set (I × h.negativeCover) := Set.univ ×ˢ (Subtype.val ⁻¹' h.negativeSide)
  let B : Set (I × h.negativeCover) :=
    Set.univ ×ˢ (Subtype.val ⁻¹' h.collarSlice (Set.Iio 1))
  have hA : IsOpen A := isOpen_univ.prod (h.isOpen_negativeSide.preimage continuous_subtype_val)
  have hB : IsOpen B :=
    isOpen_univ.prod ((h.isOpen_collarSlice isOpen_Iio).preimage continuous_subtype_val)
  have hAB : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    rcases z.2.2 with hn | hc
    · exact Or.inl ⟨trivial, hn⟩
    · exact Or.inr ⟨trivial, hc⟩
  rw [← continuousOn_univ, ← hAB, continuousOn_union_iff_of_isOpen hA hB]
  constructor
  · refine (continuous_subtype_val.comp continuous_snd).continuousOn.congr fun z hz => ?_
    exact h.negativeHomotopyValue_eq_of_mem_negativeSide z.1 z.2 hz.2
  · rw [continuousOn_iff_continuous_domRestrict]
    have hinner : Continuous fun z : B =>
        (⟨z.1.2.1, h.collarSlice_subset_range _ z.2.2⟩ : h.range) :=
      (Continuous.comp (continuous_subtype_val.comp continuous_snd)
        continuous_subtype_val).subtype_mk _
    have hP : Continuous fun z : B => h.homeomorphRange.symm
        (⟨z.1.2.1, h.collarSlice_subset_range _ z.2.2⟩ : h.range) :=
      h.homeomorphRange.symm.continuous.comp hinner
    have hift : Continuous fun z : B => z.1.1 :=
      continuous_fst.comp continuous_subtype_val
    have hq : Continuous fun z : B =>
        (z.1.1, (h.homeomorphRange.symm
          (⟨z.1.2.1, h.collarSlice_subset_range _ z.2.2⟩ : h.range)).2) :=
      Continuous.prodMk hift (continuous_snd.comp hP)
    have hscale : Continuous fun z : B =>
        collarScale (z.1.1 : ℝ)
          (h.homeomorphRange.symm
            (⟨z.1.2.1, h.collarSlice_subset_range _ z.2.2⟩ : h.range)).2 :=
      continuous_collarScale.comp hq
    have hg : Continuous fun z : B => h.toFun
        ((h.homeomorphRange.symm
            (⟨z.1.2.1, h.collarSlice_subset_range _ z.2.2⟩ : h.range)).1,
          collarScale (z.1.1 : ℝ)
            (h.homeomorphRange.symm
              (⟨z.1.2.1, h.collarSlice_subset_range _ z.2.2⟩ : h.range)).2) :=
      h.isOpenEmbedding_toFun.continuous.comp (Continuous.prodMk (continuous_fst.comp hP) hscale)
    apply hg.congr
    intro z
    simp only [Set.domRestrict_apply]
    unfold negativeHomotopyValue
    have hz : z.1.2.1 ∈ h.collarSlice (Set.Iio 1) := z.2.2
    rw [dif_pos hz]

noncomputable def negativeHomotopy
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    C(I × h.negativeCover, h.negativeCover) where
  toFun z := ⟨h.negativeHomotopyValue z.1 z.2, h.negativeHomotopyValue_mem_negativeCover z.1 z.2⟩
  continuous_toFun := h.continuous_negativeHomotopyValue.subtype_mk _

theorem negativeHomotopy_apply_val
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] (t : I) (x : h.negativeCover) :
    (h.negativeHomotopy (t, x)).1 = h.negativeHomotopyValue t x := rfl

theorem negativeHomotopy_zero
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] (x : h.negativeCover) :
    h.negativeHomotopy (0, x) = h.negativeClosureInclusion (h.negativeRetraction x) := by
  apply Subtype.ext
  rw [negativeHomotopy_apply_val]
  change h.negativeHomotopyValue 0 x = h.negativeRetractionValue x
  by_cases hx : x.1 ∈ h.collarSlice (Set.Iio 1)
  · unfold negativeHomotopyValue negativeRetractionValue
    rw [dif_pos hx, dif_pos (h.collarSlice_subset_range _ hx), collarScale_zero_fun]
  · have hxr : x.1 ∉ h.range := by
      intro hr
      have htime : h.time (⟨x.1, hr⟩ : h.range) < 1 := by
        rcases x.2 with hn | hc
        · have := h.time_neg_of_mem_negativeSide_range (⟨x.1, hr⟩ : h.range) hn
          linarith
        · exact (h.mem_collarSlice_iff_time (Set.Iio 1) _).mp hc
      exact hx ((h.mem_collarSlice_iff_time (Set.Iio 1) _).mpr htime)
    unfold negativeHomotopyValue negativeRetractionValue
    rw [dif_neg hx, dif_neg hxr]

theorem negativeHomotopy_one
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] (x : h.negativeCover) :
    h.negativeHomotopy (1, x) = x := by
  apply Subtype.ext
  rw [negativeHomotopy_apply_val]
  by_cases hx : x.1 ∈ h.collarSlice (Set.Iio 1)
  · unfold negativeHomotopyValue
    rw [dif_pos hx]
    change h.toFun
      ((h.homeomorphRange.symm ⟨x.1, h.collarSlice_subset_range _ hx⟩).1,
        collarScale ((1 : I) : ℝ)
          (h.homeomorphRange.symm ⟨x.1, h.collarSlice_subset_range _ hx⟩).2) = x.1
    rw [collarScale_one_fun]
    exact congrArg Subtype.val (h.homeomorphRange.apply_symm_apply _)
  · unfold negativeHomotopyValue
    rw [dif_neg hx]

theorem negativeCover_deformationRetract
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    (h.negativeClosureInclusion.comp h.negativeRetraction).Homotopic
      (ContinuousMap.id h.negativeCover) :=
  ⟨h.negativeHomotopy, fun x => h.negativeHomotopy_zero x,
    fun x => h.negativeHomotopy_one x⟩

theorem simplyConnectedSpace_negativeCover
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X]
    [SimplyConnectedSpace (closure h.negativeSide)] :
    SimplyConnectedSpace h.negativeCover := by
  have he : closure h.negativeSide ≃ₕ h.negativeCover :=
    { toFun := h.negativeClosureInclusion
      invFun := h.negativeRetraction
      left_inv := by
        rw [h.negativeRetraction_comp_inclusion]
      right_inv := h.negativeCover_deformationRetract }
  exact he.simplyConnectedSpace_iff.mp ‹SimplyConnectedSpace (closure h.negativeSide)›

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
