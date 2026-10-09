import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassNormal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigon

/-!
# Torus curves: the shear lemma and crossing signs

Chapter 6, packet K08, lane MC4 of the `TorusMappingClassLinear` programme.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

theorem torusCover_mem_of_band {U : Set Torus} (hU : IsOpen U) (hαU : range alphaCircle ⊆ U) :
    ∃ ε > 0, ∀ p : ℝ × ℝ, |p.2| < ε → torusCover p ∈ U := by
  have hα (x : ℝ) : torusCover (x, 0) = alphaCircle (cexp x) := by
    rw [torusCover_eq]
    exact Prod.ext rfl cexp_zero
  obtain ⟨ε, hε, hεU⟩ := exists_box_subset_of_isOpen (hU.preimage continuous_torusCover)
    zero_le_one (fun p hp => by
      have hp' : p = (p.1, 0) := Prod.ext rfl hp.2
      change torusCover p ∈ U
      rw [hp', hα]
      exact hαU ⟨_, rfl⟩)
  refine ⟨ε, hε, fun p hp => ?_⟩
  rw [abs_lt] at hp
  rw [← torusCover_fract]
  exact hεU ⟨⟨by linarith [Int.fract_nonneg p.1], by linarith [Int.fract_lt_one p.1]⟩,
    ⟨hp.1, hp.2⟩⟩

theorem exists_torusMatrix_eq_shear_of_eqOn (φ : TDiff) {U : Set Torus} (hU : IsOpen U)
    (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p) :
    ∃ n : ℤ, torusMatrix φ = !![1, n; 0, 1] := by
  obtain ⟨ε, hε, hεU⟩ := torusCover_mem_of_band hU hαU
  have h₀ : φ (torusCover 0) = torusCover 0 := hφU _ (hεU 0 (by simpa using hε))
  obtain ⟨Φ, hΦ0, hlift, hlift', hdeck⟩ := exists_torusLiftDiffeomorph φ h₀
  have hC : Convex ℝ ((univ : Set ℝ) ×ˢ Ioo (-ε) ε) := convex_univ.prod (convex_Ioo _ _)
  have hmem (q : ℝ × ℝ) : q ∈ (univ : Set ℝ) ×ˢ Ioo (-ε) ε ↔ |q.2| < ε := by
    simp [abs_lt]
  have hband : ∀ p : ℝ × ℝ, |p.2| < ε → Φ p = p := by
    have h := lift_eq_self_of_convex Φ.continuous hlift hC
      (fun q hq => hφU _ (hεU q ((hmem q).mp hq))) ((hmem 0).mpr (by simpa using hε)) hΦ0
    exact fun p hp => h p ((hmem p).mpr hp)
  set A := torusMatrix φ with hA
  have h10 := hdeck 0 1 0
  have h01 := hdeck 0 0 1
  simp only [Prod.fst_zero, Prod.snd_zero, zero_add, hΦ0, Int.cast_one, Int.cast_zero,
    mul_one, mul_zero, add_zero] at h10 h01
  have hΦ10 : Φ (1, 0) = (1, 0) := hband _ (by simpa using hε)
  rw [hΦ10] at h10
  have hA00 : A 0 0 = 1 := by
    have := h10.1
    simp only at this
    exact_mod_cast this.symm
  have hA10 : A 1 0 = 0 := by
    have := h10.2
    simp only at this
    exact_mod_cast this.symm
  have hlineinv : ∀ (x : ℝ) (k : ℤ), ∃ j : ℤ, (Φ.symm (x, k)).2 = j := by
    intro x k
    have hd : (Φ.symm (x, (0 : ℝ) + k)).2 = (Φ.symm (x, 0)).2 +
        ((torusMatrix φ.symm 1 0 * 0 + torusMatrix φ.symm 1 1 * k : ℤ) : ℝ) := by
      have hsymm : Continuous Φ.symm := Φ.symm.continuous
      have := (torusLift_add_int hsymm hlift' (x, 0) 0 k).2
      simpa using this
    have hx0 : Φ.symm (x, 0) = (x, 0) := by
      have := hband (x, 0) (by simpa using hε)
      conv_lhs => rw [← this]
      exact Φ.symm_apply_apply _
    rw [zero_add] at hd
    rw [hd, hx0]
    exact ⟨torusMatrix φ.symm 1 0 * 0 + torusMatrix φ.symm 1 1 * k, by simp⟩
  have hnotint : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ k : ℤ, (Φ (0, y)).2 ≠ k := by
    intro y hy k hk
    obtain ⟨j, hj⟩ := hlineinv (Φ (0, y)).1 k
    have he : Φ.symm ((Φ (0, y)).1, (k : ℝ)) = (0, y) := by
      rw [← hk]
      exact Φ.symm_apply_apply _
    rw [he] at hj
    have h1 : (0 : ℝ) < j := by simp only at hj; rw [← hj]; exact hy.1
    have h2 : (j : ℝ) < 1 := by simp only at hj; rw [← hj]; exact hy.2
    have h1' : 0 < j := by exact_mod_cast h1
    have h2' : j < 1 := by exact_mod_cast h2
    omega
  have hcont : Continuous fun y : ℝ => (Φ (0, y)).2 :=
    continuous_snd.comp (Φ.continuous.comp (continuous_const.prodMk continuous_id))
  set y₀ : ℝ := min (ε / 2) (1 / 2) with hy₀
  have hy₀pos : 0 < y₀ := lt_min (half_pos hε) (by norm_num)
  have hy₀lt : y₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hy₀ε : |y₀| < ε := by
    rw [abs_of_pos hy₀pos]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hΦy₀ : (Φ (0, y₀)).2 = y₀ := by rw [hband _ hy₀ε]
  have hin : ∀ y ∈ Icc y₀ 1, y < 1 → (Φ (0, y)).2 ∈ Ioo (0 : ℝ) 1 := by
    intro y hy hy1
    by_contra hn
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hn
    have hsub : Icc y₀ y ⊆ Ioo (0 : ℝ) 1 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rcases hn with hn | hn
    · obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc' hy.1 hcont.continuousOn
        ⟨hn, by rw [hΦy₀]; exact hy₀pos.le⟩
      exact hnotint u (hsub hu) 0 (by simpa using hu0)
    · obtain ⟨u, hu, hu1⟩ := intermediate_value_Icc hy.1 hcont.continuousOn
        ⟨by rw [hΦy₀]; exact hy₀lt.le, hn⟩
      exact hnotint u (hsub hu) 1 (by simpa using hu1)
  have hle : (Φ (0, 1)).2 ∈ Icc (0 : ℝ) 1 := by
    have hcl : IsClosed (Icc (0 : ℝ) 1) := isClosed_Icc
    have hseq : Filter.Tendsto (fun y : ℝ => (Φ (0, y)).2) (nhdsWithin 1 (Ico y₀ 1))
        (nhds ((Φ (0, 1)).2)) := hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hne : (nhdsWithin (1 : ℝ) (Ico y₀ 1)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hy₀lt.ne]
      exact right_mem_Icc.mpr hy₀lt.le
    refine hcl.mem_of_tendsto hseq ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact Ioo_subset_Icc_self (hin y ⟨hy.1, hy.2.le⟩ hy.2)
  rw [h01.2] at hle
  have hA11 : A 1 1 = 1 := by
    have h0 : (0 : ℤ) ≤ A 1 1 := by exact_mod_cast hle.1
    have h1 : A 1 1 ≤ 1 := by exact_mod_cast hle.2
    rcases (show A 1 1 = 0 ∨ A 1 1 = 1 by omega) with h | h
    · exfalso
      have he : Φ (0, 1) = Φ (A 0 1, 0) := by
        rw [hband (A 0 1, 0) (by simpa using hε)]
        exact Prod.ext h01.1 (by rw [h01.2, h]; simp)
      have := congrArg Prod.snd (Φ.injective he)
      simp at this
    · exact h
  refine ⟨A 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hA00, hA10, hA11]

section Crossing

variable {h : ℝ → ℝ}

theorem exists_strictMonoOn_of_deriv_pos (hh : ContDiff ℝ 1 h) {t : ℝ} (ht : 0 < deriv h t) :
    ∃ δ > 0, StrictMonoOn h (Ioo (t - δ) (t + δ)) := by
  have hc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hc) t ht
  refine ⟨δ, hδ, strictMonoOn_of_deriv_pos (convex_Ioo _ _) hh.continuous.continuousOn ?_⟩
  intro x hx
  rw [interior_Ioo] at hx
  exact hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2])

theorem exists_cross_nhds (hh : ContDiff ℝ 1 h) {t : ℝ} {k : ℤ} (hk : h t = k)
    (ht : 0 < deriv h t) :
    ∃ δ > 0, (∀ u ∈ Ioo t (t + δ), (k : ℝ) < h u ∧ h u < k + 1) ∧
      ∀ u ∈ Ioo (t - δ) t, (k : ℝ) - 1 < h u ∧ h u < k := by
  obtain ⟨δ₁, hδ₁, hmono⟩ := exists_strictMonoOn_of_deriv_pos hh ht
  obtain ⟨δ₂, hδ₂, hcont⟩ := Metric.continuous_iff.mp hh.continuous t 1 one_pos
  have hdist (u : ℝ) (hu : |u - t| < δ₂) : |h u - h t| < 1 := by
    have := hcont u (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  have htm : t ∈ Ioo (t - δ₁) (t + δ₁) := ⟨by linarith, by linarith⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun u hu => ?_, fun u hu => ?_⟩
  · have hu1 : u < t + δ₁ := lt_of_lt_of_le hu.2 (by linarith [min_le_left δ₁ δ₂])
    have hu2 : u < t + δ₂ := lt_of_lt_of_le hu.2 (by linarith [min_le_right δ₁ δ₂])
    have hlt := hmono htm ⟨by linarith [hu.1], hu1⟩ hu.1
    have hd := hdist u (by rw [abs_lt]; constructor <;> linarith [hu.1])
    rw [abs_lt, hk] at hd
    rw [hk] at hlt
    constructor <;> linarith [hd.2]
  · have hu1 : t - δ₁ < u := lt_of_le_of_lt (by linarith [min_le_left δ₁ δ₂]) hu.1
    have hu2 : t - δ₂ < u := lt_of_le_of_lt (by linarith [min_le_right δ₁ δ₂]) hu.1
    have hlt := hmono ⟨hu1, by linarith [hu.2]⟩ htm hu.2
    have hd := hdist u (by rw [abs_lt]; constructor <;> linarith [hu.2])
    rw [abs_lt, hk] at hd
    rw [hk] at hlt
    constructor <;> linarith [hd.1]

theorem exists_cross_nhds_neg (hh : ContDiff ℝ 1 h) {t : ℝ} {k : ℤ} (hk : h t = k)
    (ht : deriv h t < 0) :
    ∃ δ > 0, (∀ u ∈ Ioo t (t + δ), (k : ℝ) - 1 < h u ∧ h u < k) ∧
      ∀ u ∈ Ioo (t - δ) t, (k : ℝ) < h u ∧ h u < k + 1 := by
  have hk' : (-h) t = ((-k : ℤ) : ℝ) := by simp [hk]
  have ht' : 0 < deriv (-h) t := by rw [deriv.neg]; linarith
  obtain ⟨δ, hδ, h1, h2⟩ := exists_cross_nhds (show ContDiff ℝ 1 (-h) from hh.neg) hk' ht'
  refine ⟨δ, hδ, fun u hu => ?_, fun u hu => ?_⟩
  · have := h1 u hu
    simp only [Int.cast_neg, Pi.neg_apply] at this
    constructor <;> linarith [this.1, this.2]
  · have := h2 u hu
    simp only [Int.cast_neg, Pi.neg_apply] at this
    constructor <;> linarith [this.1, this.2]

theorem cross_isolated (hh : ContDiff ℝ 1 h) {t : ℝ} {k : ℤ} (hk : h t = k)
    (ht : deriv h t ≠ 0) :
    ∃ δ > 0, ∀ u ∈ Ioo (t - δ) (t + δ), (∃ j : ℤ, h u = j) → u = t := by
  have key : ∀ δ : ℝ, (∀ u ∈ Ioo t (t + δ), ∃ i : ℤ, (i : ℝ) < h u ∧ h u < i + 1) →
      (∀ u ∈ Ioo (t - δ) t, ∃ i : ℤ, (i : ℝ) < h u ∧ h u < i + 1) →
      ∀ u ∈ Ioo (t - δ) (t + δ), (∃ j : ℤ, h u = j) → u = t := by
    intro δ h1 h2 u hu hj
    obtain ⟨j, hj⟩ := hj
    by_contra hne
    have hb : ∃ i : ℤ, (i : ℝ) < h u ∧ h u < i + 1 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact h2 u ⟨hu.1, hlt⟩
      · exact h1 u ⟨hgt, hu.2⟩
    obtain ⟨i, hi1, hi2⟩ := hb
    rw [hj] at hi1 hi2
    have h3 : i < j := by exact_mod_cast hi1
    have h4 : j < i + 1 := by exact_mod_cast hi2
    omega
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · obtain ⟨δ, hδ, h1, h2⟩ := exists_cross_nhds_neg hh hk hneg
    refine ⟨δ, hδ, key δ (fun u hu => ⟨k - 1, ?_⟩) (fun u hu => ⟨k, h2 u hu⟩)⟩
    have := h1 u hu
    push_cast
    constructor <;> linarith [this.1, this.2]
  · obtain ⟨δ, hδ, h1, h2⟩ := exists_cross_nhds hh hk hpos
    refine ⟨δ, hδ, key δ (fun u hu => ⟨k, h1 u hu⟩) (fun u hu => ⟨k - 1, ?_⟩)⟩
    have := h2 u hu
    push_cast
    constructor <;> linarith [this.1, this.2]

theorem finite_cross (hh : ContDiff ℝ 1 h) (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0)
    (a b : ℝ) : {t | t ∈ Icc a b ∧ ∃ k : ℤ, h t = k}.Finite := by
  set S := {t | t ∈ Icc a b ∧ ∃ k : ℤ, h t = k}
  have hS : IsCompact S := by
    have he : S = Icc a b ∩ h ⁻¹' range ((↑) : ℤ → ℝ) := by
      ext t
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_range]
      exact and_congr_right fun _ => ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
    rw [he]
    exact isCompact_Icc.inter_right
      (Int.isClosedEmbedding_coe_real.isClosed_range.preimage hh.continuous)
  have hiso : ∀ t ∈ S, ∃ U ∈ 𝓝 t, ∀ u ∈ U, u ∈ S → u = t := by
    rintro t ⟨-, k, hk⟩
    obtain ⟨δ, hδ, hδiso⟩ := cross_isolated hh hk (hreg t k hk)
    exact ⟨Ioo (t - δ) (t + δ), Ioo_mem_nhds (by linarith) (by linarith),
      fun u hu huS => hδiso u hu huS.2⟩
  choose! U hU hUiso using hiso
  obtain ⟨F, hFS, hcover⟩ := hS.elim_nhds_subcover U hU
  refine F.finite_toSet.subset fun y hy => ?_
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcover hy)
  rw [hUiso x (hFS x hx) y hyx hy]
  exact hx

theorem forall_mem_Ioo_of_no_cross (hc : Continuous h) {t t' u₀ : ℝ} {k : ℤ}
    (hno : ∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) (hu₀ : u₀ ∈ Ioo t t')
    (hk : (k : ℝ) < h u₀ ∧ h u₀ < k + 1) :
    ∀ u ∈ Ioo t t', (k : ℝ) < h u ∧ h u < k + 1 := by
  intro u hu
  have hsub : uIcc u₀ u ⊆ Ioo t t' := by
    intro w hw
    rcases le_total u₀ u with hle | hle
    · rw [uIcc_of_le hle] at hw
      exact ⟨by linarith [hw.1, hu₀.1], by linarith [hw.2, hu.2]⟩
    · rw [uIcc_of_ge hle] at hw
      exact ⟨by linarith [hw.1, hu.1], by linarith [hw.2, hu₀.2]⟩
  have hivt := intermediate_value_uIcc (a := u₀) (b := u) hc.continuousOn
  by_contra hn
  rw [not_and_or, not_lt, not_lt] at hn
  rcases hn with hn | hn
  · obtain ⟨w, hw, hwk⟩ := hivt (show (k : ℝ) ∈ uIcc (h u₀) (h u) from
      mem_uIcc.mpr (Or.inr ⟨hn, hk.1.le⟩))
    exact hno w (hsub hw) k hwk
  · obtain ⟨w, hw, hwk⟩ := hivt (show ((k + 1 : ℤ) : ℝ) ∈ uIcc (h u₀) (h u) from
      mem_uIcc.mpr (Or.inl ⟨by push_cast; exact hk.2.le, by push_cast; exact hn⟩))
    exact hno w (hsub hw) (k + 1) hwk

theorem mem_Icc_of_forall_Ioo (hc : Continuous h) {t t' : ℝ} (htt' : t < t') {a b : ℝ}
    (hab : ∀ u ∈ Ioo t t', a < h u ∧ h u < b) : h t ∈ Icc a b ∧ h t' ∈ Icc a b := by
  have hsub : h '' closure (Ioo t t') ⊆ Icc a b := by
    refine (image_closure_subset_closure_image hc).trans ?_
    refine closure_minimal ?_ isClosed_Icc
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(hab u hu).1.le, (hab u hu).2.le⟩
  rw [closure_Ioo htt'.ne] at hsub
  exact ⟨hsub ⟨t, left_mem_Icc.mpr htt'.le, rfl⟩, hsub ⟨t', right_mem_Icc.mpr htt'.le, rfl⟩⟩

theorem exists_mem_Ioo_inter (t t' δ : ℝ) (htt' : t < t') (hδ : 0 < δ) :
    ∃ u, u ∈ Ioo t t' ∧ u ∈ Ioo t (t + δ) := by
  refine ⟨t + min δ (t' - t) / 2, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := lt_min hδ (sub_pos.mpr htt')
    linarith
  · linarith [min_le_right δ (t' - t)]
  · have := lt_min hδ (sub_pos.mpr htt')
    linarith
  · linarith [min_le_left δ (t' - t)]

theorem exists_mem_Ioo_inter' (t t' δ : ℝ) (htt' : t < t') (hδ : 0 < δ) :
    ∃ u, u ∈ Ioo t t' ∧ u ∈ Ioo (t' - δ) t' := by
  refine ⟨t' - min δ (t' - t) / 2, ⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [min_le_right δ (t' - t)]
  · have := lt_min hδ (sub_pos.mpr htt')
    linarith
  · linarith [min_le_left δ (t' - t)]
  · have := lt_min hδ (sub_pos.mpr htt')
    linarith

theorem forall_mem_Ioo_of_cross_pos (hh : ContDiff ℝ 1 h) {t t' : ℝ} (htt' : t < t') {k : ℤ}
    (hk : h t = k) (hpos : 0 < deriv h t) (hno : ∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) :
    ∀ u ∈ Ioo t t', (k : ℝ) < h u ∧ h u < k + 1 := by
  obtain ⟨δ, hδ, h1, -⟩ := exists_cross_nhds hh hk hpos
  obtain ⟨u₀, hu₀, hu₀'⟩ := exists_mem_Ioo_inter t t' δ htt' hδ
  exact forall_mem_Ioo_of_no_cross hh.continuous hno hu₀ (h1 u₀ hu₀')

theorem forall_mem_Ioo_of_cross_pos' (hh : ContDiff ℝ 1 h) {t t' : ℝ} (htt' : t < t') {k : ℤ}
    (hk : h t' = k) (hpos : 0 < deriv h t') (hno : ∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) :
    ∀ u ∈ Ioo t t', (k : ℝ) - 1 < h u ∧ h u < k := by
  obtain ⟨δ, hδ, -, h2⟩ := exists_cross_nhds hh hk hpos
  obtain ⟨u₀, hu₀, hu₀'⟩ := exists_mem_Ioo_inter' t t' δ htt' hδ
  have h2' := h2 u₀ hu₀'
  have := forall_mem_Ioo_of_no_cross hh.continuous hno hu₀ (k := k - 1)
    (by push_cast; constructor <;> linarith [h2'.1, h2'.2])
  intro u hu
  have := this u hu
  push_cast at this
  constructor <;> linarith [this.1, this.2]

theorem cross_step (hh : ContDiff ℝ 1 h) (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0)
    {t t' : ℝ} (htt' : t < t') {k k' : ℤ} (hk : h t = k) (hk' : h t' = k')
    (hno : ∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) (hne : h t ≠ h t') (hpos : 0 < deriv h t) :
    0 < deriv h t' ∧ h t' = h t + 1 := by
  have hbr := forall_mem_Ioo_of_cross_pos hh htt' hk hpos hno
  have hcl := (mem_Icc_of_forall_Ioo hh.continuous htt' hbr).2
  rw [hk'] at hcl
  have hc1 : k ≤ k' := by exact_mod_cast hcl.1
  have hc2 : k' ≤ k + 1 := by exact_mod_cast hcl.2
  have hkk' : k' ≠ k := by
    intro he
    apply hne
    rw [hk, hk', he]
  have hval : k' = k + 1 := by omega
  have hval' : h t' = h t + 1 := by rw [hk, hk', hval]; push_cast; ring
  refine ⟨?_, hval'⟩
  by_contra hd
  have hneg : deriv h t' < 0 := lt_of_le_of_ne (not_lt.mp hd) (hreg t' k' hk')
  obtain ⟨δ, hδ, -, h2⟩ := exists_cross_nhds_neg hh hk' hneg
  obtain ⟨u, hu, hu'⟩ := exists_mem_Ioo_inter' t t' δ htt' hδ
  have h3 := (h2 u hu').1
  have h4 := (hbr u hu).2
  rw [hval] at h3
  push_cast at h3
  linarith

theorem cross_propagate (hh : ContDiff ℝ 1 h) (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0)
    {I : Set ℝ} (hI : I.OrdConnected)
    (hno : ∀ t ∈ I, ∀ t' ∈ I, t < t' → (∃ k : ℤ, h t = k) → (∃ k : ℤ, h t' = k) →
      (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t')
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hc₀ : ∃ k : ℤ, h t₀ = k) (hpos : 0 < deriv h t₀) :
    ∀ t ∈ I, t₀ < t → (∃ k : ℤ, h t = k) → 0 < deriv h t ∧ h t₀ < h t := by
  intro t₁ ht₁ h01 hc₁
  by_contra hbad
  set B := {t | t ∈ Icc t₀ t₁ ∧ (∃ k : ℤ, h t = k) ∧ t₀ < t ∧ ¬(0 < deriv h t ∧ h t₀ < h t)}
  have hBfin : B.Finite := (finite_cross hh hreg t₀ t₁).subset fun t ht => ⟨ht.1, ht.2.1⟩
  obtain ⟨u, huB, humin⟩ := Set.exists_min_image B id hBfin
    ⟨t₁, ⟨right_mem_Icc.mpr h01.le, hc₁, h01, hbad⟩⟩
  set P := {t | t ∈ Icc t₀ t₁ ∧ (∃ k : ℤ, h t = k) ∧ t < u}
  have hPfin : P.Finite := (finite_cross hh hreg t₀ t₁).subset fun t ht => ⟨ht.1, ht.2.1⟩
  obtain ⟨v, hvP, hvmax⟩ := Set.exists_max_image P id hPfin
    ⟨t₀, ⟨left_mem_Icc.mpr h01.le, hc₀, huB.2.2.1⟩⟩
  have hvu : v < u := hvP.2.2
  have hnov : ∀ w ∈ Ioo v u, ∀ j : ℤ, h w ≠ j := by
    intro w hw j hj
    have hwP : w ∈ P := ⟨⟨by linarith [hvP.1.1, hw.1], by linarith [huB.1.2, hw.2]⟩,
      ⟨j, hj⟩, hw.2⟩
    have := hvmax w hwP
    simp only [id] at this
    linarith [hw.1]
  have hvgood : 0 < deriv h v ∧ h t₀ ≤ h v := by
    rcases eq_or_lt_of_le hvP.1.1 with he | hlt
    · rw [← he]
      exact ⟨hpos, le_rfl⟩
    · by_contra hn
      have hvB : v ∈ B := ⟨hvP.1, hvP.2.1, hlt, fun hg => hn ⟨hg.1, hg.2.le⟩⟩
      have := humin v hvB
      simp only [id] at this
      linarith
  have hvI : v ∈ I := hI.out ht₀ ht₁ hvP.1
  have huI : u ∈ I := hI.out ht₀ ht₁ huB.1
  obtain ⟨kv, hkv⟩ := hvP.2.1
  obtain ⟨ku, hku⟩ := huB.2.1
  have hne := hno v hvI u huI hvu ⟨kv, hkv⟩ ⟨ku, hku⟩ hnov
  obtain ⟨hd, hval⟩ := cross_step hh hreg hvu hkv hku hnov hne hvgood.1
  exact huB.2.2.2 ⟨hd, by linarith [hvgood.2]⟩

theorem neg_hypotheses {I : Set ℝ} (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0)
    (hno : ∀ t ∈ I, ∀ t' ∈ I, t < t' → (∃ k : ℤ, h t = k) → (∃ k : ℤ, h t' = k) →
      (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t') :
    (∀ t (k : ℤ), (-h) t = k → deriv (-h) t ≠ 0) ∧
      ∀ t ∈ I, ∀ t' ∈ I, t < t' → (∃ k : ℤ, (-h) t = k) → (∃ k : ℤ, (-h) t' = k) →
        (∀ u ∈ Ioo t t', ∀ j : ℤ, (-h) u ≠ j) → (-h) t ≠ (-h) t' := by
  have hcross (t : ℝ) : (∃ k : ℤ, (-h) t = k) ↔ ∃ k : ℤ, h t = k := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨-k, by simp only [Pi.neg_apply] at hk; push_cast; linarith⟩
    · rintro ⟨k, hk⟩
      exact ⟨-k, by simp only [Pi.neg_apply]; push_cast; linarith⟩
  refine ⟨fun t k hk => ?_, fun t ht t' ht' htt' hc hc' hnoc => ?_⟩
  · obtain ⟨j, hj⟩ := (hcross t).mp ⟨k, hk⟩
    rw [deriv.neg, neg_ne_zero]
    exact hreg t j hj
  · have h1 := hno t ht t' ht' htt' ((hcross t).mp hc) ((hcross t').mp hc')
      (fun u hu j hj => hnoc u hu (-j) (by simp only [Pi.neg_apply]; push_cast; linarith))
    simp only [Pi.neg_apply, ne_eq, neg_inj]
    exact h1

theorem cross_sign_eq (hh : ContDiff ℝ 1 h) (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0)
    {I : Set ℝ} (hI : I.OrdConnected)
    (hno : ∀ t ∈ I, ∀ t' ∈ I, t < t' → (∃ k : ℤ, h t = k) → (∃ k : ℤ, h t' = k) →
      (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t')
    {t t' : ℝ} (ht : t ∈ I) (ht' : t' ∈ I) (hc : ∃ k : ℤ, h t = k) (hc' : ∃ k : ℤ, h t' = k)
    (hpos : 0 < deriv h t) : 0 < deriv h t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact (cross_propagate hh hreg hI hno ht hc hpos t' ht' hlt hc').1
  · rwa [← heq]
  · by_contra hn
    obtain ⟨k', hk'⟩ := hc'
    have hneg : deriv h t' < 0 := lt_of_le_of_ne (not_lt.mp hn) (hreg t' k' hk')
    obtain ⟨hreg', hno'⟩ := neg_hypotheses hreg hno
    have := (cross_propagate (show ContDiff ℝ 1 (-h) from hh.neg) hreg' hI hno' ht'
      ⟨-k', by simp [hk']⟩ (by rw [deriv.neg]; linarith) t ht hgt
      (by obtain ⟨k, hk⟩ := hc; exact ⟨-k, by simp [hk]⟩)).1
    rw [deriv.neg] at this
    linarith

theorem forall_ne_int_of_periodic (hh : ContDiff ℝ 1 h)
    (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0) (hper : ∀ t, h (t + 1) = h t)
    (hno : ∀ t t', t < t' → (∃ k : ℤ, h t = k) → (∃ k : ℤ, h t' = k) →
      (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t') :
    ∀ t (k : ℤ), h t ≠ k := by
  have hno' : ∀ t ∈ (univ : Set ℝ), ∀ t' ∈ (univ : Set ℝ), t < t' → (∃ k : ℤ, h t = k) →
      (∃ k : ℤ, h t' = k) → (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t' :=
    fun t _ t' _ => hno t t'
  intro t₀ k hk
  have hc₁ : ∃ j : ℤ, h (t₀ + 1) = j := ⟨k, by rw [hper, hk]⟩
  rcases lt_or_gt_of_ne (hreg t₀ k hk) with hneg | hpos
  · obtain ⟨hreg', hno''⟩ := neg_hypotheses hreg hno'
    have := (cross_propagate (show ContDiff ℝ 1 (-h) from hh.neg) hreg' ordConnected_univ hno''
      (mem_univ t₀) ⟨-k, by simp [hk]⟩ (by rw [deriv.neg]; linarith) (t₀ + 1) (mem_univ _)
      (by linarith)
      (by obtain ⟨j, hj⟩ := hc₁; exact ⟨-j, by simp [hj]⟩)).2
    simp only [Pi.neg_apply, hper] at this
    exact lt_irrefl _ this
  · have := (cross_propagate hh hreg ordConnected_univ hno' (mem_univ t₀) ⟨k, hk⟩ hpos
      (t₀ + 1) (mem_univ _) (by linarith) hc₁).2
    rw [hper] at this
    exact lt_irrefl _ this

theorem exists_cross_of_add_one (hc : Continuous h) (hper : ∀ t, h (t + 1) = h t + 1) :
    ∃ t₀ : ℝ, ∃ k : ℤ, h t₀ = k := by
  have h1 : h 0 < ((⌊h 0⌋ + 1 : ℤ) : ℝ) := by push_cast; exact Int.lt_floor_add_one _
  have h2 : ((⌊h 0⌋ + 1 : ℤ) : ℝ) ≤ h 1 := by
    have := hper 0
    rw [zero_add] at this
    rw [this]
    push_cast
    linarith [Int.floor_le (h 0)]
  obtain ⟨t₀, -, ht₀⟩ := intermediate_value_Icc zero_le_one hc.continuousOn ⟨h1.le, h2⟩
  exact ⟨t₀, _, ht₀⟩

theorem exists_unique_cross_of_add_one (hh : ContDiff ℝ 1 h)
    (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0) (hper : ∀ t, h (t + 1) = h t + 1)
    (hno : ∀ t t', t < t' → (∃ k : ℤ, h t = k) → (∃ k : ℤ, h t' = k) →
      (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t') :
    ∃ t₀ : ℝ, ∃ k : ℤ, h t₀ = k ∧ 0 < deriv h t₀ ∧
      ∀ u ∈ Ioo t₀ (t₀ + 1), (k : ℝ) < h u ∧ h u < k + 1 := by
  have hno' : ∀ t ∈ (univ : Set ℝ), ∀ t' ∈ (univ : Set ℝ), t < t' → (∃ k : ℤ, h t = k) →
      (∃ k : ℤ, h t' = k) → (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t' :=
    fun t _ t' _ => hno t t'
  obtain ⟨t₀, k, hk⟩ := exists_cross_of_add_one hh.continuous hper
  have hc₁ : ∃ j : ℤ, h (t₀ + 1) = j := ⟨k + 1, by rw [hper, hk]; push_cast; ring⟩
  have hpos : 0 < deriv h t₀ := by
    by_contra hn
    have hneg : deriv h t₀ < 0 := lt_of_le_of_ne (not_lt.mp hn) (hreg t₀ k hk)
    obtain ⟨hreg', hno''⟩ := neg_hypotheses hreg hno'
    have := (cross_propagate (show ContDiff ℝ 1 (-h) from hh.neg) hreg' ordConnected_univ hno''
      (mem_univ t₀) ⟨-k, by simp [hk]⟩ (by rw [deriv.neg]; linarith) (t₀ + 1) (mem_univ _)
      (by linarith) (by obtain ⟨j, hj⟩ := hc₁; exact ⟨-j, by simp [hj]⟩)).2
    simp only [Pi.neg_apply, hper] at this
    linarith
  refine ⟨t₀, k, hk, hpos, ?_⟩
  have hnoc : ∀ u ∈ Ioo t₀ (t₀ + 1), ∀ j : ℤ, h u ≠ j := by
    intro u hu j hj
    obtain ⟨hd, hlt⟩ := cross_propagate hh hreg ordConnected_univ hno' (mem_univ t₀) ⟨k, hk⟩
      hpos u (mem_univ u) hu.1 ⟨j, hj⟩
    have hlt' := (cross_propagate hh hreg ordConnected_univ hno' (mem_univ u) ⟨j, hj⟩ hd
      (t₀ + 1) (mem_univ _) hu.2 hc₁).2
    rw [hper, hk, hj] at hlt'
    rw [hk, hj] at hlt
    have h3 : k < j := by exact_mod_cast hlt
    have h4 : j < k + 1 := by exact_mod_cast hlt'
    omega
  exact forall_mem_Ioo_of_cross_pos hh (by linarith) hk hpos hnoc

theorem forall_ne_int_of_eq_endpoint (hh : ContDiff ℝ 1 h)
    (hreg : ∀ t (k : ℤ), h t = k → deriv h t ≠ 0) {a b : ℝ} (hend : h a = h b)
    (hna : ∀ k : ℤ, h a ≠ k)
    (hno : ∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, t < t' → (∃ k : ℤ, h t = k) →
      (∃ k : ℤ, h t' = k) → (∀ u ∈ Ioo t t', ∀ j : ℤ, h u ≠ j) → h t ≠ h t') :
    ∀ t ∈ Icc a b, ∀ k : ℤ, h t ≠ k := by
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ 1 g → (∀ t (k : ℤ), g t = k → deriv g t ≠ 0) →
      g a = g b → (∀ k : ℤ, g a ≠ k) →
      (∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, t < t' → (∃ k : ℤ, g t = k) →
        (∃ k : ℤ, g t' = k) → (∀ u ∈ Ioo t t', ∀ j : ℤ, g u ≠ j) → g t ≠ g t') →
      ∀ y₁ ∈ Icc a b, (∃ k : ℤ, g y₁ = k) → 0 < deriv g y₁ →
      (∀ t ∈ Icc a b, (∃ k : ℤ, g t = k) → y₁ ≤ t) → False := by
    intro g hg hgreg hgend hgna hgno y₁ hy₁ hc₁ hpos hmin
    set F := {t | t ∈ Icc a b ∧ ∃ k : ℤ, g t = k}
    obtain ⟨y₂, hy₂F, hy₂max⟩ := Set.exists_max_image F id (finite_cross hg hgreg a b)
      ⟨y₁, hy₁, hc₁⟩
    have h12 : y₁ ≤ y₂ := hy₂max y₁ ⟨hy₁, hc₁⟩
    have hgood : 0 < deriv g y₂ ∧ g y₁ ≤ g y₂ := by
      rcases eq_or_lt_of_le h12 with he | hlt
      · rw [← he]
        exact ⟨hpos, le_rfl⟩
      · have := cross_propagate hg hgreg ordConnected_Icc hgno hy₁ hc₁ hpos y₂ hy₂F.1 hlt
          hy₂F.2
        exact ⟨this.1, this.2.le⟩
    obtain ⟨k₁, hk₁⟩ := hc₁
    obtain ⟨k₂, hk₂⟩ := hy₂F.2
    have ha1 : a < y₁ := by
      rcases eq_or_lt_of_le hy₁.1 with he | hlt
      · exact absurd (he ▸ hk₁) (hgna k₁)
      · exact hlt
    have hb2 : y₂ < b := by
      rcases eq_or_lt_of_le hy₂F.1.2 with he | hlt
      · exact absurd (by rw [hgend, ← he]; exact hk₂) (hgna k₂)
      · exact hlt
    have hnoa : ∀ u ∈ Ioo a y₁, ∀ j : ℤ, g u ≠ j := by
      intro u hu j hj
      have := hmin u ⟨hu.1.le, by linarith [hu.2, hy₁.2]⟩ ⟨j, hj⟩
      linarith [hu.2]
    have hnob : ∀ u ∈ Ioo y₂ b, ∀ j : ℤ, g u ≠ j := by
      intro u hu j hj
      have := hy₂max u ⟨⟨by linarith [hu.1, hy₂F.1.1], hu.2.le⟩, ⟨j, hj⟩⟩
      simp only [id] at this
      linarith [hu.1]
    have hA := (mem_Icc_of_forall_Ioo hg.continuous ha1
      (forall_mem_Ioo_of_cross_pos' hg ha1 hk₁ hpos hnoa)).1
    have hB := (mem_Icc_of_forall_Ioo hg.continuous hb2
      (forall_mem_Ioo_of_cross_pos hg hb2 hk₂ hgood.1 hnob)).2
    have hA' : g a < k₁ := lt_of_le_of_ne hA.2 (hgna k₁)
    have hB' : (k₂ : ℝ) < g b := lt_of_le_of_ne hB.1 (fun he => hgna k₂ (by rw [hgend, he]))
    rw [hk₁, hk₂] at hgood
    linarith [hgood.2]
  intro t ht k hk
  set F := {t | t ∈ Icc a b ∧ ∃ k : ℤ, h t = k}
  obtain ⟨y₁, hy₁F, hy₁min⟩ := Set.exists_min_image F id (finite_cross hh hreg a b)
    ⟨t, ht, k, hk⟩
  obtain ⟨k₁, hk₁⟩ := hy₁F.2
  have hmin : ∀ t ∈ Icc a b, (∃ k : ℤ, h t = k) → y₁ ≤ t := fun t ht hc => hy₁min t ⟨ht, hc⟩
  rcases lt_or_gt_of_ne (hreg y₁ k₁ hk₁) with hneg | hpos
  · obtain ⟨hreg', hno'⟩ := neg_hypotheses hreg hno
    have hcross (t : ℝ) : (∃ k : ℤ, (-h) t = k) → ∃ k : ℤ, h t = k := by
      rintro ⟨k, hk⟩
      exact ⟨-k, by simp only [Pi.neg_apply] at hk; push_cast; linarith⟩
    refine key (-h) (show ContDiff ℝ 1 (-h) from hh.neg) hreg' (by simp [hend])
      (fun k hk => hna (-k) (by simp only [Pi.neg_apply] at hk; push_cast; linarith)) hno' y₁
      hy₁F.1 ⟨-k₁, by simp [hk₁]⟩ (by rw [deriv.neg]; linarith)
      (fun t ht hc => hmin t ht (hcross t hc))
  · exact key h hh hreg hend hna hno y₁ hy₁F.1 ⟨k₁, hk₁⟩ hpos hmin

end Crossing

section CircleMap

def HasSameSideArcIn (f : Circle → Circle) (s : Circle) (I : Set ℝ) : Prop :=
  ∃ (g : ℝ → ℝ) (σ t₁ t₂ : ℝ), Continuous g ∧ (∀ t, f (cexp t) = cexp (g t)) ∧ cexp σ = s ∧
    t₁ ∈ I ∧ t₂ ∈ I ∧ t₁ < t₂ ∧ g t₁ = σ ∧ g t₂ = σ ∧ ∀ t ∈ Ioo t₁ t₂, f (cexp t) ≠ s

variable {f : Circle → Circle} {g : ℝ → ℝ}

theorem cexp_eq_cexp_iff_sub {σ x : ℝ} : cexp x = cexp σ ↔ ∃ k : ℤ, x - σ = k := by
  rw [cexp_eq_cexp_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩

theorem deriv_ne_zero_of_mfderiv_ne_zero (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfg : ∀ t, f (cexp t) = cexp (g t)) {t : ℝ}
    (hd : mfderiv (𝓡 1) (𝓡 1) f (cexp t) ≠ 0) : deriv g t ≠ 0 := by
  intro h0
  apply hd
  have hcomp : f ∘ cexp = cexp ∘ g := funext hfg
  have hL : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) (f ∘ cexp) t
      ((mfderiv (𝓡 1) (𝓡 1) f (cexp t)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) cexp t)) :=
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (contMDiff_cexp.mdifferentiableAt (by simp)).hasMFDerivAt
  have hR : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) (cexp ∘ g) t
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) cexp (g t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g t)) :=
    (contMDiff_cexp.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (hg.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have hL' := hL.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hcomp.symm)
  have huniq := hasMFDerivAt_unique hL' hR
  have h3 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g t = 0 := by
    rw [mfderiv_eq_fderiv, ← toSpanSingleton_deriv, h0]
    simp
  obtain ⟨e, he⟩ := (isLocalDiffeomorph_cexp t).isInvertible_mfderiv (by simp)
  ext v
  have hv := DFunLike.congr_fun huniq (e.symm v)
  rw [h3] at hv
  simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero] at hv
  have hev : (e : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace (𝓡 1) (cexp t)) (e.symm v) = v :=
    e.apply_symm_apply v
  rw [← he, hev] at hv
  exact hv

theorem cross_hypotheses (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ t, f (cexp t) = cexp (g t)) {s : Circle} {σ : ℝ} (hσ : cexp σ = s)
    (hs : ∀ z, f z = s → mfderiv (𝓡 1) (𝓡 1) f z ≠ 0) {I : Set ℝ}
    (hno : ¬ HasSameSideArcIn f s I) :
    ContDiff ℝ 1 (fun x => g x - σ) ∧
      (∀ t, f (cexp t) = s ↔ ∃ k : ℤ, (fun x => g x - σ) t = k) ∧
      (∀ t (k : ℤ), (fun x => g x - σ) t = k → deriv (fun x => g x - σ) t ≠ 0) ∧
      ∀ t ∈ I, ∀ t' ∈ I, t < t' → (∃ k : ℤ, (fun x => g x - σ) t = k) →
        (∃ k : ℤ, (fun x => g x - σ) t' = k) →
        (∀ u ∈ Ioo t t', ∀ j : ℤ, (fun x => g x - σ) u ≠ j) →
        (fun x => g x - σ) t ≠ (fun x => g x - σ) t' := by
  have hcross (t : ℝ) : f (cexp t) = s ↔ ∃ k : ℤ, (fun x => g x - σ) t = k := by
    rw [hfg, ← hσ, cexp_eq_cexp_iff_sub]
  refine ⟨(hg.sub contDiff_const).of_le (by simp), hcross, fun t k hk => ?_,
    fun t ht t' ht' htt' hc _ hnoc heq => ?_⟩
  · rw [deriv_sub_const]
    exact deriv_ne_zero_of_mfderiv_ne_zero hf hg hfg (hs _ ((hcross t).mpr ⟨k, hk⟩))
  · obtain ⟨k, hk⟩ := hc
    apply hno
    refine ⟨g, σ + k, t, t', hg.continuous, hfg, by rw [cexp_add_int, hσ], ht, ht', htt',
      by simp only at hk; linarith, by simp only at hk heq; linarith, fun u hu hfu => ?_⟩
    obtain ⟨j, hj⟩ := (hcross u).mp hfu
    exact hnoc u hu j hj

end CircleMap

theorem heightOnCircle_cexp {φ : TDiff} {Φ : ℝ × ℝ → ℝ × ℝ}
    (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p)) (t : ℝ) :
    heightOnCircle φ (cexp t) = cexp (Φ (t, 0)).2 := by
  have hα : alphaCircle (cexp t) = torusCover (t, 0) := by
    rw [torusCover_eq]
    exact Prod.ext rfl cexp_zero.symm
  rw [heightOnCircle, hα, hlift, torusCover_eq]

theorem forall_heightOnCircle_ne_of_not_hasSameSideArc (φ : TDiff) (h : torusMatrix φ = 1)
    {s : Circle} (hs : IsRegularHeight φ s) (hno : ¬ HasSameSideArcIn (heightOnCircle φ) s univ) :
    ∀ z, heightOnCircle φ z ≠ s := by
  obtain ⟨Φ, hΦ, hlift, hdeck⟩ := exists_torusLift φ
  set g : ℝ → ℝ := fun t => (Φ (t, 0)).2
  have hg : ContDiff ℝ ∞ g := hΦ.snd.comp (contDiff_id.prodMk contDiff_const)
  have hfg (t : ℝ) : heightOnCircle φ (cexp t) = cexp (g t) := heightOnCircle_cexp hlift t
  obtain ⟨hh, hcross, hreg, hno'⟩ := cross_hypotheses (contMDiff_heightOnCircle φ) hg hfg
    (cexp_rep s) hs hno
  have hper (t : ℝ) : (fun x => g x - rep s) (t + 1) = (fun x => g x - rep s) t := by
    have := (hdeck (t, 0) 1 0).2
    simp only [h, Int.cast_one, add_zero, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
      Matrix.one_apply_eq, mul_one, mul_zero, Int.cast_zero] at this
    simp only [g, this]
  have hall := forall_ne_int_of_periodic hh hreg hper
    (fun t t' htt' hc hc' hnoc => hno' t (mem_univ t) t' (mem_univ t') htt' hc hc' hnoc)
  intro z hz
  obtain ⟨k, hk⟩ := (hcross (rep z)).mp (by rw [cexp_rep]; exact hz)
  exact hall _ k hk

end GC.Seifert
