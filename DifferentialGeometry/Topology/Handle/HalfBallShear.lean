import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

noncomputable def halfBallShearRadiusSq (t : ℝ) : ℝ := (1 - t / 2) ^ 2 * (1 - t ^ 2)

theorem hasDerivAt_halfBallShearRadiusSq (t : ℝ) :
    HasDerivAt halfBallShearRadiusSq (-(1 - t / 2) * (1 + 2 * t - 2 * t ^ 2)) t := by
  have h := (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const 2)).pow 2).mul
    ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2))
  convert! h using 1
  norm_num [halfBallShearRadiusSq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

theorem deriv_halfBallShearRadiusSq_neg {t : ℝ} (ht : t ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4)) :
    deriv halfBallShearRadiusSq t < 0 := by
  rw [(hasDerivAt_halfBallShearRadiusSq t).deriv]
  have hfirst : 0 < 1 - t / 2 := by linarith [ht.2]
  have hsecond : 0 < 1 + 2 * t - 2 * t ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfirst) hsecond

theorem contDiff_halfBallShearRadiusSq : ContDiff ℝ ∞ halfBallShearRadiusSq := by
  unfold halfBallShearRadiusSq
  fun_prop

theorem strictAntiOn_halfBallShearRadiusSq :
    StrictAntiOn halfBallShearRadiusSq (Ioo (-(1 / 4 : ℝ)) (5 / 4)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) contDiff_halfBallShearRadiusSq.continuous.continuousOn
  intro t ht
  exact deriv_halfBallShearRadiusSq_neg (interior_subset ht)

private theorem exists_halfBallShearRadiusSq_inverse :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e.source = Ioo (-(1 / 4 : ℝ)) (5 / 4) ∧
      e.target = halfBallShearRadiusSq '' Ioo (-(1 / 4 : ℝ)) (5 / 4) ∧
      ∀ t, e t = halfBallShearRadiusSq t := by
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ halfBallShearRadiusSq
      (Ioo (-(1 / 4 : ℝ)) (5 / 4)) := by
    intro t
    have hd := (deriv_halfBallShearRadiusSq_neg t.property).ne
    have hdf := ((hasDerivAt_halfBallShearRadiusSq t).hasFDerivAt_equiv
      (by rwa [← (hasDerivAt_halfBallShearRadiusSq t).deriv]))
    obtain ⟨e, ht, _, he, hei, heq⟩ :=
      DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
        contDiff_halfBallShearRadiusSq.contDiffOn isOpen_univ (mem_univ t) hdf
    let e' : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
      { e with contMDiffOn_toFun := he.contMDiffOn, contMDiffOn_invFun := hei.contMDiffOn }
    exact ⟨e', ht, fun x _ => (heq x).symm⟩
  obtain ⟨e, hs, ht, he⟩ := DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    hlocal isOpen_Ioo (by use 0; norm_num) strictAntiOn_halfBallShearRadiusSq.injOn
  exact ⟨e, hs, ht, congrFun he⟩

private theorem halfBallShearRadiusSq_image_Ioo :
    halfBallShearRadiusSq '' Ioo (-(1 / 4 : ℝ)) (5 / 4) =
      Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4))) := by
  apply contDiff_halfBallShearRadiusSq.continuous.continuousOn.image_Ioo_of_strictAntiOn
    (by norm_num)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) contDiff_halfBallShearRadiusSq.continuous.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  exact deriv_halfBallShearRadiusSq_neg ht

private noncomputable def halfBallShearRadiusDiffeomorph :=
  Classical.choose exists_halfBallShearRadiusSq_inverse

private theorem halfBallShearRadiusDiffeomorph_source :
    halfBallShearRadiusDiffeomorph.source = Ioo (-(1 / 4 : ℝ)) (5 / 4) :=
  (Classical.choose_spec exists_halfBallShearRadiusSq_inverse).1

private theorem halfBallShearRadiusDiffeomorph_target :
    halfBallShearRadiusDiffeomorph.target =
      Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4))) :=
  (Classical.choose_spec exists_halfBallShearRadiusSq_inverse).2.1.trans halfBallShearRadiusSq_image_Ioo

private theorem halfBallShearRadiusDiffeomorph_apply (t : ℝ) :
    halfBallShearRadiusDiffeomorph t = halfBallShearRadiusSq t :=
  (Classical.choose_spec exists_halfBallShearRadiusSq_inverse).2.2 t

noncomputable def halfBallShearHeight (s : ℝ) : ℝ := halfBallShearRadiusDiffeomorph.symm s

theorem halfBallShearHeight_mem_Ioo {s : ℝ}
    (hs : s ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) :
    halfBallShearHeight s ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) := by
  rw [← halfBallShearRadiusDiffeomorph_source]
  exact halfBallShearRadiusDiffeomorph.map_target (halfBallShearRadiusDiffeomorph_target ▸ hs)

theorem halfBallShearHeight_radiusSq {t : ℝ} (ht : t ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4)) :
    halfBallShearHeight (halfBallShearRadiusSq t) = t := by
  rw [halfBallShearHeight, ← halfBallShearRadiusDiffeomorph_apply]
  exact halfBallShearRadiusDiffeomorph.left_inv (halfBallShearRadiusDiffeomorph_source ▸ ht)

theorem halfBallShearRadiusSq_height {s : ℝ}
    (hs : s ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) :
    halfBallShearRadiusSq (halfBallShearHeight s) = s := by
  rw [← halfBallShearRadiusDiffeomorph_apply]
  exact halfBallShearRadiusDiffeomorph.right_inv (halfBallShearRadiusDiffeomorph_target ▸ hs)

theorem contDiffOn_halfBallShearHeight : ContDiffOn ℝ ∞ halfBallShearHeight
    (Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) := by
  rw [← halfBallShearRadiusDiffeomorph_target]
  exact contMDiffOn_iff_contDiffOn.mp halfBallShearRadiusDiffeomorph.contMDiffOn_invFun

theorem strictAntiOn_halfBallShearHeight : StrictAntiOn halfBallShearHeight
    (Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4)))) := by
  intro s hs t ht hst
  apply (strictAntiOn_halfBallShearRadiusSq.lt_iff_gt
    (halfBallShearHeight_mem_Ioo hs) (halfBallShearHeight_mem_Ioo ht)).mp
  rwa [halfBallShearRadiusSq_height hs, halfBallShearRadiusSq_height ht]

@[simp] theorem halfBallShearHeight_zero : halfBallShearHeight 0 = 1 := by
  have h := halfBallShearHeight_radiusSq (t := 1) (by norm_num)
  simpa only [halfBallShearRadiusSq, one_pow, sub_self, mul_zero] using h

@[simp] theorem halfBallShearHeight_one : halfBallShearHeight 1 = 0 := by
  have h := halfBallShearHeight_radiusSq (t := 0) (by norm_num)
  simpa only [halfBallShearRadiusSq, zero_pow (by decide : 2 ≠ 0), zero_div,
    sub_zero, one_pow, one_mul] using h

theorem Icc_subset_halfBallShearHeight_domain :
    Icc (0 : ℝ) 1 ⊆ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4))) := by
  intro s hs
  norm_num [halfBallShearRadiusSq] at *
  constructor <;> linarith [hs.1, hs.2]

theorem halfBallShearHeight_mem_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    halfBallShearHeight s ∈ Icc (0 : ℝ) 1 := by
  have hzero := strictAntiOn_halfBallShearHeight.antitoneOn
    (Icc_subset_halfBallShearHeight_domain (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1))
    (Icc_subset_halfBallShearHeight_domain hs) hs.1
  have hone := strictAntiOn_halfBallShearHeight.antitoneOn
    (Icc_subset_halfBallShearHeight_domain hs)
    (Icc_subset_halfBallShearHeight_domain (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)) hs.2
  exact ⟨by simpa only [halfBallShearHeight_one] using hone,
    by simpa only [halfBallShearHeight_zero] using hzero⟩

end DifferentialGeometry.Topology.Handle

namespace PartialDiffeomorph

open DifferentialGeometry.Topology.Handle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def halfBallShear :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ :=
  fiberwiseSmulOn (f := fun t : ℝ => 1 - t / 2) (U := Iio (2 : ℝ)) isOpen_Iio
    ((contDiff_const.sub (contDiff_id.div_const 2)).contDiffOn)
    (fun t ht => ne_of_gt (by change t < 2 at ht; linarith))

theorem halfBallShear_apply (p : E × ℝ) :
    halfBallShear p = ((1 - p.2 / 2) • p.1, p.2) := rfl

theorem halfBallShear_symm_apply (p : E × ℝ) :
    halfBallShear.symm p = ((1 - p.2 / 2)⁻¹ • p.1, p.2) := rfl

@[simp] theorem halfBallShear_source : (halfBallShear (E := E)).source = {p | p.2 < 2} := rfl

@[simp] theorem halfBallShear_target : (halfBallShear (E := E)).target = {p | p.2 < 2} := rfl

theorem halfBall_subset_halfBallShear_source :
    {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ halfBallShear.source := by
  intro p hp
  change p.2 < 2
  nlinarith [hp.1, sq_nonneg ‖p.1‖]

private theorem halfBallShear_norm_sq (p : E × ℝ) :
    ‖(halfBallShear p).1‖ ^ 2 = (1 - p.2 / 2) ^ 2 * ‖p.1‖ ^ 2 := by
  simp only [halfBallShear_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem halfBallShear_height_le {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : t ≤ halfBallShearHeight s ↔ s ≤ halfBallShearRadiusSq t := by
  have hti : t ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hh := strictAntiOn_halfBallShearRadiusSq.le_iff_ge
    (halfBallShearHeight_mem_Ioo (Icc_subset_halfBallShearHeight_domain hs)) hti
  rw [halfBallShearRadiusSq_height (Icc_subset_halfBallShearHeight_domain hs)] at hh
  exact hh.symm

theorem halfBallShear_image_halfBall :
    halfBallShear (E := E) '' {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} =
      {p | ‖p.1‖ ^ 2 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ halfBallShearHeight (‖p.1‖ ^ 2)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have ht : q.2 ∈ Icc (0 : ℝ) 1 := ⟨hq.2, by nlinarith [hq.1, sq_nonneg ‖q.1‖]⟩
    have hineq : ‖(halfBallShear q).1‖ ^ 2 ≤ halfBallShearRadiusSq q.2 := by
      rw [halfBallShear_norm_sq, halfBallShearRadiusSq]
      exact mul_le_mul_of_nonneg_left (by linarith [hq.1]) (sq_nonneg _)
    have hqbound : halfBallShearRadiusSq q.2 ≤ 1 := by
      have hh := strictAntiOn_halfBallShearRadiusSq.antitoneOn
        (by norm_num : (0 : ℝ) ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4))
        (show q.2 ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) from ⟨by linarith [ht.1], by linarith [ht.2]⟩) ht.1
      simpa [halfBallShearRadiusSq] using hh
    exact ⟨hineq.trans hqbound, hq.2,
      (halfBallShear_height_le ⟨sq_nonneg _, hineq.trans hqbound⟩ ht).mpr hineq⟩
  · intro hp
    have hs : ‖p.1‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, hp.1⟩
    have ht : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp.2.1,
      hp.2.2.trans (halfBallShearHeight_mem_Icc hs).2⟩
    have hscale : 0 < 1 - p.2 / 2 := by linarith [ht.2]
    have hineq := (halfBallShear_height_le hs ht).mp hp.2.2
    let q : E × ℝ := ((1 - p.2 / 2)⁻¹ • p.1, p.2)
    refine ⟨q, ⟨?_, hp.2.1⟩, ?_⟩
    · have hratio : ‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 ≤ 1 - p.2 ^ 2 := by
        apply (div_le_iff₀ (sq_pos_of_pos hscale)).mpr
        simpa only [halfBallShearRadiusSq, mul_comm] using hineq
      have hn : ‖q.1‖ ^ 2 = ‖p.1‖ ^ 2 / (1 - p.2 / 2) ^ 2 := by
        simp only [q, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, div_eq_inv_mul]
      change ‖q.1‖ ^ 2 + p.2 ^ 2 ≤ 1
      rw [hn]
      linarith
    · ext <;> simp [halfBallShear_apply, q, smul_smul, hscale.ne']

theorem halfBallShear_image_halfspace :
    halfBallShear (E := E) '' {p | p.2 ≤ 0} = {p | p.2 ≤ 0} := by
  apply Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    exact hq
  · intro p hp
    have hscale : 1 - p.2 / 2 ≠ 0 := by change p.2 ≤ 0 at hp; linarith
    refine ⟨((1 - p.2 / 2)⁻¹ • p.1, p.2), hp, ?_⟩
    ext <;> simp [halfBallShear_apply, smul_smul, hscale]

end PartialDiffeomorph

namespace DifferentialGeometry.Topology.Handle

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def halfBallShearRoof (x : E) : ℝ :=
  if ‖x‖ ^ 2 ≤ 1 then halfBallShearHeight (‖x‖ ^ 2) else 0

theorem halfBallShearRoof_nonneg (x : E) : 0 ≤ halfBallShearRoof x := by
  unfold halfBallShearRoof
  split_ifs with hx
  · exact (halfBallShearHeight_mem_Icc ⟨sq_nonneg _, hx⟩).1
  · rfl

theorem halfBallShear_image_halfspace_union_halfBall [NormedSpace ℝ E] :
    PartialDiffeomorph.halfBallShear (E := E) ''
      ({p | p.2 ≤ 0} ∪ {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}) =
      {p | p.2 ≤ halfBallShearRoof p.1} := by
  rw [image_union, PartialDiffeomorph.halfBallShear_image_halfspace,
    PartialDiffeomorph.halfBallShear_image_halfBall]
  ext p
  constructor
  · rintro (hp | hp)
    · exact hp.trans (halfBallShearRoof_nonneg p.1)
    · simpa only [mem_ofPred_eq, halfBallShearRoof, if_pos hp.1] using hp.2.2
  · intro hp
    by_cases ht : p.2 ≤ 0
    · exact Or.inl ht
    · have hx : ‖p.1‖ ^ 2 ≤ 1 := by
        by_contra hh
        simp only [mem_ofPred_eq, halfBallShearRoof, if_neg hh] at hp
        exact ht hp
      exact Or.inr ⟨hx, (lt_of_not_ge ht).le,
        by simpa only [mem_ofPred_eq, halfBallShearRoof, if_pos hx] using hp⟩

theorem halfBallShearRoof_le_apply_iff [NormedSpace ℝ E] {p : E × ℝ} (hp : p.2 < 2) :
    halfBallShearRoof (PartialDiffeomorph.halfBallShear p).1 ≤ p.2 ↔
      0 ≤ p.2 ∧ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  let s := ‖(PartialDiffeomorph.halfBallShear p).1‖ ^ 2
  have hs : 0 ≤ s := sq_nonneg _
  have hscale : 0 < (1 - p.2 / 2) ^ 2 := sq_pos_of_pos (by linarith)
  have hseq : s = (1 - p.2 / 2) ^ 2 * ‖p.1‖ ^ 2 := by
    simp only [s, PartialDiffeomorph.halfBallShear_apply, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases ht : 0 ≤ p.2
  · simp only [ht, true_and]
    by_cases ht1 : p.2 ≤ 1
    · by_cases hs1 : s ≤ 1
      · have hsi := Icc_subset_halfBallShearHeight_domain ⟨hs, hs1⟩
        have hti : p.2 ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) := ⟨by linarith, by linarith⟩
        have hh := strictAntiOn_halfBallShearRadiusSq.le_iff_ge hti
          (halfBallShearHeight_mem_Ioo hsi)
        rw [halfBallShearRadiusSq_height hsi] at hh
        change (if s ≤ 1 then halfBallShearHeight s else 0) ≤ p.2 ↔ _
        rw [if_pos hs1, ← hh, halfBallShearRadiusSq, hseq,
          mul_le_mul_iff_right₀ hscale]
        exact ⟨fun h => by linarith, fun h => by linarith⟩
      · have hnorm : 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
          have hsc : (1 - p.2 / 2) ^ 2 ≤ 1 := by nlinarith
          have hmul := mul_le_mul_of_nonneg_right hsc (sq_nonneg ‖p.1‖)
          nlinarith
        simp only [halfBallShearRoof, show ¬ ‖(PartialDiffeomorph.halfBallShear p).1‖ ^ 2 ≤ 1 from hs1,
          if_false, ht, hnorm]
    · have hroof : halfBallShearRoof (PartialDiffeomorph.halfBallShear p).1 ≤ 1 := by
        unfold halfBallShearRoof
        split_ifs with h
        · exact (halfBallShearHeight_mem_Icc ⟨sq_nonneg _, h⟩).2
        · norm_num
      have hr : halfBallShearRoof (PartialDiffeomorph.halfBallShear p).1 ≤ p.2 := by linarith
      have hn : 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by nlinarith [sq_nonneg ‖p.1‖]
      exact iff_of_true hr hn
  · have hroof := halfBallShearRoof_nonneg (PartialDiffeomorph.halfBallShear p).1
    constructor
    · intro h
      exact (ht (hroof.trans h)).elim
    · exact fun h => (ht h.1).elim

theorem le_halfBallShearRoof_apply_iff [NormedSpace ℝ E] {p : E × ℝ} (hp : p.2 < 2) :
    p.2 ≤ halfBallShearRoof (PartialDiffeomorph.halfBallShear p).1 ↔
      p.2 ≤ 0 ∨ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 := by
  let A : Set (E × ℝ) := {p | p.2 ≤ 0} ∪ {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}
  have hA : A ⊆ PartialDiffeomorph.halfBallShear.source := by
    rintro x (hx | hx)
    · change x.2 < 2
      change x.2 ≤ 0 at hx
      linarith
    · exact PartialDiffeomorph.halfBall_subset_halfBallShear_source hx
  have hmem : PartialDiffeomorph.halfBallShear p ∈ PartialDiffeomorph.halfBallShear '' A ↔ p ∈ A := by
    constructor
    · rintro ⟨q, hq, heq⟩
      exact PartialDiffeomorph.halfBallShear.toPartialEquiv.injOn (hA hq) hp heq ▸ hq
    · exact fun h => ⟨p, h, rfl⟩
  rw [halfBallShear_image_halfspace_union_halfBall] at hmem
  change p.2 ≤ halfBallShearRoof (PartialDiffeomorph.halfBallShear p).1 ↔ _ at hmem
  rw [hmem]
  change (p.2 ≤ 0 ∨ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2) ↔ _
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases ht : p.2 ≤ 0
      · exact Or.inl ht
      · exact Or.inr ⟨h, le_of_not_ge ht⟩

theorem halfBallShearRoof_le_iff_symm [NormedSpace ℝ E] {p : E × ℝ} (hp : p.2 < 2) :
    halfBallShearRoof p.1 ≤ p.2 ↔ 0 ≤ p.2 ∧
      1 ≤ ‖(PartialDiffeomorph.halfBallShear.symm p).1‖ ^ 2 + p.2 ^ 2 := by
  have h := halfBallShearRoof_le_apply_iff (p := PartialDiffeomorph.halfBallShear.symm p) hp
  have heq : PartialDiffeomorph.halfBallShear (PartialDiffeomorph.halfBallShear.symm p) = p :=
    PartialDiffeomorph.halfBallShear.right_inv hp
  rw [heq] at h
  exact h

theorem le_halfBallShearRoof_iff_symm [NormedSpace ℝ E] {p : E × ℝ} (hp : p.2 < 2) :
    p.2 ≤ halfBallShearRoof p.1 ↔ p.2 ≤ 0 ∨
      ‖(PartialDiffeomorph.halfBallShear.symm p).1‖ ^ 2 + p.2 ^ 2 ≤ 1 := by
  have h := le_halfBallShearRoof_apply_iff (p := PartialDiffeomorph.halfBallShear.symm p) hp
  have heq : PartialDiffeomorph.halfBallShear (PartialDiffeomorph.halfBallShear.symm p) = p :=
    PartialDiffeomorph.halfBallShear.right_inv hp
  rw [heq] at h
  exact h

private theorem mem_halfBallShearHeight_domain_of_nonneg_lt {s : ℝ}
    (hs : 0 ≤ s) (hu : s < 9 / 8) :
    s ∈ Ioo (halfBallShearRadiusSq (5 / 4)) (halfBallShearRadiusSq (-(1 / 4))) := by
  norm_num [halfBallShearRadiusSq]
  constructor <;> linarith

theorem halfBallShearRoof_eq_max {x : E} (hx : ‖x‖ ^ 2 < 9 / 8) :
    halfBallShearRoof x = max (halfBallShearHeight (‖x‖ ^ 2)) 0 := by
  have hs := mem_halfBallShearHeight_domain_of_nonneg_lt (sq_nonneg ‖x‖) hx
  by_cases hle : ‖x‖ ^ 2 ≤ 1
  · rw [halfBallShearRoof, if_pos hle,
      max_eq_left (halfBallShearHeight_mem_Icc ⟨sq_nonneg _, hle⟩).1]
  · have hneg := strictAntiOn_halfBallShearHeight.antitoneOn
      (Icc_subset_halfBallShearHeight_domain (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1))
      hs (le_of_not_ge hle)
    rw [halfBallShearHeight_one] at hneg
    rw [halfBallShearRoof, if_neg hle, max_eq_right hneg]

theorem continuous_halfBallShearRoof : Continuous (halfBallShearRoof (E := E)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hn : Continuous (fun y : E => ‖y‖ ^ 2) := continuous_norm.pow 2
  by_cases hx : ‖x‖ ^ 2 < 9 / 8
  · have hg := contDiffOn_halfBallShearHeight.continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds (mem_halfBallShearHeight_domain_of_nonneg_lt (sq_nonneg ‖x‖) hx))
    have hc : ContinuousAt (fun y : E => halfBallShearHeight (‖y‖ ^ 2)) x :=
      hg.comp (f := fun y : E => ‖y‖ ^ 2) hn.continuousAt
    have hm : ContinuousAt (fun y : E => max (halfBallShearHeight (‖y‖ ^ 2)) 0) x :=
      hc.max continuousAt_const
    apply hm.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hn continuous_const).mem_nhds hx] with y hy
    exact halfBallShearRoof_eq_max hy
  · apply (show ContinuousAt (fun _ : E => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
    have hlow : 1 < ‖x‖ ^ 2 := by linarith
    filter_upwards [(isOpen_lt continuous_const hn).mem_nhds hlow] with y hy
    exact if_neg (not_le_of_gt hy)

noncomputable def roundedHalfBallShearRoof (ε : ℝ) (x : E) : ℝ :=
  if ‖x‖ ^ 2 < 9 / 8 then Real.smoothMax ε (halfBallShearHeight (‖x‖ ^ 2)) 0 else 0

theorem roundedHalfBallShearRoof_bounds {ε : ℝ} (hε : 0 < ε) (x : E) :
    halfBallShearRoof x ≤ roundedHalfBallShearRoof ε x ∧
      roundedHalfBallShearRoof ε x ≤ halfBallShearRoof x + ε := by
  by_cases hx : ‖x‖ ^ 2 < 9 / 8
  · rw [roundedHalfBallShearRoof, if_pos hx, halfBallShearRoof_eq_max hx]
    exact ⟨Real.smoothMax.max_le hε _ _, Real.smoothMax.le_max_add hε _ _⟩
  · have hle : ¬ ‖x‖ ^ 2 ≤ 1 := by linarith
    rw [roundedHalfBallShearRoof, if_neg hx, halfBallShearRoof, if_neg hle]
    exact ⟨le_rfl, by linarith⟩

theorem roundedHalfBallShearRoof_nonneg {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 ≤ roundedHalfBallShearRoof ε x :=
  (halfBallShearRoof_nonneg x).trans (roundedHalfBallShearRoof_bounds hε x).1

theorem roundedHalfBallShearRoof_eq_zero {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 4)
    {x : E} (hx : halfBallShearRadiusSq (-ε) ≤ ‖x‖ ^ 2) : roundedHalfBallShearRoof ε x = 0 := by
  unfold roundedHalfBallShearRoof
  split_ifs with hcut
  · have hs := mem_halfBallShearHeight_domain_of_nonneg_lt (sq_nonneg ‖x‖) hcut
    have he : -ε ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) := ⟨by linarith, by linarith⟩
    have hh : halfBallShearHeight (‖x‖ ^ 2) ≤ -ε := by
      apply (strictAntiOn_halfBallShearRadiusSq.le_iff_ge he (halfBallShearHeight_mem_Ioo hs)).mp
      rwa [halfBallShearRadiusSq_height hs]
    rw [Real.smoothMax.eq_max_of_le hε, max_eq_right (by linarith)]
    rw [sub_zero, abs_of_nonpos (by linarith)]
    linarith
  · rfl

private theorem halfBallShearRadiusSq_neg_lt {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 16) :
    halfBallShearRadiusSq (-ε) < 17 / 16 := by
  have he : -ε ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) := ⟨by linarith, by linarith⟩
  have hh := strictAntiOn_halfBallShearRadiusSq
    (by norm_num : (-(1 / 16 : ℝ)) ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4)) he (by linarith)
  norm_num [halfBallShearRadiusSq] at hh ⊢
  linarith

theorem contDiff_roundedHalfBallShearRoof [InnerProductSpace ℝ E]
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 16) :
    ContDiff ℝ ∞ (roundedHalfBallShearRoof (E := E) ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hn : Continuous (fun y : E => ‖y‖ ^ 2) := continuous_norm.pow 2
  by_cases hx : ‖x‖ ^ 2 < 9 / 8
  · have hg := contDiffOn_halfBallShearHeight.contDiffAt
      (isOpen_Ioo.mem_nhds (mem_halfBallShearHeight_domain_of_nonneg_lt (sq_nonneg ‖x‖) hx))
    have hh : ContDiffAt ℝ ∞ (fun y : E => Real.smoothMax ε (halfBallShearHeight (‖y‖ ^ 2)) 0) x :=
      (Real.smoothMax.contDiff ε).contDiffAt.comp x
        ((hg.comp x (contDiff_norm_sq ℝ).contDiffAt).prodMk contDiffAt_const)
    apply hh.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hn continuous_const).mem_nhds hx] with y hy
    exact if_pos hy
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hlow : 17 / 16 < ‖x‖ ^ 2 := by linarith
    filter_upwards [(isOpen_lt continuous_const hn).mem_nhds hlow] with y hy
    exact roundedHalfBallShearRoof_eq_zero hε (by linarith)
      ((halfBallShearRadiusSq_neg_lt hε hsmall).trans hy).le

theorem hasCompactSupport_roundedHalfBallShearRoof [ProperSpace E] {ε : ℝ} :
    HasCompactSupport (roundedHalfBallShearRoof (E := E) ε) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E) 2)
  intro x hx
  have hn : 2 < ‖x‖ := lt_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h))
  have hcut : ¬ ‖x‖ ^ 2 < (9 / 8 : ℝ) := by nlinarith [sq_nonneg (‖x‖ - 2)]
  rw [roundedHalfBallShearRoof, if_neg hcut]

private theorem one_lt_halfBallShearRadiusSq_neg {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 4) :
    1 < halfBallShearRadiusSq (-ε) := by
  have hh := strictAntiOn_halfBallShearRadiusSq
    (show -ε ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) from ⟨by linarith, by linarith⟩)
    (by norm_num : (0 : ℝ) ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4)) (neg_neg_of_pos hε)
  simpa only [halfBallShearRadiusSq, zero_div, sub_zero, one_pow,
    zero_pow (by decide : 2 ≠ 0), one_mul] using hh

theorem roundedHalfBallShearRoof_eq_halfBallShearRoof {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 4) {x : E}
    (hx : ‖x‖ ^ 2 ∉ Ioo (halfBallShearRadiusSq ε) (halfBallShearRadiusSq (-ε))) :
    roundedHalfBallShearRoof ε x = halfBallShearRoof x := by
  have he : ε ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4) := ⟨by linarith, by linarith⟩
  have hq : halfBallShearRadiusSq ε < 1 := by
    have hh := strictAntiOn_halfBallShearRadiusSq
      (by norm_num : (0 : ℝ) ∈ Ioo (-(1 / 4 : ℝ)) (5 / 4)) he hε
    simpa only [halfBallShearRadiusSq, zero_div, sub_zero, one_pow,
      zero_pow (by decide : 2 ≠ 0), one_mul] using hh
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  rcases hx with hx | hx
  · have hxcut : ‖x‖ ^ 2 < 9 / 8 := by linarith
    have hs := mem_halfBallShearHeight_domain_of_nonneg_lt (sq_nonneg ‖x‖) hxcut
    have hg : ε ≤ halfBallShearHeight (‖x‖ ^ 2) := by
      apply (strictAntiOn_halfBallShearRadiusSq.le_iff_ge (halfBallShearHeight_mem_Ioo hs) he).mp
      rwa [halfBallShearRadiusSq_height hs]
    rw [roundedHalfBallShearRoof, if_pos hxcut, halfBallShearRoof_eq_max hxcut,
      Real.smoothMax.eq_max_of_le hε]
    simpa only [sub_zero, abs_of_nonneg (hε.le.trans hg)] using hg
  · rw [roundedHalfBallShearRoof_eq_zero hε hsmall hx]
    have hnot : ¬ ‖x‖ ^ 2 ≤ 1 := not_le_of_gt ((one_lt_halfBallShearRadiusSq_neg hε hsmall).trans_le hx)
    exact (if_neg hnot).symm

theorem exists_halfBallShearRoof_band_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (hP : PartialDiffeomorph.halfBallShear ''
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ O) :
    ∃ η > 0, {p : E × ℝ | ‖p.1‖ ^ 2 ≤ 1 + η ∧
      p.2 ∈ Icc 0 (halfBallShearRoof p.1 + η)} ⊆ O := by
  let ρ : ℝ → ℝ := fun η => Real.sqrt (1 + η)
  have hρ : Continuous ρ := Real.continuous_sqrt.comp (continuous_const.add continuous_id)
  have hρzero : ρ 0 = 1 := by norm_num [ρ]
  let Q : Set (E × ℝ) := Metric.closedBall 0 1 ×ˢ Icc (0 : ℝ) 1
  have hQ : IsCompact Q := (isCompact_closedBall (0 : E) 1).prod isCompact_Icc
  let T : ℝ × (E × ℝ) → E × ℝ := fun p =>
    (ρ p.1 • p.2.1, p.2.2 * (halfBallShearRoof (ρ p.1 • p.2.1) + p.1))
  have hc : Continuous (fun p : ℝ × (E × ℝ) => ρ p.1 • p.2.1) :=
    (hρ.comp continuous_fst).smul continuous_snd.fst
  have hT : Continuous T := hc.prodMk
    (continuous_snd.snd.mul ((continuous_halfBallShearRoof.comp hc).add continuous_fst))
  have hzero (q : E × ℝ) (hq : q ∈ Q) : T (0, q) ∈ O := by
    apply hP
    rw [PartialDiffeomorph.halfBallShear_image_halfBall]
    have hn : ‖q.1‖ ^ 2 ≤ 1 := by
      have hh := mem_closedBall_zero_iff.mp hq.1
      nlinarith [norm_nonneg q.1]
    have hg := halfBallShearHeight_mem_Icc ⟨sq_nonneg ‖q.1‖, hn⟩
    simp only [T, hρzero, one_smul, add_zero, halfBallShearRoof, if_pos hn, mem_ofPred_eq]
    refine ⟨hn, mul_nonneg hq.2.1 hg.1, ?_⟩
    nlinarith [hq.2.2, hg.1]
  have hnear : ∀ᶠ η in 𝓝 (0 : ℝ), ∀ q ∈ Q, T (η, q) ∈ O := by
    apply hQ.eventually_forall_of_forall_eventually
    intro q hq
    exact (hO.preimage hT).mem_nhds (hzero q hq)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let η := δ / 2
  have hη : 0 < η := by dsimp [η]; linarith
  refine ⟨η, hη, ?_⟩
  intro p hp
  have hηnear : η ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη]
    dsimp [η]
    linarith
  have hρpos : 0 < ρ η := Real.sqrt_pos.mpr (by linarith)
  have hden : 0 < halfBallShearRoof p.1 + η :=
    add_pos_of_nonneg_of_pos (halfBallShearRoof_nonneg p.1) hη
  let q : E × ℝ := ((ρ η)⁻¹ • p.1, p.2 / (halfBallShearRoof p.1 + η))
  have hq : q ∈ Q := by
    refine ⟨mem_closedBall_zero_iff.mpr ?_, div_nonneg hp.2.1 hden.le, ?_⟩
    · change ‖(ρ η)⁻¹ • p.1‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρpos.le)]
      apply (inv_mul_le_iff₀ hρpos).mpr
      rw [mul_one]
      exact (Real.le_sqrt (norm_nonneg _) (by linarith)).mpr hp.1
    · exact (div_le_one hden).mpr hp.2.2
  have hTq : T (η, q) = p := by
    have hx : ρ η • q.1 = p.1 := by simp only [q, smul_smul, mul_inv_cancel₀ hρpos.ne', one_smul]
    change (ρ η • q.1, q.2 * (halfBallShearRoof (ρ η • q.1) + η)) = p
    rw [hx]
    exact Prod.ext rfl (div_mul_cancel₀ p.2 hden.ne')
  exact hTq ▸ hsub hηnear q hq

theorem exists_roundedHalfBallShearRoof_band_subset [NormedSpace ℝ E] [ProperSpace E]
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (hP : PartialDiffeomorph.halfBallShear ''
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ O) :
    ∃ δ > 0, δ ≤ 1 / 16 ∧ ∀ ε ∈ Ioo (0 : ℝ) δ,
      {p : E × ℝ | p.1 ∈ Metric.closedBall 0 (Real.sqrt (halfBallShearRadiusSq (-ε))) ∧
        p.2 ∈ Icc 0 (roundedHalfBallShearRoof ε p.1)} ⊆ O := by
  obtain ⟨η, hη, hband⟩ := exists_halfBallShearRoof_band_subset hO hP
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), halfBallShearRadiusSq (-ε) < 1 + η := by
    apply (contDiff_halfBallShearRadiusSq.continuous.comp continuous_neg).continuousAt.eventually
      (isOpen_Iio.mem_nhds _)
    norm_num [halfBallShearRadiusSq]
    exact hη
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min δ (min η (1 / 16)), by positivity,
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro ε hε p hp
  have hεδ : ε < δ := hε.2.trans_le (min_le_left _ _)
  have hεη : ε < η := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεsmall : ε < 1 / 16 := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hqpos : 0 < halfBallShearRadiusSq (-ε) :=
    zero_lt_one.trans (one_lt_halfBallShearRadiusSq_neg hε.1 (by linarith))
  have hqbound : halfBallShearRadiusSq (-ε) < 1 + η := hδnear (by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε.1] using hεδ)
  apply hband
  refine ⟨?_, hp.2.1, ?_⟩
  · have hnorm := mem_closedBall_zero_iff.mp hp.1
    have hsq := (sq_le_sq₀ (norm_nonneg p.1) (Real.sqrt_nonneg _)).mpr hnorm
    rw [Real.sq_sqrt hqpos.le] at hsq
    exact hsq.trans hqbound.le
  · exact hp.2.2.trans ((roundedHalfBallShearRoof_bounds hε.1 p.1).2.trans
      (add_le_add_right hεη.le _))

theorem exists_isotopy_roundedHalfBallShearRoof [InnerProductSpace ℝ E] [ProperSpace E]
    {O : Set (E × ℝ)} (hO : IsOpen O)
    (hP : PartialDiffeomorph.halfBallShear ''
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ O) :
    ∃ δ > 0, δ ≤ 1 / 16 ∧ ∀ ε ∈ Ioo (0 : ℝ) δ,
      ∃ Φ : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
        (∀ t p, (Φ t p).1 = p.1) ∧
        (∀ x, Φ 1 (x, roundedHalfBallShearRoof ε x) = (x, 0)) ∧
        Φ 1 '' {p : E × ℝ | roundedHalfBallShearRoof ε p.1 ≤ p.2} = {p | 0 ≤ p.2} ∧
        Φ 1 '' {p : E × ℝ | roundedHalfBallShearRoof ε p.1 < p.2} = {p | 0 < p.2} ∧
        Φ 1 '' {p : E × ℝ | p.2 ≤ roundedHalfBallShearRoof ε p.1} = {p | p.2 ≤ 0} ∧
        Φ 1 '' {p : E × ℝ | p.2 < roundedHalfBallShearRoof ε p.1} = {p | p.2 < 0} ∧
        ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Cᶜ ∧ EqOn (Φ t).symm id Cᶜ := by
  obtain ⟨δ, hδ, hδsmall, hband⟩ := exists_roundedHalfBallShearRoof_band_subset hO hP
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro ε hε
  have hsmall : ε < 1 / 16 := hε.2.trans_le hδsmall
  let k := roundedHalfBallShearRoof (E := E) ε
  let r := Real.sqrt (halfBallShearRadiusSq (-ε))
  have hrad : 0 ≤ halfBallShearRadiusSq (-ε) :=
    (zero_lt_one.trans (one_lt_halfBallShearRadiusSq_neg hε.1 (by linarith))).le
  have hk : ContDiff ℝ ∞ k := contDiff_roundedHalfBallShearRoof hε.1 hsmall
  have hzero (x : E) (hx : x ∉ Metric.closedBall 0 r) : k x = 0 := by
    apply roundedHalfBallShearRoof_eq_zero hε.1 (by linarith)
    have hn : r < ‖x‖ := lt_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h))
    have hr : r ^ 2 = halfBallShearRadiusSq (-ε) := Real.sq_sqrt hrad
    nlinarith [Real.sqrt_nonneg (halfBallShearRadiusSq (-ε))]
  let g : ℝ × E → ℝ := fun p => (1 - p.1) * k p.2
  have hg : ContDiff ℝ ∞ g := (contDiff_const.sub contDiff_fst).mul (hk.comp contDiff_snd)
  obtain ⟨Φ, hΦ, hΦi, hΦ0, hfst, hgraph, hepi, hstrict, hsupport⟩ :=
    Diffeomorph.exists_isotopy_graphOn_endpoints_in_open hg
      (isCompact_closedBall (0 : E) r)
      (by intro t _ x hx; simp only [g, hzero x hx, mul_zero]) hO (by
        intro t ht x hx
        apply hband ε hε
        refine ⟨hx, mul_nonneg (sub_nonneg.mpr ht.2) (roundedHalfBallShearRoof_nonneg hε.1 x), ?_⟩
        have hn : 0 ≤ k x := roundedHalfBallShearRoof_nonneg hε.1 x
        change (1 - t) * k x ≤ k x
        nlinarith [ht.1])
  have hepi' : Φ 1 '' {p : E × ℝ | k p.1 ≤ p.2} = {p | 0 ≤ p.2} := by
    simpa only [mem_univ, true_and, g, sub_zero, one_mul, sub_self, zero_mul] using hepi univ
  have hstrict' : Φ 1 '' {p : E × ℝ | k p.1 < p.2} = {p | 0 < p.2} := by
    simpa only [mem_univ, true_and, g, sub_zero, one_mul, sub_self, zero_mul] using hstrict univ
  refine ⟨Φ, hΦ, hΦi, hΦ0, hfst, ?_, hepi', hstrict', ?_, ?_, hsupport⟩
  · simpa only [g, sub_zero, one_mul, sub_self, zero_mul] using hgraph
  · have hh := (Φ 1).toHomeomorph.image_compl {p : E × ℝ | k p.1 < p.2}
    change Φ 1 '' {p : E × ℝ | ¬ k p.1 < p.2} = (Φ 1 '' {p : E × ℝ | k p.1 < p.2})ᶜ at hh
    simpa only [hstrict', not_lt, compl_ofPred] using hh
  · have hh := (Φ 1).toHomeomorph.image_compl {p : E × ℝ | k p.1 ≤ p.2}
    change Φ 1 '' {p : E × ℝ | ¬ k p.1 ≤ p.2} = (Φ 1 '' {p : E × ℝ | k p.1 ≤ p.2})ᶜ at hh
    simpa only [hepi', not_le, compl_ofPred] using hh

end DifferentialGeometry.Topology.Handle
