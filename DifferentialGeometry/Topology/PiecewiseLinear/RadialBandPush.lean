/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Module.Basic

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def radialTent (a b p r : ℝ) : ℝ :=
  max 0 (min ((r - a) / (p - a)) ((b - r) / (b - p)))

noncomputable def radialProfile (a b p q r : ℝ) : ℝ := r + (q - p) * radialTent a b p r

noncomputable def radialBandDirection (a : ℝ) (x : E) : E := (max ‖x‖ a)⁻¹ • x

noncomputable def radialBandPush (a b : ℝ) (P Q : E → ℝ) (x : E) : E :=
  (1 + (Q (radialBandDirection a x) - P (radialBandDirection a x)) *
    radialTent a b (P (radialBandDirection a x)) ‖x‖ / max ‖x‖ a) • x

variable {a b p q r : ℝ}

theorem radialTent_nonneg : 0 ≤ radialTent a b p r := le_max_left _ _

theorem radialTent_of_le (hap : a < p) (hr : r ≤ a) : radialTent a b p r = 0 :=
  max_eq_left ((min_le_left _ _).trans
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)))

theorem radialTent_of_ge (hpb : p < b) (hr : b ≤ r) : radialTent a b p r = 0 :=
  max_eq_left ((min_le_right _ _).trans
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)))

theorem radialProfile_of_le (hap : a < p) (hr : r ≤ a) : radialProfile a b p q r = r := by
  rw [radialProfile, radialTent_of_le hap hr, mul_zero, add_zero]

theorem radialProfile_of_ge (hpb : p < b) (hr : b ≤ r) : radialProfile a b p q r = r := by
  rw [radialProfile, radialTent_of_ge hpb hr, mul_zero, add_zero]

theorem radialProfile_of_le_of_le_left (hap : a < p) (hpb : p < b) (har : a ≤ r)
    (hrp : r ≤ p) : radialProfile a b p q r = a + (r - a) * (q - a) / (p - a) := by
  have hpa : p - a ≠ 0 := (sub_pos.mpr hap).ne'
  have h1 : (r - a) / (p - a) ≤ 1 := (div_le_one₀ (by linarith)).mpr (by linarith)
  have h2 : 1 ≤ (b - r) / (b - p) := (one_le_div₀ (by linarith)).mpr (by linarith)
  have ht : radialTent a b p r = (r - a) / (p - a) := by
    unfold radialTent
    rw [min_eq_left (h1.trans h2), max_eq_right (div_nonneg (by linarith) (by linarith))]
  rw [radialProfile, ht]
  field_simp
  ring

theorem radialProfile_of_le_of_le_right (hap : a < p) (hpb : p < b) (hpr : p ≤ r)
    (hrb : r ≤ b) : radialProfile a b p q r = b - (b - r) * (b - q) / (b - p) := by
  have hbp : b - p ≠ 0 := (sub_pos.mpr hpb).ne'
  have h1 : (b - r) / (b - p) ≤ 1 := (div_le_one₀ (by linarith)).mpr (by linarith)
  have h2 : 1 ≤ (r - a) / (p - a) := (one_le_div₀ (by linarith)).mpr (by linarith)
  have ht : radialTent a b p r = (b - r) / (b - p) := by
    unfold radialTent
    rw [min_eq_right (h1.trans h2), max_eq_right (div_nonneg (by linarith) (by linarith))]
  rw [radialProfile, ht]
  field_simp
  ring

theorem radialProfile_radialProfile (hap : a < p) (hpb : p < b) (haq : a < q) (hqb : q < b) :
    radialProfile a b q p (radialProfile a b p q r) = r := by
  have hpa : p - a ≠ 0 := (sub_pos.mpr hap).ne'
  have hqa : q - a ≠ 0 := (sub_pos.mpr haq).ne'
  have hbp : b - p ≠ 0 := (sub_pos.mpr hpb).ne'
  have hbq : b - q ≠ 0 := (sub_pos.mpr hqb).ne'
  rcases le_or_gt r a with hra | har
  · rw [radialProfile_of_le hap hra, radialProfile_of_le haq hra]
  rcases le_or_gt r p with hrp | hpr
  · rw [radialProfile_of_le_of_le_left hap hpb har.le hrp]
    have hs1 : a ≤ a + (r - a) * (q - a) / (p - a) := by
      have : 0 ≤ (r - a) * (q - a) / (p - a) :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    have hs2 : a + (r - a) * (q - a) / (p - a) ≤ q := by
      have : (r - a) * (q - a) / (p - a) ≤ q - a := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sub_nonneg.mpr haq.le) (sub_nonneg.mpr hrp)]
      linarith
    rw [radialProfile_of_le_of_le_left haq hqb hs1 hs2]
    field_simp
    ring
  rcases le_or_gt r b with hrb | hbr
  · rw [radialProfile_of_le_of_le_right hap hpb hpr.le hrb]
    have hs1 : q ≤ b - (b - r) * (b - q) / (b - p) := by
      have : (b - r) * (b - q) / (b - p) ≤ b - q := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hqb.le) (sub_nonneg.mpr hpr.le)]
      linarith
    have hs2 : b - (b - r) * (b - q) / (b - p) ≤ b := by
      have : 0 ≤ (b - r) * (b - q) / (b - p) :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    rw [radialProfile_of_le_of_le_right haq hqb hs1 hs2]
    field_simp
    ring
  · rw [radialProfile_of_ge hpb hbr.le, radialProfile_of_ge hqb hbr.le]

theorem lt_radialProfile (hap : a < p) (hpb : p < b) (haq : a < q) (hqb : q < b) (har : a < r) :
    a < radialProfile a b p q r := by
  rcases le_or_gt r p with hrp | hpr
  · rw [radialProfile_of_le_of_le_left hap hpb har.le hrp]
    have : 0 < (r - a) * (q - a) / (p - a) :=
      div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    linarith
  rcases le_or_gt r b with hrb | hbr
  · rw [radialProfile_of_le_of_le_right hap hpb hpr.le hrb]
    have : (b - r) * (b - q) / (b - p) ≤ b - q := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hqb.le) (sub_nonneg.mpr hpr.le)]
    linarith
  · rw [radialProfile_of_ge hpb hbr.le]
    exact har

theorem radialProfile_le (hap : a < p) (hpb : p < b) (haq : a < q) (hrp : r ≤ p) :
    radialProfile a b p q r ≤ q := by
  rcases le_or_gt r a with hra | har
  · rw [radialProfile_of_le hap hra]
    linarith
  · rw [radialProfile_of_le_of_le_left hap hpb har.le hrp]
    have : (r - a) * (q - a) / (p - a) ≤ q - a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr haq.le) (sub_nonneg.mpr hrp)]
    linarith

theorem radialProfile_le_self (hqp : q ≤ p) : radialProfile a b p q r ≤ r := by
  have ht : 0 ≤ radialTent a b p r := radialTent_nonneg
  rw [radialProfile]
  nlinarith

theorem radialBandDirection_of_lt {x : E} (hx : a < ‖x‖) :
    radialBandDirection a x = ‖x‖⁻¹ • x := by
  rw [radialBandDirection, max_eq_left hx.le]

theorem continuous_radialBandDirection (ha : 0 < a) :
    Continuous (radialBandDirection (E := E) a) :=
  ((continuous_norm.max continuous_const).inv₀
    fun _ => (ha.trans_le (le_max_right _ _)).ne').smul continuous_id

theorem radialBandPush_of_norm_le {P Q : E → ℝ} (hP : ∀ u, a < P u) {x : E} (hx : ‖x‖ ≤ a) :
    radialBandPush a b P Q x = x := by
  rw [radialBandPush, radialTent_of_le (hP _) hx, mul_zero, zero_div, add_zero, one_smul]

theorem radialBandPush_of_le_norm {P Q : E → ℝ} (hP : ∀ u, P u < b) {x : E} (hx : b ≤ ‖x‖) :
    radialBandPush a b P Q x = x := by
  rw [radialBandPush, radialTent_of_ge (hP _) hx, mul_zero, zero_div, add_zero, one_smul]

theorem radialBandPush_of_eq {P Q : E → ℝ} {x : E}
    (h : P (radialBandDirection a x) = Q (radialBandDirection a x)) :
    radialBandPush a b P Q x = x := by
  rw [radialBandPush, h, sub_self, zero_mul, zero_div, add_zero, one_smul]

theorem radialBandPush_of_lt {P Q : E → ℝ} {x : E} (hx : a < ‖x‖) (hx0 : ‖x‖ ≠ 0) :
    radialBandPush a b P Q x = (radialProfile a b (P (radialBandDirection a x))
      (Q (radialBandDirection a x)) ‖x‖ / ‖x‖) • x := by
  rw [radialBandPush, max_eq_left hx.le, radialProfile, add_div, div_self hx0]

theorem norm_radialBandPush {P Q : E → ℝ} (ha : 0 < a) (hP : ∀ u, a < P u ∧ P u < b)
    (hQ : ∀ u, a < Q u ∧ Q u < b) {x : E} (hx : a < ‖x‖) :
    ‖radialBandPush a b P Q x‖ =
      radialProfile a b (P (radialBandDirection a x)) (Q (radialBandDirection a x)) ‖x‖ := by
  have hpos := lt_radialProfile (hP (radialBandDirection a x)).1
    (hP (radialBandDirection a x)).2 (hQ (radialBandDirection a x)).1
    (hQ (radialBandDirection a x)).2 hx
  have hx0 : ‖x‖ ≠ 0 := (ha.trans hx).ne'
  rw [radialBandPush_of_lt hx hx0, norm_smul,
    Real.norm_of_nonneg (div_nonneg (by linarith) (norm_nonneg _)), div_mul_cancel₀ _ hx0]

theorem radialBandDirection_radialBandPush {P Q : E → ℝ} (ha : 0 < a)
    (hP : ∀ u, a < P u ∧ P u < b) (hQ : ∀ u, a < Q u ∧ Q u < b) (x : E) :
    radialBandDirection a (radialBandPush a b P Q x) = radialBandDirection a x := by
  rcases le_or_gt ‖x‖ a with hx | hx
  · rw [radialBandPush_of_norm_le (fun u => (hP u).1) hx]
  have hn := norm_radialBandPush ha hP hQ hx
  have hpos := lt_radialProfile (hP (radialBandDirection a x)).1
    (hP (radialBandDirection a x)).2 (hQ (radialBandDirection a x)).1
    (hQ (radialBandDirection a x)).2 hx
  have hy : a < ‖radialBandPush a b P Q x‖ := by
    rw [hn]
    exact hpos
  have hx0 : ‖x‖ ≠ 0 := (ha.trans hx).ne'
  have key : ∀ s t : ℝ, s ≠ 0 → t ≠ 0 → t⁻¹ • (t / s) • x = s⁻¹ • x := by
    intro s t hs ht
    rw [smul_smul, inv_mul_eq_div, div_div_cancel_left' ht]
  rw [radialBandDirection_of_lt hy, hn, radialBandPush_of_lt hx hx0,
    key _ _ hx0 (ha.trans hpos).ne', radialBandDirection_of_lt hx]

theorem radialBandPush_radialBandPush {P Q : E → ℝ} (ha : 0 < a)
    (hP : ∀ u, a < P u ∧ P u < b) (hQ : ∀ u, a < Q u ∧ Q u < b) (x : E) :
    radialBandPush a b Q P (radialBandPush a b P Q x) = x := by
  rcases le_or_gt ‖x‖ a with hx | hx
  · rw [radialBandPush_of_norm_le (fun u => (hP u).1) hx,
      radialBandPush_of_norm_le (fun u => (hQ u).1) hx]
  have hn := norm_radialBandPush ha hP hQ hx
  have hpos := lt_radialProfile (hP (radialBandDirection a x)).1
    (hP (radialBandDirection a x)).2 (hQ (radialBandDirection a x)).1
    (hQ (radialBandDirection a x)).2 hx
  have hy : a < ‖radialBandPush a b P Q x‖ := by
    rw [hn]
    exact hpos
  have hx0 : ‖x‖ ≠ 0 := (ha.trans hx).ne'
  have hd := radialBandDirection_radialBandPush ha hP hQ x
  have key : ∀ s t : ℝ, s ≠ 0 → t ≠ 0 → (s / t) • (t / s) • x = x := by
    intro s t hs ht
    rw [smul_smul, div_mul_div_comm, mul_comm s t, div_self (mul_ne_zero ht hs), one_smul]
  rw [radialBandPush_of_lt hy (ha.trans hy).ne', hd, hn,
    radialProfile_radialProfile (hP _).1 (hP _).2 (hQ _).1 (hQ _).2,
    radialBandPush_of_lt hx hx0]
  exact key _ _ hx0 (by linarith)

theorem norm_radialBandPush_le {P Q : E → ℝ} (ha : 0 < a) (hP : ∀ u, a < P u ∧ P u < b)
    (hQ : ∀ u, a < Q u ∧ Q u < b) {x : E} (hx : ‖x‖ ≤ P (radialBandDirection a x)) :
    ‖radialBandPush a b P Q x‖ ≤ Q (radialBandDirection a x) := by
  rcases le_or_gt ‖x‖ a with hxa | hxa
  · rw [radialBandPush_of_norm_le (fun u => (hP u).1) hxa]
    linarith [(hQ (radialBandDirection a x)).1]
  · rw [norm_radialBandPush ha hP hQ hxa]
    exact radialProfile_le (hP _).1 (hP _).2 (hQ _).1 hx

theorem norm_radialBandPush_le_norm {P Q : E → ℝ} (ha : 0 < a) (hP : ∀ u, a < P u ∧ P u < b)
    (hQ : ∀ u, a < Q u ∧ Q u < b) {x : E}
    (hx : Q (radialBandDirection a x) ≤ P (radialBandDirection a x)) :
    ‖radialBandPush a b P Q x‖ ≤ ‖x‖ := by
  rcases le_or_gt ‖x‖ a with hxa | hxa
  · rw [radialBandPush_of_norm_le (fun u => (hP u).1) hxa]
  · rw [norm_radialBandPush ha hP hQ hxa]
    exact radialProfile_le_self hx

theorem continuous_radialBandPush_family {P Q : ℝ × E → ℝ} (ha : 0 < a) (hPc : Continuous P)
    (hQc : Continuous Q) (hP : ∀ z, a < P z ∧ P z < b) :
    Continuous (fun z : ℝ × E =>
      radialBandPush a b (fun u => P (z.1, u)) (fun u => Q (z.1, u)) z.2) := by
  have hd : Continuous (fun z : ℝ × E => radialBandDirection a z.2) :=
    (continuous_radialBandDirection ha).comp continuous_snd
  have hp : Continuous (fun z : ℝ × E => P (z.1, radialBandDirection a z.2)) :=
    hPc.comp (continuous_fst.prodMk hd)
  have hq : Continuous (fun z : ℝ × E => Q (z.1, radialBandDirection a z.2)) :=
    hQc.comp (continuous_fst.prodMk hd)
  have hr : Continuous (fun z : ℝ × E => ‖z.2‖) := continuous_norm.comp continuous_snd
  have htent : Continuous (fun z : ℝ × E =>
      radialTent a b (P (z.1, radialBandDirection a z.2)) ‖z.2‖) := by
    unfold radialTent
    refine continuous_const.max (Continuous.min ?_ ?_)
    · exact (hr.sub continuous_const).div (hp.sub continuous_const)
        fun z => (sub_pos.mpr (hP _).1).ne'
    · exact (continuous_const.sub hr).div (continuous_const.sub hp)
        fun z => (sub_pos.mpr (hP _).2).ne'
  unfold radialBandPush
  refine Continuous.smul ?_ continuous_snd
  exact continuous_const.add (((hq.sub hp).mul htent).div (hr.max continuous_const)
    fun _ => (ha.trans_le (le_max_right _ _)).ne')

theorem exists_radialBandPush_family {P Q : ℝ × E → ℝ} (ha : 0 < a) (hPc : Continuous P)
    (hQc : Continuous Q) (hP : ∀ z, a < P z ∧ P z < b) (hQ : ∀ z, a < Q z ∧ Q z < b) :
    ∃ σ : ℝ → E ≃ₜ E, Continuous (fun z : ℝ × E => σ z.1 z.2) ∧
      Continuous (fun z : ℝ × E => (σ z.1).symm z.2) ∧
      ∀ t x, σ t x = radialBandPush a b (fun u => P (t, u)) (fun u => Q (t, u)) x ∧
        (σ t).symm x = radialBandPush a b (fun u => Q (t, u)) (fun u => P (t, u)) x := by
  have hf := continuous_radialBandPush_family ha hPc hQc hP
  have hg := continuous_radialBandPush_family ha hQc hPc hQ
  let σ : ℝ → E ≃ₜ E := fun t =>
    { toFun := radialBandPush a b (fun u => P (t, u)) (fun u => Q (t, u))
      invFun := radialBandPush a b (fun u => Q (t, u)) (fun u => P (t, u))
      left_inv := fun x =>
        radialBandPush_radialBandPush ha (fun u => hP (t, u)) (fun u => hQ (t, u)) x
      right_inv := fun x =>
        radialBandPush_radialBandPush ha (fun u => hQ (t, u)) (fun u => hP (t, u)) x
      continuous_toFun := hf.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := hg.comp (continuous_const.prodMk continuous_id) }
  exact ⟨σ, hf, hg, fun _ _ => ⟨rfl, rfl⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
