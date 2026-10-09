import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A radius-preserving straightening from a radial arc and inverse circle maps.
The total forward and inverse formulas satisfy the closed-ball identities and
quantitative Lipschitz estimates, and are smooth with invertible derivatives
away from the center.
-/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Topology.Planar

private theorem radial_straightening_closedBall
    {α : ℝ → ℂ} {R : ℝ} {h hInv : ℂ → ℂ}
    (hR : 0 ≤ R)
    (hαnorm : ∀ r ∈ Set.Icc 0 R, ‖α r‖ = r)
    (hh : ∀ z : ℂ, ‖z‖ = 1 →
      ‖h z‖ = 1 ∧ ‖hInv z‖ = 1 ∧ hInv (h z) = z ∧ h (hInv z) = z) :
    let S := fun w : ℂ => α ‖w‖ * h (w / (‖w‖ : ℂ))
    let SInv := fun w : ℂ => (‖w‖ : ℂ) * hInv (w / α ‖w‖)
    ∀ w ∈ Metric.closedBall (0 : ℂ) R,
      ‖S w‖ = ‖w‖ ∧ ‖SInv w‖ = ‖w‖ ∧ SInv (S w) = w ∧ S (SInv w) = w := by
  let S := fun w : ℂ => α ‖w‖ * h (w / (‖w‖ : ℂ))
  let SInv := fun w : ℂ => (‖w‖ : ℂ) * hInv (w / α ‖w‖)
  change ∀ w ∈ Metric.closedBall (0 : ℂ) R,
    ‖S w‖ = ‖w‖ ∧ ‖SInv w‖ = ‖w‖ ∧ SInv (S w) = w ∧ S (SInv w) = w
  have hαzero : α 0 = 0 := norm_eq_zero.mp (hαnorm 0 ⟨le_rfl, hR⟩)
  intro w hw
  by_cases hwzero : w = 0
  · subst w
    simp [S, SInv, hαzero]
  have hrne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwzero
  have hrcne : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrne
  have hr : ‖w‖ ∈ Set.Icc 0 R :=
    ⟨norm_nonneg w, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw⟩
  have hαr := hαnorm ‖w‖ hr
  have hαrne : α ‖w‖ ≠ 0 := norm_ne_zero_iff.mp (by rwa [hαr])
  have hrc : ‖(‖w‖ : ℂ)‖ = ‖w‖ := by simp
  have hunit : ‖w / (‖w‖ : ℂ)‖ = 1 := by rw [norm_div, hrc, div_self hrne]
  have hunitInv : ‖w / α ‖w‖‖ = 1 := by rw [norm_div, hαr, div_self hrne]
  have hSnorm : ‖S w‖ = ‖w‖ := by
    dsimp only [S]
    rw [norm_mul, hαr, (hh _ hunit).1, mul_one]
  have hSInvnorm : ‖SInv w‖ = ‖w‖ := by
    dsimp only [SInv]
    rw [norm_mul, hrc, (hh _ hunitInv).2.1, mul_one]
  refine ⟨hSnorm, hSInvnorm, ?_, ?_⟩
  · change (‖S w‖ : ℂ) * hInv (S w / α ‖S w‖) = w
    rw [hSnorm]
    change (‖w‖ : ℂ) * hInv ((α ‖w‖ * h (w / (‖w‖ : ℂ))) / α ‖w‖) = w
    rw [mul_div_cancel_left₀ _ hαrne, (hh _ hunit).2.2.1,
      ← mul_div_assoc, mul_div_cancel_left₀ _ hrcne]
  · change α ‖SInv w‖ * h (SInv w / (‖SInv w‖ : ℂ)) = w
    rw [hSInvnorm]
    change α ‖w‖ * h (((‖w‖ : ℂ) * hInv (w / α ‖w‖)) / (‖w‖ : ℂ)) = w
    rw [mul_div_cancel_left₀ _ hrcne, (hh _ hunitInv).2.2.2,
      ← mul_div_assoc, mul_div_cancel_left₀ _ hαrne]

private theorem radial_straightening_axis
    {α : ℝ → ℂ} {R : ℝ} {ζ : ℂ} {h : ℂ → ℂ}
    (hαnorm : ∀ r ∈ Set.Icc 0 R, ‖α r‖ = r)
    (hh1 : h 1 = 1) (hhneg : h (-1) = ζ) :
    let S := fun w : ℂ => α ‖w‖ * h (w / (‖w‖ : ℂ))
    ∀ r ∈ Set.Icc 0 R, S (r : ℂ) = α r ∧ S (-(r : ℂ)) = ζ * α r := by
  dsimp only
  intro r hr
  have hrc : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.1]
  by_cases hrzero : r = 0
  · subst r
    have hαzero : α 0 = 0 := norm_eq_zero.mp (hαnorm 0 hr)
    simp [hαzero]
  have hrcne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrzero
  constructor
  · rw [hrc, div_self hrcne, hh1, mul_one]
  · rw [norm_neg, hrc, neg_div, div_self hrcne, hhneg, mul_comm]

private theorem radial_weighted_div_sub_le
    {x y a b : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (ha : ‖a‖ = ‖x‖) (hb : ‖b‖ = ‖y‖) (hxy : ‖y‖ ≤ ‖x‖) :
    ‖y‖ * ‖x / a - y / b‖ ≤ ‖x - y‖ + ‖a - b‖ := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (ha.trans_ne (norm_ne_zero_iff.mpr hx))
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (hb.trans_ne (norm_ne_zero_iff.mpr hy))
  have heq : x / a - y / b = ((x - y) + (y / b) * (b - a)) / a := by
    field_simp [ha0, hb0]
    ring
  have hunit : ‖y / b‖ = 1 := by rw [norm_div, hb, div_self (norm_ne_zero_iff.mpr hy)]
  calc
    ‖y‖ * ‖x / a - y / b‖ ≤ ‖x‖ * ‖x / a - y / b‖ :=
      mul_le_mul_of_nonneg_right hxy (norm_nonneg _)
    _ = ‖(x - y) + (y / b) * (b - a)‖ := by
      rw [heq, norm_div, ha]
      exact mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hx)
    _ ≤ ‖x - y‖ + ‖(y / b) * (b - a)‖ := norm_add_le _ _
    _ = ‖x - y‖ + ‖a - b‖ := by rw [norm_mul, hunit, one_mul, norm_sub_rev b a]

private theorem radial_mul_quotient_lipschitz
    {s : Set ℂ} {p q h : ℂ → ℂ} {Kp Kq Kh : ℝ≥0}
    (hp : ∀ x ∈ s, ‖p x‖ = ‖x‖) (hq : ∀ x ∈ s, ‖q x‖ = ‖x‖)
    (hpLip : LipschitzOnWith Kp p s) (hqLip : LipschitzOnWith Kq q s)
    (hhnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖h z‖ = 1)
    (hhLip : LipschitzOnWith Kh h (Metric.sphere (0 : ℂ) 1)) :
    LipschitzOnWith (Kp + Kh * (1 + Kq)) (fun x => p x * h (x / q x)) s := by
  have hordered : ∀ x ∈ s, ∀ y ∈ s, ‖y‖ ≤ ‖x‖ →
      ‖p x * h (x / q x) - p y * h (y / q y)‖ ≤
        ((Kp : ℝ) + (Kh : ℝ) * (1 + (Kq : ℝ))) * ‖x - y‖ := by
    intro x hx y hy hxy
    by_cases hx0 : x = 0
    · have hy0 : y = 0 := norm_eq_zero.mp
        (le_antisymm (by simpa only [hx0, norm_zero] using hxy) (norm_nonneg y))
      subst x
      subst y
      simp
    have hxunit : ‖x / q x‖ = 1 := by
      rw [norm_div, hq x hx, div_self (norm_ne_zero_iff.mpr hx0)]
    have hhx : ‖h (x / q x)‖ = 1 := hhnorm _ hxunit
    have hpbound : ‖p x - p y‖ ≤ (Kp : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hpLip.dist_le_mul x hx y hy
    by_cases hy0 : y = 0
    · subst y
      have hp0 : p 0 = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hp 0 hy)
      have hbound : ‖p x * h (x / q x) - p 0 * h (0 / q 0)‖ ≤
          (Kp : ℝ) * ‖x - 0‖ := by
        simpa only [hp0, zero_mul, sub_zero, norm_mul, hhx, mul_one] using hpbound
      apply hbound.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact le_add_of_nonneg_right
        (mul_nonneg Kh.coe_nonneg (add_nonneg zero_le_one Kq.coe_nonneg))
    have hyunit : ‖y / q y‖ = 1 := by
      rw [norm_div, hq y hy, div_self (norm_ne_zero_iff.mpr hy0)]
    have hxSphere : x / q x ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hxunit
    have hySphere : y / q y ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hyunit
    have hhbound : ‖h (x / q x) - h (y / q y)‖ ≤
        (Kh : ℝ) * ‖x / q x - y / q y‖ := by
      simpa only [dist_eq_norm] using hhLip.dist_le_mul _ hxSphere _ hySphere
    have hqbound : ‖q x - q y‖ ≤ (Kq : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hqLip.dist_le_mul x hx y hy
    have hweighted : ‖y‖ * ‖x / q x - y / q y‖ ≤
        (1 + (Kq : ℝ)) * ‖x - y‖ := by
      calc
        _ ≤ ‖x - y‖ + ‖q x - q y‖ :=
          radial_weighted_div_sub_le hx0 hy0 (hq x hx) (hq y hy) hxy
        _ ≤ ‖x - y‖ + (Kq : ℝ) * ‖x - y‖ := add_le_add le_rfl hqbound
        _ = _ := by ring
    have heq : p x * h (x / q x) - p y * h (y / q y) =
        (p x - p y) * h (x / q x) + p y * (h (x / q x) - h (y / q y)) := by ring
    calc
      _ = ‖(p x - p y) * h (x / q x) + p y * (h (x / q x) - h (y / q y))‖ := by rw [heq]
      _ ≤ ‖(p x - p y) * h (x / q x)‖ + ‖p y * (h (x / q x) - h (y / q y))‖ :=
        norm_add_le _ _
      _ = ‖p x - p y‖ + ‖y‖ * ‖h (x / q x) - h (y / q y)‖ := by
        rw [norm_mul, hhx, mul_one, norm_mul, hp y hy]
      _ ≤ (Kp : ℝ) * ‖x - y‖ + ‖y‖ * ((Kh : ℝ) * ‖x / q x - y / q y‖) :=
        add_le_add hpbound (mul_le_mul_of_nonneg_left hhbound (norm_nonneg y))
      _ = (Kp : ℝ) * ‖x - y‖ + (Kh : ℝ) * (‖y‖ * ‖x / q x - y / q y‖) := by ring
      _ ≤ (Kp : ℝ) * ‖x - y‖ + (Kh : ℝ) * ((1 + (Kq : ℝ)) * ‖x - y‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hweighted Kh.coe_nonneg)
      _ = _ := by ring
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one]
  rcases le_total ‖y‖ ‖x‖ with hxy | hyx
  · exact hordered x hx y hy hxy
  · simpa only [norm_sub_rev] using hordered y hy x hx hyx

private theorem radial_lipschitz_inputs
    {α : ℝ → ℂ} {R : ℝ} {L : ℝ≥0}
    (hαLip : LipschitzOnWith L α (Set.Icc 0 R)) :
    LipschitzOnWith L (fun w : ℂ => α ‖w‖) (Metric.closedBall 0 R) ∧
    LipschitzOnWith 1 (fun w : ℂ => (‖w‖ : ℂ)) (Metric.closedBall 0 R) := by
  have hn : LipschitzWith 1 (fun w : ℂ => ‖w‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using dist_norm_norm_le x y
  constructor
  · have hm : Set.MapsTo (fun w : ℂ => ‖w‖) (Metric.closedBall 0 R) (Set.Icc 0 R) := by
      intro w hw
      exact ⟨norm_nonneg w, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw⟩
    simpa only [mul_one, Function.comp_def] using hαLip.comp hn.lipschitzOnWith hm
  · simpa only [mul_one, Function.comp_def] using
      (Complex.isometry_ofReal.lipschitzWith.comp hn).lipschitzOnWith

private theorem radial_straightening_lipschitz
    {α : ℝ → ℂ} {R : ℝ} {h : ℂ → ℂ} {L Kh : ℝ≥0}
    (hαnorm : ∀ r ∈ Set.Icc 0 R, ‖α r‖ = r)
    (hαLip : LipschitzOnWith L α (Set.Icc 0 R))
    (hhnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖h z‖ = 1)
    (hhLip : LipschitzOnWith Kh h (Metric.sphere (0 : ℂ) 1)) :
    LipschitzOnWith (L + 2 * Kh)
      (fun w : ℂ => α ‖w‖ * h (w / (‖w‖ : ℂ))) (Metric.closedBall 0 R) := by
  obtain ⟨hαn, hn⟩ := radial_lipschitz_inputs hαLip
  have hα : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖α ‖w‖‖ = ‖w‖ := by
    intro w hw
    exact hαnorm _ ⟨norm_nonneg w, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw⟩
  have hr : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖(‖w‖ : ℂ)‖ = ‖w‖ := by
    intro w _
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have ht := radial_mul_quotient_lipschitz hα hr hαn hn hhnorm hhLip
  convert ht using 1
  ring

private theorem radial_straightening_inv_lipschitz
    {α : ℝ → ℂ} {R : ℝ} {hInv : ℂ → ℂ} {L Ki : ℝ≥0}
    (hαnorm : ∀ r ∈ Set.Icc 0 R, ‖α r‖ = r)
    (hαLip : LipschitzOnWith L α (Set.Icc 0 R))
    (hinorm : ∀ z : ℂ, ‖z‖ = 1 → ‖hInv z‖ = 1)
    (hiLip : LipschitzOnWith Ki hInv (Metric.sphere (0 : ℂ) 1)) :
    LipschitzOnWith (1 + Ki * (L + 1))
      (fun w : ℂ => (‖w‖ : ℂ) * hInv (w / α ‖w‖)) (Metric.closedBall 0 R) := by
  obtain ⟨hαn, hn⟩ := radial_lipschitz_inputs hαLip
  have hα : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖α ‖w‖‖ = ‖w‖ := by
    intro w hw
    exact hαnorm _ ⟨norm_nonneg w, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw⟩
  have hr : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖(‖w‖ : ℂ)‖ = ‖w‖ := by
    intro w _
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  simpa only [add_comm] using radial_mul_quotient_lipschitz hr hα hn hαn hinorm hiLip


private theorem radial_straightening_contDiffOn
    {α : ℝ → ℂ} {R : ℝ} {h : ℂ → ℂ}
    (hαsmooth : ContDiffOn ℝ ∞ α (Set.Ioo 0 R))
    (hh : ∀ z : ℂ, ‖z‖ = 1 → ContDiffAt ℝ ∞ h z) :
    ContDiffOn ℝ ∞ (fun w : ℂ => α ‖w‖ * h (w / (‖w‖ : ℂ)))
      (Metric.ball (0 : ℂ) R \ {0}) := by
  intro w hw
  have hw0 : w ≠ 0 := by simpa only [Set.mem_singleton_iff] using hw.2
  have hwR : ‖w‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hw.1
  have hr : ‖w‖ ∈ Set.Ioo (0 : ℝ) R := ⟨norm_pos_iff.mpr hw0, hwR⟩
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) w := contDiffAt_norm ℂ hw0
  have hα : ContDiffAt ℝ ∞ (fun z : ℂ => α ‖z‖) w :=
    (hαsmooth.contDiffAt (isOpen_Ioo.mem_nhds hr)).comp w hn
  have hnc : ContDiffAt ℝ ∞ (fun z : ℂ => (‖z‖ : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hn
  have hn0 : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw0)
  have hdir : ContDiffAt ℝ ∞ (fun z : ℂ => z / (‖z‖ : ℂ)) w := by
    have hid : ContDiffAt ℝ ∞ (fun z : ℂ => z) w := contDiffAt_id
    simpa only [div_eq_mul_inv] using hid.mul (hnc.fun_inv hn0)
  have hunit : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w),
      div_self (norm_ne_zero_iff.mpr hw0)]
  exact (hα.mul ((hh _ hunit).comp w hdir)).contDiffWithinAt

private theorem radial_straightening_inverse_contDiffOn
    {α : ℝ → ℂ} {R : ℝ} {hInv : ℂ → ℂ}
    (hαnorm : ∀ r ∈ Set.Icc 0 R, ‖α r‖ = r)
    (hαsmooth : ContDiffOn ℝ ∞ α (Set.Ioo 0 R))
    (hhInv : ∀ z : ℂ, ‖z‖ = 1 → ContDiffAt ℝ ∞ hInv z) :
    ContDiffOn ℝ ∞ (fun w : ℂ => (‖w‖ : ℂ) * hInv (w / α ‖w‖))
      (Metric.ball (0 : ℂ) R \ {0}) := by
  intro w hw
  have hw0 : w ≠ 0 := by simpa only [Set.mem_singleton_iff] using hw.2
  have hwR : ‖w‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hw.1
  have hr : ‖w‖ ∈ Set.Ioo (0 : ℝ) R := ⟨norm_pos_iff.mpr hw0, hwR⟩
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) w := contDiffAt_norm ℂ hw0
  have hα : ContDiffAt ℝ ∞ (fun z : ℂ => α ‖z‖) w :=
    (hαsmooth.contDiffAt (isOpen_Ioo.mem_nhds hr)).comp w hn
  have hnc : ContDiffAt ℝ ∞ (fun z : ℂ => (‖z‖ : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hn
  have hαw : ‖α ‖w‖‖ = ‖w‖ := hαnorm _ ⟨norm_nonneg w, hwR.le⟩
  have hα0 : α ‖w‖ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hαw]
    exact norm_ne_zero_iff.mpr hw0
  have hdir : ContDiffAt ℝ ∞ (fun z : ℂ => z / α ‖z‖) w := by
    have hid : ContDiffAt ℝ ∞ (fun z : ℂ => z) w := contDiffAt_id
    simpa only [div_eq_mul_inv] using hid.mul (hα.fun_inv hα0)
  have hunit : ‖w / α ‖w‖‖ = 1 := by
    rw [norm_div, hαw, div_self (norm_ne_zero_iff.mpr hw0)]
  exact (hnc.mul ((hhInv _ hunit).comp w hdir)).contDiffWithinAt

private theorem radial_straightening_fderiv_bijective
    {α : ℝ → ℂ} {R : ℝ} {h hInv : ℂ → ℂ} :
    let S : ℂ → ℂ := fun w => α ‖w‖ * h (w / (‖w‖ : ℂ))
    let SInv : ℂ → ℂ := fun w => (‖w‖ : ℂ) * hInv (w / α ‖w‖)
    (∀ w ∈ Metric.closedBall (0 : ℂ) R,
      ‖S w‖ = ‖w‖ ∧ ‖SInv w‖ = ‖w‖ ∧ SInv (S w) = w ∧ S (SInv w) = w) →
    ContDiffOn ℝ ∞ S (Metric.ball (0 : ℂ) R \ {0}) →
    ContDiffOn ℝ ∞ SInv (Metric.ball (0 : ℂ) R \ {0}) →
    ∀ w ∈ Metric.ball (0 : ℂ) R \ {0},
      Function.Bijective (fderiv ℝ S w) ∧ Function.Bijective (fderiv ℝ SInv w) := by
  intro S SInv hclosed hS hSInv
  let U : Set ℂ := Metric.ball (0 : ℂ) R \ {0}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hmem {w : ℂ} (hw : w ∈ U) : w ∈ Metric.closedBall (0 : ℂ) R :=
    Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw.1).le
  have hmap (f : ℂ → ℂ)
      (hnorm : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖f w‖ = ‖w‖) :
      Set.MapsTo f U U := by
    intro w hw
    have hn := hnorm w (hmem hw)
    have hw0 : w ≠ 0 := by simpa only [Set.mem_singleton_iff] using hw.2
    have hfw0 : f w ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hn]
      exact norm_ne_zero_iff.mpr hw0
    refine ⟨?_, by simpa only [Set.mem_singleton_iff] using hfw0⟩
    rw [Metric.mem_ball, dist_zero_right, hn]
    simpa only [Metric.mem_ball, dist_zero_right] using hw.1
  have hbij (f g : ℂ → ℂ) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
      (hfmap : Set.MapsTo f U U) (hleft : ∀ w ∈ U, g (f w) = w) :
      ∀ w ∈ U, Function.Bijective (fderiv ℝ f w) := by
    intro w hw
    have hdf := ((hf w hw).contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
    have hdg := ((hg (f w) (hfmap hw)).contDiffAt
      (hU.mem_nhds (hfmap hw))).differentiableAt (by simp)
    have heq : (g ∘ f) =ᶠ[𝓝 w] id := by
      filter_upwards [hU.mem_nhds hw] with z hz
      exact hleft z hz
    have hcomp : (fderiv ℝ g (f w)).comp (fderiv ℝ f w) =
        ContinuousLinearMap.id ℝ ℂ :=
      ((hdg.hasFDerivAt.comp w hdf.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique
        (hasFDerivAt_id w)
    have hinverse : Function.LeftInverse (fderiv ℝ g (f w)) (fderiv ℝ f w) := by
      intro v
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun T : ℂ →L[ℝ] ℂ => T v) hcomp
    have hinj := hinverse.injective
    exact ⟨hinj, LinearMap.surjective_of_injective
      (f := (fderiv ℝ f w).toLinearMap) hinj⟩
  intro w hw
  exact ⟨hbij S SInv hS hSInv (hmap S (fun z hz => (hclosed z hz).1))
      (fun z hz => (hclosed z (hmem hz)).2.2.1) w hw,
    hbij SInv S hSInv hS (hmap SInv (fun z hz => (hclosed z hz).2.1))
      (fun z hz => (hclosed z (hmem hz)).2.2.2) w hw⟩

/-- Construct the radius-preserving partial homeomorphism with its exact inverse,
closed-ball laws, punctured smoothness, and paired affine-axis trace. -/
theorem exists_radial_straightening
    {α : ℝ → ℂ} {R : ℝ} {ζ : ℂ} {h hInv : ℂ → ℂ}
    {L Kh Ki : ℝ≥0}
    (hR : 0 < R)
    (hαnorm : ∀ r ∈ Set.Icc 0 R, ‖α r‖ = r)
    (hαLip : LipschitzOnWith L α (Set.Icc 0 R))
    (hαsmooth : ContDiffOn ℝ ∞ α (Set.Ioo 0 R))
    (hh1 : h 1 = 1) (hhneg : h (-1) = ζ)
    (hh : ∀ z : ℂ, ‖z‖ = 1 →
      ‖h z‖ = 1 ∧ ‖hInv z‖ = 1 ∧ hInv (h z) = z ∧ h (hInv z) = z ∧
      ContDiffAt ℝ ∞ h z ∧ ContDiffAt ℝ ∞ hInv z)
    (hhLip : LipschitzOnWith Kh h (Metric.sphere (0 : ℂ) 1))
    (hiLip : LipschitzOnWith Ki hInv (Metric.sphere (0 : ℂ) 1)) :
    ∃ S : OpenPartialHomeomorph ℂ ℂ,
      S.source = Metric.ball 0 R ∧ S.target = Metric.ball 0 R ∧
      (∀ w, S w = α ‖w‖ * h (w / (‖w‖ : ℂ))) ∧
      (∀ w, S.symm w = (‖w‖ : ℂ) * hInv (w / α ‖w‖)) ∧
      (∀ w ∈ Metric.closedBall (0 : ℂ) R,
        ‖S w‖ = ‖w‖ ∧ ‖S.symm w‖ = ‖w‖ ∧
        S.symm (S w) = w ∧ S (S.symm w) = w) ∧
      (∃ K J : ℝ≥0,
        LipschitzOnWith K (S : ℂ → ℂ) (Metric.closedBall 0 R) ∧
        LipschitzOnWith J (S.symm : ℂ → ℂ) (Metric.closedBall 0 R)) ∧
      ContDiffOn ℝ ∞ (S : ℂ → ℂ) (Metric.ball 0 R \ {0}) ∧
      ContDiffOn ℝ ∞ (S.symm : ℂ → ℂ) (Metric.ball 0 R \ {0}) ∧
      (∀ w ∈ Metric.ball (0 : ℂ) R \ {0},
        Function.Bijective (fderiv ℝ (S : ℂ → ℂ) w) ∧
        Function.Bijective (fderiv ℝ (S.symm : ℂ → ℂ) w)) ∧
      (∀ r ∈ Set.Icc 0 R, S (r : ℂ) = α r ∧ S (-(r : ℂ)) = ζ * α r) := by
  have halgebra := radial_straightening_closedBall hR.le hαnorm
    (fun z hz => ⟨(hh z hz).1, (hh z hz).2.1, (hh z hz).2.2.1, (hh z hz).2.2.2.1⟩)
  have hLip := radial_straightening_lipschitz hαnorm hαLip
    (fun z hz => (hh z hz).1) hhLip
  have hiLip' := radial_straightening_inv_lipschitz hαnorm hαLip
    (fun z hz => (hh z hz).2.1) hiLip
  have hSmooth := radial_straightening_contDiffOn hαsmooth
    (fun z hz => (hh z hz).2.2.2.2.1)
  have hiSmooth := radial_straightening_inverse_contDiffOn hαnorm hαsmooth
    (fun z hz => (hh z hz).2.2.2.2.2)
  let S : OpenPartialHomeomorph ℂ ℂ :=
    { toFun := fun w => α ‖w‖ * h (w / (‖w‖ : ℂ))
      invFun := fun w => (‖w‖ : ℂ) * hInv (w / α ‖w‖)
      source := Metric.ball 0 R
      target := Metric.ball 0 R
      map_source' := by
        intro w hw
        rw [Metric.mem_ball, dist_zero_right,
          (halgebra w (Metric.ball_subset_closedBall hw)).1]
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      map_target' := by
        intro w hw
        rw [Metric.mem_ball, dist_zero_right,
          (halgebra w (Metric.ball_subset_closedBall hw)).2.1]
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      left_inv' := fun w hw => (halgebra w (Metric.ball_subset_closedBall hw)).2.2.1
      right_inv' := fun w hw => (halgebra w (Metric.ball_subset_closedBall hw)).2.2.2
      open_source := Metric.isOpen_ball
      open_target := Metric.isOpen_ball
      continuousOn_toFun := hLip.continuousOn.mono Metric.ball_subset_closedBall
      continuousOn_invFun := hiLip'.continuousOn.mono Metric.ball_subset_closedBall }
  refine ⟨S, rfl, rfl, fun _ => rfl, fun _ => rfl, halgebra,
    ⟨L + 2 * Kh, 1 + Ki * (L + 1), hLip, hiLip'⟩, hSmooth, hiSmooth, ?_,
    radial_straightening_axis hαnorm hh1 hhneg⟩
  exact radial_straightening_fderiv_bijective halgebra hSmooth hiSmooth

end DifferentialGeometry.Topology.Planar
