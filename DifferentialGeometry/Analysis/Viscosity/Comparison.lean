import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Viscosity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem parabolic_comparison_with_smooth_supersolution
    {a b : ℝ} {K : Set E} (hK : IsCompact K) {u v : ℝ × E → ℝ}
    (hc : ContinuousOn (fun z => u z - v z) (Icc a b ×ˢ K))
    (hv : ∀ z ∈ Ioo a b ×ˢ interior K, ContDiffAt ℝ 2 v z)
    (H : (ℝ × E) → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ)
    (C : ℝ)
    (hmono : ∀ z ∈ Ioo a b ×ˢ interior K, ∀ p X, Monotone (fun r => H z r p X + C * r))
    (hsub : ∀ z ∈ Ioo a b ×ˢ interior K, ∀ phi : ℝ × E → ℝ,
      ContDiffAt ℝ 2 phi z → IsLocalMax (fun w => u w - phi w) z →
        fderiv ℝ phi z (1, 0) + H z (u z)
          (fderiv ℝ (fun x => phi (z.1, x)) z.2)
          (fderiv ℝ (fderiv ℝ (fun x => phi (z.1, x))) z.2) ≤ 0)
    (hsuper : ∀ z ∈ Ioo a b ×ˢ interior K,
      0 ≤ fderiv ℝ v z (1, 0) + H z (v z)
        (fderiv ℝ (fun x => v (z.1, x)) z.2)
        (fderiv ℝ (fderiv ℝ (fun x => v (z.1, x))) z.2))
    (hinit : ∀ x ∈ K, u (a, x) ≤ v (a, x))
    (hside : ∀ t ∈ Icc a b, ∀ x ∈ K \ interior K, u (t, x) ≤ v (t, x)) :
    ∀ z ∈ Icc a b ×ˢ K, u z ≤ v z := by
  have hinterior : ∀ z ∈ Ico a b ×ˢ K, u z ≤ v z := by
    intro z hz
    by_contra! hpos
    let w : ℝ × E → ℝ := fun q => ((b - q.1) * Real.exp (-(C * q.1))) * (u q - v q)
    have hwc : ContinuousOn w (Icc a b ×ˢ K) :=
      ((continuous_const.sub continuous_fst).mul
        (Real.continuous_exp.comp ((continuous_const.mul continuous_fst).neg))).continuousOn.mul hc
    obtain ⟨q, hq, hmax⟩ := (isCompact_Icc.prod hK).exists_isMaxOn
      ⟨z, ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩⟩ hwc
    have hwz : 0 < w z := mul_pos (mul_pos (sub_pos.mpr hz.1.2) (Real.exp_pos _)) (sub_pos.mpr hpos)
    have hwq : 0 < w q := hwz.trans_le (hmax ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩)
    have hqb : q.1 < b := by
      by_contra! hh
      have heq : q.1 = b := le_antisymm hq.1.2 hh
      simp [w, heq] at hwq
    have huv : v q < u q := by
      have := (mul_pos_iff_of_pos_left (mul_pos (sub_pos.mpr hqb) (Real.exp_pos _))).mp hwq
      exact sub_pos.mp this
    have hqa : a < q.1 := by
      by_contra! hh
      have heq : q.1 = a := le_antisymm hh hq.1.1
      have hi := hinit q.2 hq.2
      rw [← heq] at hi
      exact (not_lt_of_ge hi) huv
    have hqK : q.2 ∈ interior K := by
      by_contra hh
      exact (not_lt_of_ge (hside q.1 hq.1 q.2 ⟨hq.2, hh⟩)) huv
    have hqint : q ∈ Ioo a b ×ˢ interior K := ⟨⟨hqa, hqb⟩, hqK⟩
    let m := w q
    let phi : ℝ × E → ℝ := fun y => v y + m * Real.exp (C * y.1) / (b - y.1)
    have hn : b - q.1 ≠ 0 := (sub_pos.mpr hqb).ne'
    have hphi : ContDiffAt ℝ 2 phi q :=
      (hv q hqint).add ((contDiffAt_const.mul
        (contDiffAt_const.mul contDiffAt_fst).exp).div
          (contDiffAt_const.sub contDiffAt_fst) hn)
    have hcontact : u q - phi q = 0 := by
      dsimp only [phi, m, w]
      rw [Real.exp_neg]
      field_simp
      ring
    have hlmax : IsLocalMax (fun y => u y - phi y) q := by
      have hnhood : Ioo a b ×ˢ interior K ∈ 𝓝 q :=
        (isOpen_Ioo.prod isOpen_interior).mem_nhds hqint
      filter_upwards [hnhood] with y hy
      rw [hcontact]
      have hle := hmax ⟨⟨hy.1.1.le, hy.1.2.le⟩, interior_subset hy.2⟩
      have hm : u y - v y ≤ m * Real.exp (C * y.1) / (b - y.1) := by
        have hh : u y - v y ≤ m / ((b - y.1) * Real.exp (-(C * y.1))) := by
          apply (le_div_iff₀ (mul_pos (sub_pos.mpr hy.1.2) (Real.exp_pos _))).mpr
          simpa only [mem_ofPred_eq, m, w, mul_comm] using hle
        rw [Real.exp_neg, div_mul_eq_div_div, div_inv_eq_mul] at hh
        simpa only [div_mul_eq_mul_div] using hh
      dsimp only [phi]
      linarith
    have hspatial : fderiv ℝ (fun x => phi (q.1, x)) =
        fderiv ℝ (fun x => v (q.1, x)) := by
      funext x
      exact fderiv_add_const (𝕜 := ℝ) (f := fun x => v (q.1, x)) (x := x) (m * Real.exp (C * q.1) / (b - q.1))
    have htime : fderiv ℝ phi q (1, 0) = fderiv ℝ v q (1, 0) +
        C * (u q - v q) + m * Real.exp (C * q.1) / (b - q.1) ^ 2 := by
      have hd := (hv q hqint).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
      have hnum := (((hasDerivAt_id q.1).const_mul C).exp).const_mul m
      have hreal := hnum.div ((hasDerivAt_id q.1).const_sub b) hn
      have hquot := hreal.comp_hasFDerivAt q (hasFDerivAt_fst (𝕜 := ℝ) (p := q))
      change HasFDerivAt (fun y : ℝ × E => m * Real.exp (C * y.1) / (b - y.1)) _ q at hquot
      dsimp only [phi]
      rw [(hd.hasFDerivAt.fun_add hquot).fderiv]
      simp only [add_apply, smul_apply, id_eq, smul_eq_mul]
      change fderiv ℝ v q (1, 0) +
        ((m * (Real.exp (C * q.1) * (C * 1))) * (b - q.1) -
          (m * Real.exp (C * q.1)) * (-1)) / (b - q.1) ^ 2 * 1 = _
      have hdiff : u q - v q = m * Real.exp (C * q.1) / (b - q.1) := by
        dsimp only [phi] at hcontact
        linarith
      rw [hdiff]
      field_simp
      ring
    have hh := hsub q hqint phi hphi hlmax
    rw [hspatial, htime] at hh
    have hm0 : 0 < m * Real.exp (C * q.1) / (b - q.1) ^ 2 :=
      div_pos (mul_pos hwq (Real.exp_pos _)) (sq_pos_of_ne_zero hn)
    have hmle := hmono q hqint
      (fderiv ℝ (fun x => v (q.1, x)) q.2)
      (fderiv ℝ (fderiv ℝ (fun x => v (q.1, x))) q.2) huv.le
    have hs := hsuper q hqint
    linarith
  intro z hz
  by_cases hab : a = b
  · have hza : z.1 = a := by rcases hz.1 with ⟨h1, h2⟩; linarith
    simpa only [← hza, Prod.mk.eta] using hinit z.2 hz.2
  · have hclosure : z ∈ closure (Ico a b ×ˢ K) := by
      rw [closure_prod_eq, closure_Ico hab, hK.isClosed.closure_eq]
      exact hz
    have hc' : ContinuousWithinAt (fun y => u y - v y) (Ico a b ×ˢ K) z :=
      (hc z hz).mono (prod_mono Ico_subset_Icc_self Subset.rfl)
    have hh := ContinuousWithinAt.closure_le hclosure hc' continuousWithinAt_const
      (fun y hy => sub_nonpos.mpr (hinterior y hy))
    exact sub_nonpos.mp hh

variable {ι : Type*} [Fintype ι]

theorem linear_parabolic_comparison_with_smooth_supersolution
    {a b : ℝ} {K : Set E} (hK : IsCompact K) {u v : ℝ × E → ℝ}
    (hc : ContinuousOn (fun z => u z - v z) (Icc a b ×ˢ K))
    (hv : ∀ z ∈ Ioo a b ×ˢ interior K, ContDiffAt ℝ 2 v z)
    (A : (ℝ × E) → ι → ι → ℝ) (B : (ℝ × E) → ι → E)
    (d : (ℝ × E) → E) (c f : (ℝ × E) → ℝ)
    (C : ℝ) (hc0 : ∀ z ∈ Ioo a b ×ˢ interior K, -C ≤ c z)
    (hsub : ∀ z ∈ Ioo a b ×ˢ interior K, ∀ phi : ℝ × E → ℝ,
      ContDiffAt ℝ 2 phi z → IsLocalMax (fun w => u w - phi w) z →
        fderiv ℝ phi z (1, d z) -
          (∑ i : ι, ∑ j : ι, A z i j * fderiv ℝ (fderiv ℝ phi) z (0, B z i) (0, B z j)) +
            c z * u z ≤ f z)
    (hsuper : ∀ z ∈ Ioo a b ×ˢ interior K,
      f z ≤ fderiv ℝ v z (1, d z) -
        (∑ i : ι, ∑ j : ι, A z i j * fderiv ℝ (fderiv ℝ v) z (0, B z i) (0, B z j)) + c z * v z)
    (hinit : ∀ x ∈ K, u (a, x) ≤ v (a, x))
    (hside : ∀ t ∈ Icc a b, ∀ x ∈ K \ interior K, u (t, x) ≤ v (t, x)) :
    ∀ z ∈ Icc a b ×ˢ K, u z ≤ v z := by
  let H := fun z r (p : E →L[ℝ] ℝ) (X : E →L[ℝ] E →L[ℝ] ℝ) =>
    p (d z) - (∑ i : ι, ∑ j : ι, A z i j * X (B z i) (B z j)) + c z * r - f z
  have hjet (phi : ℝ × E → ℝ) (z : ℝ × E) (hphi : ContDiffAt ℝ 2 phi z) (r : ℝ) :
      fderiv ℝ phi z (1, 0) + H z r
        (fderiv ℝ (fun x => phi (z.1, x)) z.2)
        (fderiv ℝ (fderiv ℝ (fun x => phi (z.1, x))) z.2) =
      fderiv ℝ phi z (1, d z) -
        (∑ i : ι, ∑ j : ι, A z i j * fderiv ℝ (fderiv ℝ phi) z (0, B z i) (0, B z j)) + c z * r - f z := by
    have heq : ((1 : ℝ), d z) = (1, (0 : E)) + (0, d z) := by ext <;> simp
    dsimp only [H]
    rw [fderiv_const_prod (hphi.differentiableAt (by norm_num))]
    simp only [fderiv_fderiv_const_prod_apply hphi, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, heq, map_add]
    ring
  apply parabolic_comparison_with_smooth_supersolution hK hc hv H C _ _ _ hinit hside
  · intro z hz p X r s hrs
    dsimp only [H]
    have hh := mul_nonneg (show 0 ≤ c z + C by linarith [hc0 z hz]) (sub_nonneg.mpr hrs)
    nlinarith
  · intro z hz phi hphi hmax
    rw [hjet phi z hphi]
    exact sub_nonpos.mpr (hsub z hz phi hphi hmax)
  · intro z hz
    rw [hjet v z (hv z hz)]
    exact sub_nonneg.mpr (hsuper z hz)


end DifferentialGeometry.Analysis.Viscosity
