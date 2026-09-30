import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Tactic

namespace DifferentialGeometry.Topology

open Metric Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialStretch (δ c : ℝ) (x : E) : E :=
  ((δ + c * (max δ ‖x‖ - δ)) / max δ ‖x‖) • x

theorem radialStretch_of_norm_le {δ c : ℝ} (hδ : 0 < δ) {x : E}
    (hx : ‖x‖ ≤ δ) : radialStretch δ c x = x := by
  simp [radialStretch, max_eq_left hx, hδ.ne']

theorem radialStretch_of_le_norm {δ c : ℝ} {x : E} (hx : δ ≤ ‖x‖) :
    radialStretch δ c x = ((δ + c * (‖x‖ - δ)) / ‖x‖) • x := by
  rw [radialStretch, max_eq_right hx]

theorem continuous_radialStretch {δ c : ℝ} (hδ : 0 < δ) :
    Continuous (radialStretch δ c : E → E) := by
  apply Continuous.smul
  · exact (continuous_const.add (continuous_const.mul
      ((continuous_const.max continuous_norm).sub continuous_const))).div
      (continuous_const.max continuous_norm)
      (fun x => ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ ‖x‖)))
  · exact continuous_id

theorem norm_radialStretch_of_le_norm {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    {x : E} (hx : δ ≤ ‖x‖) :
    ‖radialStretch δ c x‖ = δ + c * (‖x‖ - δ) := by
  have hn : 0 < ‖x‖ := hδ.trans_le hx
  have hp : 0 < δ + c * (‖x‖ - δ) := by positivity
  rw [radialStretch_of_le_norm hx, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact div_mul_cancel₀ _ hn.ne'

theorem radialStretch_inverse {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (x : E) :
    radialStretch δ c⁻¹ (radialStretch δ c x) = x := by
  by_cases hx : ‖x‖ ≤ δ
  · rw [radialStretch_of_norm_le hδ hx, radialStretch_of_norm_le hδ hx]
  · have hx' : δ < ‖x‖ := lt_of_not_ge hx
    have hn : 0 < ‖x‖ := hδ.trans hx'
    have hp : 0 < δ + c * (‖x‖ - δ) := by positivity
    have hy : δ ≤ ‖radialStretch δ c x‖ := by
      rw [norm_radialStretch_of_le_norm hδ hc hx'.le]
      exact le_add_of_nonneg_right (mul_nonneg hc.le (sub_nonneg.mpr hx'.le))
    rw [radialStretch_of_le_norm hy, norm_radialStretch_of_le_norm hδ hc hx'.le,
      radialStretch_of_le_norm hx'.le, smul_smul]
    have heq : (δ + c⁻¹ * (δ + c * (‖x‖ - δ) - δ)) /
        (δ + c * (‖x‖ - δ)) * ((δ + c * (‖x‖ - δ)) / ‖x‖) = 1 := by
      field_simp
      ring
    rw [heq, one_smul]

def radialStretchHomeomorph (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) : E ≃ₜ E where
  toFun := radialStretch δ c
  invFun := radialStretch δ c⁻¹
  left_inv := radialStretch_inverse hδ hc
  right_inv x := by
    simpa using radialStretch_inverse hδ (inv_pos.mpr hc) x
  continuous_toFun := continuous_radialStretch hδ
  continuous_invFun := continuous_radialStretch hδ

theorem exists_radial_compression {δ ε R : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hεR : ε < R) :
    ∃ h : E ≃ₜ E,
      (∀ x, ‖x‖ ≤ δ → h x = x) ∧
      MapsTo h (closedBall 0 R) (ball 0 ε) := by
  let c : ℝ := ((δ + ε) / 2 - δ) / (R - δ)
  have hδR : δ < R := hδε.trans hεR
  have hc : 0 < c := div_pos (by linarith) (sub_pos.mpr hδR)
  refine ⟨radialStretchHomeomorph δ c hδ hc, ?_, ?_⟩
  · intro x hx
    exact radialStretch_of_norm_le hδ hx
  · intro x hx
    rw [mem_ball_zero_iff]
    change ‖radialStretch δ c x‖ < ε
    by_cases hxδ : ‖x‖ ≤ δ
    · rw [radialStretch_of_norm_le hδ hxδ]
      exact hxδ.trans_lt hδε
    · rw [norm_radialStretch_of_le_norm hδ hc (le_of_not_ge hxδ)]
      have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
      have hmul : c * (‖x‖ - δ) ≤ c * (R - δ) := mul_le_mul_of_nonneg_left
        (sub_le_sub_right hxR δ) hc.le
      have hcancel : c * (R - δ) = (δ + ε) / 2 - δ := by
        dsimp [c]
        exact div_mul_cancel₀ _ (sub_ne_zero.mpr hδR.ne')
      rw [hcancel] at hmul
      linarith

theorem exists_radial_compression_supported {δ ε R S : ℝ}
    (hδ : 0 < δ) (hδε : δ < ε) (hεR : ε < R) (hRS : R < S) :
    ∃ h : E ≃ₜ E,
      (∀ x, ‖x‖ ≤ δ → h x = x) ∧
      MapsTo h (closedBall 0 R) (ball 0 ε) ∧
      (∀ x, S ≤ ‖x‖ → h x = x) := by
  let η : ℝ := (δ + ε) / 2
  have hδη : δ < η := by dsimp [η]; linarith
  have hηε : η < ε := by dsimp [η]; linarith
  have hδR : δ < R := hδε.trans hεR
  have hηS : η < S := hηε.trans (hεR.trans hRS)
  have hη : 0 < η := hδ.trans hδη
  have hS : 0 < S := hη.trans hηS
  let c : ℝ := (η - δ) / (R - δ)
  let d : ℝ := (S - η) / (S - R)
  have hc : 0 < c := div_pos (sub_pos.mpr hδη) (sub_pos.mpr hδR)
  have hd : 0 < d := div_pos (sub_pos.mpr hηS) (sub_pos.mpr hRS)
  have hcR : c * (R - δ) = η - δ := div_mul_cancel₀ _ (sub_ne_zero.mpr hδR.ne')
  have hdS : d * (S - R) = S - η := div_mul_cancel₀ _ (sub_ne_zero.mpr hRS.ne')
  let h₁ : E ≃ₜ E := radialStretchHomeomorph δ c hδ hc
  let h₂ : E ≃ₜ E := radialStretchHomeomorph η (d / c) hη (div_pos hd hc)
  let h₃ : E ≃ₜ E := radialStretchHomeomorph S d⁻¹ hS (inv_pos.mpr hd)
  refine ⟨(h₁.trans h₂).trans h₃, ?_, ?_, ?_⟩
  · intro x hx
    change radialStretch S d⁻¹ (radialStretch η (d / c) (radialStretch δ c x)) = x
    rw [radialStretch_of_norm_le hδ hx,
      radialStretch_of_norm_le hη (hx.trans hδη.le),
      radialStretch_of_norm_le hS ((hx.trans hδη.le).trans hηS.le)]
  · intro x hx
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    have hx₁ : ‖radialStretch δ c x‖ ≤ η := by
      by_cases hxδ : ‖x‖ ≤ δ
      · rw [radialStretch_of_norm_le hδ hxδ]
        exact hxδ.trans hδη.le
      · rw [norm_radialStretch_of_le_norm hδ hc (le_of_not_ge hxδ)]
        have := mul_le_mul_of_nonneg_left (sub_le_sub_right hxR δ) hc.le
        linarith [hcR]
    rw [mem_ball_zero_iff]
    change ‖radialStretch S d⁻¹ (radialStretch η (d / c) (radialStretch δ c x))‖ < ε
    rw [radialStretch_of_norm_le hη hx₁,
      radialStretch_of_norm_le hS (hx₁.trans hηS.le)]
    exact hx₁.trans_lt hηε
  · intro x hx
    have hxδ : δ ≤ ‖x‖ := hδR.le.trans (hRS.le.trans hx)
    have hx₁η : η ≤ ‖radialStretch δ c x‖ := by
      rw [norm_radialStretch_of_le_norm hδ hc hxδ]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right (hRS.le.trans hx) δ) hc.le
      linarith [hcR]
    have heq : η + (d / c) * (δ + c * (‖x‖ - δ) - η) = η + d * (‖x‖ - R) := by
      have hηeq : η = δ + c * (R - δ) := by linarith [hcR]
      rw [hηeq]
      field_simp
      ring
    have hx₂ : ‖radialStretch η (d / c) (radialStretch δ c x)‖ =
        η + d * (‖x‖ - R) := by
      rw [norm_radialStretch_of_le_norm hη (div_pos hd hc) hx₁η,
        norm_radialStretch_of_le_norm hδ hc hxδ, heq]
    have hx₂S : S ≤ ‖radialStretch η (d / c) (radialStretch δ c x)‖ := by
      rw [hx₂]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hx R) hd.le
      linarith [hdS]
    have hn : 0 < ‖x‖ := hS.trans_le hx
    have hu : 0 < δ + c * (‖x‖ - δ) := by positivity
    have hv : 0 < η + d * (‖x‖ - R) := by
      have : 0 ≤ ‖x‖ - R := sub_nonneg.mpr (hRS.le.trans hx)
      positivity
    have hw : S + d⁻¹ * (η + d * (‖x‖ - R) - S) = ‖x‖ := by
      have hSeq : S = η + d * (S - R) := by linarith [hdS]
      calc
        _ = S + d⁻¹ * (d * (‖x‖ - S)) := by congr 2; nlinarith [hdS]
        _ = ‖x‖ := by field_simp; ring
    change radialStretch S d⁻¹ (radialStretch η (d / c) (radialStretch δ c x)) = x
    rw [radialStretch_of_le_norm hx₂S, hx₂, hw,
      radialStretch_of_le_norm hx₁η, norm_radialStretch_of_le_norm hδ hc hxδ,
      heq, radialStretch_of_le_norm hxδ, smul_smul, smul_smul]
    have hscalar : (‖x‖ / (η + d * (‖x‖ - R))) *
        ((η + d * (‖x‖ - R)) / (δ + c * (‖x‖ - δ))) *
        ((δ + c * (‖x‖ - δ)) / ‖x‖) = 1 := by
      field_simp
    rw [hscalar, one_smul]

end

end DifferentialGeometry.Topology
