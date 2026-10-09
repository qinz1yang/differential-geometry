import DifferentialGeometry.Topology.Manifold.CollarStretch

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12

/-- The transition `ν`: `0` for `s ≤ 1/8`, `1` for `s ≥ 3/8`. -/
def nuS12 (s : ℝ) : ℝ := Real.smoothTransition (4 * (s - 1/8))

/-- `H s = s + ν(s)/2`: the identity for `s ≤ 1/8`, the shift by `1/2` for `s ≥ 3/8`. -/
def stretchH_S12 (s : ℝ) : ℝ := s + nuS12 s / 2

theorem contDiff_stretchH_S12 : ContDiff ℝ ∞ stretchH_S12 := by
  unfold stretchH_S12 nuS12
  exact contDiff_id.add (((Real.smoothTransition.contDiff (n := ⊤)).comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))).div_const 2)

theorem stretchH_of_le_S12 {s : ℝ} (hs : s ≤ 1/8) : stretchH_S12 s = s := by
  unfold stretchH_S12 nuS12
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring

theorem stretchH_of_ge_S12 {s : ℝ} (hs : 3/8 ≤ s) : stretchH_S12 s = s + 1/2 := by
  unfold stretchH_S12 nuS12
  rw [Real.smoothTransition.one_of_one_le (by linarith)]

theorem stretchH_zero_S12 : stretchH_S12 0 = 0 := stretchH_of_le_S12 (by norm_num)

theorem stretchH_half_S12 : stretchH_S12 (1/2) = 1 := by
  rw [stretchH_of_ge_S12 (by norm_num)]; norm_num

theorem strictMono_stretchH_S12 : StrictMono stretchH_S12 := by
  intro s t hst
  have h := Real.smoothTransition.monotone (show 4 * (s - 1/8) ≤ 4 * (t - 1/8) by linarith)
  unfold stretchH_S12 nuS12
  linarith

theorem hasDerivAt_stretchH_S12 (s : ℝ) :
    HasDerivAt stretchH_S12
      (1 + (deriv Real.smoothTransition (4 * (s - 1/8)) * 4) / 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => 4 * (s - 1/8)) 4 s := by
    simpa using ((hasDerivAt_id s).sub_const (1/8 : ℝ)).const_mul (4 : ℝ)
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (4 * (s - 1/8)))
      (4 * (s - 1/8)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  exact (hasDerivAt_id s).add ((h2.comp s h1).div_const 2)

theorem stretchH_deriv_ne_zero_S12 (s : ℝ) :
    1 + (deriv Real.smoothTransition (4 * (s - 1/8)) * 4) / 2 ≠ 0 := by
  have h : 0 ≤ deriv Real.smoothTransition (4 * (s - 1/8)) :=
    Real.smoothTransition.monotone.deriv_nonneg
  exact ne_of_gt (by linarith)

theorem surjective_stretchH_S12 : Surjective stretchH_S12 := by
  refine contDiff_stretchH_S12.continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun s => ?_) tendsto_id
    have h := Real.smoothTransition.nonneg (4 * (s - 1/8))
    change s ≤ s + nuS12 s / 2
    unfold nuS12; linarith
  · refine tendsto_atBot_mono (fun s => ?_) (tendsto_atBot_add_const_right _ (1/2 : ℝ) tendsto_id)
    have h := Real.smoothTransition.le_one (4 * (s - 1/8))
    change s + nuS12 s / 2 ≤ id s + 1/2
    unfold nuS12; simp only [id]; linarith

/-- `H` as an order isomorphism of the line. -/
def stretchHIso_S12 : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective stretchH_S12 strictMono_stretchH_S12 surjective_stretchH_S12

theorem stretchHIso_apply_S12 (s : ℝ) : stretchHIso_S12 s = stretchH_S12 s := rfl

theorem contDiff_stretchHIso_symm_S12 : ContDiff ℝ ∞ stretchHIso_S12.symm :=
  Homeomorph.contDiff_symm_deriv stretchHIso_S12.toHomeomorph stretchH_deriv_ne_zero_S12
    hasDerivAt_stretchH_S12 contDiff_stretchH_S12

/-- The collar stretch `ψ u = 1 - H⁻¹(1 - u)`: `ψ 0 = 1/2`, `ψ u = u` for `u ≥ 7/8`, `ψ` is an
increasing diffeomorphism of the line. -/
def psi_S12 (u : ℝ) : ℝ := 1 - stretchHIso_S12.symm (1 - u)

/-- Its inverse `ρ v = 1 - H(1 - v)`: `ρ(1/2) = 0`, `ρ v = v` for `v ≥ 7/8`. -/
def rho_S12 (v : ℝ) : ℝ := 1 - stretchH_S12 (1 - v)

theorem contDiff_psi_S12 : ContDiff ℝ ∞ psi_S12 :=
  contDiff_const.sub (contDiff_stretchHIso_symm_S12.comp (contDiff_const.sub contDiff_id))

theorem contDiff_rho_S12 : ContDiff ℝ ∞ rho_S12 :=
  contDiff_const.sub (contDiff_stretchH_S12.comp (contDiff_const.sub contDiff_id))

theorem rho_psi_S12 (u : ℝ) : rho_S12 (psi_S12 u) = u := by
  unfold rho_S12 psi_S12
  have : 1 - (1 - stretchHIso_S12.symm (1 - u)) = stretchHIso_S12.symm (1 - u) := by ring
  rw [this, ← stretchHIso_apply_S12, OrderIso.apply_symm_apply]; ring

theorem psi_rho_S12 (v : ℝ) : psi_S12 (rho_S12 v) = v := by
  unfold rho_S12 psi_S12
  have : 1 - (1 - stretchH_S12 (1 - v)) = stretchH_S12 (1 - v) := by ring
  rw [this, ← stretchHIso_apply_S12, OrderIso.symm_apply_apply]; ring

theorem strictMono_psi_S12 : StrictMono psi_S12 := by
  intro a b hab
  unfold psi_S12
  have := stretchHIso_S12.symm.strictMono (show 1 - b < 1 - a by linarith)
  linarith

theorem strictMono_rho_S12 : StrictMono rho_S12 := by
  intro a b hab
  unfold rho_S12
  have := strictMono_stretchH_S12 (show 1 - b < 1 - a by linarith)
  linarith

theorem psi_zero_S12 : psi_S12 0 = 1/2 := by
  have : rho_S12 (1/2) = 0 := by unfold rho_S12; rw [show (1:ℝ) - 1/2 = 1/2 by norm_num, stretchH_half_S12]; norm_num
  rw [← this, psi_rho_S12]

theorem rho_half_S12 : rho_S12 (1/2) = 0 := by
  unfold rho_S12; rw [show (1:ℝ) - 1/2 = 1/2 by norm_num, stretchH_half_S12]; norm_num

theorem rho_of_ge_S12 {v : ℝ} (hv : 7/8 ≤ v) : rho_S12 v = v := by
  unfold rho_S12; rw [stretchH_of_le_S12 (by linarith)]; ring

theorem psi_of_ge_S12 {u : ℝ} (hu : 7/8 ≤ u) : psi_S12 u = u := by
  have := rho_of_ge_S12 hu
  calc psi_S12 u = psi_S12 (rho_S12 u) := by rw [this]
    _ = u := psi_rho_S12 u

theorem rho_one_S12 : rho_S12 1 = 1 := rho_of_ge_S12 (by norm_num)

theorem half_le_psi_S12 {u : ℝ} (hu : 0 ≤ u) : 1/2 ≤ psi_S12 u := by
  rw [← psi_zero_S12]; exact strictMono_psi_S12.monotone hu

theorem psi_lt_one_S12 {u : ℝ} (hu : u < 1) : psi_S12 u < 1 := by
  have h := strictMono_psi_S12 hu
  rwa [psi_of_ge_S12 (show (7:ℝ)/8 ≤ 1 by norm_num)] at h

theorem rho_nonneg_S12 {v : ℝ} (hv : 1/2 ≤ v) : 0 ≤ rho_S12 v := by
  rw [← rho_half_S12]; exact strictMono_rho_S12.monotone hv

theorem rho_lt_one_S12 {v : ℝ} (hv : v < 1) : rho_S12 v < 1 := by
  have h := strictMono_rho_S12 hv
  rwa [rho_one_S12] at h

theorem hasDerivAt_rho_S12 (v : ℝ) :
    HasDerivAt rho_S12 (1 + (deriv Real.smoothTransition (4 * ((1 - v) - 1/8)) * 4) / 2) v := by
  have h1 := hasDerivAt_stretchH_S12 (1 - v)
  have h2 : HasDerivAt (fun v : ℝ => 1 - v) (-1) v := by simpa using (hasDerivAt_id v).const_sub 1
  have h3 := (h1.comp v h2).const_sub 1
  have e : (1 + (deriv Real.smoothTransition (4 * ((1 - v) - 1/8)) * 4) / 2) =
      -((1 + deriv Real.smoothTransition (4 * (1 - v - 1 / 8)) * 4 / 2) * -1) := by ring
  rw [e]
  exact h3

theorem deriv_rho_pos_S12 (v : ℝ) : 0 < deriv rho_S12 v := by
  rw [(hasDerivAt_rho_S12 v).deriv]
  have h : 0 ≤ deriv Real.smoothTransition (4 * ((1 - v) - 1/8)) :=
    Real.smoothTransition.monotone.deriv_nonneg
  linarith

end GC.LongTime.Ch12

namespace GC.LongTime.Ch12

theorem rho_neg_half_S12 : rho_S12 (-1/2) = -1 := by
  unfold rho_S12
  rw [show (1:ℝ) - (-1/2) = 3/2 by norm_num, stretchH_of_ge_S12 (by norm_num)]; norm_num

theorem psi_neg_one_S12 : psi_S12 (-1) = -1/2 := by
  have := psi_rho_S12 (-1/2)
  rwa [rho_neg_half_S12] at this

theorem rho_zero_S12 : rho_S12 0 = -1/2 := by
  unfold rho_S12
  rw [show (1:ℝ) - 0 = 1 by norm_num, show stretchH_S12 1 = 3/2 by
    rw [stretchH_of_ge_S12 (by norm_num)]; norm_num]; norm_num

end GC.LongTime.Ch12
