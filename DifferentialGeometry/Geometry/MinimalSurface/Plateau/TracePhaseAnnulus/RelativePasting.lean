import DifferentialGeometry.Topology.LoopSpace.RadialProfile
import DifferentialGeometry.Topology.LoopSpace.RelativePhaseWidth

noncomputable section
open Set Metric
open DifferentialGeometry.Analysis
open scoped NNReal ENNReal

namespace DifferentialGeometry.Topology

def relativeDiskAnnulus {Q : Type*} (R : loopCircle → ℝ) (u : ℂ → Q)
    (H : ℝ × loopCircle → Q) (z : ℂ) : Q :=
  if ‖z‖ ≤ R (polarAnnulusCoordinates z).2 then u (radialProfileInv R z)
  else H (polarAnnulusCoordinates z)

theorem relativeDiskAnnulus_inner {Q : Type*} (R : loopCircle → ℝ) (u : ℂ → Q)
    (H : ℝ × loopCircle → Q) {z : ℂ} (hz : ‖z‖ ≤ R (polarAnnulusCoordinates z).2) :
    relativeDiskAnnulus R u H z = u (radialProfileInv R z) := ite_eq_left hz

theorem relativeDiskAnnulus_outer {Q : Type*} (R : loopCircle → ℝ) (u : ℂ → Q)
    (H : ℝ × loopCircle → Q)
    (hglue : ∀ z, ‖z‖ = R (polarAnnulusCoordinates z).2 →
      u (radialProfileInv R z) = H (polarAnnulusCoordinates z))
    {z : ℂ} (hz : R (polarAnnulusCoordinates z).2 ≤ ‖z‖) :
    relativeDiskAnnulus R u H z = H (polarAnnulusCoordinates z) := by
  unfold relativeDiskAnnulus
  split_ifs with h
  · exact hglue z (le_antisymm h hz)
  · rfl

theorem relativeDiskAnnulus_boundary {Q : Type*} (R : loopCircle → ℝ) (u : ℂ → Q)
    (H : ℝ × loopCircle → Q) (hhi : ∀ θ, R θ ≤ 1)
    (hglue : ∀ z, ‖z‖ = R (polarAnnulusCoordinates z).2 →
      u (radialProfileInv R z) = H (polarAnnulusCoordinates z)) (θ : loopCircle) :
    relativeDiskAnnulus R u H (AddCircle.toCircle θ : ℂ) = H (1, θ) := by
  rw [relativeDiskAnnulus_outer R u H hglue]
  · rw [polarAnnulusCoordinates_outer]
  · simpa only [polarAnnulusCoordinates_outer, Circle.norm_coe] using hhi θ

theorem relativeDiskAnnulus_lipschitz {Q : Type*} [PseudoEMetricSpace Q]
    {R : loopCircle → ℝ} {u : ℂ → Q} {H : ℝ × loopCircle → Q}
    {Kr Ku Kh : ℝ≥0} (hR : LipschitzWith Kr R) (hlo : ∀ θ, 1 / 2 ≤ R θ)
    (hu : LipschitzWith Ku u) (hH : LipschitzWith Kh H)
    (hglue : ∀ z, ‖z‖ = R (polarAnnulusCoordinates z).2 →
      u (radialProfileInv R z) = H (polarAnnulusCoordinates z)) :
    LipschitzWith (max (Ku * (8 * Kr + 6)) (Kh * 4)) (relativeDiskAnnulus R u H) := by
  have hpos (θ : loopCircle) : 0 < R θ := lt_of_lt_of_le (by norm_num) (hlo θ)
  have hΦ := radialProfileInv_lipschitz hR hlo
  have hin (z : ℂ) (hz : ‖radialProfileInv R z‖ ≤ 1) :
      ‖z‖ ≤ R (polarAnnulusCoordinates z).2 := by
    rw [norm_radialProfileInv hpos] at hz
    exact (div_le_one (hpos _)).mp hz
  have hout (z : ℂ) (hz : 1 ≤ ‖radialProfileInv R z‖) :
      R (polarAnnulusCoordinates z).2 ≤ ‖z‖ := by
    rw [norm_radialProfileInv hpos] at hz
    simpa only [one_mul] using (le_div_iff₀ (hpos _)).mp hz
  have hall : LipschitzOnWith (max (Ku * (8 * Kr + 6)) (Kh * 4))
      (relativeDiskAnnulus R u H) (univ : Set ℂ) := by
    apply lipschitzOnWith_of_scalar_pieces convex_univ hΦ.continuous.norm
    · intro x hx y hy
      rw [relativeDiskAnnulus_inner R u H (hin x hx.2),
        relativeDiskAnnulus_inner R u H (hin y hy.2)]
      exact ((hu.comp hΦ) x y).trans (mul_le_mul' (by
        exact_mod_cast le_max_left (Ku * (8 * Kr + 6)) (Kh * 4)) le_rfl)
    · intro x hx y hy
      have hxR := hout x hx.2
      have hyR := hout y hy.2
      rw [relativeDiskAnnulus_outer R u H hglue hxR,
        relativeDiskAnnulus_outer R u H hglue hyR]
      have hp := polarAnnulusCoordinates_lipschitz ((hlo _).trans hxR) ((hlo _).trans hyR)
      calc
        _ ≤ (Kh : ℝ≥0∞) * edist (polarAnnulusCoordinates x) (polarAnnulusCoordinates y) := hH _ _
        _ ≤ (Kh : ℝ≥0∞) * ((4 : ℝ≥0∞) * edist x y) := mul_le_mul' le_rfl hp
        _ = ((Kh * 4 : ℝ≥0) : ℝ≥0∞) * edist x y := by rw [ENNReal.coe_mul, mul_assoc]; norm_num
        _ ≤ _ := mul_le_mul' (by exact_mod_cast le_max_right (Ku * (8 * Kr + 6)) (Kh * 4)) le_rfl
  exact fun x y => hall (mem_univ x) (mem_univ y)

theorem relativeDiskAnnulus_eq_on_sector {Q : Type*} {R : loopCircle → ℝ}
    (u : ℂ → Q) (H : ℝ × loopCircle → Q) {θ : loopCircle} (hR : R θ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    relativeDiskAnnulus R u H (r • (AddCircle.toCircle θ : ℂ)) =
      u (r • (AddCircle.toCircle θ : ℂ)) := by
  have hθ : (polarAnnulusCoordinates (r • (AddCircle.toCircle θ : ℂ))).2 = θ := by
    simp only [polarAnnulusCoordinates, radialDirection_pos_smul hr,
      ← AddCircle.homeomorphCircle_apply one_ne_zero, Homeomorph.symm_apply_apply]
  have hz : ‖r • (AddCircle.toCircle θ : ℂ)‖ ≤ R (polarAnnulusCoordinates
      (r • (AddCircle.toCircle θ : ℂ))).2 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one, hθ, hR]
      using hr1
  rw [relativeDiskAnnulus_inner R u H hz, radialProfileInv_eq_self (by rw [hθ, hR])]

end DifferentialGeometry.Topology
