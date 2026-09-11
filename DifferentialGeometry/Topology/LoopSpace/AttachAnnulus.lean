import DifferentialGeometry.Topology.LoopSpace.PolarAnnulus
import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialLipschitzPasting









noncomputable section

open Set Metric
open DifferentialGeometry.Analysis
open scoped NNReal

namespace DifferentialGeometry.Topology

variable {Q : Type*}


def attachDiskAnnulus (u : ℂ → Q) (H : ℝ × loopCircle → Q) (z : ℂ) : Q :=
  if ‖z‖ ≤ 1 / 2 then u ((2 : ℝ) • z) else H (polarAnnulusCoordinates z)

theorem attachDiskAnnulus_inner (u : ℂ → Q) (H : ℝ × loopCircle → Q)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : attachDiskAnnulus u H z = u ((2 : ℝ) • z) :=
  if_pos hz



theorem attachDiskAnnulus_outer (u : ℂ → Q) (H : ℝ × loopCircle → Q)
    (hglue : ∀ θ : loopCircle, u (AddCircle.toCircle θ : ℂ) = H (0, θ))
    {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : attachDiskAnnulus u H z = H (polarAnnulusCoordinates z) := by
  by_cases hzin : ‖z‖ ≤ 1 / 2
  · rw [attachDiskAnnulus_inner u H hzin]
    have hnorm : ‖z‖ = 1 / 2 := le_antisymm hzin hz
    let θ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (radialDirection z)
    have hθ : AddCircle.toCircle θ = radialDirection z := by
      rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
      exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _
    have htwo : (2 : ℝ) • z = (radialDirection z : ℂ) := by
      calc
        _ = (2 : ℝ) • (‖z‖ • (radialDirection z : ℂ)) :=
          congrArg (fun w : ℂ => (2 : ℝ) • w) (radialDirection_reconstruct z).symm
        _ = _ := by rw [hnorm, smul_smul]; norm_num
    have hp : polarAnnulusCoordinates z = (0, θ) := by
      simp [polarAnnulusCoordinates, hnorm, θ]
    rw [htwo, ← hθ, hglue, hp]
  · exact if_neg hzin


theorem attachDiskAnnulus_boundary (u : ℂ → Q) (H : ℝ × loopCircle → Q) (θ : loopCircle) :
    attachDiskAnnulus u H (AddCircle.toCircle θ : ℂ) = H (1, θ) := by
  rw [attachDiskAnnulus, if_neg (by rw [Circle.norm_coe]; norm_num), polarAnnulusCoordinates_outer]



theorem attachDiskAnnulus_lipschitz [PseudoMetricSpace Q]
    {u : ℂ → Q} {H : ℝ × loopCircle → Q} {Ku Kh : ℝ≥0}
    (hu : LipschitzWith Ku u) (hH : LipschitzWith Kh H)
    (hglue : ∀ θ : loopCircle, u (AddCircle.toCircle θ : ℂ) = H (0, θ)) :
    LipschitzWith (max (Ku * 2) (Kh * 4)) (attachDiskAnnulus u H) := by
  have hscale : LipschitzWith 2 (fun z : ℂ => (2 : ℝ) • z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, NNReal.coe_ofNat, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact le_rfl
  have hin := (hu.comp hscale).weaken (le_max_left (Ku * 2) (Kh * 4))
  have hout := (hH.comp_lipschitzOnWith polarAnnulusCoordinates_lipschitz).weaken
    (le_max_right (Ku * 2) (Kh * 4))
  apply lipschitzOnWith_univ.mp
  apply lipschitzOnWith_of_radial_pieces (r := (1 / 2 : ℝ)) convex_univ
  · intro z hz w hw
    rw [attachDiskAnnulus_inner u H hz.2, attachDiskAnnulus_inner u H hw.2]
    exact hin z w
  · intro z hz w hw
    rw [attachDiskAnnulus_outer u H hglue hz.2, attachDiskAnnulus_outer u H hglue hw.2]
    exact hout hz.2 hw.2

end DifferentialGeometry.Topology
