import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialLipschitzPasting
import DifferentialGeometry.Analysis.Complex.BoundaryLens.Geometry
import Mathlib.Analysis.Complex.Circle
import DifferentialGeometry.Analysis.Integration.BallBoundary
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoEMetricSpace F]

theorem lipschitzOnWith_piecewise_closedBall
    {S : Set E} (hS : Convex ℝ S) (c : E) (r : ℝ)
    {u q : E → F} {Ku Kq : ℝ≥0}
    (hu : LipschitzOnWith Ku u S) (hq : LipschitzOnWith Kq q S)
    (hglue : EqOn q u (S ∩ sphere c r)) :
    LipschitzOnWith (max Kq Ku) (fun z => if dist z c ≤ r then q z else u z) S := by
  let f : E → F := fun z => if dist z c ≤ r then q z else u z
  have hfinner (z : E) (hz : dist z c ≤ r) : f z = q z := if_pos hz
  have hfouter (z : E) (hzS : z ∈ S) (hz : r ≤ dist z c) : f z = u z := by
    by_cases hi : dist z c ≤ r
    · rw [hfinner z hi]
      exact hglue ⟨hzS, le_antisymm hi hz⟩
    · exact if_neg hi
  have htranslated : LipschitzOnWith (max Kq Ku) (fun z => f (c + z))
      ((fun z => c + z) ⁻¹' S) := by
    apply lipschitzOnWith_of_radial_pieces (r := r) (hS.translate_preimage_right c)
    · intro z hz w hw
      change edist (f (c + z)) (f (c + w)) ≤ _
      rw [hfinner (c + z)
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show ‖z‖ ≤ r from hz.2)),
        hfinner (c + w)
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show ‖w‖ ≤ r from hw.2))]
      have h := (hq.weaken (le_max_left Kq Ku)) hz.1 hw.1
      simpa only [edist_dist, dist_add_left] using h
    · intro z hz w hw
      change edist (f (c + z)) (f (c + w)) ≤ _
      rw [hfouter (c + z) hz.1
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show r ≤ ‖z‖ from hz.2)),
        hfouter (c + w) hw.1
          (by simpa only [dist_eq_norm, add_sub_cancel_left] using (show r ≤ ‖w‖ from hw.2))]
      have h := (hu.weaken (le_max_right Kq Ku)) hz.1 hw.1
      simpa only [edist_dist, dist_add_left] using h
  intro z hz w hw
  have h := htranslated (x := z - c)
    (by simpa only [mem_preimage, add_sub_cancel] using hz) (y := w - c)
    (by simpa only [mem_preimage, add_sub_cancel] using hw)
  simpa only [add_sub_cancel, edist_dist, dist_eq_norm, sub_sub_sub_cancel_right, f] using h

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*}

def attachBoundaryCap (u q : ℂ → F) (ρ : ℝ) (z : ℂ) : F :=
  if ‖z + 1‖ ≤ ρ then q z else u z

theorem attachBoundaryCap_inner (u q : ℂ → F) (ρ : ℝ) {z : ℂ}
    (hz : ‖z + 1‖ ≤ ρ) : attachBoundaryCap u q ρ z = q z := if_pos hz

theorem attachBoundaryCap_outside (u q : ℂ → F) (ρ : ℝ) {z : ℂ}
    (hz : ρ < ‖z + 1‖) : attachBoundaryCap u q ρ z = u z :=
  if_neg (not_le.mpr hz)

theorem attachBoundaryCap_on_lens (u q : ℂ → F) (ρ : ℝ) :
    EqOn (attachBoundaryCap u q ρ) q (boundaryLens ρ) := by
  intro z hz
  exact attachBoundaryCap_inner u q ρ
    (by simpa only [mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz.1)

theorem attachBoundaryCap_outer (u q : ℂ → F) (ρ : ℝ)
    (hglue : EqOn q u (closedBall (0 : ℂ) 1 ∩ sphere (-1) ρ))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (hρz : ρ ≤ ‖z + 1‖) :
    attachBoundaryCap u q ρ z = u z := by
  by_cases hi : ‖z + 1‖ ≤ ρ
  · rw [attachBoundaryCap_inner u q ρ hi]
    apply hglue
    refine ⟨hz, ?_⟩
    simpa only [mem_sphere, dist_eq_norm, sub_neg_eq_add] using le_antisymm hi hρz
  · exact if_neg hi

theorem attachBoundaryCap_boundary (u q : ℂ → F) (ρ : ℝ) (z : Circle) :
    attachBoundaryCap u q ρ z = if ‖(z : ℂ) + 1‖ ≤ ρ then q z else u z := rfl

theorem attachBoundaryCap_boundary_complement (u q : ℂ → F) (ρ : ℝ)
    (hglue : EqOn q u (closedBall (0 : ℂ) 1 ∩ sphere (-1) ρ))
    {z : Circle} (hz : ρ ≤ ‖(z : ℂ) + 1‖) : attachBoundaryCap u q ρ z = u z :=
  attachBoundaryCap_outer u q ρ hglue
    (by simp only [mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl]) hz

theorem attachBoundaryCap_lipschitzOn [PseudoEMetricSpace F]
    {u q : ℂ → F} {ρ : ℝ} {Ku Kq : ℝ≥0}
    (hu : LipschitzOnWith Ku u (closedBall (0 : ℂ) 1))
    (hq : LipschitzOnWith Kq q (closedBall (0 : ℂ) 1))
    (hglue : EqOn q u (closedBall (0 : ℂ) 1 ∩ sphere (-1) ρ)) :
    LipschitzOnWith (max Kq Ku) (attachBoundaryCap u q ρ) (closedBall (0 : ℂ) 1) := by
  change LipschitzOnWith (max Kq Ku) (fun z : ℂ => if ‖z + 1‖ ≤ ρ then q z else u z) _
  simpa only [dist_eq_norm, sub_neg_eq_add] using
    lipschitzOnWith_piecewise_closedBall (convex_closedBall (0 : ℂ) 1) (-1) ρ hu hq hglue

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def quadraticPlaneEnergyDensity
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (f : ℂ → F) (z : ℂ) : ℝ :=
  (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
    A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2

private theorem quadraticPlaneEnergyDensity_congr
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) {f g : ℂ → F} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) :
    quadraticPlaneEnergyDensity A f z = quadraticPlaneEnergyDensity A g z := by
  unfold quadraticPlaneEnergyDensity
  rw [h.fderiv_eq, h.eq_of_nhds]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem attachBoundaryCap_eventuallyEq_inner
    (u q : ℂ → F) (ρ : ℝ) {z : ℂ} (hz : ‖z + 1‖ < ρ) :
    attachBoundaryCap u q ρ =ᶠ[𝓝 z] q := by
  have hc : Continuous (fun w : ℂ => ‖w + 1‖) := by fun_prop
  filter_upwards [(hc.tendsto z) (isOpen_Iio.mem_nhds hz)] with w hw
  exact attachBoundaryCap_inner u q ρ hw.le

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem attachBoundaryCap_eventuallyEq_outer
    (u q : ℂ → F) (ρ : ℝ) {z : ℂ} (hz : ρ < ‖z + 1‖) :
    attachBoundaryCap u q ρ =ᶠ[𝓝 z] u := by
  have hc : Continuous (fun w : ℂ => ‖w + 1‖) := by fun_prop
  filter_upwards [(hc.tendsto z) (isOpen_Ioi.mem_nhds hz)] with w hw
  exact attachBoundaryCap_outside u q ρ hw

theorem integral_quadratic_fderiv_attachBoundaryCap
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (u q : ℂ → F) (ρ : ℝ)
    (hg : IntegrableOn (fun z =>
      (A (attachBoundaryCap u q ρ z)
          (fderiv ℝ (attachBoundaryCap u q ρ) z 1)
          (fderiv ℝ (attachBoundaryCap u q ρ) z 1) +
        A (attachBoundaryCap u q ρ z)
          (fderiv ℝ (attachBoundaryCap u q ρ) z Complex.I)
          (fderiv ℝ (attachBoundaryCap u q ρ) z Complex.I)) / 2)
      (closedBall (0 : ℂ) 1)) :
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    (∫ z in closedBall (0 : ℂ) 1, e (attachBoundaryCap u q ρ) z) =
      (∫ z in boundaryLens ρ, e q z) +
        ∫ z in closedBall (0 : ℂ) 1 \ closedBall (-1) ρ, e u z := by
  let e : (ℂ → F) → ℂ → ℝ := quadraticPlaneEnergyDensity A
  let g := attachBoundaryCap u q ρ
  change (∫ z in closedBall (0 : ℂ) 1, e g z) =
    (∫ z in boundaryLens ρ, e q z) +
      ∫ z in closedBall (0 : ℂ) 1 \ closedBall (-1) ρ, e u z
  have hin : ∀ᵐ z ∂volume.restrict (boundaryLens ρ), z ∈ ball (-1 : ℂ) ρ := by
    have h := ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere volume (-1 : ℂ) ρ)
    exact h.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
  have hinner : (∫ z in boundaryLens ρ, e g z) = ∫ z in boundaryLens ρ, e q z := by
    apply integral_congr_ae
    filter_upwards [hin] with z hz
    apply quadraticPlaneEnergyDensity_congr
    exact attachBoundaryCap_eventuallyEq_inner u q ρ
      (by simpa only [mem_ball, dist_eq_norm, sub_neg_eq_add] using hz)
  have houter : (∫ z in closedBall (0 : ℂ) 1 \ closedBall (-1) ρ, e g z) =
      ∫ z in closedBall (0 : ℂ) 1 \ closedBall (-1) ρ, e u z := by
    apply setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
    intro z hz
    apply quadraticPlaneEnergyDensity_congr
    exact attachBoundaryCap_eventuallyEq_outer u q ρ
      (lt_of_not_ge (by simpa only [mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hz.2))
  have hsplit := integral_inter_add_sdiff (t := closedBall (-1 : ℂ) ρ)
    measurableSet_closedBall hg
  change (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ, e g z) +
    (∫ z in closedBall (0 : ℂ) 1 \ closedBall (-1) ρ, e g z) =
      ∫ z in closedBall (0 : ℂ) 1, e g z at hsplit
  rw [inter_comm] at hsplit
  change (∫ z in boundaryLens ρ, e g z) +
    (∫ z in closedBall (0 : ℂ) 1 \ closedBall (-1) ρ, e g z) =
      ∫ z in closedBall (0 : ℂ) 1, e g z at hsplit
  rw [hinner, houter] at hsplit
  exact hsplit.symm

end DifferentialGeometry.Analysis

end
