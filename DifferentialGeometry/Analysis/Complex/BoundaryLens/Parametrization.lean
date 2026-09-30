import DifferentialGeometry.Analysis.Complex.Argument
import DifferentialGeometry.Analysis.Complex.CircleArc
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import DifferentialGeometry.Topology.LoopSpace.PeriodicExtension
import DifferentialGeometry.Topology.Homeomorph.AffinePeriodic
import DifferentialGeometry.Topology.LoopSpace.JoinedLoop
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import DifferentialGeometry.Topology.LoopSpace.CircleMetric
import Mathlib.Analysis.Normed.Module.Normalize
import DifferentialGeometry.Analysis.Complex.BoundaryLens.Geometry
import DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism.Plane

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis

def lensInnerAngle (ρ t : ℝ) : ℝ :=
  Complex.arg (circleMap (-1) ρ
    (-Real.arccos (ρ / 2) + 4 * Real.arccos (ρ / 2) * t) - ((-1 + ρ / 2 : ℝ) : ℂ))

def lensOuterAngle (ρ t : ℝ) : ℝ :=
  Real.pi + Complex.arg (((-1 + ρ / 2 : ℝ) : ℂ) - circleMap 0 1
    (2 * Real.arccos (ρ / 2) + (2 * Real.pi - 4 * Real.arccos (ρ / 2)) * (2 * t - 1)))

def lensAngleProfile (ρ t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then lensInnerAngle ρ t else lensOuterAngle ρ t

theorem lens_angle_branches_endpoints {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ < 2) :
    lensInnerAngle ρ (1 / 2) = lensOuterAngle ρ (1 / 2) ∧
      lensOuterAngle ρ 1 = lensInnerAngle ρ 0 + 2 * Real.pi := by
  let a := Real.arccos (ρ / 2)
  let c : ℂ := ((-1 + ρ / 2 : ℝ) : ℂ)
  have ha0 : 0 < a := Real.arccos_pos.mpr (by linarith)
  have hapi : a < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hpos : 0 < (circleMap (-1) ρ a - c).im := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
    simpa [c, circleMap] using mul_pos hρ hs
  have hneg : (circleMap (-1) ρ (-a) - c).im < 0 := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
    simpa [c, circleMap, Complex.exp_im] using mul_neg_of_pos_of_neg hρ (neg_lt_zero.mpr hs)
  constructor
  · change Complex.arg (circleMap (-1) ρ (-a + 4 * a * (1 / 2)) - c) =
      Real.pi + Complex.arg (c - circleMap 0 1
        (2 * a + (2 * Real.pi - 4 * a) * (2 * (1 / 2) - 1)))
    rw [show -a + 4 * a * (1 / 2) = a by ring,
      show 2 * a + (2 * Real.pi - 4 * a) * (2 * (1 / 2) - 1) = 2 * a by ring]
    rw [← circleMap_neg_one_arccos (by linarith : -2 ≤ ρ) hρ2.le]
    rw [show c - circleMap (-1) ρ a = -(circleMap (-1) ρ a - c) by ring,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hpos]
    ring
  · change Real.pi + Complex.arg (c - circleMap 0 1
        (2 * a + (2 * Real.pi - 4 * a) * (2 * 1 - 1))) =
      Complex.arg (circleMap (-1) ρ (-a + 4 * a * 0) - c) + 2 * Real.pi
    rw [show 2 * a + (2 * Real.pi - 4 * a) * (2 * 1 - 1) = 2 * Real.pi - 2 * a by ring,
      show -a + 4 * a * 0 = -a by ring]
    rw [← circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ) hρ2.le]
    rw [show c - circleMap (-1) ρ (-a) = -(circleMap (-1) ρ (-a) - c) by ring,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hneg]
    ring

private theorem lens_angle_length_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Real.pi / 3 ≤ Real.arccos (ρ / 2) ∧ Real.arccos (ρ / 2) ≤ Real.pi / 2 ∧
      2 * ρ ≤ 2 * Real.pi - 4 * Real.arccos (ρ / 2) ∧
      2 * Real.pi - 4 * Real.arccos (ρ / 2) ≤ Real.pi * ρ := by
  let a := Real.arccos (ρ / 2)
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hapi : a ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by positivity)
  have hthird : Real.pi / 3 ≤ a := by
    have h := Real.arccos_le_arccos (show ρ / 2 ≤ 1 / 2 by linarith)
    have heq : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
      rw [← Real.cos_pi_div_three]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    rwa [heq] at h
  have hlower := Real.self_le_pi_sub_two_mul_arccos hρ.le (by linarith : ρ ≤ 2)
  have hupper := Real.mul_le_sin (show 0 ≤ Real.pi / 2 - a by linarith)
    (show Real.pi / 2 - a ≤ Real.pi / 2 by linarith)
  rw [Real.sin_pi_div_two_sub, Real.cos_arccos (by linarith : -1 ≤ ρ / 2)
    (by linarith : ρ / 2 ≤ 1), div_mul_eq_mul_div] at hupper
  have hupper' := (div_le_iff₀ Real.pi_pos).mp hupper
  exact ⟨hthird, hapi, by linarith, by linarith⟩

private theorem lens_inner_derivative_bounds {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    ∃ d : ℝ, HasDerivAt (lensInnerAngle ρ) d t ∧ 4 / 9 ≤ d ∧ d ≤ 8 * Real.pi := by
  let a := Real.arccos (ρ / 2)
  have hb := lens_angle_length_bounds hρ hρ1
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  obtain ⟨hd, hlo, hhi⟩ := Complex.hasDerivAt_arg_inner_circle hρ
    (show -a + 4 * a * t ∈ Icc (-a) a from ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩)
  have hx : HasDerivAt (fun s : ℝ => -a + 4 * a * s) (4 * a) t := by
    simpa using ((hasDerivAt_id t).const_mul (4 * a)).const_add (-a)
  have hd' := hd.comp t hx
  refine ⟨((1 - Real.cos (-a + 4 * a * t) / 2) /
    ‖circleMap 0 1 (-a + 4 * a * t) - (1 / 2 : ℂ)‖ ^ 2) * (4 * a), ?_, ?_, ?_⟩
  · simpa only [lensInnerAngle, Function.comp_def, a] using! hd'
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 4 * a by positivity)
    nlinarith [hb.1, Real.pi_gt_three]
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 4 * a by positivity)
    nlinarith [hb.2.1]

private theorem lens_outer_derivative_bounds {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (lensOuterAngle ρ) d t ∧ 4 / 9 ≤ d ∧ d ≤ 8 * Real.pi := by
  let a := Real.arccos (ρ / 2)
  let l := 2 * Real.pi - 4 * a
  have hb := lens_angle_length_bounds hρ hρ1
  have hl : 0 ≤ l := by dsimp only [l]; linarith [hb.2.2.1]
  obtain ⟨hd, hlo, hhi⟩ := Complex.hasDerivAt_arg_outer_circle hρ hρ1
    (show 2 * a + l * (2 * t - 1) ∈ Icc (2 * a) (2 * Real.pi - 2 * a) from
      ⟨by nlinarith [ht.1], by dsimp only [l] at *; nlinarith [ht.2]⟩)
  have hx : HasDerivAt (fun s : ℝ => 2 * a + l * (2 * s - 1)) (2 * l) t := by
    simpa only [mul_one, mul_comm l 2, id_eq] using!
      ((((hasDerivAt_id t).const_mul 2).sub_const 1).const_mul l).const_add (2 * a)
  let d := (1 - (-1 + ρ / 2) * Real.cos (2 * a + l * (2 * t - 1))) /
    ‖circleMap 0 1 (2 * a + l * (2 * t - 1)) - ((-1 + ρ / 2 : ℝ) : ℂ)‖ ^ 2
  have hd0 : 0 ≤ d := (by positivity : (0 : ℝ) ≤ 2 / (9 * ρ)).trans hlo
  have hlow : 2 / 9 ≤ d * ρ := by
    have h := (div_le_iff₀ (by positivity : 0 < 9 * ρ)).mp hlo
    change 2 ≤ d * (9 * ρ) at h
    nlinarith
  have hhigh : d * ρ ≤ 4 := (le_div_iff₀ hρ).mp hhi
  have hd' := hd.comp t hx
  refine ⟨d * (2 * l), ?_, ?_, ?_⟩
  · simpa only [lensOuterAngle, Function.comp_def, d, a, l] using! hd'
  · have h := mul_le_mul_of_nonneg_left hb.2.2.1 hd0
    change 4 / 9 ≤ d * (2 * l)
    change d * (2 * ρ) ≤ d * l at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hb.2.2.2 hd0
    change d * (2 * l) ≤ 8 * Real.pi
    change d * l ≤ d * (Real.pi * ρ) at h
    have hp := mul_le_mul_of_nonneg_left hhigh Real.pi_pos.le
    nlinarith

private theorem interval_slope_bounds {f : ℝ → ℝ} {a b m M : ℝ}
    (hf : ∀ x ∈ Icc a b, ∃ d, HasDerivAt f d x ∧ m ≤ d ∧ d ≤ M) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      m * (y - x) ≤ f y - f x ∧ f y - f x ≤ M * (y - x) := by
  have hc : ContinuousOn f (Icc a b) := fun x hx =>
    (hf x hx).choose_spec.1.continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ f (interior (Icc a b)) := fun x hx =>
    (hf x (interior_subset hx)).choose_spec.1.differentiableAt.differentiableWithinAt
  intro x hx y hy hxy
  constructor
  · exact (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hd
      (fun z hz => by
        obtain ⟨d, hd, hlo, _⟩ := hf z (interior_subset hz)
        rwa [hd.deriv]) x hx y hy hxy
  · exact (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc hd
      (fun z hz => by
        obtain ⟨d, hd, _, hhi⟩ := hf z (interior_subset hz)
        rwa [hd.deriv]) x hx y hy hxy

theorem lensAngleProfile_slope_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    (4 / 9) * (y - x) ≤ lensAngleProfile ρ y - lensAngleProfile ρ x ∧
      lensAngleProfile ρ y - lensAngleProfile ρ x ≤ (8 * Real.pi) * (y - x) := by
  have hi := interval_slope_bounds (fun t ht => lens_inner_derivative_bounds hρ hρ1 ht)
  have ho := interval_slope_bounds (fun t ht => lens_outer_derivative_bounds hρ hρ1 ht)
  have hjoin := (lens_angle_branches_endpoints hρ (by linarith : ρ < 2)).1
  by_cases hyh : y ≤ 1 / 2
  · simp only [lensAngleProfile, ite_eq_left hyh, ite_eq_left (hxy.trans hyh)]
    exact hi x ⟨hx.1, hxy.trans hyh⟩ y ⟨hy.1, hyh⟩ hxy
  · by_cases hxh : x ≤ 1 / 2
    · rw [lensAngleProfile, ite_eq_right hyh, lensAngleProfile, ite_eq_left hxh]
      have h₁ := hi x ⟨hx.1, hxh⟩ (1 / 2) (by norm_num) hxh
      have h₂ := ho (1 / 2) (by norm_num) y ⟨(le_of_not_ge hyh), hy.2⟩ (le_of_not_ge hyh)
      rw [hjoin] at h₁
      constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    · simp only [lensAngleProfile, ite_eq_right hyh, ite_eq_right hxh]
      exact ho x ⟨le_of_not_ge hxh, hx.2⟩ y ⟨le_of_not_ge hyh, hy.2⟩ hxy

theorem continuousOn_lensAngleProfile {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ContinuousOn (lensAngleProfile ρ) (Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.continuousOn (K := Real.toNNReal (8 * Real.pi))
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [Real.toNNReal_of_nonneg (by positivity : 0 ≤ 8 * Real.pi), NNReal.coe_mk]
  rcases le_total x y with hxy | hyx
  · have h := lensAngleProfile_slope_bounds hρ hρ1 hx hy hxy
    have hmono : lensAngleProfile ρ x ≤ lensAngleProfile ρ y := by nlinarith
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub] using h.2
  · have h := lensAngleProfile_slope_bounds hρ hρ1 hy hx hyx
    have hmono : lensAngleProfile ρ y ≤ lensAngleProfile ρ x := by nlinarith
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr hmono)] using h.2

theorem lensAngleProfile_one {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ < 2) :
    lensAngleProfile ρ 1 = lensAngleProfile ρ 0 + 2 * Real.pi := by
  simpa only [lensAngleProfile, show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num,
    show (0 : ℝ) ≤ 1 / 2 by norm_num, ↓reduceIte] using (lens_angle_branches_endpoints hρ hρ2).2

end DifferentialGeometry.Analysis

end

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis

private theorem add_const_slope_bounds {g : AddConstMap ℝ ℝ 1 1} {a m M : ℝ}
    (hbound : ∀ x ∈ Icc a (a + 1), ∀ y ∈ Icc a (a + 1), x ≤ y →
      m * (y - x) ≤ g y - g x ∧ g y - g x ≤ M * (y - x)) :
    ∀ x y : ℝ, x ≤ y → m * (y - x) ≤ g y - g x ∧ g y - g x ≤ M * (y - x) := by
  have hp (x : ℝ) : g (x + 1) = g x + 1 := g.map_add_const' x
  let L : AddConstMap ℝ ℝ 1 (1 - m) :=
    ⟨fun x => g x - m * x, fun x => by rw [hp]; ring⟩
  let U : AddConstMap ℝ ℝ 1 (M - 1) :=
    ⟨fun x => M * x - g x, fun x => by rw [hp]; ring⟩
  have hL : Monotone L := (AddConstMapClass.monotone_iff_Icc (f := L)
    (by norm_num : (0 : ℝ) < 1) a).mpr (by
      intro x hx y hy hxy
      have h := (hbound x hx y hy hxy).1
      change g x - m * x ≤ g y - m * y
      linarith)
  have hU : Monotone U := (AddConstMapClass.monotone_iff_Icc (f := U)
    (by norm_num : (0 : ℝ) < 1) a).mpr (by
      intro x hx y hy hxy
      have h := (hbound x hx y hy hxy).2
      change M * x - g x ≤ M * y - g y
      linarith)
  intro x y hxy
  have hlo := hL hxy
  have hhi := hU hxy
  change g x - m * x ≤ g y - m * y at hlo
  change M * x - g x ≤ M * y - g y at hhi
  constructor <;> linarith

theorem exists_lens_angle_homeomorph {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ F : ℝ ≃ₜ ℝ,
      (∀ t, F (t + 1) = F t + 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, F t = lensAngleProfile ρ t / (2 * Real.pi)) ∧
      (∀ t ∈ Icc (0 : ℝ) (1 / 2), F t = lensInnerAngle ρ t / (2 * Real.pi)) ∧
      (∀ t ∈ Icc (1 / 2 : ℝ) 1, F t = lensOuterAngle ρ t / (2 * Real.pi)) ∧
      (∀ x y : ℝ, x ≤ y → (2 / (9 * Real.pi)) * (y - x) ≤ F y - F x ∧
        F y - F x ≤ 4 * (y - x)) ∧
      LipschitzWith 4 F ∧ LipschitzWith (Real.toNNReal (9 * Real.pi / 2)) F.symm := by
  let f := fun t => lensAngleProfile ρ t / (2 * Real.pi)
  have hf : ContinuousOn f (Icc (0 : ℝ) (0 + 1)) := by
    simpa only [zero_add] using (continuousOn_lensAngleProfile hρ hρ1).div_const (2 * Real.pi)
  have hp : f (0 + 1) = f 0 + 1 := by
    dsimp only [f]
    rw [zero_add, lensAngleProfile_one hρ (by linarith : ρ < 2), add_div,
      div_self (by positivity : 2 * Real.pi ≠ 0)]
  obtain ⟨g, hgc, hg⟩ := AddConstMap.exists_continuous_extension_Icc 0 hf hp
  have hgp (t : ℝ) : g (t + 1) = g t + 1 := g.map_add_const' t
  have hgBound : ∀ x y : ℝ, x ≤ y → (2 / (9 * Real.pi)) * (y - x) ≤ g y - g x ∧
      g y - g x ≤ 4 * (y - x) := by
    apply add_const_slope_bounds (a := 0)
    intro x hx y hy hxy
    have h := lensAngleProfile_slope_bounds hρ hρ1 (by simpa only [zero_add] using hx)
      (by simpa only [zero_add] using hy) hxy
    rw [hg hx, hg hy]
    dsimp only [f]
    rw [← sub_div]
    constructor
    · apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      have heq : (2 / (9 * Real.pi)) * (y - x) * (2 * Real.pi) = (4 / 9) * (y - x) := by
        field_simp
        ring
      rw [heq]
      exact h.1
    · apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      nlinarith [h.2]
  have hm : 0 < 2 / (9 * Real.pi) := by positivity
  obtain ⟨F, _, hF, _⟩ := exists_homeomorph_affinePeriodic_of_lowerSlope hgc hgp hm
    (fun x y hxy => (hgBound x y hxy).1)
  have hFBound : ∀ x y : ℝ, x ≤ y → (2 / (9 * Real.pi)) * (y - x) ≤ F y - F x ∧
      F y - F x ≤ 4 * (y - x) := by
    intro x y hxy
    simpa only [hF] using hgBound x y hxy
  have hmono : StrictMono F := by
    intro x y hxy
    have h := (hFBound x y hxy.le).1
    have hpos := mul_pos hm (sub_pos.mpr hxy)
    linarith
  have hK : LipschitzWith 4 F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rcases le_total x y with hxy | hyx
    · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
        abs_of_nonpos (sub_nonpos.mpr (hmono.monotone hxy)), neg_sub, NNReal.coe_ofNat] using
        (hFBound x y hxy).2
    · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
        abs_of_nonneg (sub_nonneg.mpr (hmono.monotone hyx)), NNReal.coe_ofNat] using
        (hFBound y x hyx).2
  have hKi : LipschitzWith (Real.toNNReal (9 * Real.pi / 2)) F.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.toNNReal_of_nonneg (by positivity : 0 ≤ 9 * Real.pi / 2), NNReal.coe_mk]
    wlog hxy : x ≤ y generalizing x y
    · rw [dist_comm (F.symm x) (F.symm y), dist_comm x y]
      exact this y x (le_of_not_ge hxy)
    have hinv : F.symm x ≤ F.symm y := hmono.le_iff_le.mp (by simpa using hxy)
    have h := (hFBound (F.symm x) (F.symm y) hinv).1
    rw [F.apply_symm_apply, F.apply_symm_apply] at h
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hinv),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub, neg_sub]
    have h' : F.symm y - F.symm x ≤ (y - x) / (2 / (9 * Real.pi)) :=
      (le_div_iff₀ hm).mpr (by nlinarith)
    have heq : (y - x) / (2 / (9 * Real.pi)) = (9 * Real.pi / 2) * (y - x) := by
      field_simp
    rwa [heq] at h'
  have hprofile (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : F t = f t := by
    rw [hF]
    exact hg (by simpa only [zero_add] using ht)
  refine ⟨F, ?_, hprofile, ?_, ?_, hFBound, hK, hKi⟩
  · intro t
    rw [hF, hgp, hF]
  · intro t ht
    rw [hprofile t ⟨ht.1, by linarith [ht.2]⟩]
    simp only [f, lensAngleProfile, ite_eq_left ht.2]
  · intro t ht
    rw [hprofile t ⟨by linarith [ht.1], ht.2⟩]
    rcases ht.1.eq_or_lt with rfl | hlt
    · simp only [f, lensAngleProfile, le_refl, ↓reduceIte,
        (lens_angle_branches_endpoints hρ (by linarith : ρ < 2)).1]
    · simp only [f, lensAngleProfile, ite_eq_right (not_le.mpr hlt)]

end DifferentialGeometry.Analysis

end

noncomputable section

open Set
open scoped NNReal
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Analysis

def lensBoundaryLoop (ρ : ℝ) : ℝ → ℂ :=
  joinedLoop
    (fun s => circleMap (-1) ρ (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))
    (fun s => circleMap 0 1 (2 * Real.arccos (ρ / 2) +
      (2 * Real.pi - 4 * Real.arccos (ρ / 2)) * s))

private theorem lens_arc_endpoints {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    let a := Real.arccos (ρ / 2)
    let α := fun s => circleMap (-1) ρ (-a + 2 * a * s)
    let β := fun s => circleMap 0 1 (2 * a + (2 * Real.pi - 4 * a) * s)
    α 1 = β 0 ∧ β 1 = α 0 := by
  dsimp only
  constructor
  · convert circleMap_neg_one_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2) using 1 <;>
      congr 1 <;> ring
  · convert (circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ)
      (by linarith : ρ ≤ 2)).symm using 1 <;> congr 1 <;> ring

private theorem exp_arg_eq_normalize {z : ℂ} (hz : z ≠ 0) :
    (Circle.exp z.arg : ℂ) = NormedSpace.normalize z := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [Circle.coe_exp, NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv]
  calc
    Complex.exp (↑z.arg * Complex.I) =
        (‖z‖ : ℂ)⁻¹ * ((‖z‖ : ℂ) * Complex.exp (↑z.arg * Complex.I)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = (‖z‖ : ℂ)⁻¹ * z := by rw [Complex.norm_mul_exp_arg_mul_I]

private theorem inner_circle_offset_ne_zero {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    circleMap (-1) ρ t - ((-1 + ρ / 2 : ℝ) : ℂ) ≠ 0 := by
  have heq : circleMap (-1) ρ t - ((-1 + ρ / 2 : ℝ) : ℂ) =
      (ρ : ℂ) * (circleMap 0 1 t - (1 / 2 : ℂ)) := by
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_add,
      Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [heq]
  apply mul_ne_zero (by exact_mod_cast hρ.ne')
  intro h
  have hn := congrArg norm (sub_eq_zero.mp h)
  norm_num at hn

private theorem outer_circle_offset_ne_zero {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (t : ℝ) :
    circleMap 0 1 t - ((-1 + ρ / 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.mp h)
  simp only [norm_circleMap_zero, abs_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : -1 + ρ / 2 ≤ 0)] at hn
  linarith

theorem exp_lensAngleProfile_eq_normalize {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (Circle.exp (lensAngleProfile ρ t) : ℂ) =
      NormedSpace.normalize (lensBoundaryLoop ρ t - ((-1 + ρ / 2 : ℝ) : ℂ)) := by
  let a := Real.arccos (ρ / 2)
  let c : ℂ := ((-1 + ρ / 2 : ℝ) : ℂ)
  let α : ℝ → ℂ := fun s => circleMap (-1) ρ (-a + 2 * a * s)
  let β : ℝ → ℂ := fun s => circleMap 0 1 (2 * a + (2 * Real.pi - 4 * a) * s)
  have he : α 1 = β 0 ∧ β 1 = α 0 := lens_arc_endpoints hρ hρ1
  by_cases hhalf : t ≤ 1 / 2
  · rw [lensAngleProfile, ite_eq_left hhalf]
    have hj := joinedLoop_first (a := α) (b := β) he.2
      (show t ∈ Icc (0 : ℝ) (1 / 2) from ⟨ht.1, hhalf⟩)
    change lensBoundaryLoop ρ t = circleMap (-1) ρ (-a + 2 * a * (2 * t)) at hj
    rw [hj, show -a + 2 * a * (2 * t) = -a + 4 * a * t by ring]
    exact exp_arg_eq_normalize (inner_circle_offset_ne_zero hρ _)
  · rw [lensAngleProfile, ite_eq_right hhalf]
    have hj := joinedLoop_second (a := α) (b := β) he.1 he.2
      (show t ∈ Icc (1 / 2 : ℝ) 1 from ⟨le_of_not_ge hhalf, ht.2⟩)
    change lensBoundaryLoop ρ t =
      circleMap 0 1 (2 * a + (2 * Real.pi - 4 * a) * (2 * t - 1)) at hj
    rw [hj]
    let z := circleMap 0 1 (2 * a + (2 * Real.pi - 4 * a) * (2 * t - 1)) - c
    change (Circle.exp (Real.pi + Complex.arg
      (c - circleMap 0 1 (2 * a + (2 * Real.pi - 4 * a) * (2 * t - 1)))) : ℂ) =
        NormedSpace.normalize z
    rw [show c - circleMap 0 1 (2 * a + (2 * Real.pi - 4 * a) * (2 * t - 1)) = -z by
      dsimp only [z]; ring]
    have hz : z ≠ 0 := outer_circle_offset_ne_zero hρ hρ1 _
    rw [Circle.exp_add, Circle.coe_mul, exp_arg_eq_normalize (neg_ne_zero.mpr hz),
      NormedSpace.normalize_neg, Circle.coe_exp, Complex.exp_pi_mul_I]
    ring

theorem exists_lens_circle_homeomorph {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ κ : Circle ≃ₜ Circle,
      LipschitzWith (Real.toNNReal (8 * Real.pi)) κ ∧
      LipschitzWith (Real.toNNReal (9 * Real.pi ^ 2)) κ.symm ∧
      ∀ t : ℝ, (κ (Circle.exp (2 * Real.pi * t - Real.pi)) : ℂ) =
        NormedSpace.normalize (lensBoundaryLoop ρ t - ((-1 + ρ / 2 : ℝ) : ℂ)) := by
  obtain ⟨F, hp, hF, _, _, _, hK, hKi⟩ := exists_lens_angle_homeomorph hρ hρ1
  let Q : ℝ ≃ₜ ℝ := (Homeomorph.addRight (1 / 2 : ℝ)).trans F
  have hQ (t : ℝ) : Q t = F (t + 1 / 2) := rfl
  have hQi (t : ℝ) : Q.symm t = F.symm t - 1 / 2 := rfl
  have hpQ (t : ℝ) : Q (t + 1) = Q t + 1 := by
    rw [hQ, hQ, show t + 1 + 1 / 2 = (t + 1 / 2) + 1 by ring, hp]
  have hQK : LipschitzWith 4 Q := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hQ, hQ]
    simpa only [dist_add_right] using hK.dist_le_mul (x + 1 / 2) (y + 1 / 2)
  have hQKi : LipschitzWith (Real.toNNReal (9 * Real.pi / 2)) Q.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hQi, hQi, dist_sub_right]
    exact hKi.dist_le_mul x y
  let H := affineCircleHomeomorph Q hpQ
  have hHK := affineCircleHomeomorph_lipschitz Q hpQ hQK hQKi
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have heK : LipschitzWith ⟨2 * Real.pi, by positivity⟩ e := by
    intro x y
    change edist ((e x : Circle) : ℂ) ((e y : Circle) : ℂ) ≤ _
    rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply]
    exact circle_boundary_lipschitz x y
  have heKi : LipschitzWith 1 e.symm := circle_parameter_lipschitz
  let κ : Circle ≃ₜ Circle := e.symm.trans (H.trans e)
  have hκ (z : Circle) : κ z = e (H (e.symm z)) := rfl
  have hκi (z : Circle) : κ.symm z = e (H.symm (e.symm z)) := rfl
  have hκK : LipschitzWith (Real.toNNReal (8 * Real.pi)) κ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 8 * Real.pi), hκ, hκ]
    have h₁ := heK.dist_le_mul (H (e.symm x)) (H (e.symm y))
    change dist (e (H (e.symm x))) (e (H (e.symm y))) ≤
      (2 * Real.pi) * dist (H (e.symm x)) (H (e.symm y)) at h₁
    have h₂ := hHK.1.dist_le_mul (e.symm x) (e.symm y)
    have h₃ := heKi.dist_le_mul x y
    norm_num only [NNReal.coe_ofNat, NNReal.coe_one, one_mul] at h₂ h₃
    have h₂' := h₂.trans (mul_le_mul_of_nonneg_left h₃ (by norm_num : (0 : ℝ) ≤ 4))
    have h := h₁.trans (mul_le_mul_of_nonneg_left h₂' (by positivity : 0 ≤ 2 * Real.pi))
    nlinarith
  have hκKi : LipschitzWith (Real.toNNReal (9 * Real.pi ^ 2)) κ.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 9 * Real.pi ^ 2), hκi, hκi]
    have h₁ := heK.dist_le_mul (H.symm (e.symm x)) (H.symm (e.symm y))
    change dist (e (H.symm (e.symm x))) (e (H.symm (e.symm y))) ≤
      (2 * Real.pi) * dist (H.symm (e.symm x)) (H.symm (e.symm y)) at h₁
    have h₂ := hHK.2.dist_le_mul (e.symm x) (e.symm y)
    have h₃ := heKi.dist_le_mul x y
    norm_num only [NNReal.coe_one, one_mul] at h₃
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 9 * Real.pi / 2)] at h₂
    have h₂' := h₂.trans (mul_le_mul_of_nonneg_left h₃ (by positivity : 0 ≤ 9 * Real.pi / 2))
    have h := h₁.trans (mul_le_mul_of_nonneg_left h₂' (by positivity : 0 ≤ 2 * Real.pi))
    nlinarith
  have heval {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      κ (Circle.exp (2 * Real.pi * t - Real.pi)) = Circle.exp (lensAngleProfile ρ t) := by
    have hsource : e (((t - 1 / 2 : ℝ)) : loopCircle) =
        Circle.exp (2 * Real.pi * t - Real.pi) := by
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
      congr 1
      ring
    rw [← hsource, hκ, e.symm_apply_apply]
    rw [AddCircle.homeomorphCircle_apply]
    change AddCircle.toCircle ((Q (t - 1 / 2) : ℝ) : loopCircle) = _
    rw [AddCircle.toCircle_apply_mk, hQ, sub_add_cancel, hF t ht]
    congr 1
    field_simp
  have hphase : Function.Periodic (fun t : ℝ => Circle.exp (2 * Real.pi * t - Real.pi)) 1 := by
    intro t
    dsimp only
    rw [show 2 * Real.pi * (t + 1) - Real.pi = (2 * Real.pi * t - Real.pi) + 2 * Real.pi by ring]
    exact Circle.exp_add_two_pi _
  have hloop : Function.Periodic (lensBoundaryLoop ρ) 1 := joinedLoop_periodic _ _
  refine ⟨κ, hκK, hκKi, ?_⟩
  intro t
  obtain ⟨k, hk, _⟩ := existsUnique_sub_zsmul_mem_Ico (by norm_num : (0 : ℝ) < 1) t 0
  have htk : t - (k : ℝ) ∈ Icc (0 : ℝ) 1 := by
    simpa only [zsmul_eq_mul, mul_one, zero_add] using Ico_subset_Icc_self hk
  have he := congrArg (fun z : Circle => (z : ℂ)) (heval htk)
  rw [exp_lensAngleProfile_eq_normalize hρ hρ1 htk] at he
  have hp' := hphase.sub_zsmul_eq (x := t) k
  have hl' := hloop.sub_zsmul_eq (x := t) k
  simp only [zsmul_eq_mul, mul_one] at hp' hl'
  rwa [hp', hl'] at he

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Metric
open DifferentialGeometry.Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis

theorem lensBoundaryLoop_mem_frontier {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2) (t : ℝ) :
    lensBoundaryLoop ρ t ∈ frontier (boundaryLens ρ) := by
  have ha0 : 0 ≤ Real.arccos (ρ / 2) := Real.arccos_nonneg _
  have hapi : Real.arccos (ρ / 2) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (by linarith)
  apply mapsTo_joinedLoop (S := frontier (boundaryLens ρ)) _ _ (mem_univ t)
  · intro s hs
    apply circleMap_inner_mem_frontier_boundaryLens hρ hρ2
    constructor
    · nlinarith [mul_nonneg ha0 hs.1]
    · nlinarith [mul_le_mul_of_nonneg_left hs.2 ha0]
  · intro s hs
    apply circleMap_outer_mem_frontier_boundaryLens hρ hρ2
    have hd : 0 ≤ 2 * Real.pi - 4 * Real.arccos (ρ / 2) := by linarith
    constructor
    · nlinarith [mul_nonneg hd hs.1]
    · nlinarith [mul_le_mul_of_nonneg_left hs.2 hd]

theorem exists_natural_boundaryLens_bilipschitz_homeomorph {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ h : ℂ ≃ₜ ℂ,
      LipschitzWith (Real.toNNReal (12 * ρ * (16 * Real.pi + 1))) h ∧
      LipschitzWith (Real.toNNReal ((12 / ρ) * (18 * Real.pi ^ 2 + 1))) h.symm ∧
      h '' closedBall (0 : ℂ) 1 = boundaryLens ρ ∧
      h '' sphere (0 : ℂ) 1 = frontier (boundaryLens ρ) ∧
      ∀ t : ℝ, h (circleMap 0 1 (2 * Real.pi * t - Real.pi)) = lensBoundaryLoop ρ t := by
  obtain ⟨κ, hκ, hκi, hκeq⟩ := exists_lens_circle_homeomorph hρ hρ1
  obtain ⟨e, heq, he, hei, heimage, hesphere⟩ := exists_boundaryLens_bilipschitz_homeomorph hρ hρ1
  let k := radialHomeomorph κ hκ hκi
  let h := k.trans e
  have hK : Real.toNNReal (12 * ρ) * (2 * Real.toNNReal (8 * Real.pi) + 1) =
      Real.toNNReal (12 * ρ * (16 * Real.pi + 1)) := by
    apply Subtype.ext
    change (Real.toNNReal (12 * ρ) : ℝ) * (2 * (Real.toNNReal (8 * Real.pi) : ℝ) + 1) =
      (Real.toNNReal (12 * ρ * (16 * Real.pi + 1)) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by positivity)]
    ring
  have hKi : (2 * Real.toNNReal (9 * Real.pi ^ 2) + 1) * Real.toNNReal (12 / ρ) =
      Real.toNNReal ((12 / ρ) * (18 * Real.pi ^ 2 + 1)) := by
    apply Subtype.ext
    change (2 * (Real.toNNReal (9 * Real.pi ^ 2) : ℝ) + 1) * (Real.toNNReal (12 / ρ) : ℝ) =
      (Real.toNNReal ((12 / ρ) * (18 * Real.pi ^ 2 + 1)) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by positivity)]
    ring
  have hLip : LipschitzWith (Real.toNNReal (12 * ρ * (16 * Real.pi + 1))) h := by
    have hl := he.comp (radialHomeomorph_lipschitz κ hκ hκi)
    rw [hK] at hl
    exact hl
  have hLipi : LipschitzWith (Real.toNNReal ((12 / ρ) * (18 * Real.pi ^ 2 + 1))) h.symm := by
    have hl := (radialHomeomorph_symm_lipschitz κ hκ hκi).comp hei
    rw [hKi] at hl
    exact hl
  refine ⟨h, hLip, hLipi, ?_, ?_, ?_⟩
  · change (e ∘ k) '' closedBall (0 : ℂ) 1 = boundaryLens ρ
    rw [Set.image_comp, radialHomeomorph_image_closedBall]
    exact heimage
  · change (e ∘ k) '' sphere (0 : ℂ) 1 = frontier (boundaryLens ρ)
    rw [Set.image_comp, radialHomeomorph_image_sphere]
    exact hesphere
  · intro t
    have hphase : circleMap 0 1 (2 * Real.pi * t - Real.pi) =
        (Circle.exp (2 * Real.pi * t - Real.pi) : ℂ) := by
      simp only [circleMap_zero, Complex.ofReal_one, one_mul, Circle.coe_exp]
    change e (k (circleMap 0 1 (2 * Real.pi * t - Real.pi))) = lensBoundaryLoop ρ t
    rw [hphase, radialHomeomorph_circle, hκeq]
    rw [heq]
    exact boundaryLens_gaugeRescale_normalize_eq hρ hρ1
      (lensBoundaryLoop_mem_frontier hρ.le (hρ1.trans (by norm_num)) t)

end DifferentialGeometry.Analysis

end
