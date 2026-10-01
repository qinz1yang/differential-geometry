import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.TubeEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
noncomputable section

open Bundle Set Function MeasureTheory Filter Manifold
open scoped Manifold ContDiff Topology Interval

open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩


open private neckCylDomain neckCylMap isSmoothEmbedding_neckCylMap neckCylPoint neckCylPoint_eq_neckPoint
  from DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.TubeEmbedding

private def satRate (u : ℝ) : ℝ := (1 / 2) * Real.exp (-(8 * u * expNegInvGlue u))

private def satMass (s : ℝ) : ℝ := ∫ x in (0)..s, satRate x

private def satPrimitive (s : ℝ) : ℝ := ∫ x in (0)..s, (satRate x - 1 / 2)

private def satBound : ℝ := 1 / 2 + Real.exp (-2) / 4

private def cylinderHeight (t : ℝ) : ℝ :=
  t / 4 + (satPrimitive (t - 2) - satPrimitive (-t - 2)) / 2

private theorem contDiff_satRate : ContDiff ℝ ∞ satRate := by
  unfold satRate
  fun_prop

private theorem satRate_pos (u : ℝ) : 0 < satRate u := by
  unfold satRate
  positivity

private theorem satRate_nonneg (u : ℝ) : 0 ≤ satRate u := (satRate_pos u).le

private theorem satRate_le_half (u : ℝ) : satRate u ≤ 1 / 2 := by
  have h1 : (0 : ℝ) ≤ 8 * u * expNegInvGlue u := by
    rcases le_or_gt 0 u with hu | hu
    · have := expNegInvGlue.nonneg u; nlinarith
    · rw [expNegInvGlue.zero_of_nonpos hu.le]; norm_num
  have h2 : Real.exp (-(8 * u * expNegInvGlue u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  unfold satRate
  linarith

private theorem satRate_of_nonpos {u : ℝ} (hu : u ≤ 0) : satRate u = 1 / 2 := by
  unfold satRate
  rw [expNegInvGlue.zero_of_nonpos hu, mul_zero, neg_zero, Real.exp_zero, mul_one]

private theorem contDiff_satMass : ContDiff ℝ ∞ satMass := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous
    contDiff_satRate.continuous, ?_⟩
  have h : deriv satMass = satRate := by
    funext s
    exact Continuous.deriv_integral satRate contDiff_satRate.continuous 0 s
  rw [h]
  exact contDiff_satRate

private theorem satMass_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ satMass s :=
  intervalIntegral.integral_nonneg hs fun u _ => satRate_nonneg u

private theorem satMass_nonpos {s : ℝ} (hs : s ≤ 0) : satMass s ≤ 0 := by
  rw [satMass, intervalIntegral.integral_symm (μ := volume) (f := satRate) s 0]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hs fun u _ => satRate_nonneg u)

private theorem expNegInvGlue_ge_quarter {x : ℝ} (hx : 1 ≤ x) :
    (1 / 4 : ℝ) ≤ expNegInvGlue x := by
  have h1 : expNegInvGlue 1 ≤ expNegInvGlue x := expNegInvGlue.monotone hx
  have h2 : expNegInvGlue 1 = Real.exp (-1) := by
    rw [expNegInvGlue, ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 0), inv_one]
  have h3 : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    have h4 : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
    rw [h4, Real.exp_neg]
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) (Real.exp_pos 1)).mpr
      (Real.exp_one_lt_three.trans (by norm_num : (3 : ℝ) < 4)).le
  rw [h2] at h1
  exact h3.trans h1

private theorem satRate_le_exp {x : ℝ} (hx : 1 ≤ x) :
    satRate x ≤ (1 / 2) * Real.exp (-2 * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hη : (1 / 4 : ℝ) ≤ expNegInvGlue x := expNegInvGlue_ge_quarter hx
  have hmono : Real.exp (-(8 * x * expNegInvGlue x)) ≤ Real.exp (-2 * x) := by
    apply Real.exp_le_exp.mpr
    have hxη : x * (1 / 4) ≤ x * expNegInvGlue x := mul_le_mul_of_nonneg_left hη hx0.le
    nlinarith
  unfold satRate
  linarith

private theorem integral_exp_neg_two (s : ℝ) :
    ∫ x in (1)..s, (1 / 2 : ℝ) * Real.exp (-2 * x) =
      (1 / 4) * (Real.exp (-2) - Real.exp (-2 * s)) := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (a := 1) (b := s) (c := (-2 : ℝ)) Real.exp
    (by norm_num : (-2 : ℝ) ≠ 0)]
  rw [integral_exp]
  norm_num
  ring

private theorem satMass_le_satBound (s : ℝ) : satMass s ≤ satBound := by
  have hb : (0 : ℝ) ≤ Real.exp (-2) := (Real.exp_pos (-2)).le
  rcases le_or_gt s 1 with hs | hs
  · rcases le_or_gt s 0 with hs0 | hs0
    · have h := satMass_nonpos hs0
      unfold satBound
      linarith
    · have h1 : satMass s ≤ ∫ x in (0)..s, (1 / 2 : ℝ) ∂volume :=
        intervalIntegral.integral_mono_on hs0.le
          (contDiff_satRate.continuous.intervalIntegrable 0 s)
          (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ)))
          fun x _ => satRate_le_half x
      have h2 : ∫ x in (0)..s, (1 / 2 : ℝ) ∂volume = s / 2 := by
        rw [intervalIntegral.integral_const]; simp [smul_eq_mul, div_eq_mul_inv]
      unfold satBound
      linarith
  · have hsplit : satMass s =
        ∫ x in (0)..1, satRate x ∂volume + ∫ x in (1)..s, satRate x ∂volume := by
      rw [satMass, ← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (contDiff_satRate.continuous.intervalIntegrable 0 1)
        (contDiff_satRate.continuous.intervalIntegrable 1 s)]
    have h1 : ∫ x in (0)..1, satRate x ∂volume ≤ 1 / 2 := by
      have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (contDiff_satRate.continuous.intervalIntegrable 0 1)
        (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ)))
        (fun x _ => satRate_le_half x)
      have hconst : ∫ x in (0)..1, (1 / 2 : ℝ) ∂volume = 1 / 2 := by
        rw [intervalIntegral.integral_const]; simp
      linarith
    have hcont : Continuous fun x : ℝ => (1 / 2 : ℝ) * Real.exp (-2 * x) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have h2 : ∫ x in (1)..s, satRate x ∂volume ≤ Real.exp (-2) / 4 := by
      have hmono : ∫ x in (1)..s, satRate x ∂volume ≤
          ∫ x in (1)..s, (1 / 2 : ℝ) * Real.exp (-2 * x) ∂volume :=
        intervalIntegral.integral_mono_on hs.le
          (contDiff_satRate.continuous.intervalIntegrable 1 s) (hcont.intervalIntegrable 1 s)
          (fun x hx => satRate_le_exp hx.1)
      rw [integral_exp_neg_two s] at hmono
      have : (0 : ℝ) ≤ Real.exp (-2 * s) := (Real.exp_pos _).le
      linarith
    rw [hsplit]
    unfold satBound
    linarith

private theorem satBound_lt_one : satBound < 1 := by
  have h : Real.exp (-2) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  unfold satBound
  linarith

private theorem contDiff_satPrimitive : ContDiff ℝ ∞ satPrimitive := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous ?_, ?_⟩
  · exact contDiff_satRate.continuous.sub continuous_const
  · have h : deriv satPrimitive = fun s => satRate s - 1 / 2 := by
      funext s
      exact Continuous.deriv_integral (fun x => satRate x - 1 / 2)
        (contDiff_satRate.continuous.sub continuous_const) 0 s
    rw [h]
    exact contDiff_satRate.sub contDiff_const

private theorem satPrimitive_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : satPrimitive s = 0 := by
  have hcongr : ∫ x in (0)..s, (satRate x - 1 / 2) = ∫ x in (0)..s, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_ge hs] at hx
    change satRate x - 1 / 2 = 0
    rw [satRate_of_nonpos hx.2]
    ring
  rw [satPrimitive, hcongr, intervalIntegral.integral_zero]

private theorem satPrimitive_eq (s : ℝ) : satPrimitive s = satMass s - s / 2 := by
  rw [satPrimitive, satMass, intervalIntegral.integral_sub
    (contDiff_satRate.continuous.intervalIntegrable 0 s)
    (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ))),
    intervalIntegral.integral_const]
  simp [smul_eq_mul, div_eq_mul_inv]

private theorem contDiff_cylinderHeight : ContDiff ℝ ∞ cylinderHeight := by
  have h1 : ContDiff ℝ ∞ fun t : ℝ => satPrimitive (t - 2) :=
    contDiff_satPrimitive.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => satPrimitive (-t - 2) :=
    contDiff_satPrimitive.comp ((contDiff_id.neg.sub contDiff_const))
  have h3 : ContDiff ℝ ∞ fun t : ℝ => t / 4 :=
    (contDiff_id (𝕜 := ℝ) (n := ∞)).div_const 4
  have h4 : ContDiff ℝ ∞ fun t : ℝ =>
      (satPrimitive (t - 2) - satPrimitive (-t - 2)) / 2 := (h1.sub h2).div_const 2
  have h5 : cylinderHeight = fun t : ℝ =>
      t / 4 + (satPrimitive (t - 2) - satPrimitive (-t - 2)) / 2 := rfl
  rw [h5]
  exact h3.add h4

private theorem hasDerivAt_satPrimitive (s : ℝ) :
    HasDerivAt satPrimitive (satRate s - 1 / 2) s := by
  have h : HasDerivAt satPrimitive (deriv satPrimitive s) s :=
    (Differentiable.differentiableAt (contDiff_satPrimitive.differentiable (by simp))
      (x := s)).hasDerivAt
  rwa [show deriv satPrimitive s = satRate s - 1 / 2 from
    Continuous.deriv_integral (fun x => satRate x - 1 / 2)
      (contDiff_satRate.continuous.sub continuous_const) 0 s] at h

private theorem deriv_cylinderHeight (t : ℝ) :
    deriv cylinderHeight t = (satRate (t - 2) + satRate (-t - 2)) / 2 - 1 / 4 := by
  have h1 : HasDerivAt (fun s : ℝ => satPrimitive (s - 2)) (satRate (t - 2) - 1 / 2) t := by
    have h := (hasDerivAt_satPrimitive (t - 2)).comp t ((hasDerivAt_id t).sub_const 2)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have h2 : HasDerivAt (fun s : ℝ => satPrimitive (-s - 2))
      (-(satRate (-t - 2) - 1 / 2)) t := by
    have h := (hasDerivAt_satPrimitive (-t - 2)).comp t ((hasDerivAt_id t).neg.sub_const 2)
    simpa only [Function.comp_def, id_eq, Pi.neg_apply, mul_neg, mul_one] using h
  have h3 : HasDerivAt (fun s : ℝ =>
      s / 4 + (satPrimitive (s - 2) - satPrimitive (-s - 2)) / 2)
      (1 / 4 + ((satRate (t - 2) - 1 / 2) - (-(satRate (-t - 2) - 1 / 2))) / 2) t :=
    ((hasDerivAt_id t).div_const 4).add ((h1.sub h2).div_const 2)
  have h4 : cylinderHeight = fun s : ℝ =>
      s / 4 + (satPrimitive (s - 2) - satPrimitive (-s - 2)) / 2 := rfl
  rw [h4, h3.deriv]
  ring

private theorem deriv_cylinderHeight_pos (t : ℝ) : 0 < deriv cylinderHeight t := by
  rw [deriv_cylinderHeight]
  rcases le_or_gt 2 t with ht | ht
  · have h : satRate (-t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
    rw [h]
    have := satRate_pos (t - 2)
    linarith
  · rcases le_or_gt t (-2) with ht' | ht'
    · have h : satRate (t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
      rw [h]
      have := satRate_pos (-t - 2)
      linarith
    · have h1 : satRate (t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
      have h2 : satRate (-t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
      rw [h1, h2]
      norm_num

private theorem strictMono_cylinderHeight : StrictMono cylinderHeight :=
  strictMono_of_deriv_pos deriv_cylinderHeight_pos

private theorem cylinderHeight_of_le_neg_two {t : ℝ} (ht : t ≤ -2) :
    cylinderHeight t = -1 / 2 - satMass (-t - 2) / 2 := by
  rw [cylinderHeight, satPrimitive_zero_of_nonpos (by linarith : t - 2 ≤ 0),
    satPrimitive_eq (-t - 2)]
  ring

private theorem cylinderHeight_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    cylinderHeight t = 1 / 2 + satMass (t - 2) / 2 := by
  rw [cylinderHeight, satPrimitive_eq (t - 2),
    satPrimitive_zero_of_nonpos (by linarith : -t - 2 ≤ 0)]
  ring

private theorem cylinderHeight_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    cylinderHeight t = t / 4 := by
  rw [cylinderHeight, satPrimitive_zero_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0),
    satPrimitive_zero_of_nonpos (by linarith [ht.1] : -t - 2 ≤ 0)]
  ring

private theorem abs_cylinderHeight_lt_one (t : ℝ) : |cylinderHeight t| < 1 := by
  rcases le_or_gt 2 t with ht | ht
  · rw [cylinderHeight_of_two_le ht, abs_lt]
    have h1 : 0 ≤ satMass (t - 2) := satMass_nonneg (by linarith)
    have h2 : satMass (t - 2) ≤ satBound := satMass_le_satBound _
    have h3 : satBound < 1 := satBound_lt_one
    constructor <;> linarith
  · rcases le_or_gt t (-2) with ht' | ht'
    · rw [cylinderHeight_of_le_neg_two ht', abs_lt]
      have h1 : 0 ≤ satMass (-t - 2) := satMass_nonneg (by linarith)
      have h2 : satMass (-t - 2) ≤ satBound := satMass_le_satBound _
      have h3 : satBound < 1 := satBound_lt_one
      constructor <;> linarith
    · rw [cylinderHeight_of_mem_Icc ⟨ht'.le, ht.le⟩, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      have : |t| < 2 := abs_lt.mpr ⟨ht', ht⟩
      linarith

private theorem isSmoothEmbedding_cylinderHeight :
    IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ) ∞ cylinderHeight := by
  refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv
    contDiff_cylinderHeight.contMDiff strictMono_cylinderHeight.injective ?_ ?_
  · intro x
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ cylinderHeight x : ℝ →L[ℝ] ℝ)
    intro u v huv
    have h0 : (u - v) • deriv cylinderHeight x = 0 := by
      rw [← fderiv_eq_smul_deriv, map_sub, huv, sub_self]
    have h1 : (u - v) = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (ne_of_gt (deriv_cylinderHeight_pos x))
    linarith
  · simp


private theorem abs_satCylPoint_param (p : Sphere 2 × ℝ) : |cylinderHeight p.2| < 1 :=
  abs_cylinderHeight_lt_one p.2

private theorem sq_satCylPoint_param (p : Sphere 2 × ℝ) : cylinderHeight p.2 ^ 2 ≤ 1 := by
  have h := abs_cylinderHeight_lt_one p.2
  nlinarith [abs_nonneg (cylinderHeight p.2), sq_abs (cylinderHeight p.2)]

private def satBandPoint (p : Sphere 2 × ℝ) : ↥neckCylDomain :=
  ⟨(p.1, cylinderHeight p.2), by
    change cylinderHeight p.2 ∈ Ioo (-(1 : ℝ)) 1
    exact (abs_lt.mp (abs_cylinderHeight_lt_one p.2))⟩

private theorem isSmoothEmbedding_satBandPoint :
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) ∞ satBandPoint := by
  refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) neckCylDomain satBandPoint ?_
  have hprod : IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) ∞
      (Prod.map (id : Sphere 2 → Sphere 2) cylinderHeight) :=
    IsSmoothEmbedding.prodMap IsSmoothEmbedding.id isSmoothEmbedding_cylinderHeight
  convert hprod using 1
  funext p
  rfl

private def cylinderExtensionMap (p : Sphere 2 × ℝ) : Sphere 3 :=
  neckCylMap (satBandPoint p)

private theorem isSmoothEmbedding_cylinderExtensionMap :
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ cylinderExtensionMap :=
  IsSmoothEmbedding.comp (I := (𝓡 2).prod 𝓘(ℝ)) (J := (𝓡 2).prod 𝓘(ℝ))
    (J' := ThreeModel) (f := satBandPoint) (g := neckCylMap)
    isSmoothEmbedding_neckCylMap isSmoothEmbedding_satBandPoint (by decide)

private theorem cylinderExtensionMap_apply_tube (z : TubeDomain) :
    cylinderExtensionMap (z.1, (z.2 : ℝ)) = standardNeckTubeFun z := by
  apply Subtype.ext
  change neckCylPoint z.1 (cylinderHeight (z.2 : ℝ)) = neckPoint z.1 (z.2 : ℝ)
  rw [cylinderHeight_of_mem_Icc z.2.2]
  exact neckCylPoint_eq_neckPoint z.1 (z.2 : ℝ)

theorem exists_isSmoothEmbedding_eq_standardNeckTubeFun :
    ∃ g : Sphere 2 × ℝ → Sphere 3,
      IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g ∧
        ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z :=
  ⟨cylinderExtensionMap, isSmoothEmbedding_cylinderExtensionMap,
    fun z => cylinderExtensionMap_apply_tube z⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
