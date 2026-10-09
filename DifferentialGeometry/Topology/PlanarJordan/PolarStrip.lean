/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.PlanarTubeSmoothing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

noncomputable def polarStripMap (x : Plane) : Plane :=
  (3 / 2 + x 1) • Plane.mk (Real.cos (x 0)) (Real.sin (x 0))

theorem polarStripMap_apply_zero (x : Plane) :
    polarStripMap x 0 = (3 / 2 + x 1) * Real.cos (x 0) := by
  simp [polarStripMap]

theorem polarStripMap_apply_one (x : Plane) :
    polarStripMap x 1 = (3 / 2 + x 1) * Real.sin (x 0) := by
  simp [polarStripMap]

theorem norm_planeMk_cos_sin (t : ℝ) : ‖Plane.mk (Real.cos t) (Real.sin t)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.cos_sq_add_sin_sq]

theorem norm_polarStripMap (x : Plane) : ‖polarStripMap x‖ = |3 / 2 + x 1| := by
  rw [polarStripMap, norm_smul, norm_planeMk_cos_sin, mul_one, Real.norm_eq_abs]

theorem contDiff_polarStripMap : ContDiff ℝ ∞ polarStripMap := by
  have h0 : ContDiff ℝ ∞ fun x : Plane => (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x :=
    ContinuousLinearMap.contDiff _
  have h1 : ContDiff ℝ ∞ fun x : Plane => (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) x :=
    ContinuousLinearMap.contDiff _
  have hmk : ∀ x : Plane, Plane.mk (Real.cos (x 0)) (Real.sin (x 0)) =
      Real.cos (x 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        Real.sin (x 0) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) :=
    fun x => planeMk_eq_smul_add _ _
  have hc : ContDiff ℝ ∞ fun x : Plane =>
      Real.cos ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) :=
    Real.contDiff_cos.comp h0
  have hs : ContDiff ℝ ∞ fun x : Plane =>
      Real.sin ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) :=
    Real.contDiff_sin.comp h0
  have hu : ContDiff ℝ ∞ fun x : Plane =>
      Real.cos ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) •
          EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        Real.sin ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ) :=
    (hc.smul contDiff_const).add (hs.smul contDiff_const)
  have hr : ContDiff ℝ ∞ fun x : Plane =>
      3 / 2 + (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) x :=
    contDiff_const.add h1
  have heq : polarStripMap = fun x : Plane =>
      (3 / 2 + (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) x) •
        (Real.cos ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) •
            EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
          Real.sin ((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) x) •
            EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    funext x
    rw [polarStripMap, hmk]
    rfl
  rw [heq]
  exact hr.smul hu

theorem det_fderiv_polarStripMap (x : Plane) :
    LinearMap.det (fderiv ℝ polarStripMap x : Plane →ₗ[ℝ] Plane) = -(3 / 2 + x 1) := by
  let π₀ : Plane →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
  let π₁ : Plane →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 2)
  let e₀ : Plane := EuclideanSpace.single 0 1
  let e₁ : Plane := EuclideanSpace.single 1 1
  have hc := ((Real.hasDerivAt_cos (π₀ x)).hasFDerivAt.comp x π₀.hasFDerivAt).smul_const e₀
  have hs := ((Real.hasDerivAt_sin (π₀ x)).hasFDerivAt.comp x π₀.hasFDerivAt).smul_const e₁
  have hr := (π₁.hasFDerivAt (x := x)).const_add (3 / 2 : ℝ)
  have h := hr.smul (hc.add hs)
  have hfun : polarStripMap = fun y : Plane =>
      (3 / 2 + π₁ y) • (Real.cos (π₀ y) • e₀ + Real.sin (π₀ y) • e₁) := by
    funext y
    rw [polarStripMap, planeMk_eq_smul_add]
    rfl
  have h2 := h.congr_of_eventuallyEq (f₁ := polarStripMap)
    (Filter.Eventually.of_forall fun y => congrFun hfun y)
  rw [h2.fderiv, det_eq_planeDet]
  simp [π₀, π₁, e₀, e₁, Schoenflies.Plane.det]
  have h3 := Real.sin_sq_add_cos_sq (x 0)
  linear_combination (-(3 / 2 + x 1)) * h3

theorem polarStripMap_injective_of_abs_sub_lt {x y : Plane} (hx : |x 1| < 3 / 2)
    (hy : |y 1| < 3 / 2) (hxy : |x 0 - y 0| < 2 * Real.pi) (h : polarStripMap x = polarStripMap y) :
    x = y := by
  have hx' : 0 < 3 / 2 + x 1 := by linarith [neg_abs_le (x 1)]
  have hy' : 0 < 3 / 2 + y 1 := by linarith [neg_abs_le (y 1)]
  have hn := congrArg norm h
  rw [norm_polarStripMap, norm_polarStripMap, abs_of_pos hx', abs_of_pos hy'] at hn
  have h1 : x 1 = y 1 := by linarith
  have hc : Real.cos (x 0) = Real.cos (y 0) := by
    have := congrArg (fun v : Plane => v 0) h
    simp only [polarStripMap_apply_zero, h1] at this
    exact mul_left_cancel₀ hy'.ne' this
  have hs : Real.sin (x 0) = Real.sin (y 0) := by
    have := congrArg (fun v : Plane => v 1) h
    simp only [polarStripMap_apply_one, h1] at this
    exact mul_left_cancel₀ hy'.ne' this
  have hc' := Real.cos_sub_cos (x 0) (y 0)
  have hs' := Real.sin_sub_sin (x 0) (y 0)
  rw [hc, sub_self] at hc'
  rw [hs, sub_self] at hs'
  have hd : Real.sin ((x 0 - y 0) / 2) = 0 := by
    by_contra hne
    have ha : Real.sin ((x 0 + y 0) / 2) = 0 := by
      have := hc'.symm
      rcases mul_eq_zero.mp this with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · norm_num at h4
        · exact h4
      · exact absurd h3 hne
    have hb : Real.cos ((x 0 + y 0) / 2) = 0 := by
      have := hs'.symm
      rcases mul_eq_zero.mp this with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · norm_num at h4
        · exact absurd h4 hne
      · exact h3
    have := Real.sin_sq_add_cos_sq ((x 0 + y 0) / 2)
    rw [ha, hb] at this
    norm_num at this
  have hlt := abs_lt.mp hxy
  have h0 : (x 0 - y 0) / 2 = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).mp hd
  ext i
  fin_cases i
  · change x 0 = y 0
    linarith
  · exact h1

theorem exists_polarStripMap_eq {w : Plane} (hw : 0 < ‖w‖) :
    ∃ t ∈ Ico (0 : ℝ) (2 * Real.pi),
      polarStripMap (Plane.mk t (‖w‖ - 3 / 2)) = w := by
  set u0 := w 0 / ‖w‖ with hu0
  set u1 := w 1 / ‖w‖ with hu1
  have hsq : u0 ^ 2 + u1 ^ 2 = 1 := by
    have hn := EuclideanSpace.norm_eq w
    rw [Fin.sum_univ_two] at hn
    have h2 : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
      rw [hn, Real.sq_sqrt (by positivity), Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    rw [hu0, hu1, div_pow, div_pow, ← add_div, ← h2, div_self (by positivity)]
  have hu0le : -1 ≤ u0 ∧ u0 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg u1, sq_nonneg (u0 + 1), sq_nonneg (u0 - 1)]
  have hpi := Real.pi_pos
  have key : ∃ t ∈ Ico (0 : ℝ) (2 * Real.pi), Real.cos t = u0 ∧ Real.sin t = u1 := by
    rcases le_or_gt 0 u1 with h | h
    · refine ⟨Real.arccos u0, ⟨Real.arccos_nonneg _, by linarith [Real.arccos_le_pi u0]⟩,
        Real.cos_arccos hu0le.1 hu0le.2, ?_⟩
      rw [Real.sin_arccos]
      have : 1 - u0 ^ 2 = u1 ^ 2 := by linarith
      rw [this, Real.sqrt_sq h]
    · refine ⟨2 * Real.pi - Real.arccos u0, ⟨by linarith [Real.arccos_le_pi u0], ?_⟩, ?_, ?_⟩
      · have hpos : 0 < Real.arccos u0 := by
          rw [Real.arccos_pos]
          by_contra hge
          have h1 : u0 = 1 := le_antisymm hu0le.2 (not_lt.mp hge)
          rw [h1] at hsq
          nlinarith
        linarith
      · rw [Real.cos_two_pi_sub, Real.cos_arccos hu0le.1 hu0le.2]
      · rw [Real.sin_two_pi_sub, Real.sin_arccos]
        have : 1 - u0 ^ 2 = (-u1) ^ 2 := by linarith
        rw [this, Real.sqrt_sq (by linarith)]
        ring
  obtain ⟨t, ht, hc, hs⟩ := key
  refine ⟨t, ht, ?_⟩
  ext i
  fin_cases i
  · change polarStripMap (Plane.mk t (‖w‖ - 3 / 2)) 0 = w 0
    rw [polarStripMap_apply_zero]
    change (3 / 2 + (‖w‖ - 3 / 2)) * Real.cos t = w 0
    rw [hc, hu0]
    field_simp
    ring
  · change polarStripMap (Plane.mk t (‖w‖ - 3 / 2)) 1 = w 1
    rw [polarStripMap_apply_one]
    change (3 / 2 + (‖w‖ - 3 / 2)) * Real.sin t = w 1
    rw [hs, hu1]
    field_simp
    ring

theorem polarStripMap_two_pi_zero :
    polarStripMap (Plane.mk (2 * Real.pi) 0) = polarStripMap (Plane.mk 0 0) := by
  simp [polarStripMap]

theorem exists_openPartialHomeomorph_contDiffOn_symm {f : Plane → Plane} {V : Set Plane}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (hdet : ∀ z ∈ V, LinearMap.det (fderiv ℝ f z : Plane →ₗ[ℝ] Plane) ≠ 0) {x : Plane}
    (hx : x ∈ V) :
    ∃ Λ : OpenPartialHomeomorph Plane Plane, x ∈ Λ.source ∧ Λ.source ⊆ V ∧ EqOn Λ f Λ.source ∧
      ContDiffOn ℝ ∞ Λ.symm Λ.target := by
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hV.mem_nhds hx)
  have hstrict : HasStrictFDerivAt f
      (((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hdet x hx) : Plane ≃L[ℝ] Plane) :
        Plane →L[ℝ] Plane) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hfx.hasStrictFDerivAt (by simp)
  let T := hstrict.toOpenPartialHomeomorph f
  let Λ := T.restr V
  have hΛs : Λ.source = T.source ∩ V := by
    rw [OpenPartialHomeomorph.restr_source, hV.interior_eq]
  have hΛf : EqOn Λ f Λ.source := fun z _ => by
    change T z = f z
    rw [hstrict.toOpenPartialHomeomorph_coe]
  refine ⟨Λ, by rw [hΛs]; exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hx⟩,
    by rw [hΛs]; exact inter_subset_right, hΛf, fun a ha => ?_⟩
  have hsa : Λ.symm a ∈ Λ.source := Λ.map_target ha
  have hsaV : Λ.symm a ∈ V := by
    rw [hΛs] at hsa
    exact hsa.2
  have hev : (Λ : Plane → Plane) =ᶠ[𝓝 (Λ.symm a)] f :=
    Filter.eventuallyEq_of_mem (Λ.open_source.mem_nhds hsa) hΛf
  have hcd : ContDiffAt ℝ ∞ f (Λ.symm a) := hf.contDiffAt (hV.mem_nhds hsaV)
  have hd : HasFDerivAt (Λ : Plane → Plane)
      (((fderiv ℝ f (Λ.symm a)).toContinuousLinearEquivOfDetNeZero (hdet _ hsaV) :
        Plane ≃L[ℝ] Plane) : Plane →L[ℝ] Plane) (Λ.symm a) := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact ((hcd.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq hev
  exact (Λ.contDiffAt_symm ha hd (hcd.congr_of_eventuallyEq hev)).contDiffWithinAt

end DifferentialGeometry.Topology.PlanarJordan
