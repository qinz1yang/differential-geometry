/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Conformal.Euclidean.QuadraticConformalFactor
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.RingTheory.SimpleRing.Principal

open RealInnerProductSpace InnerProductSpace Filter Metric
open scoped Topology

namespace DifferentialGeometry.LiouvilleMobius

open DifferentialGeometry.LiouvilleRigidity DifferentialGeometry.LiouvilleIntegration DifferentialGeometry.LiouvilleQuadratic

noncomputable section

variable {m : ℕ}

def inversion (x₀ : ES m) (y : ES m) : ES m := x₀ + (‖y - x₀‖^2)⁻¹ • (y - x₀)

theorem inversion_sub_center (x₀ y : ES m) :
    inversion x₀ y - x₀ = (‖y - x₀‖^2)⁻¹ • (y - x₀) := by
  rw [inversion, add_sub_cancel_left]

theorem inversion_ne_center {x₀ y : ES m} (h : y ≠ x₀) : inversion x₀ y ≠ x₀ := by
  intro h00
  have h1 := inversion_sub_center x₀ y
  have h2 : (‖y - x₀‖^2)⁻¹ • (y - x₀) ≠ 0 :=
    smul_ne_zero (inv_ne_zero (pow_ne_zero 2 (norm_pos_iff.mpr (sub_ne_zero.mpr h)).ne'))
      (sub_ne_zero.mpr h)
  rw [← h1] at h2
  exact h2 (sub_eq_zero.mpr h00)

theorem norm_inversion_sub_center {x₀ y : ES m} (h : y ≠ x₀) :
    ‖inversion x₀ y - x₀‖ = ‖y - x₀‖⁻¹ := by
  rw [inversion_sub_center, norm_smul, Real.norm_eq_abs]
  have hpos : (0:ℝ) < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  rw [abs_of_pos (by positivity : (0:ℝ) < (‖y - x₀‖^2)⁻¹)]
  field_simp

theorem inversion_involution {x₀ y : ES m} (h : y ≠ x₀) :
    inversion x₀ (inversion x₀ y) = y := by
  have hnorm := norm_inversion_sub_center h
  rw [inversion, hnorm, inversion_sub_center, inv_pow, inv_inv, ← mul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 (norm_pos_iff.mpr (sub_ne_zero.mpr h)).ne'), one_smul,
    add_sub_cancel]

theorem hasFDerivAt_inversion {x₀ y : ES m} (h : y ≠ x₀) :
    HasFDerivAt (inversion x₀)
      ((‖y - x₀‖^2)⁻¹ • ContinuousLinearMap.id ℝ (ES m)
        + (((ContinuousLinearMap.toSpanSingleton ℝ (-((‖y - x₀‖^2)^2)⁻¹))).comp
            (2 • innerSL ℝ (y - x₀))).smulRight (y - x₀)) y := by
  have hu : y - x₀ ≠ 0 := sub_ne_zero.mpr h
  have hS : ‖y - x₀‖^2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr hu).ne'
  have h1 : HasFDerivAt (fun y : ES m => y - x₀) (ContinuousLinearMap.id ℝ (ES m)) y := by
    have hh : HasFDerivAt (id - fun _ : ES m => x₀)
        (ContinuousLinearMap.id ℝ (ES m) - 0) y :=
      (hasFDerivAt_id y).sub (hasFDerivAt_const x₀ y)
    rw [sub_zero] at hh
    exact hh
  have h2 : HasFDerivAt (fun y : ES m => ‖y - x₀‖^2) (2 • innerSL ℝ (y - x₀)) y := by
    have h12 := (hasStrictFDerivAt_norm_sq (y - x₀)).hasFDerivAt.comp y h1
    rwa [ContinuousLinearMap.comp_id] at h12
  have h3 : HasFDerivAt (fun y : ES m => (‖y - x₀‖^2)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖y - x₀‖^2)^2)⁻¹)).comp (2 • innerSL ℝ (y - x₀))) y := by
    have hinv := (hasFDerivAt_inv hS).comp y h2
    rwa [Function.comp_def] at hinv
  have h4 := h3.smul h1
  have h5 := h4.const_add x₀
  exact h5

theorem inversion_fderiv_apply {x₀ y : ES m} (h : y ≠ x₀) (v : ES m) :
    fderiv ℝ (inversion x₀) y v
      = (‖y - x₀‖^2)⁻¹ • v + ((2 * ⟪y - x₀, v⟫_ℝ) * (-((‖y - x₀‖^2)^2)⁻¹)) • (y - x₀) := by
  rw [(hasFDerivAt_inversion h).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, coe_innerSL_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
  norm_num [smul_eq_mul]

theorem inner_inversion_fderiv {x₀ y : ES m} (h : y ≠ x₀) (v w : ES m) :
    ⟪fderiv ℝ (inversion x₀) y v, fderiv ℝ (inversion x₀) y w⟫_ℝ
      = ((‖y - x₀‖^2)^2)⁻¹ * ⟪v, w⟫_ℝ := by
  rw [inversion_fderiv_apply h, inversion_fderiv_apply h]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_comm v (y - x₀)]
  have hS : ‖y - x₀‖^2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr (sub_ne_zero.mpr h)).ne'
  have hu0 : ‖y - x₀‖ ≠ 0 := (norm_pos_iff.mpr (sub_ne_zero.mpr h)).ne'
  field_simp [hS, hu0]
  ring

theorem isConformalMap_fderiv_inversion {x₀ y : ES m} (h : y ≠ x₀) :
    IsConformalMap (fderiv ℝ (inversion x₀) y) := by
  have hu : y - x₀ ≠ 0 := sub_ne_zero.mpr h
  have hpos : (0:ℝ) < ‖y - x₀‖ := norm_pos_iff.mpr hu
  refine (isConformalMap_iff _).2 ⟨((‖y - x₀‖^2)^2)⁻¹, ?_, inner_inversion_fderiv h⟩
  positivity

theorem confFactorSq_inversion (hm : 3 ≤ m) {x₀ y : ES m} (h : y ≠ x₀) :
    confFactorSq hm (inversion x₀) y = ((‖y - x₀‖^2)^2)⁻¹ := by
  rw [confFactorSq, confFactor, ← real_inner_self_eq_norm_sq, inner_inversion_fderiv h,
    stdBasis_inner, ite_eq_left rfl, mul_one]

theorem recipConfFactor_inversion (hm : 3 ≤ m) {x₀ y : ES m} (h : y ≠ x₀) :
    recipConfFactor hm (inversion x₀) y = ‖y - x₀‖^2 := by
  rw [recipConfFactor, confFactorSq_inversion hm h]
  have hpos : (0:ℝ) < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have hX : (0:ℝ) < (‖y - x₀‖^2)^2 := by positivity
  rw [Real.inv_rpow hX.le, ← Real.rpow_neg_one, ← Real.rpow_mul hX.le]
  rw [show (-(1/2 : ℝ)) * (-1 : ℝ) = 1/2 by norm_num]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity : (0:ℝ) ≤ ‖y - x₀‖^2)]

theorem confFactorSq_comp {F G : ES m → ES m} {y : ES m} (hm : 3 ≤ m)
    (hF : DifferentiableAt ℝ F (G y)) (hG : DifferentiableAt ℝ G y)
    (hFc : IsConformalMap (fderiv ℝ F (G y)))
    (hGc : IsConformalMap (fderiv ℝ G y)) :
    confFactorSq hm (F ∘ G) y = confFactorSq hm F (G y) * confFactorSq hm G y := by
  obtain ⟨cF, -, hFuv⟩ := (isConformalMap_iff _).1 hFc
  obtain ⟨cG, -, hGuv⟩ := (isConformalMap_iff _).1 hGc
  have hfc : confFactorSq hm F (G y) = cF := by
    rw [confFactorSq, confFactor, ← real_inner_self_eq_norm_sq, hFuv, stdBasis_inner,
      ite_eq_left rfl, mul_one]
  have hgc : confFactorSq hm G y = cG := by
    rw [confFactorSq, confFactor, ← real_inner_self_eq_norm_sq, hGuv, stdBasis_inner,
      ite_eq_left rfl, mul_one]
  rw [hfc, hgc, confFactorSq, confFactor, (hF.hasFDerivAt.comp y hG.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply, ← real_inner_self_eq_norm_sq, hFuv, hGuv,
    stdBasis_inner, ite_eq_left rfl, mul_one]

theorem recipConfFactor_comp {F G : ES m → ES m} {y : ES m} (hm : 3 ≤ m)
    (hF : DifferentiableAt ℝ F (G y)) (hG : DifferentiableAt ℝ G y)
    (hFc : IsConformalMap (fderiv ℝ F (G y)))
    (hGc : IsConformalMap (fderiv ℝ G y)) :
    recipConfFactor hm (F ∘ G) y = recipConfFactor hm F (G y) * recipConfFactor hm G y := by
  obtain ⟨cF, hcF, hFuv⟩ := (isConformalMap_iff _).1 hFc
  obtain ⟨cG, hcG, hGuv⟩ := (isConformalMap_iff _).1 hGc
  have hposF : 0 < confFactorSq hm F (G y) := by
    rw [confFactorSq, confFactor, ← real_inner_self_eq_norm_sq, hFuv, stdBasis_inner,
      ite_eq_left rfl, mul_one]
    exact hcF
  have hposG : 0 < confFactorSq hm G y := by
    rw [confFactorSq, confFactor, ← real_inner_self_eq_norm_sq, hGuv, stdBasis_inner,
      ite_eq_left rfl, mul_one]
    exact hcG
  change (confFactorSq hm (F ∘ G) y) ^ (-(1/2 : ℝ))
    = (confFactorSq hm F (G y)) ^ (-(1/2 : ℝ)) * (confFactorSq hm G y) ^ (-(1/2 : ℝ))
  rw [confFactorSq_comp hm hF hG hFc hGc, Real.mul_rpow hposF.le hposG.le]

theorem recipConfFactor_pos {F : ES m → ES m} {U : Set (ES m)} (hm : 3 ≤ m)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) {x : ES m} (hx : x ∈ U) :
    0 < recipConfFactor hm F x :=
  Real.rpow_pos_of_pos (confFactorSq_pos hm F hconf hx) _

theorem confFactorSq_comp_inversion {F : ES m → ES m} {x₀ y : ES m} (hm : 3 ≤ m)
    (hy : y ≠ x₀) (hF : DifferentiableAt ℝ F (inversion x₀ y))
    (hFc : IsConformalMap (fderiv ℝ F (inversion x₀ y))) :
    confFactorSq hm (F ∘ inversion x₀) y
      = confFactorSq hm F (inversion x₀ y) * ((‖y - x₀‖^2)^2)⁻¹ := by
  rw [confFactorSq_comp hm hF (hasFDerivAt_inversion hy).differentiableAt hFc
    (isConformalMap_fderiv_inversion hy), confFactorSq_inversion hm hy]

theorem recipConfFactor_comp_inversion {F : ES m → ES m} {x₀ y : ES m} (hm : 3 ≤ m)
    (hy : y ≠ x₀) (hF : DifferentiableAt ℝ F (inversion x₀ y))
    (hFc : IsConformalMap (fderiv ℝ F (inversion x₀ y))) :
    recipConfFactor hm (F ∘ inversion x₀) y
      = recipConfFactor hm F (inversion x₀ y) * ‖y - x₀‖^2 := by
  rw [recipConfFactor_comp hm hF (hasFDerivAt_inversion hy).differentiableAt hFc
    (isConformalMap_fderiv_inversion hy), recipConfFactor_inversion hm hy]

theorem contDiffAt_inversion {x₀ y : ES m} (h : y ≠ x₀) :
    ContDiffAt ℝ 3 (inversion x₀) y := by
  have h2 : ‖y - x₀‖^2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr (sub_ne_zero.mpr h)).ne'
  exact contDiffAt_const.add
    ((((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).inv h2).smul
      (contDiffAt_id.sub contDiffAt_const))

theorem continuousAt_inversion {x₀ y : ES m} (h : y ≠ x₀) :
    ContinuousAt (inversion x₀) y :=
  (contDiffAt_inversion h).continuousAt

theorem isOpen_punctured_preimage_inversion {x₀ : ES m} {s : Set (ES m)} (hs : IsOpen s) :
    IsOpen ({x₀}ᶜ ∩ inversion x₀ ⁻¹' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyx, hy⟩
  exact Filter.inter_mem (isOpen_compl_singleton.mem_nhds hyx)
    ((continuousAt_inversion (Set.mem_compl_singleton_iff.mp hyx)).preimage_mem_nhds
      (hs.mem_nhds hy))

theorem inversion_image_eq_punctured_preimage {x₀ : ES m} {s : Set (ES m)}
    (hs : s ⊆ {x₀}ᶜ) :
    inversion x₀ '' s = {x₀}ᶜ ∩ inversion x₀ ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨z, hzs, rfl⟩
    have hz := Set.mem_compl_singleton_iff.mp (hs hzs)
    refine ⟨inversion_ne_center hz, ?_⟩
    rw [Set.mem_preimage, inversion_involution hz]
    exact hzs
  · rintro ⟨hyx, hy⟩
    exact ⟨inversion x₀ y, hy, inversion_involution (Set.mem_compl_singleton_iff.mp hyx)⟩

theorem isOpen_inversion_image {x₀ : ES m} {s : Set (ES m)}
    (hs : s ⊆ {x₀}ᶜ) (hso : IsOpen s) : IsOpen (inversion x₀ '' s) := by
  rw [inversion_image_eq_punctured_preimage hs]
  exact isOpen_punctured_preimage_inversion hso

theorem exists_contDiff_eq_inversion_on_ball {x₀ q : ES m} {rIn : ℝ}
    (hrIn : 0 < rIn) (hd : rIn < dist q x₀) :
    ∃ Jt : ES m → ES m, ContDiff ℝ 3 Jt
      ∧ (∀ z ∈ Metric.ball q rIn, Jt z = inversion x₀ z) := by
  have hq : 0 < dist q x₀ := hrIn.trans hd
  set rOut := (rIn + dist q x₀) / 2 with hrOut_def
  have hlt : rIn < rOut := by rw [hrOut_def]; linarith
  have hlt2 : rOut < dist q x₀ := by rw [hrOut_def]; linarith
  set ψ : ContDiffBump q := ⟨rIn, rOut, hrIn, hlt⟩ with hψ_def
  refine ⟨fun y => x₀ + (ψ y * (‖y - x₀‖^2)⁻¹) • (y - x₀), ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y = x₀
    · subst y
      have hδ : 0 < dist q x₀ - rOut := by linarith
      have hEv : (fun y => x₀ + (ψ y * (‖y - x₀‖^2)⁻¹) • (y - x₀))
          =ᶠ[𝓝 x₀] fun _ => x₀ := by
        filter_upwards [Metric.ball_mem_nhds x₀ hδ] with z hz
        rw [Metric.mem_ball] at hz
        have hztri := dist_triangle q z x₀
        have hz2 : rOut ≤ dist z q := by rw [dist_comm z q]; linarith
        rw [ψ.zero_of_le_dist hz2]
        simp
      have hbase : ContDiffAt ℝ 3 (fun _ : ES m => x₀) x₀ := contDiffAt_const
      exact hbase.congr_of_eventuallyEq hEv
    · have hψ : ContDiffAt ℝ 3 ψ y := ψ.contDiffAt
      have h2 : ‖y - x₀‖^2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr (sub_ne_zero.mpr hy)).ne'
      exact contDiffAt_const.add
        ((hψ.mul (((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).inv h2)).smul
          (contDiffAt_id.sub contDiffAt_const))
  · intro z hz
    have h1 : ψ z = 1 := ψ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    calc (fun y => x₀ + (ψ y * (‖y - x₀‖^2)⁻¹) • (y - x₀)) z
        = x₀ + (ψ z * (‖z - x₀‖^2)⁻¹) • (z - x₀) := rfl
      _ = x₀ + (‖z - x₀‖^2)⁻¹ • (z - x₀) := by rw [h1, one_mul]
      _ = inversion x₀ z := rfl

theorem ne_pole_of_recipConfFactor_quadratic {F : ES m → ES m} {U : Set (ES m)} (hm : 3 ≤ m)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) {c : ES m} {r : ℝ}
    (hball : Metric.ball c r ⊆ U) {A : ℝ} {x₀ : ES m}
    (hquad : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = (A / 2) * ‖z - x₀‖ ^ 2) :
    ∀ z ∈ Metric.ball c r, z ≠ x₀ := by
  intro z hz hzx
  have h1 := recipConfFactor_pos hm hconf (hball hz)
  rw [hzx] at h1
  rw [hquad x₀ (hzx ▸ hz)] at h1
  simp at h1

theorem affine_eq_of_eq_on_open {L₁ L₂ : ES m →L[ℝ] ES m} {t₁ t₂ : ES m}
    {s : Set (ES m)} (hs : IsOpen s) (hne : s.Nonempty)
    (h : ∀ x ∈ s, L₁ x + t₁ = L₂ x + t₂) : L₁ = L₂ ∧ t₁ = t₂ := by
  obtain ⟨x, hx⟩ := hne
  have hEv : (fun y => L₁ y + t₁) =ᶠ[𝓝 x] fun y => L₂ y + t₂ :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds hx) h
  have hd1 : fderiv ℝ (fun y => L₁ y + t₁) x = L₁ := (L₁.hasFDerivAt.add_const t₁).fderiv
  have hd2 : fderiv ℝ (fun y => L₂ y + t₂) x = L₂ := (L₂.hasFDerivAt.add_const t₂).fderiv
  have hder : L₁ = L₂ := by rw [← hd1, ← hd2]; exact hEv.fderiv_eq
  refine ⟨hder, ?_⟩
  have hxx := h x hx
  rw [hder] at hxx
  exact add_left_cancel hxx

theorem isSimilarity_comp_inversion_local (hm : 3 ≤ m) {F : ES m → ES m}
    (hF : ContDiff ℝ 3 F) {U : Set (ES m)}
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) {c : ES m} {r : ℝ}
    (hball : Metric.ball c r ⊆ U) {A : ℝ} {x₀ : ES m}
    (hquad : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = (A / 2) * ‖z - x₀‖ ^ 2)
    {p : ES m} (hp : p ∈ Metric.ball c r) :
    ∃ V : Set (ES m), IsOpen V ∧ p ∈ V ∧ V ⊆ Metric.ball c r ∧
      ∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m,
        ∀ w ∈ V, F w = L (inversion x₀ w) + t := by
  have hballne : ∀ z ∈ Metric.ball c r, z ≠ x₀ :=
    ne_pole_of_recipConfFactor_quadratic hm hconf hball hquad
  have hpne : p ≠ x₀ := hballne p hp
  set S : Set (ES m) := {x₀}ᶜ ∩ inversion x₀ ⁻¹' Metric.ball c r with hS_def
  have hSopen : IsOpen S := isOpen_punctured_preimage_inversion Metric.isOpen_ball
  have hqmem : inversion x₀ p ∈ S := by
    refine ⟨inversion_ne_center hpne, ?_⟩
    rw [Set.mem_preimage, inversion_involution hpne]
    exact hp
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hSopen (inversion x₀ p) hqmem
  have hqx : 0 < dist (inversion x₀ p) x₀ := dist_pos.mpr (inversion_ne_center hpne)
  set rIn := min (ε / 2) (dist (inversion x₀ p) x₀ / 2) with hrIn_def
  have hrIn : 0 < rIn := by rw [hrIn_def]; exact lt_min (half_pos hε) (half_pos hqx)
  have hrInε : rIn ≤ ε := by
    rw [hrIn_def]
    exact (min_le_left _ _).trans (half_le_self hε.le)
  have hrInd : rIn < dist (inversion x₀ p) x₀ := by
    rw [hrIn_def]
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hqx)
  obtain ⟨Jt, hJt, hagree⟩ := exists_contDiff_eq_inversion_on_ball hrIn hrInd
  have hG : ContDiff ℝ 3 (F ∘ Jt) := hF.comp hJt
  have hB2S : Metric.ball (inversion x₀ p) rIn ⊆ S :=
    fun z hz => hεS (Metric.ball_subset_ball hrInε hz)
  have hEvG : ∀ z ∈ Metric.ball (inversion x₀ p) rIn,
      (F ∘ Jt) =ᶠ[𝓝 z] (F ∘ inversion x₀) := by
    intro z hz
    apply Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
    intro w hw
    change F (Jt w) = F (inversion x₀ w)
    rw [hagree w hw]
  have hconfG : ∀ z ∈ Metric.ball (inversion x₀ p) rIn,
      IsConformalMap (fderiv ℝ (F ∘ Jt) z) := by
    intro z hz
    have hzS := hB2S hz
    have hzne : z ≠ x₀ := Set.mem_compl_singleton_iff.mp hzS.1
    have hzJ : inversion x₀ z ∈ Metric.ball c r := hzS.2
    have hFd : DifferentiableAt ℝ F (inversion x₀ z) := hF.differentiable (by norm_num) _
    have hJd : DifferentiableAt ℝ (inversion x₀) z :=
      (hasFDerivAt_inversion hzne).differentiableAt
    have hfr : fderiv ℝ (F ∘ Jt) z
        = (fderiv ℝ F (inversion x₀ z)).comp (fderiv ℝ (inversion x₀) z) := by
      rw [(hEvG z hz).fderiv_eq]
      exact (hFd.hasFDerivAt.comp z hJd.hasFDerivAt).fderiv
    rw [hfr]
    exact (hconf _ (hball hzJ)).comp (isConformalMap_fderiv_inversion hzne)
  have hρG : ∀ z ∈ Metric.ball (inversion x₀ p) rIn,
      recipConfFactor hm (F ∘ Jt) z = A / 2 := by
    intro z hz
    have hzS := hB2S hz
    have hzne : z ≠ x₀ := Set.mem_compl_singleton_iff.mp hzS.1
    have hzJ : inversion x₀ z ∈ Metric.ball c r := hzS.2
    have hFd : DifferentiableAt ℝ F (inversion x₀ z) := hF.differentiable (by norm_num) _
    have e1 : recipConfFactor hm (F ∘ Jt) z = recipConfFactor hm (F ∘ inversion x₀) z := by
      have hfr : fderiv ℝ (F ∘ Jt) z = fderiv ℝ (F ∘ inversion x₀) z :=
        (hEvG z hz).fderiv_eq
      unfold recipConfFactor confFactorSq confFactor
      rw [hfr]
    rw [e1, recipConfFactor_comp_inversion hm hzne hFd (hconf _ (hball hzJ)),
      hquad _ hzJ, norm_inversion_sub_center hzne, inv_pow, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 (norm_pos_iff.mpr (sub_ne_zero.mpr hzne)).ne'),
      mul_one]
  obtain ⟨L, hL, t, hLt⟩ :=
    isSimilarity_on_ball_of_recipConfFactor_const hm (F ∘ Jt) hG hconfG
      Metric.isOpen_ball hrIn Set.Subset.rfl hρG
  refine ⟨inversion x₀ '' Metric.ball (inversion x₀ p) rIn,
    isOpen_inversion_image (fun z hz => (hB2S hz).1) Metric.isOpen_ball,
    ⟨inversion x₀ p, Metric.mem_ball_self hrIn, inversion_involution hpne⟩, ?_, L, hL, t, ?_⟩
  · rintro w ⟨z, hzB2, rfl⟩
    exact (hB2S hzB2).2
  · intro w hw
    obtain ⟨z, hzB2, rfl⟩ := hw
    have hzne : z ≠ x₀ := Set.mem_compl_singleton_iff.mp (hB2S hzB2).1
    have h1 : (F ∘ Jt) z = L z + t := hLt z hzB2
    have h2 : (F ∘ Jt) z = F (inversion x₀ z) := by
      change F (Jt z) = F (inversion x₀ z)
      rw [hagree z hzB2]
    rw [inversion_involution hzne]
    exact h2 ▸ h1

theorem isSimilarity_comp_inversion_on_ball (hm : 3 ≤ m) {F : ES m → ES m}
    (hF : ContDiff ℝ 3 F) {U : Set (ES m)}
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) {c : ES m} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball c r ⊆ U) {A : ℝ} {x₀ : ES m}
    (hquad : ∀ z ∈ Metric.ball c r, recipConfFactor hm F z = (A / 2) * ‖z - x₀‖ ^ 2) :
    ∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m,
      ∀ w ∈ Metric.ball c r, F w = L (inversion x₀ w) + t := by
  have hballne : ∀ z ∈ Metric.ball c r, z ≠ x₀ :=
    ne_pole_of_recipConfFactor_quadratic hm hconf hball hquad
  obtain ⟨V₀, hV₀open, hcV₀, hV₀sub, L₀, hL₀, t₀, hF₀⟩ :=
    isSimilarity_comp_inversion_local hm hF hconf hball hquad (Metric.mem_ball_self hr)
  set T : Set (ES m) := {w | w ∈ Metric.ball c r ∧ ∃ V : Set (ES m),
    IsOpen V ∧ w ∈ V ∧ V ⊆ Metric.ball c r ∧
      ∀ u ∈ V, F u = L₀ (inversion x₀ u) + t₀} with hT_def
  have hTopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    obtain ⟨-, V, hVopen, hwV, hVsub, hFV⟩ := hw
    exact Filter.mem_of_superset (hVopen.mem_nhds hwV)
      (fun u hu => ⟨hVsub hu, V, hVopen, hu, hVsub, hFV⟩)
  have hcT : c ∈ T := ⟨Metric.mem_ball_self hr, V₀, hV₀open, hcV₀, hV₀sub, hF₀⟩
  have hTcomp : IsOpen (Metric.ball c r \ T) := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    obtain ⟨hwb, hwT⟩ := hw
    obtain ⟨Vw, hVwopen, hwVw, hVwsub, Lw, hLw, tw, hFw⟩ :=
      isSimilarity_comp_inversion_local hm hF hconf hball hquad hwb
    apply Filter.mem_of_superset (hVwopen.mem_nhds hwVw)
    intro u hu
    refine ⟨hVwsub hu, ?_⟩
    intro huT
    obtain ⟨-, V', hV'open, huV', -, hF'⟩ := huT
    have hsopen : IsOpen (Vw ∩ V') := hVwopen.inter hV'open
    have hsne : (Vw ∩ V').Nonempty := ⟨u, hu, huV'⟩
    have hssub : Vw ∩ V' ⊆ {x₀}ᶜ :=
      fun z hz => Set.mem_compl_singleton_iff.mpr (hballne z (hVwsub hz.1))
    have hEq : ∀ y ∈ inversion x₀ '' (Vw ∩ V'), Lw y + tw = L₀ y + t₀ := by
      rintro y ⟨z, hzs, rfl⟩
      rw [← hFw z hzs.1, ← hF' z hzs.2]
    obtain ⟨hLeq, hteq⟩ := affine_eq_of_eq_on_open
      (isOpen_inversion_image hssub hsopen) (hsne.image _) hEq
    apply hwT
    refine ⟨hwb, Vw, hVwopen, hwVw, hVwsub, ?_⟩
    intro u' hu'
    rw [hFw u' hu', hLeq, hteq]
  have hcover : Metric.ball c r ⊆ T ∪ (Metric.ball c r \ T) := by
    intro z hz
    by_cases hzT : z ∈ T
    · exact Set.mem_union_left _ hzT
    · exact Set.mem_union_right _ ⟨hz, hzT⟩
  have hdisj : Disjoint T (Metric.ball c r \ T) :=
    Set.disjoint_left.mpr fun z hzT hz => hz.2 hzT
  obtain hsub | hsub := (convex_ball c r).isPreconnected.subset_or_subset
    hTopen hTcomp hdisj hcover
  · refine ⟨L₀, hL₀, t₀, fun w hw => ?_⟩
    obtain ⟨-, V, -, hwV, -, hFV⟩ := hsub hw
    exact hFV w hwV
  · exact absurd hcT (hsub (Metric.mem_ball_self hr)).2

theorem mobius_classification_on_ball (hm : 3 ≤ m) {F : ES m → ES m}
    (hF : ContDiff ℝ 3 F) {U : Set (ES m)} (hU : IsOpen U)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x)) {c : ES m} (hc : c ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ U ∧
      ((∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m,
          ∀ z ∈ Metric.ball c r, F z = L z + t)
        ∨ (∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m, ∃ x₀ : ES m,
          ∀ z ∈ Metric.ball c r, F z = L (inversion x₀ z) + t)) := by
  obtain ⟨r, hr, A, a₀, Bv, hball, hquad, hdisc, -, -⟩ :=
    recipConfFactor_quadratic_full hm F hF hconf hU hc
  refine ⟨r, hr, hball, ?_⟩
  obtain ⟨-, hρconst⟩ | ⟨-, hperf⟩ :=
    recipConfFactor_cases hm F hquad hdisc
  · exact Or.inl
      (isSimilarity_on_ball_of_recipConfFactor_const hm F hF hconf hU hr hball hρconst)
  · right
    have hquad' : ∀ z ∈ Metric.ball c r,
        recipConfFactor hm F z = (A / 2) * ‖z - (-(1/A) • Bv)‖^2 := by
      intro z hz
      rw [hperf z hz, neg_smul, sub_neg_eq_add]
    obtain ⟨L, hL, t, ht⟩ :=
      isSimilarity_comp_inversion_on_ball hm hF hconf hr hball hquad'
    exact ⟨L, hL, t, -(1/A) • Bv, ht⟩

theorem ddρ_const_on_preconnected {F : ES m → ES m} (hm : 3 ≤ m)
    (hF : ContDiff ℝ 3 F) {U : Set (ES m)} (hU : IsOpen U)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hconn : IsPreconnected U) {c₀ : ES m} (hc₀ : c₀ ∈ U) :
    ∀ z ∈ U, ∀ j, ddρ hm F j z = ddρ hm F ⟨0, by omega⟩ c₀ := by
  set A₀ : ℝ := ddρ hm F ⟨0, by omega⟩ c₀ with hA₀_def
  set T : Set (ES m) := {z ∈ U | ∀ j, ddρ hm F j z = A₀} with hT_def
  have hTopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨hzU, hzA⟩ := hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hzU
    obtain ⟨A, a₀, Bv, hquad, hd, hdd⟩ :=
      recipConfFactor_quadratic hm F hF hconf hU hr hball
    have hAA : A = A₀ := by
      rw [← hdd z (Metric.mem_ball_self hr) ⟨0, by omega⟩]
      exact hzA ⟨0, by omega⟩
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
      (fun w hw => ⟨hball hw, fun j => by rw [hdd w hw j, hAA]⟩)
  have hTcomp : IsOpen (U \ T) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨hzU, hzA⟩ := hz
    have hzA' : ∃ j, ddρ hm F j z ≠ A₀ := by
      by_contra h
      push Not at h
      exact hzA ⟨hzU, h⟩
    obtain ⟨j₀, hj₀⟩ := hzA'
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hzU
    obtain ⟨A, a₀, Bv, hquad, hd, hdd⟩ :=
      recipConfFactor_quadratic hm F hF hconf hU hr hball
    have hAA : A ≠ A₀ := by
      rw [← hdd z (Metric.mem_ball_self hr) j₀]
      exact hj₀
    apply Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
    intro w hw
    refine ⟨hball hw, ?_⟩
    intro hwT
    have h1 := hdd w hw j₀
    rw [hwT.2 j₀] at h1
    exact hAA h1.symm
  have hcT : c₀ ∈ T := ⟨hc₀, fun j => by
    rw [hA₀_def]; exact recipConfFactor_diag hm F hF hconf hU hc₀ j ⟨0, by omega⟩⟩
  have hcover : U ⊆ T ∪ (U \ T) := fun z hz => by
    by_cases hzT : z ∈ T
    · exact Set.mem_union_left _ hzT
    · exact Set.mem_union_right _ ⟨hz, hzT⟩
  have hdisj : Disjoint T (U \ T) := Set.disjoint_left.mpr fun z hzT hz => hz.2 hzT
  obtain hsub | hsub := hconn.subset_or_subset hTopen hTcomp hdisj hcover
  · exact fun z hz j => (hsub hz).2 j
  · exact absurd hcT (hsub hc₀).2

theorem mobius_classification_on_domain {F : ES m → ES m} (hm : 3 ≤ m)
    (hF : ContDiff ℝ 3 F) {U : Set (ES m)} (hU : IsOpen U)
    (hconf : ∀ x ∈ U, IsConformalMap (fderiv ℝ F x))
    (hconn : IsPreconnected U) {c₀ : ES m} (hc₀ : c₀ ∈ U) :
    (∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m, ∀ z ∈ U, F z = L z + t)
    ∨ (∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m, ∃ x₀ : ES m,
        ∀ z ∈ U, F z = L (inversion x₀ z) + t) := by
  have hA := ddρ_const_on_preconnected hm hF hU hconf hconn hc₀
  by_cases hA₀ : ddρ hm F ⟨0, by omega⟩ c₀ = 0
  · have hloc : ∀ w ∈ U, ∃ V : Set (ES m), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
        ∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m,
          ∀ u ∈ V, F u = L u + t := by
      intro w hw
      obtain ⟨r, hr, A, a₀, Bv, hball, hquad, hdisc, hd, hdd⟩ :=
        recipConfFactor_quadratic_full hm F hF hconf hU hw
      have hAw : A = 0 := by
        rw [← hdd w (Metric.mem_ball_self hr) ⟨0, by omega⟩, hA w hw ⟨0, by omega⟩, hA₀]
      obtain ⟨hA0, hρconst⟩ | ⟨hAne, -⟩ :=
        recipConfFactor_cases hm F hquad hdisc
      · obtain ⟨L, hL, t, ht⟩ :=
          isSimilarity_on_ball_of_recipConfFactor_const hm F hF hconf hU hr hball hρconst
        exact ⟨Metric.ball w r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball,
          L, hL, t, ht⟩
      · exact absurd hAw hAne
    obtain ⟨V₀, hV₀open, hc₀V₀, hV₀sub, L₀, hL₀, t₀, hF₀⟩ := hloc c₀ hc₀
    set T : Set (ES m) := {w ∈ U | ∃ V : Set (ES m), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∀ u ∈ V, F u = L₀ u + t₀} with hT_def
    have hTopen : IsOpen T := by
      rw [isOpen_iff_mem_nhds]
      intro w hw
      obtain ⟨-, V, hVopen, hwV, hVsub, hFV⟩ := hw
      exact Filter.mem_of_superset (hVopen.mem_nhds hwV)
        (fun u hu => ⟨hVsub hu, V, hVopen, hu, hVsub, hFV⟩)
    have hcT : c₀ ∈ T := ⟨hc₀, V₀, hV₀open, hc₀V₀, hV₀sub, hF₀⟩
    have hTcomp : IsOpen (U \ T) := by
      rw [isOpen_iff_mem_nhds]
      intro w hw
      obtain ⟨hwU, hwT⟩ := hw
      obtain ⟨Vw, hVwopen, hwVw, hVwsub, Lw, hLw, tw, hFw⟩ := hloc w hwU
      apply Filter.mem_of_superset (hVwopen.mem_nhds hwVw)
      intro u hu
      refine ⟨hVwsub hu, ?_⟩
      intro huT
      obtain ⟨-, V', hV'open, huV', -, hF'⟩ := huT
      obtain ⟨hLeq, hteq⟩ := affine_eq_of_eq_on_open (s := Vw ∩ V') (L₁ := Lw) (L₂ := L₀)
        (t₁ := tw) (t₂ := t₀) (hVwopen.inter hV'open)
        ⟨u, hu, huV'⟩ (fun y hy => by rw [← hFw y hy.1, ← hF' y hy.2])
      apply hwT
      exact ⟨hwU, Vw, hVwopen, hwVw, hVwsub,
        fun u' hu' => by rw [hFw u' hu', hLeq, hteq]⟩
    have hcover : U ⊆ T ∪ (U \ T) := fun z hz => by
      by_cases hzT : z ∈ T
      · exact Set.mem_union_left _ hzT
      · exact Set.mem_union_right _ ⟨hz, hzT⟩
    have hdisj : Disjoint T (U \ T) := Set.disjoint_left.mpr fun z hzT hz => hz.2 hzT
    obtain hsub | hsub := hconn.subset_or_subset hTopen hTcomp hdisj hcover
    · left
      refine ⟨L₀, hL₀, t₀, fun z hz => ?_⟩
      obtain ⟨-, V, -, hwV, -, hFV⟩ := hsub hz
      exact hFV z hwV
    · exact absurd hcT (hsub hc₀).2
  · obtain ⟨r₀, hr₀, A, a₀, Bv, hball₀, hquad₀, hdisc₀, hd₀, hdd₀⟩ :=
      recipConfFactor_quadratic_full hm F hF hconf hU hc₀
    have hAA : A = ddρ hm F ⟨0, by omega⟩ c₀ := by
      rw [← hdd₀ c₀ (Metric.mem_ball_self hr₀) ⟨0, by omega⟩]
    have hAne : A ≠ 0 := by rw [hAA]; exact hA₀
    set G : ES m → ES m := fun z => ∑ j, (dρ hm F j z - A * (z j)) • stdBasis m j
      with hG_def
    have hGloc : ∀ (w : ES m) (r : ℝ) (Bv_w : ES m),
        (∀ z ∈ Metric.ball w r, ∀ j, dρ hm F j z = A * (z j) + ⟪Bv_w, stdBasis m j⟫_ℝ) →
        ∀ z ∈ Metric.ball w r, G z = Bv_w := by
      intro w r Bv_w hd_w z hz
      change (∑ j, (dρ hm F j z - A * (z j)) • stdBasis m j) = Bv_w
      rw [← sum_coord_stdBasis Bv_w]
      apply Finset.sum_congr rfl
      intro j _
      rw [hd_w z hz j, add_sub_cancel_left, inner_stdBasis_right]
    have haux : ∀ w ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball w r ⊆ U ∧
        ∃ Bv_w : ES m, ∀ z ∈ Metric.ball w r, G z = Bv_w := by
      intro w hw
      obtain ⟨r, hr, A', a₀', Bv', hball, hquad, hdisc, hd, hdd⟩ :=
        recipConfFactor_quadratic_full hm F hF hconf hU hw
      have hA' : A' = A := by
        rw [← hdd w (Metric.mem_ball_self hr) ⟨0, by omega⟩, hA w hw ⟨0, by omega⟩, hAA]
      exact ⟨r, hr, hball, Bv', hGloc w r Bv' (hA' ▸ hd)⟩
    have hGconst : ∀ z ∈ U, G z = Bv := by
      set TG : Set (ES m) := {z ∈ U | G z = Bv} with hTG_def
      have hTGopen : IsOpen TG := by
        rw [isOpen_iff_mem_nhds]
        intro z hz
        obtain ⟨hzU, hzG⟩ := hz
        obtain ⟨r, hr, hball, Bv', hGB⟩ := haux z hzU
        have hB' : Bv' = Bv := by rw [← hGB z (Metric.mem_ball_self hr)]; exact hzG
        exact Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
          (fun u hu => ⟨hball hu, by rw [hGB u hu, hB']⟩)
      have hTGcomp : IsOpen (U \ TG) := by
        rw [isOpen_iff_mem_nhds]
        intro z hz
        obtain ⟨hzU, hzG⟩ := hz
        have hzG' : G z ≠ Bv := fun h => hzG ⟨hzU, h⟩
        obtain ⟨r, hr, hball, Bv', hGB⟩ := haux z hzU
        have hB' : Bv' ≠ Bv := by rw [← hGB z (Metric.mem_ball_self hr)]; exact hzG'
        apply Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
        intro u hu
        exact ⟨hball hu, fun h => hB' ((hGB u hu).symm.trans h.2)⟩
      have hcTG : c₀ ∈ TG :=
        ⟨hc₀, hGloc c₀ r₀ Bv hd₀ c₀ (Metric.mem_ball_self hr₀)⟩
      have hcover : U ⊆ TG ∪ (U \ TG) := fun z hz => by
        by_cases hzT : z ∈ TG
        · exact Set.mem_union_left _ hzT
        · exact Set.mem_union_right _ ⟨hz, hzT⟩
      have hdisj : Disjoint TG (U \ TG) := Set.disjoint_left.mpr fun z hzT hz => hz.2 hzT
      obtain hsub | hsub := hconn.subset_or_subset hTGopen hTGcomp hdisj hcover
      · exact fun z hz => (hsub hz).2
      · exact absurd hcTG (hsub hc₀).2
    set x₀ : ES m := -(1/A) • Bv with hx₀_def
    have hρx₀ : ∀ z ∈ U, recipConfFactor hm F z = (A / 2) * ‖z - x₀‖^2 := by
      intro z hz
      obtain ⟨r, hr, A', a₀', Bv', hball, hquad, hdisc, hd, hdd⟩ :=
        recipConfFactor_quadratic_full hm F hF hconf hU hz
      have hA' : A' = A := by
        rw [← hdd z (Metric.mem_ball_self hr) ⟨0, by omega⟩, hA z hz ⟨0, by omega⟩, hAA]
      have hB' : Bv' = Bv := by
        have hGB : ∀ u ∈ Metric.ball z r, G u = Bv' := hGloc z r Bv' (hA' ▸ hd)
        rw [← hGB z (Metric.mem_ball_self hr)]
        exact hGconst z hz
      obtain ⟨hA0', -⟩ | ⟨-, hperf⟩ := recipConfFactor_cases hm F hquad hdisc
      · exact absurd (hA'.symm.trans hA0') hAne
      · have h1 : recipConfFactor hm F z = (A' / 2) * ‖z - (-(1/A') • Bv')‖^2 := by
          rw [hperf z (Metric.mem_ball_self hr), neg_smul, sub_neg_eq_add]
        rwa [hA', hB'] at h1
    have hUne : ∀ z ∈ U, z ≠ x₀ := by
      intro z hz hzx
      have h1 := recipConfFactor_pos hm hconf hz
      rw [hρx₀ z hz, hzx] at h1
      simp at h1
    have hlocV : ∀ w ∈ U, ∃ V : Set (ES m), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
        ∃ L : ES m →L[ℝ] ES m, IsConformalMap L ∧ ∃ t : ES m,
          ∀ u ∈ V, F u = L (inversion x₀ u) + t := by
      intro w hw
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU w hw
      have hq : ∀ z ∈ Metric.ball w r, recipConfFactor hm F z = (A / 2) * ‖z - x₀‖^2 :=
        fun z hz => hρx₀ z (hball hz)
      obtain ⟨V, hVopen, hwV, hVsub, L, hL, t, ht⟩ :=
        isSimilarity_comp_inversion_local hm hF hconf hball hq (Metric.mem_ball_self hr)
      exact ⟨V, hVopen, hwV, hVsub.trans hball, L, hL, t, ht⟩
    obtain ⟨V₀, hV₀open, hc₀V₀, hV₀sub, L₀, hL₀, t₀, hF₀⟩ := hlocV c₀ hc₀
    set T : Set (ES m) := {w ∈ U | ∃ V : Set (ES m), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∀ u ∈ V, F u = L₀ (inversion x₀ u) + t₀} with hT_def
    have hTopen : IsOpen T := by
      rw [isOpen_iff_mem_nhds]
      intro w hw
      obtain ⟨-, V, hVopen, hwV, hVsub, hFV⟩ := hw
      exact Filter.mem_of_superset (hVopen.mem_nhds hwV)
        (fun u hu => ⟨hVsub hu, V, hVopen, hu, hVsub, hFV⟩)
    have hcT : c₀ ∈ T := ⟨hc₀, V₀, hV₀open, hc₀V₀, hV₀sub, hF₀⟩
    have hTcomp : IsOpen (U \ T) := by
      rw [isOpen_iff_mem_nhds]
      intro w hw
      obtain ⟨hwU, hwT⟩ := hw
      obtain ⟨Vw, hVwopen, hwVw, hVwsub, Lw, hLw, tw, hFw⟩ := hlocV w hwU
      apply Filter.mem_of_superset (hVwopen.mem_nhds hwVw)
      intro u hu
      refine ⟨hVwsub hu, ?_⟩
      intro huT
      obtain ⟨-, V', hV'open, huV', -, hF'⟩ := huT
      have hsopen : IsOpen (Vw ∩ V') := hVwopen.inter hV'open
      have hsne : (Vw ∩ V').Nonempty := ⟨u, hu, huV'⟩
      have hssub : Vw ∩ V' ⊆ {x₀}ᶜ :=
        fun z hz => Set.mem_compl_singleton_iff.mpr (hUne z (hVwsub hz.1))
      have hEq : ∀ y ∈ inversion x₀ '' (Vw ∩ V'), Lw y + tw = L₀ y + t₀ := by
        rintro y ⟨z, hzs, rfl⟩
        rw [← hFw z hzs.1, ← hF' z hzs.2]
      obtain ⟨hLeq, hteq⟩ := affine_eq_of_eq_on_open
        (isOpen_inversion_image hssub hsopen) (hsne.image _) hEq
      apply hwT
      exact ⟨hwU, Vw, hVwopen, hwVw, hVwsub,
        fun u' hu' => by rw [hFw u' hu', hLeq, hteq]⟩
    have hcover : U ⊆ T ∪ (U \ T) := fun z hz => by
      by_cases hzT : z ∈ T
      · exact Set.mem_union_left _ hzT
      · exact Set.mem_union_right _ ⟨hz, hzT⟩
    have hdisj : Disjoint T (U \ T) := Set.disjoint_left.mpr fun z hzT hz => hz.2 hzT
    obtain hsub | hsub := hconn.subset_or_subset hTopen hTcomp hdisj hcover
    · right
      refine ⟨L₀, hL₀, t₀, x₀, fun z hz => ?_⟩
      obtain ⟨-, V, -, hwV, -, hFV⟩ := hsub hz
      exact hFV z hwV
    · exact absurd hcT (hsub hc₀).2

end

end DifferentialGeometry.LiouvilleMobius
