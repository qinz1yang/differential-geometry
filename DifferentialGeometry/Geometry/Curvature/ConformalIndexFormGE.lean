import DifferentialGeometry.Geometry.Curvature.IndexFormPointwiseGE
import DifferentialGeometry.Geometry.Curvature.WeightedLengthVariationGE
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# 共形度量 `ĝ = ρ²|dz|²` 下极小曲线的第二变分：指标形式非负（S-W-GEO G2）

`ρ : ℂ → ℝ` 为 `C²` 且处处为正，`c : ℝ → ℂ` 为 `C²` 正则曲线（`c′ ≠ 0`），在 `C¹` 曲线类里
（固定端点）使 `ℓ(c) = ∫₀ᴸ ρ(c)‖c′‖` 极小。对每个 `C¹` 的 `φ`（`φ(0) = φ(L) = 0`）：

`0 ≤ ∫₀ᴸ ( φ′²/ê − K̂ ê φ² ) ds`，`ê = ρ(c)‖c′‖`，`K̂ = −ρ⁻² Δ(log ρ)`。

证明（见 sheet §4）：欧氏法向位移 `f = φ/ρ(c)`，变分场 `X = f ν`（二阶变分 `d2 ≥ 0`，
`WeightedLengthVariationGE`），`Yν`，`Y = f² ρ_ν/ρ`（一阶变分 `d1 = 0`），`Z = ρ_T f²`（`∫ Z′ = 0`）；
逐点恒等式 `指标形式被积函数 = d2 + Z′ − d1`（`IndexFormPointwiseGE`）。
**没有用到测地线方程 / 正则性定理**。
-/

set_option autoImplicit false
noncomputable section

open Set intervalIntegral
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

/-- `t ↦ ‖a t‖` 的导数 `⟪a, a′⟫/‖a‖`（`a s ≠ 0`）。 -/
theorem hasDerivAt_norm_curve_GE {a : ℝ → ℂ} {b : ℂ} {s : ℝ} (ha : HasDerivAt a b s)
    (h : a s ≠ 0) : HasDerivAt (fun t => ‖a t‖) (inner ℝ (a s) b / ‖a s‖) s := by
  have h1 := ha.norm_sq
  have hn : ‖a s‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have h2 := h1.sqrt hn
  have h3 : (fun t => √(‖a t‖ ^ 2)) = fun t => ‖a t‖ := by
    funext t
    exact Real.sqrt_sq (norm_nonneg _)
  rw [h3] at h2
  refine h2.congr_deriv ?_
  rw [Real.sqrt_sq (norm_nonneg _)]
  have : ‖a s‖ ≠ 0 := norm_ne_zero_iff.2 h
  field_simp

/-- 单位法向 `ν = nuVec (c′)` 的导数。 -/
theorem hasDerivAt_nuVec_GE {a : ℝ → ℂ} {b : ℂ} {s : ℝ} (ha : HasDerivAt a b s)
    (h : a s ≠ 0) : HasDerivAt (fun t => nuVec (a t)) (nuDeriv (a s) b) s := by
  have hn := hasDerivAt_norm_curve_GE ha h
  have hne : ‖a s‖ ≠ 0 := norm_ne_zero_iff.2 h
  exact (hn.inv hne).smul (ha.const_mul Complex.I)

/-- 欧氏法向位移 `f = φ/ρ(c)`（`φ` 是 `ĝ`-法向位移）。 -/
def fTil (ρ : ℂ → ℝ) (c : ℝ → ℂ) (φ : ℝ → ℝ) (s : ℝ) : ℝ := φ s / ρ (c s)

/-- 一阶变分的系数 `Y = f² Dρ(c)(ν)/ρ(c)`。 -/
def yCoef (ρ : ℂ → ℝ) (c : ℝ → ℂ) (φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  fTil ρ c φ s ^ 2 * (fderiv ℝ ρ (c s) (nuVec (deriv c s)) / ρ (c s))

/-- `Z = Dρ(c)(c′) f²/‖c′‖`（`= ρ_T f²`）。 -/
def potZ (ρ : ℂ → ℝ) (c : ℝ → ℂ) (φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  fderiv ℝ ρ (c s) (deriv c s) * fTil ρ c φ s ^ 2 / ‖deriv c s‖

theorem contDiff_deriv_one_GE {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) : ContDiff ℝ 1 (deriv c) := by
  have h : ContDiff ℝ (1 + 1) c := by simpa [one_add_one_eq_two] using hc
  exact (contDiff_succ_iff_deriv.1 h).2.2

theorem contDiff_of_hasDerivAt_GE {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s)
    (hφ' : Continuous φ') : ContDiff ℝ 1 φ := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hφ s).differentiableAt, ?_⟩
  have : deriv φ = φ' := funext fun s => (hφ s).deriv
  rw [this]
  exact hφ'

/-- 光滑性：`f`、`Y`、两个变分场、`Z` 都是 `C¹`。 -/
theorem index_smooth_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (hφ' : Continuous φ') :
    ContDiff ℝ 1 (fTil ρ c φ) ∧ ContDiff ℝ 1 (yCoef ρ c φ) ∧
    ContDiff ℝ 1 (fun s => fTil ρ c φ s • nuVec (deriv c s)) ∧
    ContDiff ℝ 1 (fun s => yCoef ρ c φ s • nuVec (deriv c s)) ∧ ContDiff ℝ 1 (potZ ρ c φ) := by
  have hc1 : ContDiff ℝ 1 c := hc.of_le (by norm_num)
  have hdc := contDiff_deriv_one_GE hc
  have hφ1 := contDiff_of_hasDerivAt_GE hφ hφ'
  have hR : ContDiff ℝ 1 (fun s => ρ (c s)) := (hρ.comp hc).of_le (by norm_num)
  have hf : ContDiff ℝ 1 (fTil ρ c φ) := hφ1.div hR (fun s => (hρpos _).ne')
  have hn : ContDiff ℝ 1 (fun s => ‖deriv c s‖) := hdc.norm ℝ hreg
  have hν : ContDiff ℝ 1 (fun s => nuVec (deriv c s)) :=
    (hn.inv (fun s => norm_ne_zero_iff.2 (hreg s))).smul (contDiff_const.mul hdc)
  have hg : ContDiff ℝ 1 (fun s => fderiv ℝ ρ (c s)) :=
    (hρ.fderiv_right (m := 1) (by norm_num)).comp hc1
  have hY : ContDiff ℝ 1 (yCoef ρ c φ) :=
    (hf.pow 2).mul ((hg.clm_apply hν).div hR (fun s => (hρpos _).ne'))
  refine ⟨hf, hY, hf.smul hν, hY.smul hν, ?_⟩
  exact ((hg.clm_apply hdc).mul (hf.pow 2)).div hn (fun s => norm_ne_zero_iff.2 (hreg s))

/-- 变分场 `X = f ν`。 -/
def varX (ρ : ℂ → ℝ) (c : ℝ → ℂ) (φ : ℝ → ℝ) (s : ℝ) : ℂ :=
  fTil ρ c φ s • nuVec (deriv c s)

/-- 变分场 `Y ν`。 -/
def varY (ρ : ℂ → ℝ) (c : ℝ → ℂ) (φ : ℝ → ℝ) (s : ℝ) : ℂ :=
  yCoef ρ c φ s • nuVec (deriv c s)

/-- `f` 的导数 `f₁ = (φ′ − Dρ(c)(c′) f)/ρ(c)`。 -/
def fDer (ρ : ℂ → ℝ) (c : ℝ → ℂ) (φ φ' : ℝ → ℝ) (s : ℝ) : ℝ :=
  (φ' s - fderiv ℝ ρ (c s) (deriv c s) * fTil ρ c φ s) / ρ (c s)

theorem hasDerivAt_rho_curve_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) {c : ℝ → ℂ}
    (hc : ContDiff ℝ 2 c) (s : ℝ) :
    HasDerivAt (fun t => ρ (c t)) (fderiv ℝ ρ (c s) (deriv c s)) s :=
  ((hρ.differentiable (by norm_num)) (c s)).hasFDerivAt.comp_hasDerivAt s
    (((hc.differentiable (by norm_num)) s).hasDerivAt)

theorem hasDerivAt_fTil_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (s : ℝ) :
    HasDerivAt (fTil ρ c φ) (fDer ρ c φ φ' s) s := by
  have hR := hasDerivAt_rho_curve_GE hρ hc s
  have h := (hφ s).div hR (hρpos _).ne'
  have hne : ρ (c s) ≠ 0 := (hρpos _).ne'
  refine h.congr_deriv ?_
  simp only [fDer, fTil]
  field_simp

theorem hasDerivAt_varX_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (s : ℝ) :
    HasDerivAt (varX ρ c φ)
      (fDer ρ c φ φ' s • nuVec (deriv c s) +
        fTil ρ c φ s • nuDeriv (deriv c s) (deriv (deriv c) s)) s := by
  have hdc := contDiff_deriv_one_GE hc
  have hν := hasDerivAt_nuVec_GE (a := deriv c) ((hdc.differentiable (by norm_num)) s).hasDerivAt
    (hreg s)
  exact ((hasDerivAt_fTil_GE hρ hρpos hc hφ s).smul hν).congr_deriv (add_comm _ _)

theorem hasDerivAt_varY_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (hφ' : Continuous φ') (s : ℝ) :
    HasDerivAt (varY ρ c φ)
      (deriv (yCoef ρ c φ) s • nuVec (deriv c s) +
        yCoef ρ c φ s • nuDeriv (deriv c s) (deriv (deriv c) s)) s := by
  have hdc := contDiff_deriv_one_GE hc
  have hν := hasDerivAt_nuVec_GE (a := deriv c) ((hdc.differentiable (by norm_num)) s).hasDerivAt
    (hreg s)
  have hY := (index_smooth_GE hρ hρpos hc hreg hφ hφ').2.1
  exact ((((hY.differentiable (by norm_num)) s).hasDerivAt).smul hν).congr_deriv (add_comm _ _)

theorem hasDerivAt_potZ_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (s : ℝ) :
    HasDerivAt (potZ ρ c φ)
      ((fderiv ℝ (fderiv ℝ ρ) (c s) (deriv c s) (deriv c s) +
          fderiv ℝ ρ (c s) (deriv (deriv c) s)) * fTil ρ c φ s ^ 2 / ‖deriv c s‖ +
        fderiv ℝ ρ (c s) (deriv c s) * (2 * fTil ρ c φ s * fDer ρ c φ φ' s) / ‖deriv c s‖ -
        fderiv ℝ ρ (c s) (deriv c s) * fTil ρ c φ s ^ 2 *
          (inner ℝ (deriv c s) (deriv (deriv c) s) / ‖deriv c s‖) / ‖deriv c s‖ ^ 2) s := by
  have hdc := contDiff_deriv_one_GE hc
  have hρ1 : ContDiff ℝ 1 (fderiv ℝ ρ) := hρ.fderiv_right (m := 1) (by norm_num)
  have ha : HasDerivAt (deriv c) (deriv (deriv c) s) s :=
    ((hdc.differentiable (by norm_num)) s).hasDerivAt
  have hg : HasDerivAt (fun t => fderiv ℝ ρ (c t))
      (fderiv ℝ (fderiv ℝ ρ) (c s) (deriv c s)) s :=
    ((hρ1.differentiable (by norm_num)) (c s)).hasFDerivAt.comp_hasDerivAt s
      (((hc.differentiable (by norm_num)) s).hasDerivAt)
  have hG := hg.clm_apply ha
  have hf2 := (hasDerivAt_fTil_GE hρ hρpos hc hφ s).pow 2
  have hn := hasDerivAt_norm_curve_GE ha (hreg s)
  have hne : ‖deriv c s‖ ≠ 0 := norm_ne_zero_iff.2 (hreg s)
  refine ((hG.mul hf2).div hn hne).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, fTil, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hR0 : ρ (c s) ≠ 0 := (hρpos _).ne'
  field_simp

theorem laplacian_second_GE (ρ : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian ρ z =
      fderiv ℝ (fderiv ℝ ρ) z 1 1 + fderiv ℝ (fderiv ℝ ρ) z Complex.I Complex.I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply]

theorem laplacian_log_second_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    (z : ℂ) :
    Laplacian.laplacian (fun p => Real.log (ρ p)) z =
      (fderiv ℝ (fderiv ℝ ρ) z 1 1 + fderiv ℝ (fderiv ℝ ρ) z Complex.I Complex.I) / ρ z -
        (fderiv ℝ ρ z 1 ^ 2 + fderiv ℝ ρ z Complex.I ^ 2) / ρ z ^ 2 := by
  rw [laplacian_log hρ.contDiffAt (hρpos z).ne', laplacian_second_GE]

/-- 逐点：指标形式被积函数 `= d2(X) + Z′ − d1(Yν)`。 -/
theorem index_integrand_eq_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (hφ' : Continuous φ') (s : ℝ) :
    φ' s ^ 2 / (ρ (c s) * ‖deriv c s‖) -
      (-(ρ (c s))⁻¹ ^ 2 * Laplacian.laplacian (fun p => Real.log (ρ p)) (c s)) *
        (ρ (c s) * ‖deriv c s‖) * φ s ^ 2 =
    (fderiv ℝ (fderiv ℝ ρ) (c s) (varX ρ c φ s) (varX ρ c φ s) * ‖deriv c s‖ +
      2 * fderiv ℝ ρ (c s) (varX ρ c φ s) *
        (inner ℝ (deriv c s) (deriv (varX ρ c φ) s) / ‖deriv c s‖) +
      ρ (c s) * ((‖deriv (varX ρ c φ) s‖ ^ 2 -
        (inner ℝ (deriv c s) (deriv (varX ρ c φ) s) / ‖deriv c s‖) ^ 2) / ‖deriv c s‖)) +
    deriv (potZ ρ c φ) s -
    (fderiv ℝ ρ (c s) (varY ρ c φ s) * ‖deriv c s‖ +
      ρ (c s) * (inner ℝ (deriv c s) (deriv (varY ρ c φ) s) / ‖deriv c s‖)) := by
  rw [(hasDerivAt_varX_GE hρ hρpos hc hreg hφ s).deriv,
    (hasDerivAt_varY_GE hρ hρpos hc hreg hφ hφ' s).deriv,
    (hasDerivAt_potZ_GE hρ hρpos hc hreg hφ s).deriv, laplacian_log_second_GE hρ hρpos (c s)]
  have hR0 : ρ (c s) ≠ 0 := (hρpos _).ne'
  have e1 : φ' s = fderiv ℝ ρ (c s) (deriv c s) * fTil ρ c φ s + ρ (c s) * fDer ρ c φ φ' s := by
    simp only [fDer, fTil]
    field_simp
    ring
  have e2 : φ s = ρ (c s) * fTil ρ c φ s := by
    simp only [fTil]
    field_simp
  have key := index_pointwise_GE (fderiv ℝ ρ (c s)) (fderiv ℝ (fderiv ℝ ρ) (c s))
    (a := deriv c s) (b := deriv (deriv c) s) (hreg s) (hρpos (c s)) (fTil ρ c φ s)
    (fDer ρ c φ φ' s) (deriv (yCoef ρ c φ) s)
  rw [e1, e2]
  simp only [varX, varY, yCoef]
  exact key

theorem varX_zero_GE (ρ : ℂ → ℝ) (c : ℝ → ℂ) {φ : ℝ → ℝ} {t : ℝ} (h : φ t = 0) :
    varX ρ c φ t = 0 := by
  simp [varX, fTil, h]

theorem varY_zero_GE (ρ : ℂ → ℝ) (c : ℝ → ℂ) {φ : ℝ → ℝ} {t : ℝ} (h : φ t = 0) :
    varY ρ c φ t = 0 := by
  simp [varY, yCoef, fTil, h]

theorem potZ_zero_GE (ρ : ℂ → ℝ) (c : ℝ → ℂ) {φ : ℝ → ℝ} {t : ℝ} (h : φ t = 0) :
    potZ ρ c φ t = 0 := by
  simp [potZ, fTil, h]

/-- 指标形式非负：`c` 在 `C¹` 曲线类里极小 ⇒ 对所有 `C¹` 的 `φ`（`φ(0) = φ(L) = 0`），
`0 ≤ ∫₀ᴸ (φ′²/ê − K̂ ê φ²)`，`ê = ρ(c)‖c′‖`，`K̂ = −ρ⁻² Δ(log ρ)`。 -/
theorem index_form_nonneg_GE {ρ : ℂ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρpos : ∀ z, 0 < ρ z)
    {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0) {L : ℝ} (hL : 0 ≤ L)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρ (η s) * ‖deriv η s‖)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (hφ' : Continuous φ')
    (h0 : φ 0 = 0) (hL' : φ L = 0) :
    0 ≤ ∫ s in (0 : ℝ)..L, (φ' s ^ 2 / (ρ (c s) * ‖deriv c s‖) -
      (-(ρ (c s))⁻¹ ^ 2 * Laplacian.laplacian (fun p => Real.log (ρ p)) (c s)) *
        (ρ (c s) * ‖deriv c s‖) * φ s ^ 2) := by
  obtain ⟨hf, hY, hXs, hYs, hZs⟩ := index_smooth_GE hρ hρpos hc hreg hφ hφ'
  have hc1 : ContDiff ℝ 1 c := hc.of_le (by norm_num)
  have hmin' : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ (univ : Set ℂ)) →
      η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρ (η s) * ‖deriv η s‖ :=
    fun η hη _ h0' hL'' => hmin η hη h0' hL''
  obtain ⟨_, hd2int, _, hd2⟩ := weightedLength_variation_GE (X := varX ρ c φ) isOpen_univ
    hρ.contDiffOn hL hc1 hXs (fun s _ => mem_univ _) (fun s _ => hreg s)
    (varX_zero_GE ρ c h0) (varX_zero_GE ρ c hL') hmin'
  obtain ⟨hd1int, _, hd1, _⟩ := weightedLength_variation_GE (X := varY ρ c φ) isOpen_univ
    hρ.contDiffOn hL hc1 hYs (fun s _ => mem_univ _) (fun s _ => hreg s)
    (varY_zero_GE ρ c h0) (varY_zero_GE ρ c hL') hmin'
  have hZint : IntervalIntegrable (deriv (potZ ρ c φ)) MeasureTheory.volume 0 L :=
    (hZs.continuous_deriv le_rfl).intervalIntegrable 0 L
  have hZ : ∫ s in (0 : ℝ)..L, deriv (potZ ρ c φ) s = potZ ρ c φ L - potZ ρ c φ 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun s _ => (hZs.differentiable (by norm_num)) s)
      hZint
  rw [intervalIntegral.integral_congr (fun s _ =>
    index_integrand_eq_GE hρ hρpos hc hreg hφ hφ' s),
    intervalIntegral.integral_sub (hd2int.add hZint) hd1int,
    intervalIntegral.integral_add hd2int hZint, hZ, hd1, potZ_zero_GE ρ c h0,
    potZ_zero_GE ρ c hL']
  linarith

end DifferentialGeometry.Geometry
