import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredRadialR13
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# O-MY-R13 G2：radial extension 在 seam 点附近是 smooth local diffeo（R13-S(ii)，D-25/27）

MYD3 合同 `radial_extension_seam_smooth_MYD3`（`R10R14.lean:346`）：`β` 沿角参数在 `t₀` 附近 `C^∞`、
导数非零 ⇒ `E_β` 在 `e^{it₀}` 附近（闭盘一侧）`C^∞`、`fderivWithin` 单射（R4r / R4C 要的 one-sided
collar 间 smooth local diffeo）。

**偏差（必须）**：加前提 `hβS : MapsTo β S¹ S¹`。没有它陈述是假的：`β(e^{it}) = 1 + (t − t₀)`（实值）在
`t₀` 附近光滑、导数 `1 ≠ 0`，但 `E_β(r e^{it}) = r β(e^{it})` 的两个偏导 `∂_r = β`、`∂_t = r β′` 都是实数，
`E_β` 的导数退化。有了 `|β| = 1` 就有 `⟪β, β′⟫ = 0`，`∂_r`、`∂_t` 线性无关。R13-S 的用法（`β = F₁⁻¹ ∘ b ∘ F₂`，
`BijOn β S¹ S¹`）总满足此前提。外审 R-MY3 的 seam 条件（`c₂′(t₀) ≠ 0`、`(b∘c₂)′(t₀) ≠ 0`，原点不要求光滑）
与本陈述相容：这里只在 `e^{it₀}` 附近要求光滑。

证明：`θ(z) = t₀ + arg(z e^{−it₀})` 是 `e^{it₀}` 附近光滑的角函数（`Complex.log` 在 slit plane 上解析），
`e^{iθ(z)} = z / ‖z‖`，故 `E_β = ‖z‖ · g(θ z)`（`g t = β(e^{it})`）在 `e^{it₀}` 的一个开邻域上光滑。
导数沿两条曲线 `s ↦ s ξ`、`τ ↦ r e^{iτ}` 求出 `L ξ = g t`、`L (ξ I) = g′ t`，再由 `⟪g, g′⟫ = 0`、`‖g‖ = 1`、
`g′ ≠ 0` 得 `L` 单射。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Complex
open scoped Topology ContDiff RealInnerProductSpace ComplexConjugate

namespace DifferentialGeometry.Geometry

/-- seam 点 `e^{it₀}` 附近的光滑角函数 `θ(z) = t₀ + arg(z e^{−it₀})`。 -/
def seamAngle_R13 (t₀ : ℝ) (z : ℂ) : ℝ :=
  t₀ + arg (z * exp (-(t₀ * I)))

theorem seamAngle_self_R13 (t₀ : ℝ) : seamAngle_R13 t₀ (exp (t₀ * I)) = t₀ := by
  simp [seamAngle_R13, ← Complex.exp_add]

/-- `z ≠ 0` ⇒ `e^{iθ(z)} = z / ‖z‖`。 -/
theorem exp_seamAngle_R13 (t₀ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    exp (seamAngle_R13 t₀ z * I) = z / (‖z‖ : ℂ) := by
  set w := z * exp (-(t₀ * I)) with hw
  have hnw : ‖w‖ = ‖z‖ := by
    rw [hw, norm_mul, show -((t₀ : ℂ) * I) = ((-t₀ : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
  have hz' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  have hpolar := norm_mul_exp_arg_mul_I w
  rw [hnw] at hpolar
  have harg : exp (arg w * I) = w / (‖z‖ : ℂ) := by
    rw [eq_div_iff hz', mul_comm]
    exact hpolar
  have hsplit : exp (seamAngle_R13 t₀ z * I) = exp (t₀ * I) * exp (arg w * I) := by
    rw [← Complex.exp_add, seamAngle_R13, ← hw]
    push_cast
    ring_nf
  rw [hsplit, harg, hw, mul_div_assoc', ← mul_assoc, mul_comm (exp _) z, mul_assoc,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- `‖z − e^{it₀}‖ < 1` ⇒ `θ` 在 `z` 处 `C^∞`。 -/
theorem contDiffAt_seamAngle_R13 (t₀ : ℝ) {z : ℂ} (hz : ‖z - exp (t₀ * I)‖ < 1) :
    ContDiffAt ℝ ∞ (seamAngle_R13 t₀) z := by
  have hw : z * exp (-(t₀ * I)) ∈ slitPlane := by
    have hnorm : ‖z * exp (-(t₀ * I)) - 1‖ < 1 := by
      have : z * exp (-(t₀ * I)) - 1 = (z - exp (t₀ * I)) * exp (-(t₀ * I)) := by
        rw [sub_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      rw [this, norm_mul, show -((t₀ : ℂ) * I) = ((-t₀ : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, mul_one]
      exact hz
    have hre : |(z * exp (-(t₀ * I)) - 1).re| < 1 :=
      (abs_re_le_norm _).trans_lt hnorm
    rw [mem_slitPlane_iff]
    left
    rw [sub_re, one_re] at hre
    linarith [(abs_lt.mp hre).1]
  have hlog : ContDiffAt ℝ ∞ (fun y : ℂ => log (y * exp (-(t₀ * I)))) z :=
    ((contDiffAt_log hw).restrict_scalars ℝ).comp z
      ((contDiff_id.mul contDiff_const).contDiffAt)
  have him : ContDiffAt ℝ ∞ (fun y : ℂ => (log (y * exp (-(t₀ * I)))).im) z :=
    imCLM.contDiff.contDiffAt.comp z hlog
  have : seamAngle_R13 t₀ = fun y : ℂ => t₀ + (log (y * exp (-(t₀ * I)))).im := by
    funext y
    rw [seamAngle_R13, log_im]
  rw [this]
  exact contDiffAt_const.add him

/-- `z ≠ 0` ⇒ `E_β z = ‖z‖ · β(e^{iθ(z)})`。 -/
theorem radialExtension_eq_seamAngle_R13 (β : ℂ → ℂ) (t₀ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    radialExtension_R13 β z = (‖z‖ : ℂ) * β (exp (seamAngle_R13 t₀ z * I)) := by
  rw [exp_seamAngle_R13 t₀ hz]
  simp only [radialExtension_R13, hz, ↓reduceIte]

/-- seam 点附近 `E_β` 是 `C^∞`：`‖z − e^{it₀}‖ < 1`、`z ≠ 0`、`θ(z)` 落在 `t ↦ β(e^{it})` 的光滑区间里。 -/
theorem contDiffAt_radialExtension_seam_R13 {β : ℂ → ℂ} {t₀ ε : ℝ}
    (hβs : ContDiffOn ℝ ∞ (fun t : ℝ => β (exp (t * I))) (Ioo (t₀ - ε) (t₀ + ε)))
    {z : ℂ} (hz : ‖z - exp (t₀ * I)‖ < 1) (hz0 : z ≠ 0)
    (hθ : seamAngle_R13 t₀ z ∈ Ioo (t₀ - ε) (t₀ + ε)) :
    ContDiffAt ℝ ∞ (radialExtension_R13 β) z := by
  have hnorm : ContDiffAt ℝ ∞ (fun y : ℂ => ((‖y‖ : ℝ) : ℂ)) z :=
    ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℝ hz0)
  have hgθ : ContDiffAt ℝ ∞ (fun y : ℂ => β (exp (seamAngle_R13 t₀ y * I))) z :=
    (hβs.contDiffAt (isOpen_Ioo.mem_nhds hθ)).comp z (contDiffAt_seamAngle_R13 t₀ hz)
  apply (hnorm.mul hgθ).congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
  exact radialExtension_eq_seamAngle_R13 β t₀ hy

/-- 导数单射：`z = ‖z‖ e^{it}`、`g = (τ ↦ β(e^{iτ}))` 在 `t` 可微且 `g′ t ≠ 0`、`MapsTo β S¹ S¹`
⇒ `fderiv E_β z` 单射（`L ξ = g t`、`L (ξ I) = g′ t`、`⟪g t, g′ t⟫ = 0`、`‖g t‖ = 1`）。 -/
theorem injective_fderiv_radialExtension_R13 {β : ℂ → ℂ}
    (hβS : MapsTo β (Metric.sphere 0 1) (Metric.sphere 0 1)) {z : ℂ} (hz0 : z ≠ 0)
    (hE : DifferentiableAt ℝ (radialExtension_R13 β) z) {t : ℝ}
    (ht : exp (t * I) = z / (‖z‖ : ℂ))
    (hg : DifferentiableAt ℝ (fun τ : ℝ => β (exp (τ * I))) t)
    (hg' : deriv (fun τ : ℝ => β (exp (τ * I))) t ≠ 0) :
    Function.Injective (fderiv ℝ (radialExtension_R13 β) z) := by
  set g : ℝ → ℂ := fun τ => β (exp (τ * I)) with hgdef
  set g' := deriv g t with hg'def
  set ξ := exp (t * I) with hξ
  set r := ‖z‖ with hrdef
  set L := fderiv ℝ (radialExtension_R13 β) z with hLdef
  have hr : 0 < r := norm_pos_iff.mpr hz0
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hzξ : z = r • ξ := by
    rw [ht, Complex.real_smul, mul_div_cancel₀ z hrc]
  have hτS (τ : ℝ) : exp (τ * I) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_exp_ofReal_mul_I]
  have hξS : ξ ∈ Metric.sphere (0 : ℂ) 1 := hτS t
  have hL : HasFDerivAt (radialExtension_R13 β) L (r • ξ) := by
    rw [← hzξ]
    exact hE.hasFDerivAt
  -- (1) 径向：`L ξ = β ξ`
  have h1 : L ξ = β ξ := by
    have hc : HasDerivAt (fun s : ℝ => s • ξ) ξ r := by
      simpa using (hasDerivAt_id r).smul_const ξ
    have hA : HasDerivAt (fun s : ℝ => radialExtension_R13 β (s • ξ)) (L ξ) r :=
      HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => s • ξ) r hL hc
    have hB : HasDerivAt (fun s : ℝ => radialExtension_R13 β (s • ξ)) (β ξ) r := by
      have : HasDerivAt (fun s : ℝ => s • β ξ) (β ξ) r := by
        simpa using (hasDerivAt_id r).smul_const (β ξ)
      apply this.congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hr] with s hs
      exact radialExtension_smul_R13 β hs.le hξS
    exact hA.unique hB
  -- (2) 角向：`L (ξ I) = g′`
  have h2 : L (ξ * I) = g' := by
    have hc : HasDerivAt (fun τ : ℝ => r • exp (τ * I)) (r • (ξ * I)) t := by
      have he : HasDerivAt (fun τ : ℝ => exp (τ * I)) (ξ * I) t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).cexp
      exact he.const_smul r
    have hA : HasDerivAt (fun τ : ℝ => radialExtension_R13 β (r • exp (τ * I)))
        (L (r • (ξ * I))) t :=
      HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => r • exp (τ * I)) t hL hc
    have hB : HasDerivAt (fun τ : ℝ => radialExtension_R13 β (r • exp (τ * I))) (r • g') t := by
      apply (hg.hasDerivAt.const_smul r).congr_of_eventuallyEq
      filter_upwards with τ
      exact radialExtension_smul_R13 β hr.le (hτS τ)
    have h := hA.unique hB
    rw [map_smul] at h
    exact smul_right_injective ℂ hr.ne' h
  -- (3) `⟪g t, g′⟫ = 0`、`‖β ξ‖ = 1`
  have hβξ : ‖β ξ‖ = 1 := mem_sphere_zero_iff_norm.mp (hβS hξS)
  have h3 : ⟪β ξ, g'⟫ = 0 := by
    have hn := hg.hasDerivAt.norm_sq
    have hconst : (fun τ : ℝ => ‖g τ‖ ^ 2) = fun _ => (1 : ℝ) := by
      funext τ
      rw [mem_sphere_zero_iff_norm.mp (hβS (hτS τ)), one_pow]
    rw [hconst] at hn
    have h0 := hn.unique (hasDerivAt_const t (1 : ℝ))
    change 2 * ⟪β ξ, g'⟫ = 0 at h0
    linarith
  -- (4) 单射
  rw [injective_iff_map_eq_zero]
  intro v hv
  set q := v * conj ξ with hq
  have hξξ : conj ξ * ξ = 1 := by
    rw [conj_mul', mem_sphere_zero_iff_norm.mp hξS]
    norm_num
  have hvq : v = q.re • ξ + q.im • (ξ * I) := by
    have hv1 : v = q * ξ := by rw [hq, mul_assoc, hξξ, mul_one]
    conv_lhs => rw [hv1, ← re_add_im q]
    rw [Complex.real_smul, Complex.real_smul]
    ring
  have hLv : q.re • β ξ + q.im • g' = 0 := by
    rw [← h1, ← h2, ← map_smul, ← map_smul, ← map_add, ← hvq]
    exact hv
  have hre : q.re = 0 := by
    have hi := congrArg (fun w : ℂ => ⟪β ξ, w⟫) hLv
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hβξ, h3,
      inner_zero_right] at hi
    linarith
  have him : q.im = 0 := by
    rw [hre, zero_smul, zero_add, smul_eq_zero] at hLv
    exact hLv.resolve_right hg'
  rw [hvq, hre, him, zero_smul, zero_smul, add_zero]

/-- **G2 主定理**（MYD3 `radial_extension_seam_smooth_MYD3` + 前提 `hβS : MapsTo β S¹ S¹`）：
`t ↦ β(e^{it})` 在 `(t₀ − ε, t₀ + ε)` 上 `C^∞`、`t₀` 处导数非零 ⇒ 存在 `δ > 0`，`E_β` 在
`ball(e^{it₀}, δ) ∩ D̄` 上 `C^∞`，且 `fderivWithin ℝ E_β D̄` 处处单射。 -/
theorem radial_extension_seam_smooth_R13 {β : ℂ → ℂ} {t₀ ε : ℝ} (hε : 0 < ε)
    (hβS : MapsTo β (Metric.sphere 0 1) (Metric.sphere 0 1))
    (hβs : ContDiffOn ℝ ∞ (fun t : ℝ => β (exp (t * I))) (Ioo (t₀ - ε) (t₀ + ε)))
    (hβ' : deriv (fun t : ℝ => β (exp (t * I))) t₀ ≠ 0) :
    ∃ δ > 0, ContDiffOn ℝ ∞ (radialExtension_R13 β)
        (Metric.ball (exp (t₀ * I)) δ ∩ Metric.closedBall 0 1) ∧
      ∀ z ∈ Metric.ball (exp (t₀ * I)) δ ∩ Metric.closedBall 0 1, Function.Injective
        (fderivWithin ℝ (radialExtension_R13 β) (Metric.closedBall 0 1) z) := by
  set g : ℝ → ℂ := fun t => β (exp (t * I)) with hgdef
  have hIoo : Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : ContinuousAt (deriv g) t₀ :=
    (hβs.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt hIoo
  have hev : ∀ᶠ t in 𝓝 t₀, deriv g t ≠ 0 ∧ t ∈ Ioo (t₀ - ε) (t₀ + ε) :=
    (hcont.eventually_ne hβ').and hIoo
  obtain ⟨ε₁, hε₁, hε₁g⟩ := Metric.eventually_nhds_iff.mp hev
  have hξ₀ : ‖exp (t₀ * I)‖ = 1 := norm_exp_ofReal_mul_I t₀
  have hθc : ContinuousAt (seamAngle_R13 t₀) (exp (t₀ * I)) :=
    (contDiffAt_seamAngle_R13 t₀ (by simp)).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁θ⟩ := Metric.continuousAt_iff.mp hθc ε₁ hε₁
  -- 逐点事实
  have hpt : ∀ z ∈ Metric.ball (exp (t₀ * I)) (min δ₁ (1 / 2)),
      ‖z - exp (t₀ * I)‖ < 1 ∧ z ≠ 0 ∧ deriv g (seamAngle_R13 t₀ z) ≠ 0 ∧
        seamAngle_R13 t₀ z ∈ Ioo (t₀ - ε) (t₀ + ε) := by
    intro z hz
    rw [Metric.mem_ball, lt_min_iff] at hz
    have hzn : ‖z - exp (t₀ * I)‖ < 1 / 2 := by rw [← dist_eq_norm]; exact hz.2
    refine ⟨hzn.trans (by norm_num), ?_, ?_⟩
    · rintro rfl
      rw [zero_sub, norm_neg, hξ₀] at hzn
      norm_num at hzn
    · have hθ := hδ₁θ hz.1
      rw [seamAngle_self_R13] at hθ
      exact hε₁g hθ
  have hCD : ∀ z ∈ Metric.ball (exp (t₀ * I)) (min δ₁ (1 / 2)),
      ContDiffAt ℝ ∞ (radialExtension_R13 β) z := by
    intro z hz
    obtain ⟨h1, h0, -, hI⟩ := hpt z hz
    exact contDiffAt_radialExtension_seam_R13 hβs h1 h0 hI
  refine ⟨min δ₁ (1 / 2), lt_min hδ₁ (by norm_num), fun z hz => (hCD z hz.1).contDiffWithinAt,
    ?_⟩
  intro z hz
  obtain ⟨-, h0, hd, hI⟩ := hpt z hz.1
  have hEd : DifferentiableAt ℝ (radialExtension_R13 β) z :=
    (hCD z hz.1).differentiableAt (by simp)
  have huniq : UniqueDiffWithinAt ℝ (Metric.closedBall (0 : ℂ) 1) z :=
    uniqueDiffOn_convex (convex_closedBall 0 1)
      ⟨0, by rw [interior_closedBall _ one_ne_zero]; simp⟩ z hz.2
  rw [hEd.fderivWithin huniq]
  have hgd : DifferentiableAt ℝ g (seamAngle_R13 t₀ z) :=
    ((hβs.contDiffAt (isOpen_Ioo.mem_nhds hI)).differentiableAt (by simp))
  exact injective_fderiv_radialExtension_R13 hβS h0 hEd (exp_seamAngle_R13 t₀ h0) hgd hd

/-- consumer：`β = id`（`E_id = id`）在任意 seam 点 `e^{it₀}` 附近满足 G2 的结论。 -/
example (t₀ : ℝ) : ∃ δ > 0, ContDiffOn ℝ ∞ (radialExtension_R13 id)
      (Metric.ball (exp (t₀ * I)) δ ∩ Metric.closedBall 0 1) ∧
    ∀ z ∈ Metric.ball (exp (t₀ * I)) δ ∩ Metric.closedBall 0 1, Function.Injective
      (fderivWithin ℝ (radialExtension_R13 id) (Metric.closedBall 0 1) z) := by
  have hd : HasDerivAt (fun t : ℝ => id (exp (t * I))) (exp (t₀ * I) * I) t₀ := by
    simpa using ((hasDerivAt_id t₀).ofReal_comp.mul_const I).cexp
  have hs : ContDiff ℝ ∞ (fun t : ℝ => id (exp (t * I))) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp (ofRealCLM.contDiff.mul contDiff_const)
  refine radial_extension_seam_smooth_R13 (ε := 1) one_pos (mapsTo_id _) hs.contDiffOn ?_
  rw [hd.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) I_ne_zero

end DifferentialGeometry.Geometry
