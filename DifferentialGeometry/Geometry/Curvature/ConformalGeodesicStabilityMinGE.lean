import DifferentialGeometry.Geometry.Curvature.ConformalIndexFormGE
import DifferentialGeometry.Geometry.Curvature.ConformalGeodesicStabilityConsumerGE

/-!
# IMS05′ 第 (5) 步：极小曲线 ⇒ 一维稳定性不等式 ⇒ 半径界（S-W-GEO G2 收口）

`ConformalIndexFormGE.index_form_nonneg_GE`（极小性 ⇒ 指标形式非负，`ρ` 全局 `C²` 且为正）与
G1 的 `weighted_stability_of_second_variation_GE` / `radius_le_of_second_variation_GE`（指标形式 ⇒
`g_Σ` 弧长下的 `hstab` ⇒ `r ≤ 2π√(2/(3σ))`）串联：

* `ρ̃`（`hρt`）是全局 `C²` 正函数，**只在 `c([0, L])` 的邻域上等于 `u √lam`**（`hloc`）——
  这正是 complete-ification（`ρ̃ ≥ δ > 0` 截断延拓）给出的形状；
* `c` 为全局 `C²` 正则曲线，在 `g_Σ` 弧长参数化（`lam(c)‖c′‖² = 1` 在 `[0, L]` 上），
  在 `C¹` 曲线类里（固定端点）`ℓ_ρ̃` 极小（`hmin`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter intervalIntegral InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

/-- 极小性 ⇒ 以 `ρ = u √lam` 表述的指标形式非负（`hρt` 与 `u √lam` 在 `c([0,L])` 邻域上相等）。 -/
theorem index_form_of_minimizing_GE {u lam ρt : ℂ → ℝ} {L : ℝ} {c : ℝ → ℂ} (hL : 0 ≤ L)
    (hρt : ContDiff ℝ 2 ρt) (hρtpos : ∀ z, 0 < ρt z)
    (hloc : ∀ s ∈ Icc 0 L, ρt =ᶠ[𝓝 (c s)] fun p => u p * Real.sqrt (lam p))
    (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρt (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρt (η s) * ‖deriv η s‖) :
    ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' → φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, (φ' s ^ 2 / ((u (c s) * Real.sqrt (lam (c s))) * ‖deriv c s‖) -
        (-(u (c s) * Real.sqrt (lam (c s)))⁻¹ ^ 2 *
          Laplacian.laplacian (fun p => Real.log (u p * Real.sqrt (lam p))) (c s)) *
          ((u (c s) * Real.sqrt (lam (c s))) * ‖deriv c s‖) * φ s ^ 2) := by
  intro φ φ' h1 h2 h3 h4
  have := index_form_nonneg_GE hρt hρtpos hc hreg hL hmin h1 h2 h3 h4
  refine this.trans_eq (intervalIntegral.integral_congr fun s hs => ?_)
  have hs' : s ∈ Icc 0 L := by rwa [uIcc_of_le hL] at hs
  have e1 : ρt (c s) = u (c s) * Real.sqrt (lam (c s)) := (hloc s hs').eq_of_nhds
  have e2 : Laplacian.laplacian (fun p => Real.log (ρt p)) (c s) =
      Laplacian.laplacian (fun p => Real.log (u p * Real.sqrt (lam p))) (c s) := by
    refine (laplacian_congr_nhds ?_).eq_of_nhds
    filter_upwards [hloc s hs'] with p hp
    rw [hp]
  rw [e1, e2]

/-- 收口：`ρ̃ = u√lam`（局部）下，`g_Σ` 弧长参数化的 `ĝ`-极小曲线满足 `hstab`（O-IFACE G3 的第一输入）。 -/
theorem weighted_stability_of_minimizing_GE
    {u lam q ρt : ℂ → ℝ} {μ L : ℝ} {c : ℝ → ℂ} {v Q : ℝ → ℝ} (hL : 0 ≤ L)
    (hρt : ContDiff ℝ 2 ρt) (hρtpos : ∀ z, 0 < ρt z)
    (hloc : ∀ s ∈ Icc 0 L, ρt =ᶠ[𝓝 (c s)] fun p => u p * Real.sqrt (lam p))
    (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρt (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρt (η s) * ‖deriv η s‖)
    (hu0 : ∀ s ∈ Icc 0 L, 0 < u (c s)) (hlam0 : ∀ s ∈ Icc 0 L, 0 < lam (c s))
    (hu : ∀ s ∈ Icc 0 L, ContDiffAt ℝ 2 u (c s))
    (hlam : ∀ s ∈ Icc 0 L, ContDiffAt ℝ 2 lam (c s))
    (hpde : ∀ s ∈ Icc 0 L, Laplacian.laplacian u (c s) = lam (c s) *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) (c s) / (2 * lam (c s)) - q (c s) - μ) *
        u (c s))
    (harc : ∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1)
    (hv : ∀ s ∈ Icc 0 L, v s = Real.log (u (c s)))
    (hQ : ∀ s ∈ Icc 0 L, Q s = q (c s) + μ + (lam (c s))⁻¹ *
      (fderiv ℝ (fun p => Real.log (u p)) (c s) 1 ^ 2 +
        fderiv ℝ (fun p => Real.log (u p)) (c s) Complex.I ^ 2)) :
    ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' → φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, Real.exp (-v s) * (φ' s ^ 2 - Q s * φ s ^ 2) :=
  weighted_stability_of_second_variation_GE (ρ := fun p => u p * Real.sqrt (lam p)) hL
    (fun _ => rfl) hu0 hlam0 hu hlam hpde harc hv hQ
    (index_form_of_minimizing_GE hL hρt hρtpos hloc hc hreg hmin)

/-- 全链 consumer：极小曲线 ⇒ `r ≤ 2π √(2/(3σ))`（IMS05 的 (5) ⇒ (6)，唯一的输入是 `ĝ`-极小性）。 -/
theorem radius_le_of_minimizing_GE
    {u lam q ρt : ℂ → ℝ} {μ σ r L : ℝ} {c : ℝ → ℂ}
    (hL : 0 < L) (hσ : 0 < σ) (hrL : r ≤ L) (hμ : 0 ≤ μ)
    (hu : ContDiff ℝ 2 u) (hu0 : ∀ p, 0 < u p) (hlam : ContDiff ℝ 2 lam) (hlam0 : ∀ p, 0 < lam p)
    (hq : Continuous q) (hqσ : ∀ s ∈ Icc 0 L, σ / 2 ≤ q (c s))
    (hρt : ContDiff ℝ 2 ρt) (hρtpos : ∀ z, 0 < ρt z)
    (hloc : ∀ s ∈ Icc 0 L, ρt =ᶠ[𝓝 (c s)] fun p => u p * Real.sqrt (lam p))
    (hc : ContDiff ℝ 2 c) (hreg : ∀ s, deriv c s ≠ 0)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρt (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρt (η s) * ‖deriv η s‖)
    (hpde : ∀ s ∈ Icc 0 L, Laplacian.laplacian u (c s) = lam (c s) *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) (c s) / (2 * lam (c s)) - q (c s) - μ) *
        u (c s))
    (harc : ∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1) :
    r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) :=
  radius_le_of_second_variation_GE (ρ := fun p => u p * Real.sqrt (lam p)) hL hσ hrL hμ hu hu0
    hlam hlam0 hq (hc.of_le (by norm_num)) (fun _ => rfl) hqσ hpde harc
    (index_form_of_minimizing_GE hL.le hρt hρtpos hloc hc hreg hmin)

end DifferentialGeometry.Geometry
