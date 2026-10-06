import DifferentialGeometry.Geometry.Curvature.ConformalGeodesicStabilityGE
import DifferentialGeometry.Analysis.ODE.StabilityRadiusIF

/-!
# IMS05′ (5) ⇒ (6) 的串联 consumer（S-W-GEO G1）

`weighted_stability_of_second_variation_GE`（本车道）给出 O-IFACE G3
`mul_sq_le_of_weighted_stability_IF` 的 `hstab` 输入；这里把两边串起来：
共形度量 `ĝ = u² g_Σ` 的 `g_Σ` 弧长参数化测地线 `c : [0, L]`（`L ≥ r`），第二变分非负（指标形式，显式假设 `hd`），
`q ≥ σ/2`、`μ ≥ 0` ⇒ `r ≤ 2π √(2/(3σ))`（蓝图 IMS05 的结论）。

整体光滑 / 正性假设（`u`、`lam` 在全平面 `C²` 且为正）只是为了让 `v = log u ∘ c` 在 `ℝ` 上整体可导（O-IFACE G3
的 `hv : ∀ s, HasDerivAt v (v' s) s`）；若 `u` 只在 `Ω` 上有定义，先把 `v`、`Q` 延拓（积分只看 `[0, L]`），
定理 `weighted_stability_of_second_variation_GE` 本身只要求 `[0, L]` 上的等式。
-/

set_option autoImplicit false
noncomputable section

open Set intervalIntegral

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

theorem radius_le_of_second_variation_GE
    {u lam q ρ : ℂ → ℝ} {μ σ r L : ℝ} {c : ℝ → ℂ}
    (hL : 0 < L) (hσ : 0 < σ) (hrL : r ≤ L) (hμ : 0 ≤ μ)
    (hu : ContDiff ℝ 2 u) (hu0 : ∀ p, 0 < u p) (hlam : ContDiff ℝ 2 lam) (hlam0 : ∀ p, 0 < lam p)
    (hq : Continuous q) (hc : ContDiff ℝ 1 c) (hρ : ∀ p, ρ p = u p * Real.sqrt (lam p))
    (hqσ : ∀ s ∈ Icc 0 L, σ / 2 ≤ q (c s))
    (hpde : ∀ s ∈ Icc 0 L, Laplacian.laplacian u (c s) = lam (c s) *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) (c s) / (2 * lam (c s)) - q (c s) - μ) *
        u (c s))
    (harc : ∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1)
    (hd : ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' → φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, (φ' s ^ 2 / (ρ (c s) * ‖deriv c s‖) -
        (-(ρ (c s))⁻¹ ^ 2 * Laplacian.laplacian (fun p => Real.log (ρ p)) (c s)) *
          (ρ (c s) * ‖deriv c s‖) * φ s ^ 2)) :
    r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  have hlogu : ContDiff ℝ 2 (fun p => Real.log (u p)) := hu.log fun p => (hu0 p).ne'
  have hfd : Continuous (fderiv ℝ (fun p => Real.log (u p))) :=
    hlogu.continuous_fderiv (by norm_num)
  have hcd : Continuous (deriv c) := hc.continuous_deriv le_rfl
  have hcc : Continuous c := hc.continuous
  have hcdiff : ∀ s, HasDerivAt c (deriv c s) s := fun s =>
    ((hc.differentiable (by norm_num)) s).hasDerivAt
  -- `v = log u ∘ c`，`v' = d(log u)(c′)`
  have hv : ∀ s, HasDerivAt (fun s => Real.log (u (c s)))
      (fderiv ℝ (fun p => Real.log (u p)) (c s) (deriv c s)) s := fun s =>
    ((hlogu.differentiable (by norm_num)) (c s)).hasFDerivAt.comp_hasDerivAt s (hcdiff s)
  have hv' : Continuous fun s => fderiv ℝ (fun p => Real.log (u p)) (c s) (deriv c s) :=
    ((hfd.comp hcc).clm_apply hcd)
  have hQc : Continuous fun s => q (c s) + μ + (lam (c s))⁻¹ *
      (fderiv ℝ (fun p => Real.log (u p)) (c s) 1 ^ 2 +
        fderiv ℝ (fun p => Real.log (u p)) (c s) Complex.I ^ 2) := by
    have hl : Continuous fun s => (lam (c s))⁻¹ :=
      (hlam.continuous.comp hcc).inv₀ fun s => (hlam0 (c s)).ne'
    have h1 : Continuous fun s => fderiv ℝ (fun p => Real.log (u p)) (c s) 1 :=
      (hfd.comp hcc).clm_apply continuous_const
    have h2 : Continuous fun s => fderiv ℝ (fun p => Real.log (u p)) (c s) Complex.I :=
      (hfd.comp hcc).clm_apply continuous_const
    exact ((hq.comp hcc).add continuous_const).add (hl.mul ((h1.pow 2).add (h2.pow 2)))
  have hstab := weighted_stability_of_second_variation_GE (u := u) (lam := lam) (q := q) (ρ := ρ)
    (μ := μ) (c := c) (L := L) (v := fun s => Real.log (u (c s)))
    (Q := fun s => q (c s) + μ + (lam (c s))⁻¹ *
      (fderiv ℝ (fun p => Real.log (u p)) (c s) 1 ^ 2 +
        fderiv ℝ (fun p => Real.log (u p)) (c s) Complex.I ^ 2)) hL.le hρ
    (fun s _ => hu0 _) (fun s _ => hlam0 _) (fun s _ => hu.contDiffAt) (fun s _ => hlam.contDiffAt)
    hpde harc (fun s _ => rfl) (fun s _ => rfl) hd
  have hsq := mul_sq_le_of_weighted_stability_IF (σ := σ) (L := L) hL hv hv' hQc.continuousOn
    (fun s hs => sigma_half_add_sq_le_GE (hlam0 (c s)) (harc s hs) (hqσ s hs) hμ) hstab
  exact le_two_pi_sqrt_of_mul_sq_le_IF hσ hL.le hrL hsq

end DifferentialGeometry.Geometry
