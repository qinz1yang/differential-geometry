import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.MinimizingPathSphereGM
import DifferentialGeometry.Geometry.Curvature.ConformalGeodesicStabilityMinGE

/-!
# IMS05′ 的曲面层主定理（给定 `u`）（O-W-GEO-MIN G3，后缀 `_GM`）

`g_Σ = lam |dz|²` 在开集 `Ω ⊆ ℂ` 上（`lam > 0` 光滑，K16b 后的 Morrey 盘内部），`u > 0` 光滑满足
`Δ₀ u = lam (K_Σ − q − μ) u`（`K_Σ = −Δ₀ log lam / (2 lam)`，即 `Δ_Σ u = (K_Σ − q − μ) u`；S-W-EIG 的第一
特征函数方程），`μ ≥ 0`，在闭内蕴球 `B̄ = {z ∈ Ω | d z ≤ r}`（紧）上 `q ≥ σ/2 > 0`
⇒ **`r ≤ L ≤ 2π √(2/(3σ))`**（`L` = 极小路径的 `g_Σ`-长度）。

串联：G1 `exists_minimizing_path_to_sphere_GM`（`ĝ = u² g_Σ` 下到 `S_r` 的极小路径）+ S-W-GEO G2
`radius_le_of_minimizing_GE`（极小 ⇒ 指标形式 ≥ 0 ⇒ O-IFACE G3 `hstab` ⇒ 半径界）。后者要求 `u`、`lam`、
`q` 在全平面上 `C²` / 连续且 `u, lam > 0`：这里用 cutoff 延拓 `ũ = χu + (1−χ)`、`l̃am = χ lam + (1−χ)`、
`q̃ = χ q`（在 `B̄` 的开邻域上与原函数相等），PDE 在 `c(s)` 处经 `laplacian_congr_nhds` 转移。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

/-- cutoff 乘积 `χ q` 在全平面连续（`q` 只在 `Ω` 上连续，`tsupport χ ⊆ Ω`）。 -/
theorem continuous_cutoff_mul_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {χ q : ℂ → ℝ}
    (hχ : Continuous χ) (hχΩ : tsupport χ ⊆ Ω) (hq : ContinuousOn q Ω) :
    Continuous (fun z => χ z * q z) := by
  refine continuous_iff_continuousAt.mpr fun z => ?_
  by_cases hz : z ∈ Ω
  · exact hχ.continuousAt.mul (hq.continuousAt (hΩ.mem_nhds hz))
  · have hev : χ =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hχΩ h))
    have hev' : (fun z => χ z * q z) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with w hw
      simp [hw]
    exact continuousAt_const.congr hev'.symm

/-- **G3 主定理（IMS05′ 曲面层，给定 `u`）**：`r ≤ L ≤ 2π √(2/(3σ))`，`L` 为 `ĝ = u² g_Σ` 下到内蕴
球面 `S_r` 的极小路径的 `g_Σ`-长度。 -/
theorem exists_length_le_of_sphere_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {lam u q d : ℂ → ℝ}
    {μ σ : ℝ} (hlam : ContDiffOn ℝ ∞ lam Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hlam0 : ∀ z ∈ Ω, 0 < lam z) (hu0 : ∀ z ∈ Ω, 0 < u z) (hq : ContinuousOn q Ω)
    (hσ : 0 < σ) (hμ : 0 ≤ μ) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {p : ℂ} (hp : p ∈ Ω) (hdp : d p = 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r})
    (hqσ : ∀ z ∈ Ω, d z ≤ r → σ / 2 ≤ q z)
    (hpde : ∀ z ∈ Ω, d z ≤ r → Laplacian.laplacian u z = lam z *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) z / (2 * lam z) - q z - μ) * u z) :
    ∃ (c : ℝ → ℂ) (L : ℝ), c 0 = p ∧ d (c L) = r ∧
      (∀ s ∈ Icc 0 L, c s ∈ Ω ∧ d (c s) ≤ r) ∧
      (∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1) ∧
      r ≤ L ∧ L ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  have hKΩ : {z | z ∈ Ω ∧ d z ≤ r} ⊆ Ω := fun z hz => hz.1
  obtain ⟨c, L, ρt, V, -, -, -, hρt, hρtpos, -, hloc, hc, hreg, hc0, hcL, hrL, hcK, -,
    harc, hmin⟩ := exists_minimizing_path_to_sphere_GM hΩ hlam hu hlam0 hu0 hd hseg hp hdp hr hK
  -- cutoff 延拓 `u`、`lam`、`q`
  obtain ⟨χ, V', hχ, hV', hKV', -, hχ1, hχ01, -, hχΩ⟩ := exists_cutoff_GM hΩ hK hKΩ
  have hut : ContDiff ℝ ∞ (posExt_GM χ u) := contDiff_posExt_GM hΩ hχ hχΩ hu
  have hlt : ContDiff ℝ ∞ (posExt_GM χ lam) := contDiff_posExt_GM hΩ hχ hχΩ hlam
  have hqt : Continuous (fun z => χ z * q z) := continuous_cutoff_mul_GM hΩ hχ.continuous hχΩ hq
  have hnear : ∀ s ∈ Icc 0 L, ∀ᶠ z in 𝓝 (c s), χ z = 1 := fun s hs =>
    Filter.eventually_of_mem (hV'.mem_nhds (hKV' (hcK s hs))) fun z hz => hχ1 z hz
  have hχc : ∀ s ∈ Icc 0 L, χ (c s) = 1 := fun s hs => hχ1 _ (hKV' (hcK s hs))
  have hueq : ∀ s ∈ Icc 0 L, posExt_GM χ u =ᶠ[𝓝 (c s)] u := fun s hs => by
    filter_upwards [hnear s hs] with z hz
    exact posExt_eq_GM hz
  have hleq : ∀ s ∈ Icc 0 L, posExt_GM χ lam =ᶠ[𝓝 (c s)] lam := fun s hs => by
    filter_upwards [hnear s hs] with z hz
    exact posExt_eq_GM hz
  have hloc' : ∀ s ∈ Icc 0 L,
      ρt =ᶠ[𝓝 (c s)] fun z => posExt_GM χ u z * Real.sqrt (posExt_GM χ lam z) := by
    intro s hs
    filter_upwards [hloc s hs, hnear s hs] with z hz hz1
    rw [hz, posExt_eq_GM hz1, posExt_eq_GM hz1]
  have hpde' : ∀ s ∈ Icc 0 L, Laplacian.laplacian (posExt_GM χ u) (c s) =
      posExt_GM χ lam (c s) * (-Laplacian.laplacian (fun p => Real.log (posExt_GM χ lam p)) (c s) /
        (2 * posExt_GM χ lam (c s)) - (χ (c s) * q (c s)) - μ) * posExt_GM χ u (c s) := by
    intro s hs
    have hlog : (fun p => Real.log (posExt_GM χ lam p)) =ᶠ[𝓝 (c s)]
        fun p => Real.log (lam p) := by
      filter_upwards [hleq s hs] with z hz
      rw [hz]
    rw [(InnerProductSpace.laplacian_congr_nhds (hueq s hs)).eq_of_nhds,
      (InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds,
      posExt_eq_GM (hχc s hs), posExt_eq_GM (hχc s hs), hχc s hs, one_mul]
    exact hpde _ (hcK s hs).1 (hcK s hs).2
  have hqσ' : ∀ s ∈ Icc 0 L, σ / 2 ≤ χ (c s) * q (c s) := fun s hs => by
    rw [hχc s hs, one_mul]
    exact hqσ _ (hcK s hs).1 (hcK s hs).2
  have harc' : ∀ s ∈ Icc 0 L, posExt_GM χ lam (c s) * ‖deriv c s‖ ^ 2 = 1 := fun s hs => by
    rw [posExt_eq_GM (hχc s hs)]
    exact harc s hs
  have hL : 0 < L := hr.trans_le hrL
  have hbound := radius_le_of_minimizing_GE (r := L) (q := fun z => χ z * q z) hL hσ le_rfl hμ
    (hut.of_le (by simp)) (posExt_pos_GM hχΩ hχ01 hu0) (hlt.of_le (by simp))
    (posExt_pos_GM hχΩ hχ01 hlam0) hqt hqσ' (hρt.of_le (by simp)) hρtpos hloc'
    (hc.of_le (by simp)) hreg hmin hpde' harc'
  exact ⟨c, L, hc0, hcL, hcK, harc, hrL, hbound⟩

/-- **IMS05′（曲面层，给定 `u`）**：`r ≤ 2π √(2/(3σ))`。 -/
theorem radius_le_of_sphere_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {lam u q d : ℂ → ℝ}
    {μ σ : ℝ} (hlam : ContDiffOn ℝ ∞ lam Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hlam0 : ∀ z ∈ Ω, 0 < lam z) (hu0 : ∀ z ∈ Ω, 0 < u z) (hq : ContinuousOn q Ω)
    (hσ : 0 < σ) (hμ : 0 ≤ μ) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {p : ℂ} (hp : p ∈ Ω) (hdp : d p = 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r})
    (hqσ : ∀ z ∈ Ω, d z ≤ r → σ / 2 ≤ q z)
    (hpde : ∀ z ∈ Ω, d z ≤ r → Laplacian.laplacian u z = lam z *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) z / (2 * lam z) - q z - μ) * u z) :
    r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  obtain ⟨-, L, -, -, -, -, hrL, hL⟩ := exists_length_le_of_sphere_GM hΩ hlam hu hlam0 hu0 hq hσ
    hμ hd hseg hp hdp hr hK hqσ hpde
  exact hrL.trans hL

end DifferentialGeometry.Geometry
