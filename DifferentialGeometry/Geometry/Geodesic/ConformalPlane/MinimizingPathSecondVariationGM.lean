import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.MinimizingPathSphereGM
import DifferentialGeometry.Geometry.Curvature.WeightedLengthVariationGE
import DifferentialGeometry.Geometry.Curvature.ConformalGeodesicStabilityMinGE

/-!
# IMS05′ (5)：极小路径的第二变分非负（O-W-GEO-MIN G2，后缀 `_GM`）

G1（`exists_minimizing_path_to_sphere_GM`）给出的曲线 `c`（`ĝ = (u √lam)²|dz|²` 下到内蕴球面
`S_r` 的极小路径）在固定端点 `C¹` 变分 `c + εX`（`X(0) = X(L) = 0`）下：

* `second_variation_nonneg_of_minimizing_GM`（`c` 如 G1 的局部形状：`V` 开、`c [0,L] ⊆ V`、`V` 内
  `ĝ`-长度极小）：存在窗口 `ε₀ > 0`，`|ε| ≤ ε₀` 时 `c + εX` 留在 `V`（`ĝ` 未改动、远离 `∂Ω`）且
  `ℓ_ĝ(c) ≤ ℓ_ĝ(c + εX)`；`ε ↦ ℓ_ĝ(c + εX)` 在 `0` 取局部极小；一阶变分 `= 0`、**二阶变分 `≥ 0`**
  （显式被积函数，来自 S-W-GEO G2 的 `weightedLength_variation_GE`，`W = V`）。
* `variation_mem_ball_GM`（首次碰面 / 内部性）：`X` 在 `[a, L]`（`a < L`）上为零 ⇒ 小 `|ε|` 时
  `c + εX` 在 `[0, L)` 上仍留在开内蕴球 `{z ∈ Ω | d z < r}` 里，终点仍是 `c L ∈ S_r`。
* `index_form_nonneg_of_sphere_GM`：G1 存在定理 + S-W-GEO `index_form_of_minimizing_GE` ⇒ 极小路径存在
  且指标形式 `∫ (φ′²/ê − K̂ ê φ²) ≥ 0`（`ê = u√lam(c)‖c′‖`，`K̂ = −ρ⁻²Δ log ρ`）对所有 `C¹₀` 的 `φ`。

「二阶导 = 指标形式」的计算归 S-W-GEO（`ConformalIndexFormGE`），本文件只做极小性 ⇒ `≥ 0` 的接线、
变分窗口与首次碰面的保持。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

/-- **G2 主定理**：`c` 在 `V` 内同端点 `C¹` 曲线中 `ĝ`-长度极小（G1 的局部形状）⇒ 对每个 `C¹`
固定端点变分 `c + εX`：窗口内 `c + εX ⊆ V` 且 `ℓ_ĝ(c) ≤ ℓ_ĝ(c + εX)`、`ε = 0` 为局部极小、
一阶变分 `= 0`、二阶变分 `≥ 0`。`ρ = u √lam`（`hρ`）。 -/
theorem second_variation_nonneg_of_minimizing_GM {u lam ρ : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V)
    (hρ : ∀ z, ρ z = u z * Real.sqrt (lam z)) (hu : ContDiffOn ℝ 2 u V)
    (hlam : ContDiffOn ℝ 2 lam V) (hlam0 : ∀ z ∈ V, 0 < lam z)
    {c : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hc : ContDiff ℝ 1 c) (hcV : ∀ s ∈ Icc 0 L, c s ∈ V)
    (hreg : ∀ s ∈ Icc 0 L, deriv c s ≠ 0)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ V) → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, u (c s) * Real.sqrt (lam (c s)) * ‖deriv c s‖ ≤
        ∫ s in (0 : ℝ)..L, u (η s) * Real.sqrt (lam (η s)) * ‖deriv η s‖)
    {X : ℝ → ℂ} (hX : ContDiff ℝ 1 X) (hX0 : X 0 = 0) (hXL : X L = 0) :
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc (-ε₀) ε₀, (∀ s ∈ Icc 0 L, c s + ε • X s ∈ V) ∧
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤
        ∫ s in (0 : ℝ)..L, ρ (c s + ε • X s) * ‖deriv c s + ε • deriv X s‖) ∧
    IsLocalMin (fun ε : ℝ =>
      ∫ s in (0 : ℝ)..L, ρ (c s + ε • X s) * ‖deriv c s + ε • deriv X s‖) 0 ∧
    (∫ s in (0 : ℝ)..L, (fderiv ℝ ρ (c s) (X s) * ‖deriv c s‖ +
        ρ (c s) * (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖))) = 0 ∧
    0 ≤ ∫ s in (0 : ℝ)..L, (fderiv ℝ (fderiv ℝ ρ) (c s) (X s) (X s) * ‖deriv c s‖ +
        2 * fderiv ℝ ρ (c s) (X s) * (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) +
        ρ (c s) * ((‖deriv X s‖ ^ 2 - (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) ^ 2) /
          ‖deriv c s‖)) := by
  have hρeq : ρ = fun z => u z * Real.sqrt (lam z) := funext hρ
  have hρsm : ContDiffOn ℝ 2 ρ V := by
    rw [hρeq]
    exact hu.mul (hlam.sqrt fun z hz => (hlam0 z hz).ne')
  have hminρ : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ V) → η 0 = c 0 →
      η L = c L →
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρ (η s) * ‖deriv η s‖ := by
    intro η hη hηV h0 h1
    simp only [hρ]
    exact hmin η hη hηV h0 h1
  obtain ⟨ε₀, hε₀, hwin⟩ := exists_variation_window_GE hV hc hX hcV hreg
  have hmloc := wl_minimality_GE hc hX hX0 hXL hwin hminρ
  simp only [wlF, zero_smul, add_zero] at hmloc
  have hwinmin : ∀ ε ∈ Icc (-ε₀) ε₀, (∀ s ∈ Icc 0 L, c s + ε • X s ∈ V) ∧
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤
        ∫ s in (0 : ℝ)..L, ρ (c s + ε • X s) * ‖deriv c s + ε • deriv X s‖ :=
    fun ε hε => ⟨fun s hs => (hwin ε hε s hs).1, hmloc ε hε⟩
  obtain ⟨-, -, h1, h2⟩ := weightedLength_variation_GE hV hρsm hL hc hX hcV hreg hX0 hXL hminρ
  refine ⟨⟨ε₀, hε₀, hwinmin⟩, ?_, h1, h2⟩
  have hnhds : Icc (-ε₀) ε₀ ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hε₀
  filter_upwards [hnhds] with ε hε
  simpa only [zero_smul, add_zero] using (hwinmin ε hε).2

/-- **首次碰面的保持**：`c` 在 `[0, L)` 上留在开内蕴球 `{z ∈ Ω | d z < r}`，`X` 在 `[a, L]`（`a < L`）
上为零 ⇒ 小 `|ε|` 时 `c + εX` 在 `[0, L)` 上仍在开球内（变分不碰 `S_r`、不碰 `∂Ω`），终点不动。 -/
theorem variation_mem_ball_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {d : ℂ → ℝ} (hd : ContinuousOn d Ω)
    {r : ℝ} {c X : ℝ → ℂ} {L a : ℝ} (haL : a < L) (hc : ContDiff ℝ 1 c)
    (hX : ContDiff ℝ 1 X) (hreg : ∀ s ∈ Icc 0 a, deriv c s ≠ 0)
    (hball : ∀ s ∈ Ico 0 L, c s ∈ Ω ∧ d (c s) < r) (hXa : ∀ s ∈ Icc a L, X s = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc (-ε₀) ε₀,
      (∀ s ∈ Ico 0 L, c s + ε • X s ∈ Ω ∧ d (c s + ε • X s) < r) ∧ c L + ε • X L = c L := by
  have hB : IsOpen (Ω ∩ d ⁻¹' Iio r) := hd.isOpen_inter_preimage hΩ isOpen_Iio
  obtain ⟨ε₀, hε₀, hwin⟩ := exists_variation_window_GE (L := a) hB hc hX
    (fun s hs => hball s ⟨hs.1, hs.2.trans_lt haL⟩) hreg
  refine ⟨ε₀, hε₀, fun ε hε => ⟨fun s hs => ?_, ?_⟩⟩
  · rcases le_or_gt s a with h | h
    · exact (hwin ε hε s ⟨hs.1, h⟩).1
    · rw [hXa s ⟨h.le, hs.2.le⟩, smul_zero, add_zero]
      exact hball s hs
  · rw [hXa L ⟨haL.le, le_rfl⟩, smul_zero, add_zero]

/-- **G1 + S-W-GEO G2**：内蕴球面的极小路径存在，且其指标形式非负（`u √lam` 形式），
即 `index_form_of_minimizing_GE` 的结论；同时给出 G1 的全部几何结论。 -/
theorem index_form_nonneg_of_sphere_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {lam u d : ℂ → ℝ}
    (hlam : ContDiffOn ℝ ∞ lam Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hlam0 : ∀ z ∈ Ω, 0 < lam z) (hu0 : ∀ z ∈ Ω, 0 < u z) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {p : ℂ} (hp : p ∈ Ω) (hdp : d p = 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r}) :
    ∃ (c : ℝ → ℂ) (L : ℝ), ContDiff ℝ ∞ c ∧ c 0 = p ∧ d (c L) = r ∧ r ≤ L ∧
      (∀ s ∈ Icc 0 L, c s ∈ Ω ∧ d (c s) ≤ r) ∧ (∀ s ∈ Ico 0 L, d (c s) < r) ∧
      (∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1) ∧
      ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' → φ 0 = 0 → φ L = 0 →
        0 ≤ ∫ s in (0 : ℝ)..L, (φ' s ^ 2 / ((u (c s) * Real.sqrt (lam (c s))) * ‖deriv c s‖) -
          (-(u (c s) * Real.sqrt (lam (c s)))⁻¹ ^ 2 *
            Laplacian.laplacian (fun p => Real.log (u p * Real.sqrt (lam p))) (c s)) *
            ((u (c s) * Real.sqrt (lam (c s))) * ‖deriv c s‖) * φ s ^ 2) := by
  obtain ⟨c, L, ρt, V, -, -, -, hρt, hρtpos, -, hloc, hc, hreg, hc0, hcL, hrL, hcK, hfirst,
    harc, hmin⟩ := exists_minimizing_path_to_sphere_GM hΩ hlam hu hlam0 hu0 hd hseg hp hdp hr hK
  exact ⟨c, L, hc, hc0, hcL, hrL, hcK, hfirst, harc,
    index_form_of_minimizing_GE (hr.le.trans hrL) (hρt.of_le (by simp)) hρtpos hloc
      (hc.of_le (by simp)) hreg hmin⟩

end DifferentialGeometry.Geometry
