import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFIX
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexCone
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary

/-!
# S-MY-FIX G2：平坦标准盘 fixture 的 source 侧（`T`、`α`，`_FIX`）

R9 新模型（`PreparedSheetComplexFIX.lean`）对平坦标准盘 `z ↦ (Re z, Im z, 0)` 的 witness 的 **ℂ 侧**数据：

* **`T`** = 三角形 `Δ = conv{(-1,-1), (2,-1), (-1,2)}`（重心在原点）的边界复形 `simplexBoundary Δ`
  以原点为 apex 的 `coneComplex`：三个三角形 `{0, vᵢ, vⱼ}`；`|T| = Δ = {g ≤ 1}`，`g` 是 `Δ` 的 gauge
  `g z = max (-Re z) (-Im z) (Re z + Im z)`。
* **`α`** = 径向 gauge 映射 `α z = (g z / ‖z‖) • z`（`Δ → D̄`，`‖α z‖ = g z`）。逆有显式闭式
  `w ↦ (‖w‖ / g w) • w`，故双射 / 边界对边界是初等估计；`α` 在原点（`T` 的顶点）处是 cusp 型奇点，
  正好落在 (S3) 允许的“顶点例外”里；Lipschitz 常数 `6`（`norm_radialGrid_sub_le_FIX`）。
* 每个 2-面 `{0, vᵢ, vⱼ}` 上 `g = ℓ`（`ℓ` 是线性泛函），所以 `α` 在该面上等于扇区公式
  `ψ_ℓ z = (ℓ z / ‖z‖) • z`（`C^∞` on `z ≠ 0`），且 `χ_ℓ w = (‖w‖ / ℓ w) • w` 是它在 `{ℓ > 0}` 上的
  左逆，故导数单射（`injective_fderiv_sectorMap_FIX`，不需要显式 Jacobian）。

与 scratch 冻结文本（`R09.lean:251`）的偏差：scratch 用“正方形两三角剖分 + elliptical grid map”；这里换成
“三角形 cone 剖分 + 径向 gauge 映射”，因为后者双射 / Lipschitz 的证明是初等的，且 `|T|` 的描述由库里的
`coneComplex_space_eq_of_convex` 直接给出。notion 本身（22 字段）逐字不变。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Geometry

/-- 三角形 `Δ = conv{(-1,-1), (2,-1), (-1,2)}`（重心在原点）的 gauge：`Δ = {g ≤ 1}`。 -/
def triGauge_FIX (z : ℂ) : ℝ := max (max (-z.re) (-z.im)) (z.re + z.im)

theorem triGauge_zero_FIX : triGauge_FIX 0 = 0 := by simp [triGauge_FIX]

theorem triGauge_smul_FIX {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    triGauge_FIX (t • z) = t * triGauge_FIX z := by
  simp only [triGauge_FIX, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ ht, mul_max_of_nonneg _ _ ht]
  congr 2 <;> ring

theorem triGauge_ge_re_FIX (z : ℂ) : -z.re ≤ triGauge_FIX z :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem triGauge_ge_im_FIX (z : ℂ) : -z.im ≤ triGauge_FIX z :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem triGauge_ge_sum_FIX (z : ℂ) : z.re + z.im ≤ triGauge_FIX z := le_max_right _ _

theorem triGauge_nonneg_FIX (z : ℂ) : 0 ≤ triGauge_FIX z := by
  linarith [triGauge_ge_re_FIX z, triGauge_ge_im_FIX z, triGauge_ge_sum_FIX z]

theorem triGauge_pos_FIX {z : ℂ} (hz : z ≠ 0) : 0 < triGauge_FIX z := by
  refine lt_of_le_of_ne (triGauge_nonneg_FIX z) fun h => hz ?_
  have h1 := triGauge_ge_re_FIX z
  have h2 := triGauge_ge_im_FIX z
  have h3 := triGauge_ge_sum_FIX z
  exact Complex.ext (by simp; linarith) (by simp; linarith)

theorem continuous_triGauge_FIX : Continuous triGauge_FIX := by
  unfold triGauge_FIX; fun_prop

theorem abs_triGauge_sub_le_FIX (z w : ℂ) : |triGauge_FIX z - triGauge_FIX w| ≤ 2 * ‖z - w‖ := by
  have hre : |z.re - w.re| ≤ ‖z - w‖ := by
    simpa using Complex.abs_re_le_norm (z - w)
  have him : |z.im - w.im| ≤ ‖z - w‖ := by
    simpa using Complex.abs_im_le_norm (z - w)
  have hn := norm_nonneg (z - w)
  unfold triGauge_FIX
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ((abs_max_sub_max_le_max _ _ _ _).trans
    (max_le ?_ ?_)) ?_)
  · rw [show -z.re - -w.re = -(z.re - w.re) by ring, abs_neg]; linarith
  · rw [show -z.im - -w.im = -(z.im - w.im) by ring, abs_neg]; linarith
  · rw [show z.re + z.im - (w.re + w.im) = (z.re - w.re) + (z.im - w.im) by ring]
    exact (abs_add_le _ _).trans (by linarith)

theorem triGauge_le_FIX (z : ℂ) : triGauge_FIX z ≤ 2 * ‖z‖ := by
  have := abs_triGauge_sub_le_FIX z 0
  rw [triGauge_zero_FIX, sub_zero, sub_zero] at this
  exact (le_abs_self _).trans this

/-- `α`：径向 gauge 映射 `z ↦ (g z / ‖z‖) • z`（`Δ → D̄`）。 -/
def radialGrid_FIX (z : ℂ) : ℂ := (triGauge_FIX z / ‖z‖) • z

theorem radialGrid_zero_FIX : radialGrid_FIX 0 = 0 := by simp [radialGrid_FIX]

theorem norm_radialGrid_FIX (z : ℂ) : ‖radialGrid_FIX z‖ = triGauge_FIX z := by
  by_cases hz : z = 0
  · subst hz; simp [radialGrid_zero_FIX, triGauge_zero_FIX]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [radialGrid_FIX, norm_smul, Real.norm_of_nonneg (div_nonneg (triGauge_nonneg_FIX z) hn.le)]
    field_simp


theorem radialGrid_injective_FIX : Function.Injective radialGrid_FIX := by
  intro z w hzw
  have hgn : triGauge_FIX z = triGauge_FIX w := by
    rw [← norm_radialGrid_FIX, ← norm_radialGrid_FIX, hzw]
  by_cases hz : z = 0
  · subst hz
    by_contra hw
    have := triGauge_pos_FIX (Ne.symm hw)
    rw [triGauge_zero_FIX] at hgn
    linarith
  have hw : w ≠ 0 := by
    rintro rfl
    have := triGauge_pos_FIX hz
    rw [triGauge_zero_FIX] at hgn
    linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hr : 0 < triGauge_FIX z := triGauge_pos_FIX hz
  set r := triGauge_FIX z with hrdef
  have h : (r / ‖z‖) • z = (r / ‖w‖) • w := by
    have h0 := hzw
    rw [radialGrid_FIX, radialGrid_FIX, ← hgn] at h0
    exact h0
  have hc : w = (‖w‖ / ‖z‖) • z := by
    calc w = (‖w‖ / r) • ((r / ‖w‖) • w) := by
          rw [smul_smul, show ‖w‖ / r * (r / ‖w‖) = 1 by field_simp, one_smul]
      _ = (‖w‖ / r) • ((r / ‖z‖) • z) := by rw [h]
      _ = (‖w‖ / ‖z‖) • z := by
          rw [smul_smul, show ‖w‖ / r * (r / ‖z‖) = ‖w‖ / ‖z‖ by field_simp]
  have hgw : triGauge_FIX w = ‖w‖ / ‖z‖ * r := by
    conv_lhs => rw [hc]
    exact triGauge_smul_FIX (div_nonneg hwn.le hzn.le) z
  have hone : ‖w‖ / ‖z‖ = 1 := by
    have : r = ‖w‖ / ‖z‖ * r := hgn.trans hgw
    have h2 : (‖w‖ / ‖z‖ - 1) * r = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hr.ne'
  rw [hone, one_smul] at hc
  exact hc.symm

theorem radialGrid_mapsTo_FIX :
    MapsTo radialGrid_FIX {z | triGauge_FIX z ≤ 1} (closedBall (0 : ℂ) 1) := by
  intro z hz
  rw [mem_closedBall, dist_zero_right, norm_radialGrid_FIX]
  exact hz

theorem radialGrid_surjOn_FIX :
    SurjOn radialGrid_FIX {z | triGauge_FIX z ≤ 1} (closedBall (0 : ℂ) 1) := by
  intro u hu
  rw [mem_closedBall, dist_zero_right] at hu
  by_cases h0 : u = 0
  · subst h0
    exact ⟨0, by simp [triGauge_zero_FIX], radialGrid_zero_FIX⟩
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr h0
  have hgu : 0 < triGauge_FIX u := triGauge_pos_FIX h0
  have hgz : triGauge_FIX ((‖u‖ / triGauge_FIX u) • u) = ‖u‖ := by
    rw [triGauge_smul_FIX (div_nonneg hun.le hgu.le)]
    field_simp
  refine ⟨(‖u‖ / triGauge_FIX u) • u, by rw [mem_ofPred_eq, hgz]; exact hu, ?_⟩
  rw [radialGrid_FIX, hgz, norm_smul, Real.norm_of_nonneg (div_nonneg hun.le hgu.le), smul_smul]
  rw [show ‖u‖ / (‖u‖ / triGauge_FIX u * ‖u‖) * (‖u‖ / triGauge_FIX u) = 1 by field_simp,
    one_smul]


theorem norm_radialGrid_sub_le_aux_FIX {z w : ℂ} (h : ‖w‖ ≤ ‖z‖) :
    ‖radialGrid_FIX z - radialGrid_FIX w‖ ≤ 6 * ‖z - w‖ := by
  have hn := norm_nonneg (z - w)
  by_cases hz : z = 0
  · have : w = 0 := by
      rw [hz, norm_zero] at h
      exact norm_le_zero_iff.mp h
    rw [hz, this]; simp
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases hw : w = 0
  · rw [hw, radialGrid_zero_FIX, sub_zero, norm_radialGrid_FIX, sub_zero]
    have := triGauge_le_FIX z
    linarith
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set gz := triGauge_FIX z
  set gw := triGauge_FIX w
  have hdec : radialGrid_FIX z - radialGrid_FIX w =
      (gz / ‖z‖) • (z - w) + (gz / ‖z‖ - gw / ‖w‖) • w := by
    simp only [radialGrid_FIX, smul_sub, sub_smul]
    abel
  have hgz : gz ≤ 2 * ‖z‖ := triGauge_le_FIX z
  have hgw : gw ≤ 2 * ‖w‖ := triGauge_le_FIX w
  have hgz0 : 0 ≤ gz := triGauge_nonneg_FIX z
  have hgw0 : 0 ≤ gw := triGauge_nonneg_FIX w
  have hdiff : |gz - gw| ≤ 2 * ‖z - w‖ := abs_triGauge_sub_le_FIX z w
  have hnorm : |‖w‖ - ‖z‖| ≤ ‖z - w‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le z w
  have h1 : ‖(gz / ‖z‖) • (z - w)‖ ≤ 2 * ‖z - w‖ := by
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hgz0 hzn.le)]
    have : gz / ‖z‖ ≤ 2 := by rw [div_le_iff₀ hzn]; linarith
    exact mul_le_mul_of_nonneg_right this hn
  have h2 : ‖(gz / ‖z‖ - gw / ‖w‖) • w‖ ≤ 4 * ‖z - w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hkey : (gz / ‖z‖ - gw / ‖w‖) * ‖w‖ = (gz * ‖w‖ - gw * ‖z‖) / ‖z‖ := by
      field_simp
    rw [show |gz / ‖z‖ - gw / ‖w‖| * ‖w‖ = |(gz / ‖z‖ - gw / ‖w‖) * ‖w‖| by
      rw [abs_mul, abs_of_pos hwn], hkey, abs_div, abs_of_pos hzn, div_le_iff₀ hzn]
    have hsplit : gz * ‖w‖ - gw * ‖z‖ = (gz - gw) * ‖w‖ + gw * (‖w‖ - ‖z‖) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hwn.le, abs_of_nonneg hgw0]
    have e1 : |gz - gw| * ‖w‖ ≤ 2 * ‖z - w‖ * ‖z‖ :=
      mul_le_mul hdiff h (norm_nonneg w) (by positivity)
    have e2 : gw * |‖w‖ - ‖z‖| ≤ 2 * ‖w‖ * ‖z - w‖ :=
      mul_le_mul hgw hnorm (abs_nonneg _) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h hn]
  rw [hdec]
  exact (norm_add_le _ _).trans (by linarith)

theorem norm_radialGrid_sub_le_FIX (z w : ℂ) :
    ‖radialGrid_FIX z - radialGrid_FIX w‖ ≤ 6 * ‖z - w‖ := by
  rcases le_total ‖w‖ ‖z‖ with h | h
  · exact norm_radialGrid_sub_le_aux_FIX h
  · rw [norm_sub_rev, norm_sub_rev z w]
    exact norm_radialGrid_sub_le_aux_FIX h

theorem radialGrid_lipschitz_FIX : LipschitzWith 6 radialGrid_FIX :=
  LipschitzWith.of_dist_le_mul fun z w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact_mod_cast norm_radialGrid_sub_le_FIX z w


/-! ## 扇区公式 `ψ_ℓ z = (ℓ z / ‖z‖) • z` 及其左逆 `χ_ℓ w = (‖w‖ / ℓ w) • w` -/

/-- 扇区上的公式 `ψ_ℓ z = (ℓ z / ‖z‖) • z`。 -/
def sectorMap_FIX (ℓ : ℂ →L[ℝ] ℝ) (z : ℂ) : ℂ := (ℓ z / ‖z‖) • z

/-- 左逆 `χ_ℓ w = (‖w‖ / ℓ w) • w`。 -/
def sectorInv_FIX (ℓ : ℂ →L[ℝ] ℝ) (w : ℂ) : ℂ := (‖w‖ / ℓ w) • w

theorem contDiffAt_sectorMap_FIX (ℓ : ℂ →L[ℝ] ℝ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (sectorMap_FIX ℓ) z := by
  unfold sectorMap_FIX
  exact ((ℓ.contDiff.contDiffAt).div (contDiffAt_norm ℝ hz) (norm_ne_zero_iff.mpr hz)).smul
    contDiffAt_id

theorem contDiffOn_sectorMap_FIX (ℓ : ℂ →L[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (sectorMap_FIX ℓ) {z : ℂ | z ≠ 0} :=
  fun _ hz => (contDiffAt_sectorMap_FIX ℓ hz).contDiffWithinAt

theorem contDiffAt_sectorInv_FIX (ℓ : ℂ →L[ℝ] ℝ) {w : ℂ} (hw : w ≠ 0) (hℓ : ℓ w ≠ 0) :
    ContDiffAt ℝ ∞ (sectorInv_FIX ℓ) w := by
  unfold sectorInv_FIX
  exact ((contDiffAt_norm ℝ hw).div ℓ.contDiff.contDiffAt hℓ).smul contDiffAt_id

theorem sectorInv_sectorMap_FIX (ℓ : ℂ →L[ℝ] ℝ) {z : ℂ} (hz : 0 < ℓ z) :
    sectorInv_FIX ℓ (sectorMap_FIX ℓ z) = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hℓψ : ℓ (sectorMap_FIX ℓ z) = ℓ z / ‖z‖ * ℓ z := by
    rw [sectorMap_FIX, map_smul, smul_eq_mul]
  have hnψ : ‖sectorMap_FIX ℓ z‖ = ℓ z := by
    rw [sectorMap_FIX, norm_smul, Real.norm_of_nonneg (div_nonneg hz.le hzn.le)]
    field_simp
  unfold sectorInv_FIX
  rw [hnψ, hℓψ, sectorMap_FIX, smul_smul]
  rw [show ℓ z / (ℓ z / ‖z‖ * ℓ z) * (ℓ z / ‖z‖) = 1 by field_simp, one_smul]

theorem injective_fderiv_sectorMap_FIX (ℓ : ℂ →L[ℝ] ℝ) {z : ℂ} (hz : 0 < ℓ z) :
    Function.Injective (fderiv ℝ (sectorMap_FIX ℓ) z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hψ := contDiffAt_sectorMap_FIX ℓ hz0
  have hℓψ : 0 < ℓ (sectorMap_FIX ℓ z) := by
    have : ℓ (sectorMap_FIX ℓ z) = ℓ z / ‖z‖ * ℓ z := by
      rw [sectorMap_FIX, map_smul, smul_eq_mul]
    rw [this]; positivity
  have hψ0 : sectorMap_FIX ℓ z ≠ 0 := by intro h; rw [h] at hℓψ; simp at hℓψ
  have hχ := contDiffAt_sectorInv_FIX ℓ hψ0 hℓψ.ne'
  have hev : (sectorInv_FIX ℓ ∘ sectorMap_FIX ℓ) =ᶠ[𝓝 z] id := by
    have hopen : IsOpen {z' : ℂ | 0 < ℓ z'} := isOpen_lt continuous_const ℓ.continuous
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    exact sectorInv_sectorMap_FIX ℓ hz'
  have hcomp := fderiv_comp z (hχ.differentiableAt (by simp)) (hψ.differentiableAt (by simp))
  rw [hev.fderiv_eq, fderiv_id] at hcomp
  intro v₁ v₂ h
  have e1 : (ContinuousLinearMap.id ℝ ℂ) v₁ =
      (fderiv ℝ (sectorInv_FIX ℓ) (sectorMap_FIX ℓ z)) (fderiv ℝ (sectorMap_FIX ℓ) z v₁) := by
    rw [hcomp]; rfl
  have e2 : (ContinuousLinearMap.id ℝ ℂ) v₂ =
      (fderiv ℝ (sectorInv_FIX ℓ) (sectorMap_FIX ℓ z)) (fderiv ℝ (sectorMap_FIX ℓ) z v₂) := by
    rw [hcomp]; rfl
  rw [← h] at e2
  exact e1.trans e2.symm


/-- 一次齐次连续函数的 `{F ≤ 1}` 的 frontier 含 `{F = 1}`（沿射线外推）。 -/
theorem mem_frontier_sublevel_FIX {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : X → ℝ} (hF : Continuous F) (hhom : ∀ (t : ℝ) (x : X), 0 ≤ t → F (t • x) = t * F x)
    {x : X} (hx : F x = 1) : x ∈ frontier {y : X | F y ≤ 1} := by
  have hclosed : IsClosed {y : X | F y ≤ 1} := isClosed_le hF continuous_const
  refine ⟨subset_closure (show x ∈ {y : X | F y ≤ 1} from hx.le), fun hint => ?_⟩
  have hnhds : {y : X | F y ≤ 1} ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hint
  have hcont : ContinuousAt (fun t : ℝ => t • x) 1 :=
    (continuous_id.smul continuous_const).continuousAt
  have hpre : {t : ℝ | t • x ∈ {y : X | F y ≤ 1}} ∈ 𝓝 (1 : ℝ) :=
    hcont.preimage_mem_nhds (by simpa using hnhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : (1 + ε / 2) ∈ ball (1 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have h2 : F ((1 + ε / 2) • x) ≤ 1 := hball hmem
  rw [hhom _ _ (by linarith), hx] at h2
  linarith


theorem affineIndependent_triple_FIX {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    {a b c : E} (h : AffineIndependent ℝ ![a, b, c]) :
    AffineIndependent ℝ ((↑) : ({a, b, c} : Finset E) → E) := by
  have hinj : Function.Injective ![a, b, c] := h.injective
  let e : Fin 3 ≃ ({a, b, c} : Finset E) := Equiv.ofBijective
    (fun i => ⟨![a, b, c] i, by fin_cases i <;> simp⟩)
    ⟨fun i j hij => hinj (congrArg Subtype.val hij), fun x => by
      obtain ⟨x, hx⟩ := x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]⟩
  have : ((↑) : ({a, b, c} : Finset E) → E) ∘ e = ![a, b, c] := by
    ext i; fin_cases i <;> rfl
  rw [← this] at h
  exact (affineIndependent_equiv e).mp h

/-- 三个顶点：`Δ` 的重心在原点。 -/
def triV1_FIX : ℂ := ⟨-1, -1⟩
def triV2_FIX : ℂ := ⟨2, -1⟩
def triV3_FIX : ℂ := ⟨-1, 2⟩

def triVerts_FIX : Finset ℂ := {triV1_FIX, triV2_FIX, triV3_FIX}

theorem triVerts_indep_FIX : AffineIndependent ℝ ((↑) : triVerts_FIX → ℂ) := by
  refine affineIndependent_triple_FIX ?_
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  simp only [Fin.sum_univ_three] at hw hv
  have h1 := congrArg Complex.re hv
  have h2 := congrArg Complex.im hv
  simp [triV1_FIX, triV2_FIX, triV3_FIX] at h1 h2
  intro i
  fin_cases i <;> simp <;> linarith


theorem triVerts_card_FIX : triVerts_FIX.card = 3 := by
  have h12 : triV1_FIX ≠ triV2_FIX := by
    intro h; have := congrArg Complex.re h; norm_num [triV1_FIX, triV2_FIX] at this
  have h13 : triV1_FIX ≠ triV3_FIX := by
    intro h; have := congrArg Complex.im h; norm_num [triV1_FIX, triV3_FIX] at this
  have h23 : triV2_FIX ≠ triV3_FIX := by
    intro h; have := congrArg Complex.re h; norm_num [triV2_FIX, triV3_FIX] at this
  exact Finset.card_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩

theorem triGauge_V1_FIX : triGauge_FIX triV1_FIX = 1 := by norm_num [triGauge_FIX, triV1_FIX]
theorem triGauge_V2_FIX : triGauge_FIX triV2_FIX = 1 := by norm_num [triGauge_FIX, triV2_FIX]
theorem triGauge_V3_FIX : triGauge_FIX triV3_FIX = 1 := by norm_num [triGauge_FIX, triV3_FIX]

theorem convex_triSet_FIX : Convex ℝ {z : ℂ | triGauge_FIX z ≤ 1} := by
  intro x hx y hy a b ha hb hab
  rw [mem_ofPred_eq] at hx hy ⊢
  unfold triGauge_FIX at hx hy ⊢
  simp only [max_le_iff] at hx hy ⊢
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb,
      mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb,
      mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]

theorem convexHull_triVerts_FIX :
    convexHull ℝ (triVerts_FIX : Set ℂ) = {z | triGauge_FIX z ≤ 1} := by
  apply Subset.antisymm
  · apply convexHull_min _ convex_triSet_FIX
    intro v hv
    simp only [triVerts_FIX, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
      mem_singleton_iff] at hv
    rw [mem_ofPred_eq]
    rcases hv with rfl | rfl | rfl
    exacts [triGauge_V1_FIX.le, triGauge_V2_FIX.le, triGauge_V3_FIX.le]
  · intro z hz
    rw [mem_ofPred_eq] at hz
    have h1 : -z.re ≤ 1 := (triGauge_ge_re_FIX z).trans hz
    have h2 : -z.im ≤ 1 := (triGauge_ge_im_FIX z).trans hz
    have h3 : z.re + z.im ≤ 1 := (triGauge_ge_sum_FIX z).trans hz
    have h12 : triV1_FIX ≠ triV2_FIX := by
      intro h; have := congrArg Complex.re h; norm_num [triV1_FIX, triV2_FIX] at this
    have h13 : triV1_FIX ≠ triV3_FIX := by
      intro h; have := congrArg Complex.im h; norm_num [triV1_FIX, triV3_FIX] at this
    have h23 : triV2_FIX ≠ triV3_FIX := by
      intro h; have := congrArg Complex.re h; norm_num [triV2_FIX, triV3_FIX] at this
    let w : ℂ → ℝ := fun v => if v = triV1_FIX then (1 - z.re - z.im) / 3 else
      if v = triV2_FIX then (1 + z.re) / 3 else (1 + z.im) / 3
    have w1 : w triV1_FIX = (1 - z.re - z.im) / 3 := by simp [w]
    have w2 : w triV2_FIX = (1 + z.re) / 3 := by simp [w, h12.symm]
    have w3 : w triV3_FIX = (1 + z.im) / 3 := by simp [w, h13.symm, h23.symm]
    rw [mem_convexHull_iff_exists_weights]
    refine ⟨w, ?_, ?_, ?_⟩
    · intro v _
      simp only [w]
      split_ifs <;> linarith
    · rw [triVerts_FIX, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
        Finset.sum_singleton, w1, w2, w3]
      ring
    · rw [triVerts_FIX, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
        Finset.sum_singleton, w1, w2, w3]
      refine Complex.ext ?_ ?_
      · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, triV1_FIX, triV2_FIX, triV3_FIX]
        ring
      · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, triV1_FIX, triV2_FIX, triV3_FIX]
        ring


/-- 三角形边界复形（三条边 + 三个顶点）。 -/
def triBoundary_FIX : Geometry.SimplicialComplex ℝ ℂ :=
  simplexBoundary triVerts_FIX triVerts_indep_FIX

theorem frontier_triSet_FIX :
    frontier (convexHull ℝ (triVerts_FIX : Set ℂ)) = triBoundary_FIX.space :=
  frontier_convexHull_eq_simplexBoundary triVerts_indep_FIX
    (by rw [triVerts_card_FIX, Complex.finrank_real_complex])

theorem zero_mem_interior_triSet_FIX :
    (0 : ℂ) ∈ interior (convexHull ℝ (triVerts_FIX : Set ℂ)) := by
  rw [convexHull_triVerts_FIX]
  refine mem_interior.mpr ⟨ball 0 (1 / 2), fun z hz => ?_, isOpen_ball, mem_ball_self (by norm_num)⟩
  rw [mem_ball, dist_zero_right] at hz
  rw [mem_ofPred_eq]
  have := triGauge_le_FIX z
  linarith

theorem isConeBase_tri_FIX : IsConeBase (0 : ℂ) triBoundary_FIX :=
  isConeBase_of_space_subset_frontier_convex (convex_convexHull ℝ _)
    (triVerts_FIX.finite_toSet.isCompact_convexHull ℝ).isClosed zero_mem_interior_triSet_FIX _
    frontier_triSet_FIX.ge

/-- source 复形 `T`：以原点为中心、对三角形 `Δ` 的边界做 cone 的三三角形剖分。 -/
def triComplex_FIX : Geometry.SimplicialComplex ℝ ℂ := coneComplex isConeBase_tri_FIX

theorem triComplex_space_FIX : triComplex_FIX.space = {z : ℂ | triGauge_FIX z ≤ 1} := by
  rw [← convexHull_triVerts_FIX]
  exact coneComplex_space_eq_of_convex (convex_convexHull ℝ _)
    (triVerts_FIX.finite_toSet.isCompact_convexHull ℝ)
    (interior_subset zero_mem_interior_triSet_FIX) isConeBase_tri_FIX frontier_triSet_FIX.symm

theorem triComplex_faces_finite_FIX : triComplex_FIX.faces.Finite :=
  coneComplex_faces_finite _ (simplexBoundary_faces_finite _ _)

theorem triComplex_face_card_three_FIX {s : Finset ℂ} (hs : s ∈ triComplex_FIX.faces)
    (hc : s.card = 3) : ∃ σ ∈ triBoundary_FIX.faces, s = insert 0 σ := by
  rcases (mem_coneComplex_faces_iff isConeBase_tri_FIX).mp hs with h | h | ⟨σ, hσ, hs⟩
  · exfalso
    have hlt : s.card < triVerts_FIX.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h.1, h.2.2⟩)
    rw [triVerts_card_FIX] at hlt
    omega
  · rw [h] at hc; simp at hc
  · exact ⟨σ, hσ, hs⟩


theorem triGauge_convex_FIX {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : ℂ) :
    triGauge_FIX (a • x + b • y) ≤ a * triGauge_FIX x + b * triGauge_FIX y := by
  have hx1 := triGauge_ge_re_FIX x
  have hx2 := triGauge_ge_im_FIX x
  have hx3 := triGauge_ge_sum_FIX x
  have hy1 := triGauge_ge_re_FIX y
  have hy2 := triGauge_ge_im_FIX y
  have hy3 := triGauge_ge_sum_FIX y
  unfold triGauge_FIX
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  unfold triGauge_FIX at hx1 hx2 hx3 hy1 hy2 hy3
  refine max_le (max_le ?_ ?_) ?_ <;>
    nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb,
      mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb,
      mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]

/-- 在以 `s` 为顶点集的扇区上，`g` 等于线性泛函 `ℓ`（`ℓ ≤ g` 处处成立，顶点上取等）。 -/
theorem triGauge_eq_on_hull_FIX {s : Finset ℂ} {ℓ : ℂ →L[ℝ] ℝ}
    (hle : ∀ z, ℓ z ≤ triGauge_FIX z) (hv : ∀ v ∈ s, triGauge_FIX v = ℓ v) :
    ∀ z ∈ convexHull ℝ (s : Set ℂ), triGauge_FIX z = ℓ z := by
  have hsub : convexHull ℝ (s : Set ℂ) ⊆ {z | triGauge_FIX z ≤ ℓ z} := by
    refine convexHull_min (fun v hv' => ?_) ?_
    · rw [mem_ofPred_eq]; exact (hv v hv').le
    · intro x hx y hy a b ha hb hab
      rw [mem_ofPred_eq] at hx hy ⊢
      refine (triGauge_convex_FIX ha hb x y).trans ?_
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  intro z hz
  exact le_antisymm (hsub hz) (hle z)

theorem triFace_sector_FIX {σ : Finset ℂ} (hσ : σ ∈ triBoundary_FIX.faces) :
    ∃ ℓ : ℂ →L[ℝ] ℝ, (∀ z, ℓ z ≤ triGauge_FIX z) ∧
      ∀ v ∈ insert (0 : ℂ) σ, triGauge_FIX v = ℓ v := by
  obtain ⟨hsub, -, hneq⟩ := hσ
  obtain ⟨m, hmΔ, hmσ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneq⟩)
  have hσv : ∀ v ∈ σ, v ≠ m ∧ (v = triV1_FIX ∨ v = triV2_FIX ∨ v = triV3_FIX) := by
    intro v hv
    refine ⟨fun h => hmσ (h ▸ hv), ?_⟩
    simpa [triVerts_FIX] using hsub hv
  have hm : m = triV1_FIX ∨ m = triV2_FIX ∨ m = triV3_FIX := by simpa [triVerts_FIX] using hmΔ
  rcases hm with rfl | rfl | rfl
  · refine ⟨Complex.reCLM + Complex.imCLM, fun z => ?_, ?_⟩
    · simpa using triGauge_ge_sum_FIX z
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp [triGauge_zero_FIX]
      · obtain ⟨hne, hcases⟩ := hσv v hv
        rcases hcases with rfl | rfl | rfl
        · exact absurd rfl hne
        · rw [triGauge_V2_FIX]; norm_num [triV2_FIX]
        · rw [triGauge_V3_FIX]; norm_num [triV3_FIX]
  · refine ⟨-Complex.reCLM, fun z => ?_, ?_⟩
    · simpa using triGauge_ge_re_FIX z
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp [triGauge_zero_FIX]
      · obtain ⟨hne, hcases⟩ := hσv v hv
        rcases hcases with rfl | rfl | rfl
        · rw [triGauge_V1_FIX]; norm_num [triV1_FIX]
        · exact absurd rfl hne
        · rw [triGauge_V3_FIX]; norm_num [triV3_FIX]
  · refine ⟨-Complex.imCLM, fun z => ?_, ?_⟩
    · simpa using triGauge_ge_im_FIX z
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp [triGauge_zero_FIX]
      · obtain ⟨hne, hcases⟩ := hσv v hv
        rcases hcases with rfl | rfl | rfl
        · rw [triGauge_V1_FIX]; norm_num [triV1_FIX]
        · rw [triGauge_V2_FIX]; norm_num [triV2_FIX]
        · exact absurd rfl hne


/-! ## `α` 的字段（对 `T = triComplex_FIX`） -/

theorem triComplex_dim_le_FIX : ∀ s ∈ triComplex_FIX.faces, s.card ≤ 3 := by
  intro s hs
  have h := (triComplex_FIX.indep hs).card_le_finrank_succ
  have h2 := (Submodule.finrank_le (vectorSpan ℝ (range ((↑) : s → ℂ)))).trans_eq
    Complex.finrank_real_complex
  rw [Fintype.card_coe] at h
  omega

theorem radialGrid_bijOn_FIX :
    BijOn radialGrid_FIX triComplex_FIX.space (closedBall (0 : ℂ) 1) := by
  rw [triComplex_space_FIX]
  exact ⟨radialGrid_mapsTo_FIX, radialGrid_injective_FIX.injOn, radialGrid_surjOn_FIX⟩

theorem radialGrid_continuous_FIX : Continuous radialGrid_FIX :=
  radialGrid_lipschitz_FIX.continuous

theorem frontier_triSet_eq_FIX :
    frontier {z : ℂ | triGauge_FIX z ≤ 1} = {z : ℂ | triGauge_FIX z = 1} :=
  Subset.antisymm (frontier_le_subset_eq continuous_triGauge_FIX continuous_const) fun _ hz =>
    mem_frontier_sublevel_FIX continuous_triGauge_FIX (fun _ z ht => triGauge_smul_FIX ht z) hz

theorem radialGrid_bdry_FIX :
    ∀ {z : ℂ}, z ∈ triComplex_FIX.space →
      (‖radialGrid_FIX z‖ = 1 ↔ z ∈ frontier triComplex_FIX.space) := by
  intro z _
  rw [triComplex_space_FIX, frontier_triSet_eq_FIX, norm_radialGrid_FIX, mem_ofPred_eq]

theorem radialGrid_lip_FIX : ∃ L : NNReal, LipschitzOnWith L radialGrid_FIX triComplex_FIX.space :=
  ⟨6, radialGrid_lipschitz_FIX.lipschitzOnWith⟩

theorem uniqueDiffOn_hull_face_FIX {s : Finset ℂ} (hs : s ∈ triComplex_FIX.faces)
    (hc : s.card = 3) : UniqueDiffOn ℝ (convexHull ℝ (s : Set ℂ)) := by
  refine uniqueDiffOn_convex (convex_convexHull ℝ _) ?_
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
  have h := (triComplex_FIX.indep hs).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    (by rw [Fintype.card_coe, hc, Complex.finrank_real_complex])
  simpa using h


theorem radialGrid_eqOn_sector_FIX {s : Finset ℂ} {ℓ : ℂ →L[ℝ] ℝ}
    (hle : ∀ z, ℓ z ≤ triGauge_FIX z) (hv : ∀ v ∈ s, triGauge_FIX v = ℓ v) :
    EqOn radialGrid_FIX (sectorMap_FIX ℓ) (convexHull ℝ (s : Set ℂ)) := fun z hz => by
  rw [radialGrid_FIX, sectorMap_FIX, triGauge_eq_on_hull_FIX hle hv z hz]

theorem face_sector_data_FIX {s : Finset ℂ} (hs : s ∈ triComplex_FIX.faces) (hc : s.card = 3) :
    (0 : ℂ) ∈ s ∧ ∃ ℓ : ℂ →L[ℝ] ℝ, (∀ z, ℓ z ≤ triGauge_FIX z) ∧
      ∀ v ∈ s, triGauge_FIX v = ℓ v := by
  obtain ⟨σ, hσ, rfl⟩ := triComplex_face_card_three_FIX hs hc
  exact ⟨Finset.mem_insert_self _ _, triFace_sector_FIX hσ⟩

theorem radialGrid_smooth_FIX : ∀ s ∈ triComplex_FIX.faces, s.card = 3 →
    ContDiffOn ℝ ∞ radialGrid_FIX (convexHull ℝ (s : Set ℂ) \ (s : Set ℂ)) := by
  intro s hs hc
  obtain ⟨h0, ℓ, hle, hv⟩ := face_sector_data_FIX hs hc
  refine ((contDiffOn_sectorMap_FIX ℓ).mono ?_).congr ?_
  · rintro z ⟨-, hzs⟩ rfl
    exact hzs h0
  · intro z hz
    exact radialGrid_eqOn_sector_FIX hle hv hz.1

theorem radialGrid_rank_FIX : ∀ s ∈ triComplex_FIX.faces, s.card = 3 →
    ∀ z ∈ convexHull ℝ (s : Set ℂ) \ (s : Set ℂ),
      Function.Injective (fderivWithin ℝ radialGrid_FIX (convexHull ℝ (s : Set ℂ)) z) := by
  intro s hs hc z hz
  obtain ⟨h0, ℓ, hle, hv⟩ := face_sector_data_FIX hs hc
  have hz0 : z ≠ 0 := fun h => hz.2 (h ▸ h0)
  have hℓz : 0 < ℓ z := (triGauge_eq_on_hull_FIX hle hv z hz.1) ▸ triGauge_pos_FIX hz0
  have heq := radialGrid_eqOn_sector_FIX hle hv
  rw [fderivWithin_congr heq (heq hz.1),
    DifferentiableAt.fderivWithin ((contDiffAt_sectorMap_FIX ℓ hz0).differentiableAt (by simp))
      (uniqueDiffOn_hull_face_FIX hs hc z hz.1)]
  exact injective_fderiv_sectorMap_FIX ℓ hℓz


end DifferentialGeometry.Geometry
