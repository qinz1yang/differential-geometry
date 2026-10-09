import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk

/-!
# O-MY-R5 G1：R5 三点归一（`u = q₂ ∘ mob ∨ u = q₂ ∘ mob ∘ conj` ⇒ `u = q₂`）

D-R-MY3-1：证明显式使用 `diskTrace q₂` 单射（`q₂(φ θⱼ) = q₂(θⱼ) ⇒ φ θⱼ = θⱼ`）。D-1 建议的 cyclic order 论证
由更强的**二次方程根数**取代：单位圆上 Möbius `z ↦ c (z − a) / (1 − ā z)` 的不动点方程是
`ā z² + (c − 1) z − c a = 0`，反共形重参数化 `z ↦ c (z̄ − a) / (1 − ā z̄)` 的是 `z² + (c a − ā) z − c = 0`
（首项 1）。三个不同根 ⇒ 系数全 0 ⇒ 保向分支 `a = 0, c = 1`（= id），反向分支矛盾——即"保向固定三点 ⇒ id，
反向不能固定三个不同点"。本文件纯代数 + 圆周拓扑，target 是任意拓扑空间。
-/

set_option autoImplicit false
noncomputable section

open Set Function ComplexConjugate
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

/-- 盘的共形自同构 `z ↦ c (z − a) / (1 − ā z)`（`‖a‖ < 1`，`‖c‖ = 1` 时）；与 scratch `diskMobius_MYD3` 同式。 -/
def diskMobius_R5 (a c : ℂ) (z : ℂ) : ℂ := c * (z - a) / (1 - conj a * z)

/-- `‖a‖ < 1`、`‖z‖ ≤ 1` ⇒ Möbius 分母非零。 -/
theorem one_sub_conj_mul_ne_zero_R5 {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  intro h
  have h1 : conj a * z = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ < 1 := by simpa using ha
  rw [h1, norm_one] at hn
  exact lt_irrefl 1 hn

/-- 单位圆上 `z z̄ = 1`。 -/
theorem conj_mul_self_of_norm_eq_one_R5 {z : ℂ} (hz : ‖z‖ = 1) : conj z * z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- 单位圆上 `‖1 − ā z‖ = ‖z − a‖`。 -/
theorem norm_one_sub_conj_mul_R5 {a z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - conj a * z‖ = ‖z - a‖ := by
  have hzz := conj_mul_self_of_norm_eq_one_R5 hz
  have hfac : 1 - conj a * z = z * conj (z - a) := by
    rw [map_sub, mul_sub, mul_comm z (conj z), hzz, mul_comm z (conj a)]
  rw [hfac, norm_mul, Complex.norm_conj, hz, one_mul]

/-- Möbius 把单位圆映到单位圆。 -/
theorem norm_diskMobius_R5 {a c z : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1) (hz : ‖z‖ = 1) :
    ‖diskMobius_R5 a c z‖ = 1 := by
  have hden := one_sub_conj_mul_ne_zero_R5 ha hz.le
  have hza : ‖z - a‖ ≠ 0 := by
    rw [← norm_one_sub_conj_mul_R5 hz]
    exact norm_ne_zero_iff.mpr hden
  unfold diskMobius_R5
  rw [norm_div, norm_mul, hc, one_mul, norm_one_sub_conj_mul_R5 hz]
  exact div_self hza

/-- 二次方程三个不同根 ⇒ 系数全为 0。 -/
theorem quadratic_coeff_eq_zero_of_three_roots_R5 {α β γ : ℂ} {z : Fin 3 → ℂ}
    (hz : Injective z) (h : ∀ j, α * z j ^ 2 + β * z j + γ = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have h01 : z 0 - z 1 ≠ 0 := sub_ne_zero.mpr (hz.ne (by decide))
  have h02 : z 0 - z 2 ≠ 0 := sub_ne_zero.mpr (hz.ne (by decide))
  have h12 : z 1 - z 2 ≠ 0 := sub_ne_zero.mpr (hz.ne (by decide))
  have e01 : (z 0 - z 1) * (α * (z 0 + z 1) + β) = 0 := by
    linear_combination h 0 - h 1
  have e02 : (z 0 - z 2) * (α * (z 0 + z 2) + β) = 0 := by
    linear_combination h 0 - h 2
  have s01 := (mul_eq_zero.mp e01).resolve_left h01
  have s02 := (mul_eq_zero.mp e02).resolve_left h02
  have hα : α = 0 := by
    have e : (z 1 - z 2) * α = 0 := by linear_combination s01 - s02
    exact (mul_eq_zero.mp e).resolve_left h12
  have hβ : β = 0 := by
    have e := s01
    rw [hα, zero_mul, zero_add] at e
    exact e
  refine ⟨hα, hβ, ?_⟩
  have e := h 0
  rw [hα, hβ, zero_mul, zero_mul, zero_add, zero_add] at e
  exact e

/-- 保向不动点方程：`‖z‖ = 1` 且 `mob z = z` ⇒ `ā z² + (c − 1) z − c a = 0`。 -/
theorem diskMobius_fixed_quadratic_R5 {a c z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1)
    (hfix : diskMobius_R5 a c z = z) :
    conj a * z ^ 2 + (c - 1) * z + -(c * a) = 0 := by
  have hden := one_sub_conj_mul_ne_zero_R5 ha hz.le
  unfold diskMobius_R5 at hfix
  rw [div_eq_iff hden] at hfix
  linear_combination hfix

/-- 反向不动点方程：`‖z‖ = 1` 且 `mob z̄ = z` ⇒ `z² + (c a − ā) z − c = 0`。 -/
theorem diskMobius_conj_fixed_quadratic_R5 {a c z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1)
    (hfix : diskMobius_R5 a c (conj z) = z) :
    1 * z ^ 2 + (c * a - conj a) * z + -c = 0 := by
  have hz' : ‖conj z‖ = 1 := by rw [Complex.norm_conj, hz]
  have hden := one_sub_conj_mul_ne_zero_R5 ha hz'.le
  have hzz := conj_mul_self_of_norm_eq_one_R5 hz
  unfold diskMobius_R5 at hfix
  rw [div_eq_iff hden] at hfix
  linear_combination (-z) * hfix + (c + conj a * z) * hzz

/-- 单位圆上的点都是某个 `diskBoundary θ`。 -/
theorem exists_diskBoundary_coe_eq_R5 {w : ℂ} (hw : ‖w‖ = 1) :
    ∃ θ : loopCircle, (diskBoundary θ : ℂ) = w := by
  let c : Circle := ⟨w, mem_sphere_zero_iff_norm.mpr hw⟩
  obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  refine ⟨θ, ?_⟩
  have hc := congrArg (fun v : Circle => (v : ℂ)) hθ
  simp only [AddCircle.homeomorphCircle_apply] at hc
  change ((AddCircle.toCircle θ : Circle) : ℂ) = w
  exact hc

/-- `diskBoundary` 在 `ℂ` 中单射。 -/
theorem diskBoundary_coe_injective_R5 : Injective (fun θ : loopCircle => (diskBoundary θ : ℂ)) := by
  intro θ θ' h
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  exact Subtype.ext h

/-- `diskBoundary` 点的范数为 1。 -/
theorem norm_diskBoundary_R5 (θ : loopCircle) : ‖(diskBoundary θ : ℂ)‖ = 1 := by
  change ‖((AddCircle.toCircle θ : Circle) : ℂ)‖ = 1
  exact Circle.norm_coe _

/-- 边界标记点的 rigidity：`diskTrace q₂` 单射，`w` 在单位圆上，`q₂ w = diskTrace q₂ θ` ⇒ `w = ∂θ`。 -/
theorem eq_diskBoundary_of_diskTrace_injective_R5 {Q : Type*} [TopologicalSpace Q]
    {q₂ : C(closedDisk, Q)} (hinj : Injective (diskTrace q₂)) {w : ℂ} (hw : ‖w‖ = 1)
    {θ : loopCircle} (hval : diskExtension q₂ w = diskTrace q₂ θ) :
    w = (diskBoundary θ : ℂ) := by
  obtain ⟨θ', hθ'⟩ := exists_diskBoundary_coe_eq_R5 hw
  have hmem : w ∈ closedDisk := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hw.le
  have hpt : (⟨w, hmem⟩ : closedDisk) = diskBoundary θ' := Subtype.ext hθ'.symm
  have hext : diskExtension q₂ w = q₂ (diskBoundary θ') := by
    rw [← hpt]
    exact diskExtension_coe q₂ ⟨w, hmem⟩
  have htr : diskTrace q₂ θ' = diskTrace q₂ θ := by
    rw [← hval, hext]
    rfl
  rw [← hθ', hinj htr]

/-- **G1（R5 三点归一）**：`diskTrace q₂` 单射；`u = q₂ ∘ mob` 或 `u = q₂ ∘ mob ∘ conj`；三个不同标记点上
`u` 与 `q₂` 的 trace 相同 ⇒ `u = q₂`。证明：`diskTrace q₂` 单射把三点钉成 `mob` 的不动点；不动点方程是
二次方程，三个不同根 ⇒ 保向分支 `a = 0, c = 1`、反向分支矛盾。 -/
theorem normalized_uniqueness_of_unique_up_to_mobius_R5 {Q : Type*} [TopologicalSpace Q]
    {q₂ u : C(closedDisk, Q)} (hinj : Injective (diskTrace q₂))
    (hmob : ∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧
      ((∀ z : closedDisk, u z = diskExtension q₂ (diskMobius_R5 a c z)) ∨
        (∀ z : closedDisk, u z = diskExtension q₂ (diskMobius_R5 a c (conj (z : ℂ))))))
    (θ : Fin 3 → loopCircle) (hθ : Injective θ)
    (hmark : ∀ j, diskTrace u (θ j) = diskTrace q₂ (θ j)) : u = q₂ := by
  obtain ⟨a, c, ha, hc, hbranch⟩ := hmob
  let e : Fin 3 → ℂ := fun j => (diskBoundary (θ j) : ℂ)
  have he : Injective e := diskBoundary_coe_injective_R5.comp hθ
  have hen : ∀ j, ‖e j‖ = 1 := fun j => norm_diskBoundary_R5 (θ j)
  rcases hbranch with hu | hu
  · -- 保向分支：三个不动点 ⇒ `a = 0`、`c = 1`
    have hfix : ∀ j, diskMobius_R5 a c (e j) = e j := by
      intro j
      have hval : diskExtension q₂ (diskMobius_R5 a c (e j)) = diskTrace q₂ (θ j) := by
        rw [← hmark j, ← hu (diskBoundary (θ j))]
        rfl
      exact eq_diskBoundary_of_diskTrace_injective_R5 hinj (norm_diskMobius_R5 ha hc (hen j)) hval
    obtain ⟨h2, h1, -⟩ := quadratic_coeff_eq_zero_of_three_roots_R5 he
      (fun j => diskMobius_fixed_quadratic_R5 ha (hen j) (hfix j))
    have ha0 : a = 0 := by simpa using h2
    have hc1 : c = 1 := sub_eq_zero.mp h1
    ext z
    rw [hu z, ha0, hc1]
    simp [diskMobius_R5]
  · -- 反共形分支：首项系数 1 ≠ 0，矛盾
    have hfix : ∀ j, diskMobius_R5 a c (conj (e j)) = e j := by
      intro j
      have hval : diskExtension q₂ (diskMobius_R5 a c (conj (e j))) = diskTrace q₂ (θ j) := by
        rw [← hmark j, ← hu (diskBoundary (θ j))]
        rfl
      have hn : ‖diskMobius_R5 a c (conj (e j))‖ = 1 :=
        norm_diskMobius_R5 ha hc (by rw [Complex.norm_conj, hen j])
      exact eq_diskBoundary_of_diskTrace_injective_R5 hinj hn hval
    obtain ⟨h2, -, -⟩ := quadratic_coeff_eq_zero_of_three_roots_R5 he
      (fun j => diskMobius_conj_fixed_quadratic_R5 ha (hen j) (hfix j))
    exact absurd h2 one_ne_zero

/-- consumer：Möbius 恒等分支（`a = 0, c = 1`）对任何三点标记都成立——G1 的结论在 `u := q₂` 时退化为 `rfl`。 -/
example {Q : Type*} [TopologicalSpace Q] {q₂ : C(closedDisk, Q)}
    (hinj : Injective (diskTrace q₂)) (θ : Fin 3 → loopCircle) (hθ : Injective θ) :
    q₂ = q₂ :=
  normalized_uniqueness_of_unique_up_to_mobius_R5 hinj
    ⟨0, 1, by simp, by simp, Or.inl fun z => by simp [diskMobius_R5]⟩ θ hθ (fun _ => rfl)

end DifferentialGeometry.Geometry
