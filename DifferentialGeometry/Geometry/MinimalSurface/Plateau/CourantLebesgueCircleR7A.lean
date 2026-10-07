import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Real
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.WeaklyMonotoneLimitR7A

/-!
# S-MY-R7A G2（一维部分）：三点归一 + weakly monotone once 边界参数化的 lift 增量 / 振幅

`increment_small_R7A`：`ψ` 单调、`+1` 周期，三个标记点的像（模 1）分离 `≥ g₀`、域内标记点分离 `≥ g₀`；
短区间端点像近 ⇒ lift 增量小（"长弧"一侧会塞进两个标记点的像）。
`wmo_oscillation_R7A`：`σ` weakly monotone once（单调或反单调 lift）+ 三点固定 ⇒ 短区间上 `σ` 的振幅
`≤ 2ε`（反单调情形取 `ψ ↦ −ψ`、标记点像取 `−x`）。纯圆周论证，不用 crosscut 拓扑。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

/-- `ψ (t + k) = ψ t + k`（整数 `k`）。 -/
theorem lift_add_int_R7A {ψ : ℝ → ℝ} (hψp : ∀ t, ψ (t + 1) = ψ t + 1) (t : ℝ) (k : ℤ) :
    ψ (t + k) = ψ t + k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    push_cast at ih ⊢
    rw [← add_assoc, hψp, ih]
    ring
  | pred n ih =>
    push_cast at ih ⊢
    have h := hψp (t + (-(n : ℝ) - 1))
    have h1 : t + (-(n : ℝ) - 1) + 1 = t + -(n : ℝ) := by ring
    rw [h1, ih] at h
    linarith

/-- **1D 引理**：`ψ` 单调、`+1` 周期，三个标记点的像（模 1）分离 `≥ g₀`，域内标记点分离 `≥ g₀`；
短区间 `[a, b]`（长 `< g₀`）的端点像在圆周上近（`< ε < g₀`）⇒ lift 增量 `ψ b − ψ a ≤ ε`（
只可能是"短弧"，不可能是"长弧"——长弧一侧会塞进两个标记点的像）。 -/
theorem increment_small_R7A {ψ : ℝ → ℝ} (hψm : Monotone ψ) (hψp : ∀ t, ψ (t + 1) = ψ t + 1)
    {x c : Fin 3 → ℝ} {g₀ : ℝ} (hg₀ : g₀ ≤ 1 / 4)
    (hx : ∀ i j, i ≠ j → ∀ m : ℤ, g₀ ≤ |x i - x j - m|)
    (hc : ∀ i j, i ≠ j → ∀ m : ℤ, g₀ ≤ |c i - c j - m|)
    (hmark : ∀ j, ∃ m : ℤ, ψ (x j) = c j + m)
    {a b ε : ℝ} (hab : a ≤ b) (hba : b - a < g₀) (hε : ε < g₀)
    (hclose : ∃ n : ℤ, |ψ b - ψ a - n| < ε) : ψ b - ψ a ≤ ε := by
  obtain ⟨n, hn⟩ := hclose
  have hε4 : ε < 1 / 4 := lt_of_lt_of_le hε hg₀
  have hl0 : 0 ≤ ψ b - ψ a := sub_nonneg.mpr (hψm hab)
  have hl1 : ψ b - ψ a ≤ 1 := by
    have : ψ b ≤ ψ (a + 1) := hψm (by linarith)
    rw [hψp] at this
    linarith
  have hn' := abs_lt.mp hn
  have hnlo : (-1 : ℝ) < n := by linarith [hn'.2]
  have hnhi : (n : ℝ) < 2 := by linarith [hn'.1]
  have hnZ : n = 0 ∨ n = 1 := by
    have h1 : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have h2 : n < 2 := by exact_mod_cast hnhi
    omega
  rcases hnZ with rfl | rfl
  · simp only [Int.cast_zero, sub_zero] at hn'
    linarith [hn'.2]
  · exfalso
    have hlam : 1 - ε < ψ b - ψ a := by
      have := hn'.1
      simp only [Int.cast_one] at this
      linarith
    -- 每个标记点在 `[a, a + 1)` 的代表
    let k : Fin 3 → ℤ := fun j => ⌈a - x j⌉
    let y : Fin 3 → ℝ := fun j => x j + k j
    have hya : ∀ j, a ≤ y j := fun j => by
      have := Int.le_ceil (a - x j)
      simp only [y, k]
      linarith
    have hya1 : ∀ j, y j < a + 1 := fun j => by
      have := Int.ceil_lt_add_one (a - x j)
      simp only [y, k]
      linarith
    have hψy : ∀ j, ∃ m : ℤ, ψ (y j) = c j + m := fun j => by
      obtain ⟨m, hm⟩ := hmark j
      exact ⟨m + k j, by simp only [y]; rw [lift_add_int_R7A hψp, hm]; push_cast; ring⟩
    have hysep : ∀ i j, i ≠ j → g₀ ≤ |y i - y j| := fun i j hij => by
      have := hx i j hij (-(k i - k j))
      simp only [y]
      convert this using 2
      push_cast
      ring
    -- 两个标记点同落在 `[a, b]`：不可能
    have hS : ∀ i j, i ≠ j → y i ≤ b → y j ≤ b → False := fun i j hij hi hj => by
      have h := hysep i j hij
      have h1 := hya i
      have h2 := hya j
      have : |y i - y j| ≤ b - a := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    -- 两个标记点同落在 `[b, a + 1)`：lift 增量 `≤ 1 − (ψ b − ψ a) < ε`，但像分离
    have hT : ∀ i j, i ≠ j → b ≤ y i → y i ≤ y j → False := fun i j hij hi hij' => by
      have h1 : ψ b ≤ ψ (y i) := hψm hi
      have h2 : ψ (y i) ≤ ψ (y j) := hψm hij'
      have h3 : ψ (y j) ≤ ψ a + 1 := by
        have := hψm (hya1 j).le
        rwa [hψp] at this
      obtain ⟨mi, hmi⟩ := hψy i
      obtain ⟨mj, hmj⟩ := hψy j
      have hsep := hc j i (Ne.symm hij) (mi - mj)
      have heq : c j - c i - ((mi - mj : ℤ) : ℝ) = ψ (y j) - ψ (y i) := by
        rw [hmi, hmj]
        push_cast
        ring
      rw [heq, abs_of_nonneg (by linarith)] at hsep
      linarith
    have hT' : ∀ i j, i ≠ j → b ≤ y i → b ≤ y j → False := fun i j hij hi hj => by
      rcases le_total (y i) (y j) with h | h
      · exact hT i j hij hi h
      · exact hT j i (Ne.symm hij) hj h
    rcases le_total (y 0) b with h0 | h0 <;> rcases le_total (y 1) b with h1 | h1 <;>
      rcases le_total (y 2) b with h2 | h2
    · exact hS 0 1 (by decide) h0 h1
    · exact hS 0 1 (by decide) h0 h1
    · exact hS 0 2 (by decide) h0 h2
    · exact hT' 1 2 (by decide) h1 h2
    · exact hS 1 2 (by decide) h1 h2
    · exact hT' 0 2 (by decide) h0 h2
    · exact hT' 0 1 (by decide) h0 h1
    · exact hT' 0 1 (by decide) h0 h1

/-- 圆周上相等的实数代表差整数。 -/
theorem exists_int_of_coe_eq_R7A {a b : ℝ} (h : (a : loopCircle) = (b : loopCircle)) :
    ∃ m : ℤ, b = a + m := by
  have h' := (QuotientAddGroup.eq (s := AddSubgroup.zmultiples (1 : ℝ))).mp h
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp h'
  exact ⟨m, by simp only [zsmul_eq_mul, mul_one] at hm; linarith⟩

/-- 圆周范数 `≤` 实数绝对值（对任意整数平移）。 -/
theorem norm_coe_le_abs_sub_int_R7A (r : ℝ) (m : ℤ) : ‖(r : loopCircle)‖ ≤ |r - m| := by
  have h : (r : loopCircle) = ((r - m : ℝ) : loopCircle) := by
    rw [AddCircle.coe_sub]
    have : ((m : ℝ) : loopCircle) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m, by simp⟩
    rw [this, sub_zero]
  rw [h]
  exact (QuotientAddGroup.norm_mk_le_norm (m := r - m)).trans (le_of_eq (Real.norm_eq_abs _))

theorem norm_coe_le_abs_R7A (r : ℝ) : ‖(r : loopCircle)‖ ≤ |r| := by
  simpa using norm_coe_le_abs_sub_int_R7A r 0

/-- **核心**：`σ` 的单调 lift `ψ`（`dist (σ x) (σ y) = ‖ψ y − ψ x‖`）+ 三点归一 + 短区间端点像近 ⇒
整个短区间上 `σ` 的振幅 `≤ 2 ε`。 -/
theorem equicontinuity_core_R7A {σ : C(loopCircle, loopCircle)} {ψ : ℝ → ℝ}
    (hψm : Monotone ψ) (hψp : ∀ t, ψ (t + 1) = ψ t + 1)
    (hdist : ∀ x y : ℝ, dist (σ (x : loopCircle)) (σ (y : loopCircle)) =
      ‖((ψ y - ψ x : ℝ) : loopCircle)‖)
    {x c : Fin 3 → ℝ} {g₀ : ℝ} (hg₀ : g₀ ≤ 1 / 4)
    (hx : ∀ i j, i ≠ j → ∀ m : ℤ, g₀ ≤ |x i - x j - m|)
    (hc : ∀ i j, i ≠ j → ∀ m : ℤ, g₀ ≤ |c i - c j - m|)
    (hmark : ∀ j, ∃ m : ℤ, ψ (x j) = c j + m)
    {a b ε : ℝ} (hab : a ≤ b) (hba : b - a < g₀) (hε : ε < g₀)
    (hclose : dist (σ (a : loopCircle)) (σ (b : loopCircle)) < ε) :
    ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b,
      dist (σ (t₁ : loopCircle)) (σ (t₂ : loopCircle)) ≤ 2 * ε := by
  rw [hdist] at hclose
  have hinc := increment_small_R7A hψm hψp hg₀ hx hc hmark hab hba hε
    (exists_int_abs_lt_of_norm_lt_R7A hclose)
  have hle : ∀ t ∈ Icc a b, dist (σ (a : loopCircle)) (σ (t : loopCircle)) ≤ ε := by
    intro t ht
    rw [hdist]
    refine (norm_coe_le_abs_R7A _).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr (hψm ht.1))]
    linarith [hψm ht.2]
  intro t₁ ht₁ t₂ ht₂
  calc dist (σ (t₁ : loopCircle)) (σ (t₂ : loopCircle))
      ≤ dist (σ (t₁ : loopCircle)) (σ (a : loopCircle)) +
        dist (σ (a : loopCircle)) (σ (t₂ : loopCircle)) := dist_triangle _ _ _
    _ ≤ ε + ε := by
      rw [dist_comm (σ (t₁ : loopCircle))]
      exact add_le_add (hle t₁ ht₁) (hle t₂ ht₂)
    _ = 2 * ε := by ring

/-- 圆周上两个实数代表的距离 = 差的圆周范数。 -/
theorem dist_coe_eq_norm_R7A (a b : ℝ) :
    dist (a : loopCircle) (b : loopCircle) = ‖((b - a : ℝ) : loopCircle)‖ := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, ← norm_neg, ← AddCircle.coe_neg]
  congr 2
  ring

/-- **WMO 振幅引理**（G2 一维部分）：`σ` weakly monotone once、三个标记点固定（模 1）、分离 `≥ g₀`；
短区间 `[a, b]`（长 `< g₀`）的端点像近（`< ε < g₀`）⇒ 区间上任两点像的距离 `≤ 2 ε`。 -/
theorem wmo_oscillation_R7A {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    {x : Fin 3 → ℝ} {g₀ : ℝ} (hg₀ : g₀ ≤ 1 / 4)
    (hx : ∀ i j, i ≠ j → ∀ m : ℤ, g₀ ≤ |x i - x j - m|)
    (hfix : ∀ j, σ ((x j : ℝ) : loopCircle) = ((x j : ℝ) : loopCircle))
    {a b ε : ℝ} (hab : a ≤ b) (hba : b - a < g₀) (hε : ε < g₀)
    (hclose : dist (σ (a : loopCircle)) (σ (b : loopCircle)) < ε) :
    ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b,
      dist (σ (t₁ : loopCircle)) (σ (t₂ : loopCircle)) ≤ 2 * ε := by
  obtain ⟨ψ, -, hψl, hsign⟩ := hσ
  have hdist : ∀ u v : ℝ, dist (σ (u : loopCircle)) (σ (v : loopCircle)) =
      ‖((ψ v - ψ u : ℝ) : loopCircle)‖ := by
    intro u v
    rw [← hψl u, ← hψl v, dist_coe_eq_norm_R7A]
  have hmark : ∀ j, ∃ m : ℤ, ψ (x j) = x j + m := by
    intro j
    have h := hψl (x j)
    rw [hfix j] at h
    obtain ⟨m, hm⟩ := exists_int_of_coe_eq_R7A h
    exact ⟨-m, by push_cast; linarith⟩
  rcases hsign with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · exact equicontinuity_core_R7A hm hp hdist hg₀ hx hx hmark hab hba hε hclose
  · refine equicontinuity_core_R7A (ψ := fun t => -ψ t) (c := fun j => -x j)
      (fun u v huv => neg_le_neg (hm huv)) (fun t => by simp only [hp]; ring) ?_ hg₀ hx ?_ ?_
      hab hba hε hclose
    · intro u v
      rw [hdist u v, ← norm_neg, ← AddCircle.coe_neg]
      congr 2
      ring
    · intro i j hij m
      have := hx i j hij (-m)
      rw [show -x i - -x j - (m : ℝ) = -(x i - x j - ((-m : ℤ) : ℝ)) by push_cast; ring, abs_neg]
      exact this
    · intro j
      obtain ⟨m, hm'⟩ := hmark j
      exact ⟨-m, by simp only [hm']; push_cast; ring⟩

end DifferentialGeometry.Geometry
