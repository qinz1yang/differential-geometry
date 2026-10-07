import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalArcsR3AW
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexCurve2FIX2

/-!
# S-MY-FIX2：S8 `IsCollisionNodal_FIX2` 与 S-MY-R3AW `IsNodalHalfArcsAt_R3AW` 的型对齐（`_FIX2`）

`IsNodalHalfArcsAt_R3AW O a w p` 的输出（Ico 版）给出 `V` 开、`2k` 条 `C¹` half-arcs，弧段数据
（`Γ m 0 = p`、`ContDiffOn ℝ 1`、`InjOn`、`HasDerivWithinAt`、`MapsTo (Ico 0 ρ) V`、
两两只在 `p` 相交）与零集覆盖 `w z = 0 ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z = Γ m r`，
正是 `IsCollisionNodal_FIX2` 的 Γ 部分（`V` 取代 `ball z ρ`，`w = 0` 取代"配对 sheet 的碰撞集"），
初始方向 `v m = T e^{iθ_m}` 两两不同射线（`θ_m = θ₀ + mπ/k`，`m < 2k`）。
本文件证这个对齐（`nodal_shape_align_FIX2`）：R3AW 的输出 ⇒ S8 的 Γ 部分的陈述，
**只差** `V` 是任意开集而不是 `ball z ρ`。差别的两处（rev3 建议）：S8 把 `V`、`W` 改成 `∃` 开邻域；
transversality 的 `fderiv w ≠ 0` 与 `Surjective (coprod …)` 是同一件事的两种写法
（R9 S8 是前者对"两张 sheet 的差函数"的转写）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

/-- R3AW 的输出 ⇒ S8 的 Γ 部分的陈述（`V` 取代 `ball z ρ`，`w = 0` 取代配对碰撞集）。 -/
theorem nodal_shape_align_FIX2 {O : Set ℂ} {a : Fin 2 → Fin 2 → ℂ → ℝ} {w : ℂ → ℝ} {p : ℂ}
    (h : DifferentialGeometry.Analysis.IsNodalHalfArcsAt_R3AW O a w p) :
    ∃ (V : Set ℂ) (ρ : ℝ) (k : ℕ) (Γ : Fin (2 * k) → ℝ → ℂ) (v : Fin (2 * k) → ℂ),
      IsOpen V ∧ p ∈ V ∧ 0 < ρ ∧ 1 ≤ k ∧
      (∀ m, Γ m 0 = p ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧ v m ≠ 0 ∧
        HasDerivWithinAt (Γ m) (v m) (Icc 0 ρ) 0 ∧ MapsTo (Γ m) (Ico 0 ρ) V) ∧
      (∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
        ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
      (∀ z ∈ V, w z = 0 ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z = Γ m r) := by
  obtain ⟨k, hk, -, -, V, T, lam, θ₀, ρ, Γ, hVo, hpV, -, -, hρ, -, harc, hpair, hcover, -⟩ := h
  refine ⟨V, ρ, k, Γ, fun m => T (Complex.exp (((θ₀ + ((m : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) *
    Complex.I)), hVo, hpV, hρ, hk, ?_, ?_, hcover⟩
  · intro m
    obtain ⟨h0, hc, hi, -, hd, hm⟩ := harc m
    refine ⟨h0, hc, hi, ?_, hd, hm⟩
    intro h0'
    have h0'' : T (Complex.exp (((θ₀ + ((m : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I)) =
        0 := h0'
    exact Complex.exp_ne_zero _ (T.injective (h0''.trans (map_zero T).symm))
  · intro m m' hmm'
    refine ⟨?_, hpair m m' hmm'⟩
    intro hsr
    have hne : ∀ x : ℝ, T (Complex.exp ((x : ℂ) * Complex.I)) ≠ 0 := fun x h0 =>
      Complex.exp_ne_zero _ (T.injective (by rw [h0, map_zero]))
    obtain ⟨r₁, r₂, hr₁, hr₂, he⟩ := hsr.exists_pos (hne _) (hne _)
    rw [← map_smul, ← map_smul] at he
    have he' := T.injective he
    have hn := congrArg norm he'
    rw [norm_smul, norm_smul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
      mul_one, mul_one, Real.norm_of_nonneg hr₁.le, Real.norm_of_nonneg hr₂.le] at hn
    subst hn
    have he'' : Complex.exp (((θ₀ + ((m : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((θ₀ + ((m' : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I) :=
      smul_right_injective ℂ hr₁.ne' he'
    rw [mul_comm _ Complex.I, mul_comm _ Complex.I] at he''
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hmlt : ((m : ℕ) : ℝ) < 2 * k := by exact_mod_cast m.isLt
    have hm'lt : ((m' : ℕ) : ℝ) < 2 * k := by exact_mod_cast m'.isLt
    have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm'0 : (0 : ℝ) ≤ ((m' : ℕ) : ℝ) := Nat.cast_nonneg _
    have hd : |((m : ℕ) : ℝ) - ((m' : ℕ) : ℝ)| < 2 * k := by
      rw [abs_lt]
      constructor <;> linarith
    have h1 : (θ₀ + ((m : ℕ) : ℝ) * Real.pi / k) - (θ₀ + ((m' : ℕ) : ℝ) * Real.pi / k) =
        (((m : ℕ) : ℝ) - ((m' : ℕ) : ℝ)) * (Real.pi / k) := by ring
    have hxy : |(θ₀ + ((m : ℕ) : ℝ) * Real.pi / k) - (θ₀ + ((m' : ℕ) : ℝ) * Real.pi / k)| <
        2 * Real.pi := by
      rw [h1, abs_mul, abs_of_pos (div_pos Real.pi_pos hkpos)]
      calc |((m : ℕ) : ℝ) - ((m' : ℕ) : ℝ)| * (Real.pi / k) < 2 * k * (Real.pi / k) :=
            mul_lt_mul_of_pos_right hd (div_pos Real.pi_pos hkpos)
        _ = 2 * Real.pi := by field_simp
    have hx := exp_I_inj_FIX2 he'' hxy
    have hx2 : ((m : ℕ) : ℝ) * (Real.pi / k) = ((m' : ℕ) : ℝ) * (Real.pi / k) := by
      have : θ₀ + ((m : ℕ) : ℝ) * (Real.pi / k) = θ₀ + ((m' : ℕ) : ℝ) * (Real.pi / k) := by
        rw [← mul_div_assoc, ← mul_div_assoc]
        exact hx
      linarith
    have hx3 := mul_right_cancel₀ (div_pos Real.pi_pos hkpos).ne' hx2
    exact hmm' (Fin.ext (by exact_mod_cast hx3))

end DifferentialGeometry.Geometry
