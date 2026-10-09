import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# R3a-ω（`_R3AW`）F3：局部根弧（IFT）与正规化坐标（Cholesky）

* `exists_simple_root_arc_R3AW`：极坐标 blow-up 函数 `W(r, θ)` 在 `(0, θs)` 处单根 ⇒ 局部光滑根 `ϑ(r)`，
  带逼近 / 局部唯一 / 非退化三条（`(r, θ) ↦ (r, W)` 的局部逆；剪切 `shearEquivR3AW` 为导数）。
* `exists_normalizing_equiv_R3AW`：正定对称 `2×2` 矩阵 `m` ⇒ `T : ℂ ≃L[ℝ] ℂ`，
  `T Tᵀ = m`（Cholesky）且 `T⁻¹ m T⁻ᵀ = I`（合同的正规化读法，`lam = 1`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- 剪切 `(x, y) ↦ (x, c x + d y)` 作为 `ℝ × ℝ` 上的连续线性同构（`d ≠ 0`）。 -/
def shearEquivR3AW (c d : ℝ) (hd : d ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (c • ContinuousLinearMap.fst ℝ ℝ ℝ + d • ContinuousLinearMap.snd ℝ ℝ ℝ))
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((-(c / d)) • ContinuousLinearMap.fst ℝ ℝ ℝ + d⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ))
    (fun q => by
      ext
      · simp
      · simp
        field_simp
        ring)
    (fun q => by
      ext
      · simp
      · simp
        field_simp
        ring)

theorem shearEquivR3AW_apply (c d : ℝ) (hd : d ≠ 0) (q : ℝ × ℝ) :
    shearEquivR3AW c d hd q = (q.1, c * q.1 + d * q.2) := by
  simp [shearEquivR3AW]

/-- `f_W q = (q.1, W q)` 的导数是剪切（系数为 `W` 的偏导数）。 -/
theorem hasFDerivAt_graphMap_R3AW {W : ℝ × ℝ → ℝ} {b : ℝ × ℝ} (hW : DifferentiableAt ℝ W b)
    (hd : fderiv ℝ W b (0, 1) ≠ 0) :
    HasFDerivAt (fun q : ℝ × ℝ => (q.1, W q))
      ((shearEquivR3AW (fderiv ℝ W b (1, 0)) (fderiv ℝ W b (0, 1)) hd :
        (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) b := by
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := b)).prodMk hW.hasFDerivAt
  convert h using 1
  refine ContinuousLinearMap.ext (fun q => ?_)
  have hq : q = q.1 • ((1 : ℝ), (0 : ℝ)) + q.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  refine Prod.ext ?_ ?_
  · simp [shearEquivR3AW_apply]
  · have e2 : (fderiv ℝ W b) q =
        q.1 * (fderiv ℝ W b) (1, 0) + q.2 * (fderiv ℝ W b) (0, 1) := by
      conv_lhs => rw [hq, map_add, map_smul, map_smul]
      simp
    simp only [ContinuousLinearEquiv.coe_coe, shearEquivR3AW_apply, e2,
      ContinuousLinearMap.prod_apply]
    ring

/-- 单根 IFT（极坐标 blow-up 的局部根弧）：`W` 在 `{|r| < ε}` 上光滑，`W(0, θs) = 0` 且
`∂_θ W(0, θs) ≠ 0` ⇒ 局部光滑根 `ϑ`，满足逼近、局部唯一与非退化。 -/
theorem exists_simple_root_arc_R3AW {W : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hW : ContDiffOn ℝ ∞ W {q : ℝ × ℝ | |q.1| < ε}) {θs : ℝ}
    (h0 : W (0, θs) = 0) (hd : fderiv ℝ W (0, θs) (0, 1) ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ η' : ℝ, 0 < η' ∧ η' ≤ η ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∃ ϑ : ℝ → ℝ, ϑ 0 = θs ∧
      ContDiffOn ℝ ∞ ϑ (Ioo (-δ) δ) ∧
      (∀ r : ℝ, |r| < δ → |ϑ r - θs| < η' ∧ W (r, ϑ r) = 0 ∧
        fderiv ℝ W (r, ϑ r) (0, 1) ≠ 0) ∧
      (∀ r : ℝ, |r| < δ → ∀ θ : ℝ, |θ - θs| < η' → W (r, θ) = 0 → θ = ϑ r) := by
  classical
  set a : ℝ × ℝ := (0, θs) with ha
  have hopen : IsOpen {q : ℝ × ℝ | |q.1| < ε} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hWat : ∀ q ∈ {q : ℝ × ℝ | |q.1| < ε}, ContDiffAt ℝ ∞ W q :=
    fun q hq => hW.contDiffAt (hopen.mem_nhds hq)
  have haε : a ∈ {q : ℝ × ℝ | |q.1| < ε} := by simp [ha, hε]
  let f : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, W q)
  have hfC : ∀ q ∈ {q : ℝ × ℝ | |q.1| < ε}, ContDiffAt ℝ ∞ f q :=
    fun q hq => contDiffAt_fst.prodMk (hWat q hq)
  have hfd : HasFDerivAt f ((shearEquivR3AW (fderiv ℝ W a (1, 0)) (fderiv ℝ W a (0, 1)) hd :
      (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) a :=
    hasFDerivAt_graphMap_R3AW ((hWat a haε).differentiableAt (by simp)) hd
  let e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    (hfC a haε).toOpenPartialHomeomorph f hfd (by simp)
  have he : (e : ℝ × ℝ → ℝ × ℝ) = f := rfl
  have hae : a ∈ e.source := (hfC a haε).mem_toOpenPartialHomeomorph_source hfd (by simp)
  have hfa : f a = (0, 0) := by
    change (a.1, W a) = (0, 0)
    rw [h0]
  have hea : e a = (0, 0) := by rw [he, hfa]
  have hsymm0 : e.symm (0, 0) = a := by rw [← hea]; exact e.left_inv hae
  have htgt : ((0 : ℝ), (0 : ℝ)) ∈ e.target := by rw [← hea]; exact e.map_source hae
  -- 保持非退化的邻域
  have hcont : ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ W q (0, 1)) a := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ W) a := (hWat a haε).fderiv_right (by norm_cast)
    exact (h1.continuousAt).clm_apply continuousAt_const
  have hnhds : e.source ∩ {q : ℝ × ℝ | |q.1| < ε} ∩ {q : ℝ × ℝ | fderiv ℝ W q (0, 1) ≠ 0} ∈
      𝓝 a :=
    inter_mem (inter_mem (e.open_source.mem_nhds hae) (hopen.mem_nhds haε))
      (hcont.eventually_ne hd)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  set η' : ℝ := min η ρ₀ with hη'
  have hη'pos : 0 < η' := lt_min hη hρ₀
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'ρ : η' ≤ ρ₀ := min_le_right _ _
  -- 选 δ
  have hev : ∀ᶠ r : ℝ in 𝓝 0, ((r, (0 : ℝ)) ∈ e.target ∧ e.symm (r, 0) ∈ Metric.ball a η') := by
    have hlim : Tendsto (fun r : ℝ => (r, (0 : ℝ))) (𝓝 0) (𝓝 ((0 : ℝ), (0 : ℝ))) :=
      (continuous_id.prodMk continuous_const).tendsto 0
    have h1 : ∀ᶠ y in 𝓝 ((0 : ℝ), (0 : ℝ)), y ∈ e.target := e.open_target.mem_nhds htgt
    have h2 : ∀ᶠ y in 𝓝 ((0 : ℝ), (0 : ℝ)), e.symm y ∈ Metric.ball a η' := by
      have hc := (e.continuousAt_symm htgt).tendsto
      rw [hsymm0] at hc
      exact hc.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hη'pos))
    exact (hlim.eventually h1).and (hlim.eventually h2)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min δ₀ (min ρ₀ ε) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min hρ₀ hε)
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have hδρ : δ ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδδ : δ ≤ δ₀ := min_le_left _ _
  have hr₀ : ∀ r : ℝ, |r| < δ → (r, (0 : ℝ)) ∈ e.target ∧ e.symm (r, 0) ∈ Metric.ball a η' := by
    intro r hr
    apply hδ₀'
    rw [Real.dist_eq, sub_zero]
    exact hr.trans_le hδδ
  -- 弧
  let ϑ : ℝ → ℝ := fun r => (e.symm (r, 0)).2
  have hb : ∀ r : ℝ, |r| < δ → e.symm (r, 0) = (r, ϑ r) ∧ W (r, ϑ r) = 0 := by
    intro r hr
    obtain ⟨hrt, hrb⟩ := hr₀ r hr
    have hinv : f (e.symm (r, 0)) = (r, 0) := by
      have := e.right_inv hrt
      rwa [he] at this
    have h1 : (e.symm (r, 0)).1 = r := by simpa [f] using congrArg Prod.fst hinv
    have h2 : W (e.symm (r, 0)) = 0 := by simpa [f] using congrArg Prod.snd hinv
    have hpair : e.symm (r, 0) = (r, ϑ r) := Prod.ext h1 rfl
    exact ⟨hpair, by rw [← hpair]; exact h2⟩
  refine ⟨η', hη'pos, hη'η, δ, hδpos, hδε, ϑ, ?_, ?_, ?_, ?_⟩
  · simp [ϑ, hsymm0, ha]
  · intro r hr
    have hr' : |r| < δ := by
      rw [mem_Ioo] at hr
      exact abs_lt.mpr hr
    obtain ⟨hrt, hrb⟩ := hr₀ r hr'
    obtain ⟨hpair, hW0⟩ := hb r hr'
    have hbS := hball (Metric.ball_subset_ball hη'ρ hrb)
    have hndeg : fderiv ℝ W (e.symm (r, 0)) (0, 1) ≠ 0 := hbS.2
    have hbε : e.symm (r, 0) ∈ {q : ℝ × ℝ | |q.1| < ε} := hbS.1.2
    have hfd' := hasFDerivAt_graphMap_R3AW ((hWat _ hbε).differentiableAt (by simp)) hndeg
    have hcd : ContDiffAt ℝ ∞ e.symm (r, 0) :=
      e.contDiffAt_symm hrt (f₀' := shearEquivR3AW _ _ hndeg) hfd' (hfC _ hbε)
    have hcd2 : ContDiffAt ℝ ∞ ϑ r :=
      contDiffAt_snd.comp r (hcd.comp r (contDiffAt_id.prodMk contDiffAt_const))
    exact hcd2.contDiffWithinAt
  · intro r hr
    obtain ⟨hrt, hrb⟩ := hr₀ r hr
    obtain ⟨hpair, hW0⟩ := hb r hr
    have hbS := hball (Metric.ball_subset_ball hη'ρ hrb)
    refine ⟨?_, hW0, ?_⟩
    · have := hrb
      rw [Metric.mem_ball, hpair, Prod.dist_eq] at this
      have h2 := (max_lt_iff.mp this).2
      simpa [ha, Real.dist_eq] using h2
    · rw [← hpair]
      exact hbS.2
  · intro r hr θ hθ hW0
    obtain ⟨hrt, hrb⟩ := hr₀ r hr
    obtain ⟨hpair, hWr⟩ := hb r hr
    have hmem : (r, θ) ∈ Metric.ball a ρ₀ := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ (lt_of_lt_of_le ?_ hη'ρ)
      · simpa [ha, Real.dist_eq] using hr.trans_le hδρ
      · simpa [ha, Real.dist_eq] using hθ
    have hbS := hball (Metric.ball_subset_ball hη'ρ hrb)
    have hsrc : (r, θ) ∈ e.source := (hball hmem).1.1
    have heq : e (r, θ) = e (e.symm (r, 0)) := by
      rw [e.right_inv hrt, he]
      change (r, W (r, θ)) = (r, 0)
      rw [hW0]
    have := e.injOn hsrc hbS.1.1 heq
    rw [hpair] at this
    exact congrArg Prod.snd this

/-- 实线性映射 `z ↦ (a x, b x + c y)`（`z = x + i y`）。 -/
def triLinR3AW (a b c : ℝ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := ⟨a * z.re, b * z.re + c * z.im⟩
  map_add' z w := by
    apply Complex.ext <;> simp <;> ring
  map_smul' t z := by
    apply Complex.ext <;> simp <;> ring

/-- Cholesky 型线性同构 `z ↦ (r x, g x + s y)`。 -/
def cholEquivR3AW (r s g : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.equivOfInverse
    (LinearMap.toContinuousLinearMap (triLinR3AW r g s))
    (LinearMap.toContinuousLinearMap (triLinR3AW (1 / r) (-g / (r * s)) (1 / s)))
    (fun z => by
      apply Complex.ext
      · simp [triLinR3AW]
        field_simp
      · simp [triLinR3AW]
        field_simp
        ring)
    (fun z => by
      apply Complex.ext
      · simp [triLinR3AW]
        field_simp
      · simp [triLinR3AW]
        field_simp
        ring)

theorem cholEquivR3AW_apply (r s g : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (z : ℂ) :
    cholEquivR3AW r s g hr hs z = ⟨r * z.re, g * z.re + s * z.im⟩ := rfl

theorem cholEquivR3AW_symm_apply (r s g : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (z : ℂ) :
    (cholEquivR3AW r s g hr hs).symm z = ⟨1 / r * z.re, -g / (r * s) * z.re + 1 / s * z.im⟩ :=
  rfl

/-- 正定对称 `2×2` 矩阵 `m` 的正规化：`T Tᵀ = m`（`T` 由 Cholesky 给出）与
`T⁻¹ m T⁻ᵀ = I` 两种读法（合同 `lam = 1`）。 -/
theorem exists_normalizing_equiv_R3AW (m : Fin 2 → Fin 2 → ℝ) (hsymm : m 1 0 = m 0 1)
    (h00 : 0 < m 0 0) (hdet : 0 < m 0 0 * m 1 1 - m 0 1 ^ 2) :
    ∃ T : ℂ ≃L[ℝ] ℂ,
      (∀ i j : Fin 2, ∑ l : Fin 2, ![Complex.re, Complex.im] i (T (![1, Complex.I] l)) *
          ![Complex.re, Complex.im] j (T (![1, Complex.I] l)) = m i j) ∧
      (∀ k' l : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, m i j *
          ![Complex.re, Complex.im] k' (T.symm (![1, Complex.I] i)) *
          ![Complex.re, Complex.im] l (T.symm (![1, Complex.I] j)) = if k' = l then 1 else 0) := by
  set r : ℝ := Real.sqrt (m 0 0) with hr
  set s : ℝ := Real.sqrt ((m 0 0 * m 1 1 - m 0 1 ^ 2) / m 0 0) with hs
  have hrpos : 0 < r := Real.sqrt_pos.mpr h00
  have hspos : 0 < s := Real.sqrt_pos.mpr (div_pos hdet h00)
  have hr2 : r * r = m 0 0 := Real.mul_self_sqrt h00.le
  have hs2 : s * s = (m 0 0 * m 1 1 - m 0 1 ^ 2) / m 0 0 :=
    Real.mul_self_sqrt (div_pos hdet h00).le
  have hs2' : s * s * m 0 0 = m 0 0 * m 1 1 - m 0 1 ^ 2 := by
    rw [hs2]
    field_simp
  refine ⟨cholEquivR3AW r s (m 0 1 / r) hrpos.ne' hspos.ne', ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        cholEquivR3AW_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Fin.sum_univ_two, Complex.one_re, mul_one, Matrix.cons_val_one, Complex.I_re, mul_zero,
        add_zero]
      exact hr2
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        cholEquivR3AW_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Fin.mk_one, Matrix.cons_val_one, Fin.sum_univ_two, Complex.one_re, mul_one,
        Complex.one_im, mul_zero, add_zero, Complex.I_re, Complex.I_im, zero_add, zero_mul]
      field_simp
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        cholEquivR3AW_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Fin.zero_eta, Matrix.cons_val_zero, Fin.sum_univ_two, Complex.one_re, mul_one,
        Complex.one_im, mul_zero, add_zero, Complex.I_re, Complex.I_im, zero_add, hsymm]
      field_simp
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        cholEquivR3AW_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Fin.sum_univ_two, Matrix.cons_val_zero, Complex.one_re, mul_one, Complex.one_im,
        mul_zero, add_zero, Complex.I_re, Complex.I_im, zero_add]
      have e1 : m 0 1 / r * (m 0 1 / r) = m 0 1 ^ 2 / m 0 0 := by
        rw [← hr2]
        field_simp
      rw [e1, hs2]
      field_simp
      ring
  · intro k' l
    fin_cases k' <;> fin_cases l
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        cholEquivR3AW_symm_apply, one_div, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, Fin.sum_univ_two, Complex.one_re, mul_one, Matrix.cons_val_one,
        Complex.I_re, mul_zero, add_zero, hsymm, zero_mul, ↓reduceIte]
      rw [← hr2]
      field_simp
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        cholEquivR3AW_symm_apply, one_div, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.sum_univ_two,
        Complex.one_re, mul_one, Complex.one_im, mul_zero, add_zero, Complex.I_re, Complex.I_im,
        zero_add, hsymm, zero_mul, zero_ne_one, ↓reduceIte]
      rw [← hr2]
      field_simp
      ring
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        cholEquivR3AW_symm_apply, one_div, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, Fin.zero_eta, Matrix.cons_val_zero, Fin.sum_univ_two,
        Complex.one_re, mul_one, Complex.I_re, mul_zero, add_zero, Complex.one_im, hsymm,
        Complex.I_im, zero_add, one_ne_zero, ↓reduceIte]
      rw [← hr2]
      field_simp
      ring
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        cholEquivR3AW_symm_apply, one_div, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, Fin.sum_univ_two, Matrix.cons_val_zero, Complex.one_re, mul_one,
        Complex.one_im, mul_zero, add_zero, Complex.I_re, Complex.I_im, zero_add, hsymm,
        ↓reduceIte]
      have h11 : m 1 1 = (s * s * m 0 0 + m 0 1 ^ 2) / m 0 0 := by
        field_simp
        linarith [hs2']
      rw [h11, ← hr2]
      field_simp
      ring

end DifferentialGeometry.Analysis

end
