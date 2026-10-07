import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalAngularR3AW

/-!
# R3a-ω（`_R3AW`）F2b：主部调和（G2）

`w` 实解析、满足 smooth 系数方程、在 `p` 处 `k` 阶消失：沿射线 jets 给出 `Σ a_ij(p) D^k w(p)(e_j, e_i, h^{k-2}) = 0`；
在正规化坐标（`T Tᵀ = A(p)`）下即 `Σ_l S(ξ_l, ξ_l, h^{k-2}) = 0`，于是角函数 `S((T e^{iθ})^k)` 满足
`φ'' = -k² φ`，非零 ⇒ `A sin (k (θ - θ₀))`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- 方程在 `p` 处的 `n` 阶（沿射线）jet 给出 `D^{n+2} w(p)` 的主部恒等式：
`w` 在 `p` 的 `< n+2` 阶 jets 全零时，`Σ a_ij(p) D^{n+2}w(p)(e_j, e_i, h, …, h) = 0`。 -/
theorem principal_jets_harmonic_R3AW {w : ℂ → ℝ} {p : ℂ} {n : ℕ} (e : Fin 2 → ℂ)
    (hw : ContDiffAt ℝ ∞ w p) {A : Fin 2 → Fin 2 → ℂ → ℝ} {β : Fin 2 → ℂ → ℝ} {c : ℂ → ℝ}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (A i j) p) (hβ : ∀ i, ContDiffAt ℝ ∞ (β i) p)
    (hc : ContDiffAt ℝ ∞ c p)
    (heq : ∀ᶠ y in 𝓝 p, ∑ i, ∑ j, A i j y * iteratedFDeriv ℝ 2 w y ![e i, e j] +
      ∑ i, β i y * fderiv ℝ w y (e i) + c y * w y = 0)
    (hjet : ∀ j < n + 2, iteratedFDeriv ℝ j w p = 0) (h : ℂ) :
    ∑ i, ∑ j, A i j p * iteratedFDeriv ℝ (n + 2) w p
      (Fin.cons (e j) (Fin.cons (e i) (fun _ : Fin n => h))) = 0 := by
  classical
  let L : ℝ → ℂ := fun s => p + s • h
  have hLp : L 0 = p := by simp [L]
  have hLc : ContDiff ℝ ∞ L := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hline : ∀ {F : ℂ → ℝ}, ContDiffAt ℝ ∞ F p → ∀ m : ℕ,
      ContDiffAt ℝ (m : WithTop ℕ∞) (fun s : ℝ => F (L s)) 0 := by
    intro F hF m
    have hF' : ContDiffAt ℝ ∞ F (L 0) := by rw [hLp]; exact hF
    have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => F (L s)) 0 := hF'.comp 0 hLc.contDiffAt
    exact h1.of_le (by exact_mod_cast le_top)
  let ψ : Fin 2 → Fin 2 → ℂ → ℝ := fun i j y => fderiv ℝ (fderiv ℝ w) y (e i) (e j)
  let χ : Fin 2 → ℂ → ℝ := fun i y => fderiv ℝ w y (e i)
  have hwd : ContDiffAt ℝ ∞ (fderiv ℝ w) p := hw.fderiv_right (by simp)
  have hwdd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ w)) p := hwd.fderiv_right (by simp)
  have hψ : ∀ i j, ContDiffAt ℝ ∞ (ψ i j) p := fun i j =>
    (hwdd.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hχ : ∀ i, ContDiffAt ℝ ∞ (χ i) p := fun i => hwd.clm_apply contDiffAt_const
  -- the equation along the line vanishes near 0
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∑ i, ∑ j, A i j (L s) * ψ i j (L s) +
      ∑ i, β i (L s) * χ i (L s) + c (L s) * w (L s) = 0 := by
    have hlim : Filter.Tendsto L (𝓝 0) (𝓝 p) := by
      rw [← hLp]
      exact hLc.continuous.tendsto 0
    filter_upwards [hlim.eventually heq] with s hs
    simpa only [ψ, χ, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hs
  have hfun : (fun s : ℝ => ∑ i, ∑ j, A i j (L s) * ψ i j (L s) +
      ∑ i, β i (L s) * χ i (L s) + c (L s) * w (L s)) =ᶠ[𝓝 0] (0 : ℝ → ℝ) := by
    filter_upwards [hev] with s hs
    simpa using hs
  have h0 : iteratedDeriv n (fun s : ℝ => ∑ i, ∑ j, A i j (L s) * ψ i j (L s) +
      ∑ i, β i (L s) * χ i (L s) + c (L s) * w (L s)) 0 = 0 := by
    rw [hfun.iteratedDeriv_eq, iteratedDeriv_const_zero]
  -- jets of the line restrictions
  have hjψ : ∀ i j, ∀ l ≤ n, iteratedDeriv l (fun s : ℝ => ψ i j (L s)) 0 =
      iteratedFDeriv ℝ (l + 2) w p (Fin.cons (e j) (Fin.cons (e i) (fun _ : Fin l => h))) := by
    intro i j l _
    rw [iteratedDeriv_line (x := p) (v := h) (hψ i j) l]
    exact iteratedFDeriv_fderiv_fderiv_apply_R3AW hw l (e i) (e j) (fun _ => h)
  have hjχ : ∀ i, ∀ l ≤ n, iteratedDeriv l (fun s : ℝ => χ i (L s)) 0 =
      iteratedFDeriv ℝ (l + 1) w p (Fin.cons (e i) (fun _ : Fin l => h)) := by
    intro i l _
    rw [iteratedDeriv_line (x := p) (v := h) (hχ i) l]
    exact iteratedFDeriv_fderiv_apply_R3AW hw l (e i) (fun _ => h)
  have hjw : ∀ l, iteratedDeriv l (fun s : ℝ => w (L s)) 0 =
      iteratedFDeriv ℝ l w p (fun _ => h) := fun l => iteratedDeriv_line (x := p) (v := h) hw l
  have hF₁ : ∀ i j, ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => A i j (L s) * ψ i j (L s)) 0 := fun i j =>
    (hline (hA i j) n).mul (hline (hψ i j) n)
  have hF₂ : ∀ i, ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => β i (L s) * χ i (L s)) 0 :=
    fun i => (hline (hβ i) n).mul (hline (hχ i) n)
  have hF₃ : ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => c (L s) * w (L s)) 0 :=
    (hline hc n).mul (hline hw n)
  have hT₁ : ∀ i j, iteratedDeriv n (fun s : ℝ => A i j (L s) * ψ i j (L s)) 0 =
      A i j p * iteratedFDeriv ℝ (n + 2) w p
        (Fin.cons (e j) (Fin.cons (e i) (fun _ : Fin n => h))) := by
    intro i j
    rw [iteratedDeriv_mul_of_vanishing_R3AW n (hline (hA i j) n) (hline (hψ i j) n), hLp,
      hjψ i j n le_rfl]
    intro l hl
    rw [hjψ i j l hl.le, hjet (l + 2) (by omega)]
    simp
  have hT₂ : ∀ i, iteratedDeriv n (fun s : ℝ => β i (L s) * χ i (L s)) 0 = 0 := by
    intro i
    rw [iteratedDeriv_mul_of_vanishing_R3AW n (hline (hβ i) n) (hline (hχ i) n), hjχ i n le_rfl,
      hjet (n + 1) (by omega)]
    · simp
    · intro l hl
      rw [hjχ i l hl.le, hjet (l + 1) (by omega)]
      simp
  have hT₃ : iteratedDeriv n (fun s : ℝ => c (L s) * w (L s)) 0 = 0 := by
    rw [iteratedDeriv_mul_of_vanishing_R3AW n (hline hc n) (hline hw n), hjw n,
      hjet n (by omega)]
    · simp
    · intro l hl
      rw [hjw l, hjet l (by omega)]
      simp
  have hS₁i : ∀ i, ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => ∑ j, A i j (L s) * ψ i j (L s)) 0 := fun i =>
    ContDiffAt.sum fun j _ => hF₁ i j
  have hS₁ : ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => ∑ i, ∑ j, A i j (L s) * ψ i j (L s)) 0 :=
    ContDiffAt.sum fun i _ => hS₁i i
  have hS₂ : ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => ∑ i, β i (L s) * χ i (L s)) 0 :=
    ContDiffAt.sum fun i _ => hF₂ i
  rw [iteratedDeriv_fun_add (hS₁.add hS₂) hF₃, iteratedDeriv_fun_add hS₁ hS₂,
    iteratedDeriv_fun_sum (fun i _ => hS₁i i), iteratedDeriv_fun_sum (fun i _ => hF₂ i),
    hT₃] at h0
  have hinner : ∀ i, iteratedDeriv n (fun s : ℝ => ∑ j, A i j (L s) * ψ i j (L s)) 0 =
      ∑ j, A i j p * iteratedFDeriv ℝ (n + 2) w p
        (Fin.cons (e j) (Fin.cons (e i) (fun _ : Fin n => h))) := by
    intro i
    rw [iteratedDeriv_fun_sum (fun j _ => hF₁ i j)]
    exact Finset.sum_congr rfl fun j _ => hT₁ i j
  simp only [hinner, hT₂, Finset.sum_const_zero, add_zero] at h0
  exact h0

/-- 平面标准基 `e₀ = 1`、`e₁ = I`。 -/
def planeBasisR3AW : Fin 2 → ℂ := ![1, Complex.I]

theorem T_exp_eq_circ_R3AW (T : ℂ ≃L[ℝ] ℂ) (θ : ℝ) :
    T (Complex.exp ((θ : ℂ) * Complex.I)) = circR3AW (T 1) (T Complex.I) θ := by
  have h : Complex.exp ((θ : ℂ) * Complex.I) = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
    rw [Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.real_smul]
  rw [h, map_add, map_smul, map_smul]
  rfl

theorem sin_form_of_ode_R3AW {k : ℕ} (hk : 1 ≤ k)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℝ)
    (hS : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → ℂ), S (v ∘ σ) = S v) (hS0 : S ≠ 0)
    (T : ℂ ≃L[ℝ] ℂ) (φ₁ : ℝ → ℝ)
    (h1 : ∀ θ : ℝ, HasDerivAt (fun s : ℝ => S (fun _ => T (Complex.exp ((s : ℂ) * Complex.I))))
      (φ₁ θ) θ)
    (h2 : ∀ θ : ℝ, HasDerivAt φ₁ (-((k : ℝ) ^ 2) *
      S (fun _ => T (Complex.exp ((θ : ℂ) * Complex.I)))) θ) :
    ∃ θ₀ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      S (fun _ => T (Complex.exp (((θ₀ + t : ℝ) : ℂ) * Complex.I))) = A * Real.sin (k * t) := by
  set φ : ℝ → ℝ := fun s => S (fun _ => T (Complex.exp ((s : ℂ) * Complex.I))) with hφ
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsol := ode_solution_R3AW hkpos h1 h2
  have hnz : φ 0 ≠ 0 ∨ φ₁ 0 / k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    have hφ0 : ∀ θ, φ θ = 0 := by
      intro θ
      rw [hsol θ, ha, hb]
      simp
    apply hS0
    refine multilinear_eq_zero_of_diag_zero_R3AW S hS (fun h => ?_)
    set y : ℂ := T.symm h with hy
    have hyexp : (‖y‖ : ℂ) * Complex.exp ((y.arg : ℂ) * Complex.I) = y :=
      Complex.norm_mul_exp_arg_mul_I y
    have hTy : h = ‖y‖ • T (Complex.exp ((y.arg : ℂ) * Complex.I)) := by
      rw [← map_smul, Complex.real_smul, hyexp, hy]
      simp
    rw [hTy]
    have := S.map_smul_univ (fun _ : Fin k => ‖y‖)
      (fun _ : Fin k => T (Complex.exp ((y.arg : ℂ) * Complex.I)))
    rw [this]
    have h0 := hφ0 y.arg
    simp only [hφ] at h0
    rw [h0]
    simp
  obtain ⟨θ₀, A, hA, hform⟩ := sin_form_R3AW (a := φ 0) (b := φ₁ 0 / k) hkpos hnz
  refine ⟨θ₀, A, hA, fun t => ?_⟩
  have := hsol (θ₀ + t)
  simp only [hφ] at this
  rw [this]
  exact hform t

theorem bil_expand_R3AW {n : ℕ} (S : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 2) => ℂ) ℝ)
    (r : Fin n → ℂ) (ξ : ℂ) :
    S (Fin.cons ξ (Fin.cons ξ r)) =
      ξ.re * ξ.re * S (Fin.cons 1 (Fin.cons 1 r)) +
      ξ.re * ξ.im * S (Fin.cons 1 (Fin.cons Complex.I r)) +
      ξ.im * ξ.re * S (Fin.cons Complex.I (Fin.cons 1 r)) +
      ξ.im * ξ.im * S (Fin.cons Complex.I (Fin.cons Complex.I r)) := by
  have B1 : ∀ (x y : ℂ) (a b : ℝ) (v : ℂ),
      S (Fin.cons (a • x + b • y) (Fin.cons v r)) =
        a * S (Fin.cons x (Fin.cons v r)) + b * S (Fin.cons y (Fin.cons v r)) := by
    intro x y a b v
    rw [S.cons_add, S.cons_smul, S.cons_smul]
    simp
  have B2 : ∀ (u x y : ℂ) (a b : ℝ),
      S (Fin.cons u (Fin.cons (a • x + b • y) r)) =
        a * S (Fin.cons u (Fin.cons x r)) + b * S (Fin.cons u (Fin.cons y r)) := by
    intro u x y a b
    have e : ∀ v : ℂ, S (Fin.cons u (Fin.cons v r)) = (S.curryLeft u) (Fin.cons v r) :=
      fun v => (ContinuousMultilinearMap.curryLeft_apply _ _ _).symm
    rw [e, e, e, (S.curryLeft u).cons_add, (S.curryLeft u).cons_smul,
      (S.curryLeft u).cons_smul]
    simp
  have hξ : ξ = ξ.re • (1 : ℂ) + ξ.im • Complex.I := by
    apply Complex.ext <;> simp
  have key : ∀ x y : ℝ, S (Fin.cons (x • (1 : ℂ) + y • Complex.I)
      (Fin.cons (x • (1 : ℂ) + y • Complex.I) r)) =
      x * x * S (Fin.cons 1 (Fin.cons 1 r)) + x * y * S (Fin.cons 1 (Fin.cons Complex.I r)) +
      y * x * S (Fin.cons Complex.I (Fin.cons 1 r)) +
      y * y * S (Fin.cons Complex.I (Fin.cons Complex.I r)) := by
    intro x y
    rw [B1, B2, B2]
    ring
  have := key ξ.re ξ.im
  rwa [← hξ] at this


/-- G2：`k` 阶消失的实解析 `w` 满足 smooth 系数齐次椭圆方程时，在正规化坐标 `x = p + T y`
（`T Tᵀ = A(p)`，即 `hT`）下，最低阶项的角函数是 `A₀ sin (k t)`（`t` 为从零点方向起算的角）。 -/
theorem principal_part_harmonic_R3AW {w : ℂ → ℝ} {p : ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hw : AnalyticAt ℝ w p) {A : Fin 2 → Fin 2 → ℂ → ℝ} {β : Fin 2 → ℂ → ℝ} {c : ℂ → ℝ}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (A i j) p) (hβ : ∀ i, ContDiffAt ℝ ∞ (β i) p)
    (hc : ContDiffAt ℝ ∞ c p)
    (heq : ∀ᶠ y in 𝓝 p, ∑ i, ∑ j, A i j y *
        iteratedFDeriv ℝ 2 w y ![planeBasisR3AW i, planeBasisR3AW j] +
      ∑ i, β i y * fderiv ℝ w y (planeBasisR3AW i) + c y * w y = 0)
    (hjet : ∀ j < k, iteratedFDeriv ℝ j w p = 0) (hjk : iteratedFDeriv ℝ k w p ≠ 0)
    (T : ℂ ≃L[ℝ] ℂ)
    (hT : ∀ i j : Fin 2, ∑ l : Fin 2, ![Complex.re, Complex.im] i (T (planeBasisR3AW l)) *
      ![Complex.re, Complex.im] j (T (planeBasisR3AW l)) = A i j p) :
    ∃ θ₀ A₀ : ℝ, 0 < A₀ ∧ ∀ t : ℝ,
      iteratedFDeriv ℝ k w p (fun _ => T (Complex.exp (((θ₀ + t : ℝ) : ℂ) * Complex.I))) =
        A₀ * Real.sin (k * t) := by
  have hwi : ContDiffAt ℝ ∞ w p := hw.contDiffAt.of_le (by exact_mod_cast le_top)
  have hsym : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → ℂ),
      iteratedFDeriv ℝ k w p (v ∘ σ) = iteratedFDeriv ℝ k w p v :=
    fun σ v => hw.contDiffAt.iteratedFDeriv_comp_perm v σ
  rcases k with _ | _ | n
  · omega
  · -- k = 1：`S` 是线性型
    set S := iteratedFDeriv ℝ 1 w p with hS
    refine sin_form_of_ode_R3AW (le_refl 1) S hsym hjk T
      (fun θ => S (fun _ => circVelR3AW (T 1) (T Complex.I) θ)) (fun θ => ?_) (fun θ => ?_)
    · have h := hasDerivAt_diag_R3AW (n := 0) S hsym (hasDerivAt_circ_R3AW (T 1) (T Complex.I) θ)
      simp only [T_exp_eq_circ_R3AW]
      convert h using 1
      have : (Fin.cons (circVelR3AW (T 1) (T Complex.I) θ)
          (fun _ : Fin 0 => circR3AW (T 1) (T Complex.I) θ) : Fin 1 → ℂ) =
          fun _ => circVelR3AW (T 1) (T Complex.I) θ := by
        funext i
        simp [Fin.fin_one_eq_zero i]
      rw [this]
      simp
    · have h := hasDerivAt_diag_R3AW (n := 0) S hsym (hasDerivAt_circVel_R3AW (T 1) (T Complex.I) θ)
      simp only [T_exp_eq_circ_R3AW]
      convert h using 1
      have hneg := S.map_smul_univ (fun _ : Fin 1 => (-1 : ℝ))
        (fun _ : Fin 1 => circR3AW (T 1) (T Complex.I) θ)
      simp only [neg_smul, one_smul, Finset.univ_unique, Finset.prod_singleton] at hneg
      have : (Fin.cons (-circR3AW (T 1) (T Complex.I) θ)
          (fun _ : Fin 0 => circVelR3AW (T 1) (T Complex.I) θ) : Fin 1 → ℂ) =
          fun _ => -circR3AW (T 1) (T Complex.I) θ := by
        funext i
        simp [Fin.fin_one_eq_zero i]
      rw [this, hneg]
      simp
  · -- k = n + 2：主部调和 + 角函数 ODE
    set S := iteratedFDeriv ℝ (n + 2) w p with hS
    have hharm : ∀ h : ℂ, S (Fin.cons (T 1) (Fin.cons (T 1) (fun _ : Fin n => h))) +
        S (Fin.cons (T Complex.I) (Fin.cons (T Complex.I) (fun _ : Fin n => h))) = 0 := by
      intro h
      have hH1 := principal_jets_harmonic_R3AW (e := planeBasisR3AW) (n := n) hwi hA hβ hc heq
        (fun j hj => hjet j hj) h
      have e0 : planeBasisR3AW 0 = 1 := by simp [planeBasisR3AW]
      have e1 : planeBasisR3AW 1 = Complex.I := by simp [planeBasisR3AW]
      have h00 := hT 0 0
      have h01 := hT 0 1
      have h10 := hT 1 0
      have h11 := hT 1 1
      simp only [Fin.sum_univ_two, e0, e1, Matrix.cons_val_zero,
        Matrix.cons_val_one] at h00 h01 h10 h11
      simp only [Fin.sum_univ_two, e0, e1] at hH1
      rw [← h00, ← h01, ← h10, ← h11] at hH1
      rw [bil_expand_R3AW S (fun _ : Fin n => h) (T 1),
        bil_expand_R3AW S (fun _ : Fin n => h) (T Complex.I)]
      linear_combination hH1
    have hd := fun θ => angular_ode_R3AW S hsym (T 1) (T Complex.I) hharm θ
    refine sin_form_of_ode_R3AW (by omega) S hsym hjk T
      (fun θ => ((n : ℝ) + 2) * S (Fin.cons (circVelR3AW (T 1) (T Complex.I) θ)
        (fun _ : Fin (n + 1) => circR3AW (T 1) (T Complex.I) θ))) (fun θ => ?_) (fun θ => ?_)
    · simpa only [T_exp_eq_circ_R3AW] using (hd θ).1
    · simp only [T_exp_eq_circ_R3AW]
      convert (hd θ).2 using 2
      push_cast
      ring

end DifferentialGeometry.Analysis

end
