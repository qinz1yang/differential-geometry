import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalJetsR3AW
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# R3a-ω（`_R3AW`）F2a：角函数 ODE 层

`g(θ) = cos θ ξ₀ + sin θ ξ₁` 上对称多线性型的对角值 `φ(θ) = S(g(θ), …, g(θ))`：若主部调和条件
`S(ξ₀, ξ₀, h^{k-2}) + S(ξ₁, ξ₁, h^{k-2}) = 0`（`∀ h`）成立，则 `φ'' = -k² φ`；该 ODE 的解是
`a cos kθ + b sin kθ`，非零时平移后为 `A sin (k t)`。纯多线性 + 一元微积分，不涉及 elliptic 方程。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- 平面上以 `ξ₀ ξ₁` 为基的「圆」`θ ↦ cos θ ξ₀ + sin θ ξ₁`。 -/
def circR3AW (ξ₀ ξ₁ : ℂ) (θ : ℝ) : ℂ := Real.cos θ • ξ₀ + Real.sin θ • ξ₁

/-- 圆的速度 `-sin θ ξ₀ + cos θ ξ₁`。 -/
def circVelR3AW (ξ₀ ξ₁ : ℂ) (θ : ℝ) : ℂ := -Real.sin θ • ξ₀ + Real.cos θ • ξ₁

theorem hasDerivAt_circ_R3AW (ξ₀ ξ₁ : ℂ) (θ : ℝ) :
    HasDerivAt (circR3AW ξ₀ ξ₁) (circVelR3AW ξ₀ ξ₁ θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).smul_const ξ₀).add ((Real.hasDerivAt_sin θ).smul_const ξ₁)
  exact h

theorem hasDerivAt_circVel_R3AW (ξ₀ ξ₁ : ℂ) (θ : ℝ) :
    HasDerivAt (circVelR3AW ξ₀ ξ₁) (-circR3AW ξ₀ ξ₁ θ) θ := by
  have h := (((Real.hasDerivAt_sin θ).neg).smul_const ξ₀).add
    ((Real.hasDerivAt_cos θ).smul_const ξ₁)
  have e : -circR3AW ξ₀ ξ₁ θ = -Real.cos θ • ξ₀ + -Real.sin θ • ξ₁ := by
    simp only [circR3AW, neg_smul]
    abel
  rw [e]
  exact h

/-- 旋转下 `Σ_l B(ξ_l, ξ_l)` 不变（`B` 为 `Fin.cons` 前两槽的双线性型）。 -/
theorem trace_rotate_R3AW {n : ℕ} (S : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 2) => ℂ) ℝ)
    (ξ₀ ξ₁ : ℂ) (r : Fin n → ℂ) (θ : ℝ) :
    S (Fin.cons (circR3AW ξ₀ ξ₁ θ) (Fin.cons (circR3AW ξ₀ ξ₁ θ) r)) +
      S (Fin.cons (circVelR3AW ξ₀ ξ₁ θ) (Fin.cons (circVelR3AW ξ₀ ξ₁ θ) r)) =
    S (Fin.cons ξ₀ (Fin.cons ξ₀ r)) + S (Fin.cons ξ₁ (Fin.cons ξ₁ r)) := by
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
  simp only [circR3AW, circVelR3AW, B1, B2]
  have := Real.cos_sq_add_sin_sq θ
  linear_combination (S (Fin.cons ξ₀ (Fin.cons ξ₀ r)) + S (Fin.cons ξ₁ (Fin.cons ξ₁ r))) * this

theorem cons_cons_const_R3AW {n : ℕ} (g : ℂ) :
    (Fin.cons g (Fin.cons g (fun _ : Fin n => g)) : Fin (n + 2) → ℂ) = fun _ => g := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j =>
    induction j using Fin.cases with
    | zero => simp
    | succ l => simp

/-- 角函数 `φ(θ) = S(g(θ)^k)` 满足 `φ'' = -k² φ`（`k = n + 2`，调和条件 `hharm`）。 -/
theorem angular_ode_R3AW {n : ℕ}
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 2) => ℂ) ℝ)
    (hS : ∀ (σ : Equiv.Perm (Fin (n + 2))) (v : Fin (n + 2) → ℂ), S (v ∘ σ) = S v)
    (ξ₀ ξ₁ : ℂ)
    (hharm : ∀ h : ℂ, S (Fin.cons ξ₀ (Fin.cons ξ₀ (fun _ : Fin n => h))) +
      S (Fin.cons ξ₁ (Fin.cons ξ₁ (fun _ : Fin n => h))) = 0) (θ : ℝ) :
    HasDerivAt (fun s => S (fun _ => circR3AW ξ₀ ξ₁ s))
      (((n : ℝ) + 2) * S (Fin.cons (circVelR3AW ξ₀ ξ₁ θ)
        (fun _ : Fin (n + 1) => circR3AW ξ₀ ξ₁ θ))) θ ∧
    HasDerivAt (fun s => ((n : ℝ) + 2) * S (Fin.cons (circVelR3AW ξ₀ ξ₁ s)
        (fun _ : Fin (n + 1) => circR3AW ξ₀ ξ₁ s)))
      (-(((n : ℝ) + 2) ^ 2) * S (fun _ => circR3AW ξ₀ ξ₁ θ)) θ := by
  refine ⟨?_, ?_⟩
  · have h := hasDerivAt_diag_R3AW (n := n + 1) S hS (hasDerivAt_circ_R3AW ξ₀ ξ₁ θ)
    convert h using 2
    push_cast
    ring
  · have h := (hasDerivAt_diag_cons_R3AW (n := n) S hS (hasDerivAt_circ_R3AW ξ₀ ξ₁ θ)
      (hasDerivAt_circVel_R3AW ξ₀ ξ₁ θ)).const_mul ((n : ℝ) + 2)
    have h1 : S (Fin.cons (-circR3AW ξ₀ ξ₁ θ) (fun _ : Fin (n + 1) => circR3AW ξ₀ ξ₁ θ)) =
        -S (fun _ => circR3AW ξ₀ ξ₁ θ) := by
      have := S.cons_smul (fun _ : Fin (n + 1) => circR3AW ξ₀ ξ₁ θ) (-1 : ℝ) (circR3AW ξ₀ ξ₁ θ)
      rw [neg_one_smul, neg_one_smul] at this
      rw [this]
      have h2 : (Fin.cons (circR3AW ξ₀ ξ₁ θ) (fun _ : Fin (n + 1) => circR3AW ξ₀ ξ₁ θ) :
          Fin (n + 2) → ℂ) = fun _ => circR3AW ξ₀ ξ₁ θ := by
        funext i
        induction i using Fin.cases <;> simp
      rw [h2]
    have h3 := trace_rotate_R3AW S ξ₀ ξ₁ (fun _ : Fin n => circR3AW ξ₀ ξ₁ θ) θ
    rw [hharm ((circR3AW ξ₀ ξ₁ θ)), cons_cons_const_R3AW] at h3
    have h4 : S (Fin.cons (circVelR3AW ξ₀ ξ₁ θ) (Fin.cons (circVelR3AW ξ₀ ξ₁ θ)
        (fun _ : Fin n => circR3AW ξ₀ ξ₁ θ))) = -S (fun _ => circR3AW ξ₀ ξ₁ θ) := by
      linarith
    convert h using 1
    rw [h1, h4]
    ring

theorem hasDerivAt_cos_mul_R3AW (k θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (k * x)) (-(Real.sin (k * θ)) * k) θ := by
  have h := ((hasDerivAt_id θ).const_mul k).cos
  simpa using h

theorem hasDerivAt_sin_mul_R3AW (k θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (k * x)) (Real.cos (k * θ) * k) θ := by
  have h := ((hasDerivAt_id θ).const_mul k).sin
  simpa using h

/-- `φ'' = -k² φ` 的唯一解（能量法）。 -/
theorem ode_solution_R3AW {k : ℝ} (hk : 0 < k) {φ φ₁ : ℝ → ℝ}
    (h1 : ∀ θ, HasDerivAt φ (φ₁ θ) θ) (h2 : ∀ θ, HasDerivAt φ₁ (-(k ^ 2) * φ θ) θ) (θ : ℝ) :
    φ θ = φ 0 * Real.cos (k * θ) + φ₁ 0 / k * Real.sin (k * θ) := by
  set a : ℝ := φ 0 with ha
  set b : ℝ := φ₁ 0 / k with hb
  have hbk : b * k = φ₁ 0 := by rw [hb]; field_simp
  let E : ℝ → ℝ := fun x => φ x - (a * Real.cos (k * x) + b * Real.sin (k * x))
  let E₁ : ℝ → ℝ := fun x => φ₁ x - (-(a * k) * Real.sin (k * x) + φ₁ 0 * Real.cos (k * x))
  have hE : ∀ x, HasDerivAt E (E₁ x) x := by
    intro x
    have h := (h1 x).sub (((hasDerivAt_cos_mul_R3AW k x).const_mul a).add
      ((hasDerivAt_sin_mul_R3AW k x).const_mul b))
    convert h using 1
    simp only [E₁]
    rw [← hbk]
    ring
  have hE₁ : ∀ x, HasDerivAt E₁ (-(k ^ 2) * E x) x := by
    intro x
    have h := (h2 x).sub ((((hasDerivAt_sin_mul_R3AW k x).const_mul (-(a * k))).add
      ((hasDerivAt_cos_mul_R3AW k x).const_mul (φ₁ 0))))
    convert h using 1
    simp only [E]
    rw [← hbk]
    ring
  let Q : ℝ → ℝ := fun x => E₁ x ^ 2 + k ^ 2 * E x ^ 2
  have hQ : ∀ x, HasDerivAt Q 0 x := by
    intro x
    have h := ((hE₁ x).pow 2).add (((hE x).pow 2).const_mul (k ^ 2))
    convert h using 1
    simp
    ring
  have hconst : Q θ = Q 0 := is_const_of_deriv_eq_zero (fun x => (hQ x).differentiableAt)
    (fun x => (hQ x).deriv) θ 0
  have hQ0 : Q 0 = 0 := by
    simp only [Q, E, E₁]
    simp [ha]
  have hEθ : E θ = 0 := by
    have h : k ^ 2 * E θ ^ 2 ≤ 0 := by
      have := hconst
      have hsq : 0 ≤ E₁ θ ^ 2 := sq_nonneg _
      rw [hQ0] at this
      simp only [Q] at this
      linarith
    have hk2 : 0 < k ^ 2 := by positivity
    have : E θ ^ 2 ≤ 0 := by nlinarith
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  simp only [E] at hEθ
  linarith

/-- `a cos x + b sin x = A sin (x + α)`：把非零 `(a, b)` 写成 `A sin` 形，平移 `θ₀` 吸收相位。 -/
theorem sin_form_R3AW {a b k : ℝ} (hk : 0 < k) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ θ₀ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      a * Real.cos (k * (θ₀ + t)) + b * Real.sin (k * (θ₀ + t)) = A * Real.sin (k * t) := by
  let z : ℂ := ⟨b, a⟩
  have hz : z ≠ 0 := by
    intro h
    rcases hab with ha | hb
    · exact ha (by simpa [z] using congrArg Complex.im h)
    · exact hb (by simpa [z] using congrArg Complex.re h)
  refine ⟨-(Complex.arg z) / k, ‖z‖, norm_pos_iff.mpr hz, fun t => ?_⟩
  have hb : b = ‖z‖ * Real.cos (Complex.arg z) := (Complex.norm_mul_cos_arg z).symm
  have ha : a = ‖z‖ * Real.sin (Complex.arg z) := (Complex.norm_mul_sin_arg z).symm
  have hx : k * (-(Complex.arg z) / k + t) = k * t - Complex.arg z := by
    field_simp
    ring
  rw [hx, ha, hb, Real.cos_sub, Real.sin_sub]
  have := Real.sin_sq_add_cos_sq (Complex.arg z)
  linear_combination (‖z‖ * Real.sin (k * t)) * this

end DifferentialGeometry.Analysis

end
