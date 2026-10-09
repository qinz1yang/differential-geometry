import DifferentialGeometry.Geometry.Fibration.FinitePacketCalculus
import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization
import DifferentialGeometry.Analysis.Calculus.CutoffAdjustment

/-!
# Abstract chapter 14 calculus rows: FC05, FC10, FC31, FC32 (row-named wrappers)

Blueprint `master207B.tex`: FC05 (`lem:fibration-scaled-cutoff`, 251–296), FC10
(`lem:fibration-joint-cutoff`, 586–650), FC31 (`lem:fibration-adjustment-estimate`, 2808–2838),
FC32 (`lem:fibration-postcomposition`, 2847–2864). These rows are stated for abstract data
(cutoff profiles, maps into Euclidean or Hilbert spaces); the existing kernels prove them. Each
theorem below has the row's hypotheses and the row's conclusions, in the row's notation.

* `fc05_row`: `F_s(u) = (u φ(u/s), s φ(u/s))` (`scaledCutoffBlock s φ`) has `‖DF_s‖ ≤ A`,
  `‖D²F_s‖ ≤ B/s` everywhere, and `‖F_s∘u − F_s∘v‖_{C¹} ≤ (A + BL/s) ε` on a domain `D`;
  `fc05_row_pointwise`: the same bound at one point of a Riemannian domain, stated for the values
  `u(p), v(p)` and the differentials `Du(p), Dv(p) : T → ℝᵏ` on ANY normed space `T` of tangent
  vectors (so the norms may be the `g`-norms); `fc05_row_blocks`: at most `N` orthogonal blocks
  with `s ≥ s_* > 0` give `√N (A + BL/s_*) ε`.
* `fc10_row`: the joint edge network `W` (`jointCutoffNetwork`, `n` edge blocks, `N = n + 1`)
  satisfies `|W| ≤ 20√N Δ`, `‖DW‖ ≤ A_n`, `‖D²W‖ ≤ B_n/Δ` globally, and the `C¹` composition bound
  `(A_n + B_n L₀/Δ) ε` on a domain. The hypothesis `χ(0) = 0` is not needed (strengthening);
  the coordinates `u_j, v` are any linear functionals of norm `≤ 1` (the coordinates of `ℝⁿ⁺¹`).
* `fc31_row`: the adjustment `g = Ψ f` has `|g − f| ≤ aρ`, `‖Dg − Df‖ ≤ abL + dL + e`;
  `fc31_row_plateau`: where `ψ ∘ f = 1` near `x`, `D(π_Q g) = DP ∘ π_Q ∘ Df`, so `π_Q g` is a
  submersion onto whatever `DP D(π_Q f)` is onto.
* `fc32_row`: fibres and kernels are kept (inclusion), `π_{Q⊥} Ψ = π_{Q⊥}`, and for `Q₃ ≤ Q₂` with
  a cutoff depending only on the `Q₂`-coordinates, `π₂ Ψ₃ = Ψ₃₂ π₂`; an injective `Ψ` keeps fibres
  exactly.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

section FC05

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- FC05 (`lem:fibration-scaled-cutoff`): global derivative bounds of `F_s` and the `C¹`
composition bound on a domain `D` of a normed space. -/
theorem fc05_row {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {s C L₁ L₂ : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hvalue : ∀ y, φ y ∈ Icc 0 1)
    (hsupport : tsupport φ ⊆ closedBall 0 C) (hfirst : ∀ y, ‖fderiv ℝ φ y‖ ≤ L₁)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ L₂)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (D : Set X) {u v : X → E}
    (hu : ∀ x ∈ D, DifferentiableAt ℝ u x) (hv : ∀ x ∈ D, DifferentiableAt ℝ v x)
    {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L) (hclose : ∀ x ∈ D, ‖u x - v x‖ ≤ ε)
    (hDclose : ∀ x ∈ D, ‖fderiv ℝ u x - fderiv ℝ v x‖ ≤ ε)
    (hDv : ∀ x ∈ D, ‖fderiv ℝ v x‖ ≤ L) :
    (∀ y, ‖fderiv ℝ (scaledCutoffBlock s φ) y‖ ≤ 1 + (C + 1) * L₁ ∧
      ‖fderiv ℝ (fderiv ℝ (scaledCutoffBlock s φ)) y‖ ≤ (2 * L₁ + (C + 1) * L₂) / s) ∧
    ∀ x ∈ D, max ‖scaledCutoffBlock s φ (u x) - scaledCutoffBlock s φ (v x)‖
      ‖fderiv ℝ (scaledCutoffBlock s φ ∘ u) x - fderiv ℝ (scaledCutoffBlock s φ ∘ v) x‖ ≤
      (1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s * L) * ε :=
  ⟨fun y => scaledCutoffBlock_derivative_bounds hφ hs hC hL₁ hL₂ hvalue hsupport hfirst hsecond y,
    fun x hx => scaledCutoffBlock_c1_comp_sub_le hφ hs hC hL₁ hL₂ hvalue hsupport hfirst hsecond
      (hu x hx) (hv x hx) hε hL (hclose x hx) (hDclose x hx) (hDv x hx)⟩

/-- FC05 at one point of a Riemannian domain: values `y₁ = u(p)`, `y₂ = v(p)` and differentials
`a = Du(p)`, `b = Dv(p)` on any normed space `T` of tangent vectors. -/
theorem fc05_row_pointwise {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {s C L₁ L₂ : ℝ} (hs : 0 < s)
    (hC : 0 ≤ C) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hvalue : ∀ y, φ y ∈ Icc 0 1)
    (hsupport : tsupport φ ⊆ closedBall 0 C) (hfirst : ∀ y, ‖fderiv ℝ φ y‖ ≤ L₁)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ L₂)
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] (y₁ y₂ : E) (a b : T →L[ℝ] E)
    {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L) (hclose : ‖y₁ - y₂‖ ≤ ε) (hDclose : ‖a - b‖ ≤ ε)
    (hDv : ‖b‖ ≤ L) :
    max ‖scaledCutoffBlock s φ y₁ - scaledCutoffBlock s φ y₂‖
      ‖(fderiv ℝ (scaledCutoffBlock s φ) y₁).comp a -
        (fderiv ℝ (scaledCutoffBlock s φ) y₂).comp b‖ ≤
      (1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s * L) * ε := by
  have hUd : HasFDerivAt (fun w : T => y₁ + a w) a 0 := a.hasFDerivAt.const_add y₁
  have hVd : HasFDerivAt (fun w : T => y₂ + b w) b 0 := b.hasFDerivAt.const_add y₂
  have hF : Differentiable ℝ (scaledCutoffBlock s φ) :=
    (contDiff_scaledCutoffBlock hφ s).differentiable (by norm_num)
  have h := scaledCutoffBlock_c1_comp_sub_le hφ hs hC hL₁ hL₂ hvalue hsupport hfirst hsecond
    hUd.differentiableAt hVd.differentiableAt hε hL
    (by simpa using hclose) (by rwa [hUd.fderiv, hVd.fderiv])
    (by rwa [hVd.fderiv])
  have hcU : fderiv ℝ (scaledCutoffBlock s φ ∘ fun w : T => y₁ + a w) 0 =
      (fderiv ℝ (scaledCutoffBlock s φ) y₁).comp a := by
    rw [fderiv_comp 0 (by simpa using hF y₁) hUd.differentiableAt, hUd.fderiv]
    simp
  have hcV : fderiv ℝ (scaledCutoffBlock s φ ∘ fun w : T => y₂ + b w) 0 =
      (fderiv ℝ (scaledCutoffBlock s φ) y₂).comp b := by
    rw [fderiv_comp 0 (by simpa using hF y₂) hVd.differentiableAt, hVd.fderiv]
    simp
  rw [hcU, hcV] at h
  simpa using h

/-- FC05 for at most `N` orthogonal blocks with common bounds and `s ≥ s_* > 0`. -/
theorem fc05_row_blocks {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*}
    [Fintype ι] {N : ℕ} (hN : Fintype.card ι ≤ N)
    (φ : ι → E → ℝ) (s : ι → ℝ) {s₀ C L₁ L₂ ε L : ℝ}
    (hs₀ : 0 < s₀) (hs : ∀ j, s₀ ≤ s j) (hC : 0 ≤ C)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hφ : ∀ j, ContDiff ℝ 2 (φ j)) (hvalue : ∀ j y, φ j y ∈ Icc 0 1)
    (hsupport : ∀ j, tsupport (φ j) ⊆ closedBall 0 C)
    (hfirst : ∀ j y, ‖fderiv ℝ (φ j) y‖ ≤ L₁)
    (hsecond : ∀ j y, ‖fderiv ℝ (fderiv ℝ (φ j)) y‖ ≤ L₂)
    (U V₀ : ι → V → E) (x : V)
    (hU : ∀ j, DifferentiableAt ℝ (U j) x) (hV : ∀ j, DifferentiableAt ℝ (V₀ j) x)
    (hclose : ∀ j, ‖U j x - V₀ j x‖ ≤ ε)
    (hDclose : ∀ j, ‖fderiv ℝ (U j) x - fderiv ℝ (V₀ j) x‖ ≤ ε)
    (hDV : ∀ j, ‖fderiv ℝ (V₀ j) x‖ ≤ L) :
    let F : V → PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)) :=
      fun y => WithLp.toLp 2 (fun j => scaledCutoffBlock (s j) (φ j) (U j y))
    let G : V → PiLp 2 (fun _ : ι => WithLp 2 (E × ℝ)) :=
      fun y => WithLp.toLp 2 (fun j => scaledCutoffBlock (s j) (φ j) (V₀ j y))
    max ‖F x - G x‖ ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤
      Real.sqrt N * ((1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s₀ * L) * ε) := by
  have h := Geometry.Fibration.finite_scaled_packet_c1 φ s hs₀ hs hC hL₁ hL₂ hε hL hφ hvalue
    hsupport hfirst hsecond U V₀ x hU hV hclose hDclose hDV
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.sqrt_le_sqrt (by exact_mod_cast hN)

end FC05

section FC10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- FC10 (`lem:fibration-joint-cutoff`) with `n` edge blocks (`N = n + 1`), constant
`s_j ∈ [1/2, 2]`, profiles bounded by `P ≥ 1` with the row's supports. -/
theorem fc10_row {n : ℕ} {f g h χ : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (hχ : ContDiff ℝ 2 χ)
    {Δ P : ℝ} (hΔ : 1 ≤ Δ) (hP : 1 ≤ P)
    (hfv : ∀ x, f x ∈ Icc 0 1) (hgv : ∀ x, g x ∈ Icc 0 1)
    (hhv : ∀ x, h x ∈ Icc 0 1) (hχv : ∀ x, χ x ∈ Icc 0 1)
    (hDf : ∀ x, ‖fderiv ℝ f x‖ ≤ P) (hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ P)
    (hDh : ∀ x, ‖fderiv ℝ h x‖ ≤ P) (hDχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ P)
    (hDDf : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P)
    (hDDg : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ P)
    (hDDh : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ P)
    (hDDχ : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ P)
    (hfsupp : tsupport f ⊆ Icc (-9) 9) (hhsupp : tsupport h ⊆ Icc (1 / 5) 9)
    (s : Fin n → ℝ) (hs : ∀ i, s i ∈ Icc (1 / 2) 2)
    (u : Fin n → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (D : Set X) {U V : X → E}
    (hU : ∀ x ∈ D, DifferentiableAt ℝ U x) (hV : ∀ x ∈ D, DifferentiableAt ℝ V x)
    {ε L₀ : ℝ} (hε : 0 ≤ ε) (hL₀ : 0 ≤ L₀) (hclose : ∀ x ∈ D, ‖U x - V x‖ ≤ ε)
    (hDclose : ∀ x ∈ D, ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ∀ x ∈ D, ‖fderiv ℝ V x‖ ≤ L₀) :
    let K := 10 * ((n : ℝ) + 1) ^ 2 * P ^ 3
    let An := Real.sqrt ((n : ℝ) + 1) * (2 + 20 * K)
    let Bn := 24 * Real.sqrt ((n : ℝ) + 1) * K
    let W := jointCutoffNetwork Δ s f g h χ u v
    (∀ y, ‖W y‖ ≤ 20 * Real.sqrt ((n : ℝ) + 1) * Δ ∧ ‖fderiv ℝ W y‖ ≤ An ∧
      ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ Bn / Δ) ∧
    ∀ x ∈ D, max ‖W (U x) - W (V x)‖ ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V) x‖ ≤
      (An + Bn * L₀ / Δ) * ε := by
  have hcard : ((Fintype.card (Fin n) : ℕ) : ℝ) = n := by simp
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · have hb := jointCutoffNetwork_bounds hf hg hh hχ hΔ hP hfv hgv hhv hχv hDf hDg hDh hDχ
      hDDf hDDg hDDh hDDχ hfsupp hhsupp s hs u v hu hv y
    simp only [hcard] at hb
    exact hb
  · have hb := jointCutoffNetwork_c1_comp_sub_le hf hg hh hχ hΔ hP hfv hgv hhv hχv hDf hDg hDh
      hDχ hDDf hDDg hDDh hDDχ hfsupp hhsupp s hs u v hu hv (hU x hx) (hV x hx) hε hL₀
      (hclose x hx) (hDclose x hx) (hDV x hx)
    simp only [hcard] at hb
    refine hb.trans_eq ?_
    ring

end FC10

section FC31FC32

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- FC31 (`lem:fibration-adjustment-estimate`): `g = Ψ f` with
`Ψ x = x + ψ(x)(P(π_Q x) − π_Q x)` satisfies `|g − f| ≤ aρ` and `‖Dg − Df‖ ≤ abL + dL + e`. -/
theorem fc31_row {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] {P : H → H} {ψ : H → ℝ} {f : E → H} {x : E}
    (A : H →L[ℝ] H) (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    (hP : DifferentiableAt ℝ P (Q.starProjection (f x))) {a b L d e ρ : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d) (hρ : 0 < ρ)
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hvalue : ‖P (Q.starProjection (f x)) - Q.starProjection (f x)‖ ≤ a * ρ)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ) (hfirst : ‖fderiv ℝ f x‖ ≤ L)
    (hcomparison : ‖fderiv ℝ P (Q.starProjection (f x)) - A‖ ≤ d)
    (hnormal : ‖(ContinuousLinearMap.id ℝ H - A).comp
      (Q.starProjection.comp (fderiv ℝ f x))‖ ≤ e) :
    ‖adjustmentMap Q P ψ (f x) - f x‖ ≤ a * ρ ∧
      ‖fderiv ℝ (fun y => adjustmentMap Q P ψ (f y)) x - fderiv ℝ f x‖ ≤
        a * b * L + d * L + e := by
  have h := projected_cutoff_adjustment_value_derivative_le (F := H) (P := P)
    Q.starProjection (ContinuousLinearMap.id ℝ H) A Q.starProjection_norm_le
    ContinuousLinearMap.norm_id_le hf hψ hP hb hL hd hρ hcutoff hvalue hcutoffDeriv hfirst
    hcomparison hnormal
  simpa only [adjustmentMap_apply, ContinuousLinearMap.id_apply] using h

/-- FC31's plateau clause: where `ψ ∘ f = 1` near `x`, the derivative of `π_Q g = P π_Q f` is
`DP ∘ π_Q ∘ Df`; hence `π_Q g` is onto exactly what `DP D(π_Q f)` is onto. -/
theorem fc31_row_plateau {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] {P : H → H} (hPQ : ∀ z, P z ∈ Q)
    {ψ : H → ℝ} {f : E → H} {x : E} {Df : E →L[ℝ] H} {DP : H →L[ℝ] H}
    (hf : HasFDerivAt f Df x) (hPd : HasFDerivAt P DP (Q.starProjection (f x)))
    (hone : ∀ᶠ y in 𝓝 x, ψ (f y) = 1) :
    (∀ᶠ y in 𝓝 x, Q.starProjection (adjustmentMap Q P ψ (f y)) = P (Q.starProjection (f y))) ∧
      fderiv ℝ (fun y => Q.starProjection (adjustmentMap Q P ψ (f y))) x =
        DP.comp (Q.starProjection.comp Df) ∧
      LinearMap.range ((fderiv ℝ (fun y => Q.starProjection (adjustmentMap Q P ψ (f y))) x :
          E →L[ℝ] H) : E →ₗ[ℝ] H) =
        LinearMap.range ((DP.comp (Q.starProjection.comp Df) : E →L[ℝ] H) : E →ₗ[ℝ] H) := by
  have hd := (hasFDerivAt_starProjection_adjustmentMap_of_eventually_eq_one Q hPQ hf hPd
    hone).fderiv
  refine ⟨?_, hd, by rw [hd]⟩
  filter_upwards [hone] with y hy
  exact starProjection_adjustmentMap_of_eq_one Q hPQ hy

/-- FC32 (`lem:fibration-postcomposition`): fibres and kernels are kept (inclusion), the
`Q⊥`-coordinates are unchanged, an injective adjustment keeps fibres exactly, and for `Q ≤ Q₂`
with a cutoff depending only on the `Q₂`-coordinates the adjustment factors over `π₂`. -/
theorem fc32_row {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] [Qᗮ.HasOrthogonalProjection]
    {P : H → H} (hPQ : ∀ z, P z ∈ Q) (Q₂ : Submodule ℝ H) [Q₂.HasOrthogonalProjection]
    (h32 : Q ≤ Q₂) (ψ' : H → ℝ) (f : E → H) :
    let Ψ := adjustmentMap Q P (ψ' ∘ Q₂.starProjection)
    (∀ p q, f p = f q → Ψ (f p) = Ψ (f q)) ∧
    (∀ x (Df : E →L[ℝ] H) (DΨ : H →L[ℝ] H), HasFDerivAt f Df x → HasFDerivAt Ψ DΨ (f x) →
      LinearMap.ker (Df : E →ₗ[ℝ] H) ≤ LinearMap.ker (fderiv ℝ (Ψ ∘ f) x : E →ₗ[ℝ] H)) ∧
    (Function.Injective Ψ → ∀ p q, Ψ (f p) = Ψ (f q) → f p = f q) ∧
    (∀ y, Qᗮ.starProjection (Ψ y) = Qᗮ.starProjection y) ∧
    (∀ y, Q₂.starProjection (Ψ y) = adjustmentMap Q P ψ' (Q₂.starProjection y)) := by
  intro Ψ
  refine ⟨fun p q hpq => comp_eq_comp_of_eq Ψ hpq, fun x Df DΨ hf hΨ =>
    ker_le_ker_of_hasFDerivAt_comp hf hΨ, fun hinj p q hpq => hinj hpq,
    starProjection_orthogonal_adjustmentMap Q hPQ _, ?_⟩
  exact starProjection_adjustmentMap_of_le Q h32 hPQ ψ'

end FC31FC32

end DifferentialGeometry.Analysis
