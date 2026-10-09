import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets

/-!
# TCP05: the graph estimate (TG) block by block, at one point (generic part)

Blueprint `master207B.tex`, TCP05 (B:5571–5594): "On `D_i` the actual/model input difference ...
FC10, FC05 and TCP03–TCP04 therefore bound all fixed-scale block errors ...". Every block of
`R_i⁻¹𝓔⁰` near a point `x ∈ D_i` is a fixed `C²` map `G` of actual inputs `V` (possibly times the
variable scale `σ = ρ/R_i`), and the corresponding block of `Φ_i ∘ η_i` is `G(U η_i + u₀)`.

* `tg_block_pointwise_KA6`: `‖R⁻¹f(x) − G(Uη(x) + u₀)‖ ≤ A₁ε` and the directional derivative
  error `≤ (A₁ + A₂L) ε ν(w)` for an actual block `f = R • (G ∘ V)` near `x`, from
  `‖V(x) − (Uη(x) + u₀)‖ ≤ ε`, `‖dV(w) − U dη(w)‖ ≤ εν(w)`, `‖U dη(w)‖ ≤ Lν(w)`.
* `tg_scaled_block_pointwise_KA6`: the same with the variable factor `σ` (`f = (Rσ) • (G ∘ V)`):
  the extra terms `|σ(x) − 1| ‖G(V x)‖` and `|dσ(w)| ‖G(V x)‖ + |σ(x) − 1| ‖DG dV(w)‖` (FC11).
* `fderiv_circleBump_eq_zero_KA6`: the circle bump has derivative zero on its plateau `|v| ≤ 8`.
* `norm_le_of_active_blocks_KA6`: a vector of `ℓ²(⊕_t V_t)` vanishing off `s` with components at
  most `b` on `s` has norm at most `√#s · b`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- The derivative of the model block `a ↦ G (U a + u₀)`. -/
theorem fderiv_affine_comp_apply_KA6 {G : F' → W} (hG : Differentiable ℝ G) (U : Ep →L[ℝ] F')
    (u₀ : F') (a v : Ep) :
    fderiv ℝ (fun a => G (U a + u₀)) a v = fderiv ℝ G (U a + u₀) (U v) := by
  have hk : HasFDerivAt (fun a => U a + u₀) U a := U.hasFDerivAt.add_const u₀
  have h := (hG (U a + u₀)).hasFDerivAt.comp a hk
  rw [show (fun a => G (U a + u₀)) = G ∘ fun a => U a + u₀ from rfl, h.fderiv]
  rfl

/-- **(TG) for one block at a point.** -/
theorem tg_block_pointwise_KA6 {G : F' → W} (hG : ContDiff ℝ 2 G) {A₁ A₂ : ℝ}
    (h1 : ∀ y, ‖fderiv ℝ G y‖ ≤ A₁) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ G) y‖ ≤ A₂)
    {f : M → W} {Vf : M → F'} {x : M} {R : ℝ} (hR : R ≠ 0)
    (hf : f =ᶠ[𝓝 x] fun y => R • G (Vf y)) (hV : MDifferentiableAt I 𝓘(ℝ, F') Vf x)
    (η : M → Ep) (U : Ep →L[ℝ] F') (u₀ : F') (ν : TangentSpace I x → ℝ) {ε L : ℝ}
    (hval : ‖Vf x - (U (η x) + u₀)‖ ≤ ε)
    (hder : ∀ w, ‖mvfderiv I Vf x w - U (mvfderiv I η x w)‖ ≤ ε * ν w)
    (hbd : ∀ w, ‖U (mvfderiv I η x w)‖ ≤ L * ν w) :
    ‖R⁻¹ • f x - G (U (η x) + u₀)‖ ≤ A₁ * ε ∧
      ∀ w, ‖R⁻¹ • mvfderiv I f x w -
        fderiv ℝ (fun a => G (U a + u₀)) (η x) (mvfderiv I η x w)‖ ≤ (A₁ + A₂ * L) * ε * ν w := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hfx : f x = R • G (Vf x) := hf.eq_of_nhds
  have hφ : HasFDerivAt (fun z => R • G z) (R • fderiv ℝ G (Vf x)) (Vf x) :=
    (hGd (Vf x)).hasFDerivAt.const_smul R
  have hdf : ∀ w, mvfderiv I f x w = R • fderiv ℝ G (Vf x) (mvfderiv I Vf x w) := by
    intro w
    rw [mvfderiv_apply_congr_KA2 hf w, mvfderiv_comp_hasFDerivAt hV hφ w]
    rfl
  have hc := fun w => comp_c1_pointwise_KA6 hG h1 h2 (Vf x) (U (η x) + u₀) (mvfderiv I Vf x w)
    (U (mvfderiv I η x w)) hval (hder w) (hbd w)
  refine ⟨?_, fun w => ?_⟩
  · rw [hfx, smul_smul, inv_mul_cancel₀ hR, one_smul]
    exact (hc 0).1
  · rw [hdf w, smul_smul, inv_mul_cancel₀ hR, one_smul, fderiv_affine_comp_apply_KA6 hGd]
    exact (hc w).2

/-- **(TG) for a block with the variable scale `σ`** (FC11's product): an actual block
`f = (Rσ) • (G ∘ V)` near `x`, with `|σ(x) − 1| ≤ s₀`, `|dσ(w)| ≤ s₁ν(w)`, `‖G(V x)‖ ≤ Gm`. -/
theorem tg_scaled_block_pointwise_KA6 {G : F' → W} (hG : ContDiff ℝ 2 G) {A₁ A₂ : ℝ}
    (h1 : ∀ y, ‖fderiv ℝ G y‖ ≤ A₁) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ G) y‖ ≤ A₂)
    {f : M → W} {Vf : M → F'} {σ : M → ℝ} {x : M} {R : ℝ} (hR : R ≠ 0)
    (hf : f =ᶠ[𝓝 x] fun y => (R * σ y) • G (Vf y)) (hV : MDifferentiableAt I 𝓘(ℝ, F') Vf x)
    (hσ : MDifferentiableAt I 𝓘(ℝ, ℝ) σ x)
    (η : M → Ep) (U : Ep →L[ℝ] F') (u₀ : F') (ν : TangentSpace I x → ℝ) {ε L s₀ s₁ Gm : ℝ}
    (hval : ‖Vf x - (U (η x) + u₀)‖ ≤ ε)
    (hder : ∀ w, ‖mvfderiv I Vf x w - U (mvfderiv I η x w)‖ ≤ ε * ν w)
    (hbd : ∀ w, ‖U (mvfderiv I η x w)‖ ≤ L * ν w)
    (hσ0 : |σ x - 1| ≤ s₀) (hσ1 : ∀ w, |mvfderiv I σ x w| ≤ s₁ * ν w) (hGm : ‖G (Vf x)‖ ≤ Gm) :
    ‖R⁻¹ • f x - G (U (η x) + u₀)‖ ≤ s₀ * Gm + A₁ * ε ∧
      ∀ w, ‖R⁻¹ • mvfderiv I f x w -
        fderiv ℝ (fun a => G (U a + u₀)) (η x) (mvfderiv I η x w)‖ ≤
          (s₁ * Gm + s₀ * (A₁ * (L + ε)) + (A₁ + A₂ * L) * ε) * ν w := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans (h1 0)
  have hs₀ : 0 ≤ s₀ := (abs_nonneg _).trans hσ0
  have hfx : f x = (R * σ x) • G (Vf x) := hf.eq_of_nhds
  have hGV : MDifferentiableAt I 𝓘(ℝ, W) (fun y => G (Vf y)) x :=
    (hGd (Vf x)).mdifferentiableAt.comp x hV
  have hRσ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => R * σ y) x :=
    (mdifferentiableAt_const (c := R)).mul hσ
  have hdGV : ∀ w, mvfderiv I (fun y => G (Vf y)) x w =
      fderiv ℝ G (Vf x) (mvfderiv I Vf x w) :=
    fun w => mvfderiv_comp_hasFDerivAt hV (hGd (Vf x)).hasFDerivAt w
  have hdRσ : ∀ w, mvfderiv I (fun y => R * σ y) x w = R * mvfderiv I σ x w := by
    intro w
    rw [mvfderiv_mul_apply_KA2 mdifferentiableAt_const hσ, mvfderiv_const]
    simp
  have hdf : ∀ w, mvfderiv I f x w =
      (R * σ x) • fderiv ℝ G (Vf x) (mvfderiv I Vf x w) +
        (R * mvfderiv I σ x w) • G (Vf x) := by
    intro w
    rw [mvfderiv_apply_congr_KA2 hf w, mvfderiv_fun_smul hRσ hGV]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hdGV, hdRσ]
  have hc := fun w => comp_c1_pointwise_KA6 hG h1 h2 (Vf x) (U (η x) + u₀) (mvfderiv I Vf x w)
    (U (mvfderiv I η x w)) hval (hder w) (hbd w)
  refine ⟨?_, fun w => ?_⟩
  · rw [hfx, smul_smul, ← mul_assoc, inv_mul_cancel₀ hR, one_mul]
    have he : σ x • G (Vf x) - G (U (η x) + u₀) =
        (σ x - 1) • G (Vf x) + (G (Vf x) - G (U (η x) + u₀)) := by
      rw [sub_smul, one_smul]
      abel
    rw [he]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hc 0).1)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hσ0 hGm (norm_nonneg _) hs₀
  · rw [hdf w, fderiv_affine_comp_apply_KA6 hGd, smul_add, smul_smul, smul_smul, ← mul_assoc,
      ← mul_assoc, inv_mul_cancel₀ hR, one_mul, one_mul]
    set D₁ := fderiv ℝ G (Vf x) (mvfderiv I Vf x w) with hD₁
    set D₂ := fderiv ℝ G (U (η x) + u₀) (U (mvfderiv I η x w)) with hD₂
    have he : σ x • D₁ + mvfderiv I σ x w • G (Vf x) - D₂ =
        mvfderiv I σ x w • G (Vf x) + (σ x - 1) • D₁ + (D₁ - D₂) := by
      rw [sub_smul, one_smul]
      abel
    rw [he]
    have hD₁b : ‖D₁‖ ≤ A₁ * ((L + ε) * ν w) := by
      refine ((fderiv ℝ G (Vf x)).le_opNorm _).trans (mul_le_mul (h1 _) ?_ (norm_nonneg _) hA₁)
      have h3 := norm_sub_norm_le (mvfderiv I Vf x w) (U (mvfderiv I η x w))
      have h4 := hder w
      have h5 := hbd w
      nlinarith
    have hb1 : ‖mvfderiv I σ x w • G (Vf x)‖ ≤ s₁ * Gm * ν w := by
      rw [norm_smul, Real.norm_eq_abs]
      have hGm0 : 0 ≤ Gm := (norm_nonneg _).trans hGm
      calc |mvfderiv I σ x w| * ‖G (Vf x)‖ ≤ (s₁ * ν w) * Gm :=
            mul_le_mul (hσ1 w) hGm (norm_nonneg _) ((abs_nonneg _).trans (hσ1 w))
        _ = s₁ * Gm * ν w := by ring
    have hb2 : ‖(σ x - 1) • D₁‖ ≤ s₀ * (A₁ * (L + ε)) * ν w := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |σ x - 1| * ‖D₁‖ ≤ s₀ * (A₁ * ((L + ε) * ν w)) :=
            mul_le_mul hσ0 hD₁b (norm_nonneg _) hs₀
        _ = s₀ * (A₁ * (L + ε)) * ν w := by ring
    have hb3 := (hc w).2
    calc ‖mvfderiv I σ x w • G (Vf x) + (σ x - 1) • D₁ + (D₁ - D₂)‖ ≤
        ‖mvfderiv I σ x w • G (Vf x)‖ + ‖(σ x - 1) • D₁‖ + ‖D₁ - D₂‖ :=
          norm_add₃_le
      _ ≤ s₁ * Gm * ν w + s₀ * (A₁ * (L + ε)) * ν w + (A₁ + A₂ * L) * ε * ν w := by
          linarith
      _ = (s₁ * Gm + s₀ * (A₁ * (L + ε)) + (A₁ + A₂ * L) * ε) * ν w := by ring

end Generic

section Bump

/-- The circle bump has derivative zero on its plateau `‖v‖ ≤ 8`. -/
theorem fderiv_circleBump_eq_zero_KA6 {v : ℝ²} (hv : ‖v‖ ≤ 8) :
    fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v = 0 := by
  have hcont : Continuous (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) :=
    (circleCutoffBump_LC87.contDiff (n := 1)).continuous_fderiv (by simp)
  have hclosed : IsClosed {v : ℝ² | fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v = 0} :=
    isClosed_eq hcont continuous_const
  have hball : ball (0 : ℝ²) 8 ⊆ {v : ℝ² | fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v = 0} := by
    intro y hy
    have hev : (circleCutoffBump_LC87 : ℝ² → ℝ) =ᶠ[𝓝 y] fun _ => 1 := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact circleCutoffBump_LC87.one_of_mem_closedBall (ball_subset_closedBall hz)
    change fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) y = 0
    rw [hev.fderiv_eq, fderiv_const_apply]
  have hcl : closedBall (0 : ℝ²) 8 ⊆
      {v : ℝ² | fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v = 0} := by
    rw [← closure_ball (0 : ℝ²) (by norm_num : (8 : ℝ) ≠ 0)]
    exact closure_minimal hball hclosed
  exact hcl (mem_closedBall_zero_iff.mpr hv)

end Bump

section Sum

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ t, NormedAddCommGroup (V t)]

/-- A vector of `ℓ²(⊕_t V_t)` vanishing off `s`, with components at most `b` on `s`, has norm at
most `√#s · b`. -/
theorem norm_le_of_active_blocks_KA6 (v : PiLp 2 V) (s : Finset κ) {b : ℝ} (hb : 0 ≤ b)
    (hs : ∀ t ∈ s, ‖v t‖ ≤ b) (hz : ∀ t, t ∉ s → v t = 0) :
    ‖v‖ ≤ Real.sqrt (s.card : ℝ) * b := by
  classical
  have hsq : ‖v‖ ^ 2 ≤ (s.card : ℝ) * b ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ t, ‖v t‖ ^ 2 = ∑ t, if t ∈ s then ‖v t‖ ^ 2 else 0 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases ht : t ∈ s
          · rw [ite_eq_left ht]
          · rw [ite_eq_right ht, hz t ht, norm_zero]
            norm_num
      _ ≤ ∑ t, if t ∈ s then b ^ 2 else 0 := by
          refine Finset.sum_le_sum fun t _ => ?_
          by_cases ht : t ∈ s
          · rw [ite_eq_left ht, ite_eq_left ht]
            exact pow_le_pow_left₀ (norm_nonneg _) (hs t ht) 2
          · rw [ite_eq_right ht, ite_eq_right ht]
      _ = (s.card : ℝ) * b ^ 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have h0 : 0 ≤ Real.sqrt (s.card : ℝ) * b := by positivity
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact hsq

end Sum

end DifferentialGeometry.Geometry.Collapse
