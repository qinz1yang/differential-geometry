import DifferentialGeometry.Analysis.ODE.GeodesicLimits.UniformLocalFlows
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.TwoSidedGronwall
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.FrechetDerivative

/-!
# Comparison of two local flows and of their derivatives (CM4.b, steps 6–7)

* `gronwallBound_zero_le_mul_exp`: `gronwallBound 0 K ε x ≤ ε x e^{K x}` for `K, ε, x ≥ 0`.
* `norm_flow_sub_le`: two local flows from the same initial points, the second field
  `M`-Lipschitz on a set `S` containing all orbits, the fields `η`-close on `S`:
  `‖Φ₁ (x, t) - Φ₂ (x, t)‖ ≤ η |t| e^{M |t|}`.
* `norm_sub_le_of_linear_odes`: two solutions of linear equations `y' = A₁ y`, `y' = A₂ y` with
  the same value at `t₀`, `‖A₂‖ ≤ M`, `‖A₁ - A₂‖ ≤ ε`, `‖y₁‖ ≤ B`:
  `‖y₁ t - y₂ t‖ ≤ ε B |t - t₀| e^{M |t - t₀|}`.
* `norm_fderiv_flow_sub_le`: the derivatives of two flows of `C¹` fields differ by at most
  `ε e^{MT} T e^{MT} + ‖w₁ (Φ₁ q) - w₂ (Φ₂ q)‖`, where `ε` bounds `‖Dw₁ (Φ₁) - Dw₂ (Φ₂)‖` along
  the orbit.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.Analysis.ODE.Flow

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `gronwallBound 0 K ε x ≤ ε x e^{K x}` for nonnegative `K`, `ε`, `x`. -/
theorem gronwallBound_zero_le_mul_exp {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · rw [← hK0, gronwallBound_K0]
    simp
  · exact Flow.gronwallBound_zero_le hKpos hε hx

/-- **`C⁰` comparison of two local flows.** -/
theorem norm_flow_sub_le {w₁ w₂ : F → F} {z₀ : F} {r : ℝ≥0} {T : ℝ} {Φ₁ Φ₂ : F × ℝ → F}
    (h₁ : IsLocalFlow (fun _ z => w₁ z) 0 z₀ r (-T) T Φ₁)
    (h₂ : IsLocalFlow (fun _ z => w₂ z) 0 z₀ r (-T) T Φ₂) {S : Set F} {M : ℝ≥0} {η : ℝ}
    (hlip : LipschitzOnWith M w₂ S) (hη : ∀ z ∈ S, ‖w₁ z - w₂ z‖ ≤ η)
    (h₁S : ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, Φ₁ (x, t) ∈ S)
    (h₂S : ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, Φ₂ (x, t) ∈ S)
    {x : F} (hx : x ∈ closedBall z₀ r) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖Φ₁ (x, t) - Φ₂ (x, t)‖ ≤ η * |t| * Real.exp (M * |t|) := by
  have ht₀ : (0 : ℝ) ∈ Icc (-T) T := h₁.t₀_mem_Icc
  have hη0 : 0 ≤ η := le_trans (norm_nonneg _) (hη _ (h₁S x hx 0 ht₀))
  have hg := dist_le_gronwallBound_of_approx_trajectories_Icc (v := fun _ => w₂) (S := S) (K := M)
    (fun _ => hlip) (f := fun s => Φ₁ (x, s)) (g := fun s => Φ₂ (x, s))
    (f' := fun s => w₁ (Φ₁ (x, s))) (g' := fun s => w₂ (Φ₂ (x, s))) (εf := η) (εg := 0)
    (δ := 0) ht₀ (fun s hs => h₁.hasDerivWithinAt x hx s hs)
    (fun s hs => h₂.hasDerivWithinAt x hx s hs)
    (fun s hs => by
      rw [dist_eq_norm]
      exact hη _ (h₁S x hx s hs))
    (fun s _ => by simp)
    (fun s hs => h₁S x hx s hs) (fun s hs => h₂S x hx s hs)
    (by rw [h₁.apply_initial x hx, h₂.apply_initial x hx, dist_self]) t ht
  rw [add_zero, sub_zero, dist_eq_norm] at hg
  exact hg.trans (gronwallBound_zero_le_mul_exp M.coe_nonneg hη0 (abs_nonneg t))

/-- **Comparison of two linear equations** `y₁' = A₁ y₁`, `y₂' = A₂ y₂` on `[a, b]` with the same
value at `t₀`. -/
theorem norm_sub_le_of_linear_odes {A₁ A₂ : ℝ → F →L[ℝ] F} {y₁ y₂ : ℝ → F} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) {M : ℝ≥0} {ε B : ℝ}
    (hy₁ : ∀ t ∈ Icc a b, HasDerivWithinAt y₁ (A₁ t (y₁ t)) (Icc a b) t)
    (hy₂ : ∀ t ∈ Icc a b, HasDerivWithinAt y₂ (A₂ t (y₂ t)) (Icc a b) t)
    (hA₂ : ∀ t ∈ Icc a b, ‖A₂ t‖ ≤ M) (hA : ∀ t ∈ Icc a b, ‖A₁ t - A₂ t‖ ≤ ε)
    (hB : ∀ t ∈ Icc a b, ‖y₁ t‖ ≤ B) (h0 : y₁ t₀ = y₂ t₀) :
    ∀ t ∈ Icc a b, ‖y₁ t - y₂ t‖ ≤ ε * B * |t - t₀| * Real.exp (M * |t - t₀|) := by
  classical
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hA t₀ ht₀)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB t₀ ht₀)
  set v : ℝ → F → F := fun t y => (if t ∈ Icc a b then A₂ t else 0) y with hv_def
  have hv : ∀ t, LipschitzOnWith M (v t) univ := by
    intro t
    refine LipschitzOnWith.of_dist_le_mul fun y _ z _ => ?_
    rw [dist_eq_norm, dist_eq_norm]
    simp only [hv_def]
    rw [← map_sub]
    split_ifs with ht
    · exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hA₂ t ht) (norm_nonneg _))
    · simp only [_root_.zero_apply, norm_zero]
      positivity
  intro t ht
  have hg := dist_le_gronwallBound_of_approx_trajectories_Icc (v := v) (S := univ) (K := M)
    hv (f := y₁) (g := y₂) (f' := fun s => A₁ s (y₁ s)) (g' := fun s => A₂ s (y₂ s))
    (εf := ε * B) (εg := 0) (δ := 0) ht₀ hy₁ hy₂
    (fun s hs => by
      simp only [hv_def, hs, ↓reduceIte]
      rw [dist_eq_norm, ← _root_.sub_apply]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hA s hs) (hB s hs) (norm_nonneg _) hε0))
    (fun s hs => by simp only [hv_def, hs, ↓reduceIte, dist_self, le_refl])
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
    (by rw [h0, dist_self]) t ht
  rw [add_zero, dist_eq_norm] at hg
  refine hg.trans ?_
  have h := gronwallBound_zero_le_mul_exp M.coe_nonneg (mul_nonneg hε0 hB0)
    (abs_nonneg (t - t₀))
  exact h

/-- **Comparison of the derivatives of two flows of `C¹` fields.** At `(x, t)` with
`x ∈ ball z₀ r`, `|t| < T`, if `‖Dw₁ (Φ₁ (x, s)) - Dw₂ (Φ₂ (x, s))‖ ≤ ε` along the orbit, then
`‖DΦ₁ (x, t) - DΦ₂ (x, t)‖ ≤ ε e^{MT} T e^{MT} + ‖w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t))‖`. -/
theorem norm_fderiv_flow_sub_le [CompleteSpace F] {w₁ w₂ : F → F} (hw₁ : ContDiff ℝ 1 w₁)
    (hw₂ : ContDiff ℝ 1 w₂) {z₀ : F} {r : ℝ≥0} {T : ℝ} {Φ₁ Φ₂ : F × ℝ → F}
    (h₁ : IsLocalFlow (fun _ z => w₁ z) 0 z₀ r (-T) T Φ₁)
    (h₂ : IsLocalFlow (fun _ z => w₂ z) 0 z₀ r (-T) T Φ₂) {M : ℝ≥0} (hMT : M * T < 1)
    (hA₁ : ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, ‖fderiv ℝ w₁ (Φ₁ (x, t))‖ ≤ M)
    (hA₂ : ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, ‖fderiv ℝ w₂ (Φ₂ (x, t))‖ ≤ M)
    {x : F} (hx : x ∈ ball z₀ r) {ε : ℝ}
    (hε : ∀ s ∈ Icc (-T) T, ‖fderiv ℝ w₁ (Φ₁ (x, s)) - fderiv ℝ w₂ (Φ₂ (x, s))‖ ≤ ε)
    {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    ‖fderiv ℝ Φ₁ (x, t) - fderiv ℝ Φ₂ (x, t)‖ ≤
      ε * Real.exp (M * T) * (T * Real.exp (M * T)) + ‖w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t))‖ := by
  have hT : 0 < T := by linarith [ht.1, ht.2]
  have ht₀ : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have htI : t ∈ Icc (-T) T := Ioo_subset_Icc_self ht
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hε 0 ht₀)
  have hx' : x ∈ closedBall z₀ (r : ℝ) := ball_subset_closedBall hx
  obtain ⟨L₁, hL₁, hy₁⟩ := exists_hasFDerivAt_flow_coprod hw₁ h₁ M.coe_nonneg hMT hA₁ hx ht
  obtain ⟨L₂, hL₂, hy₂⟩ := exists_hasFDerivAt_flow_coprod hw₂ h₂ M.coe_nonneg hMT hA₂ hx ht
  rw [hL₁.fderiv, hL₂.fderiv]
  have hE : 0 ≤ Real.exp (M * T) := (Real.exp_pos _).le
  have hC0 : 0 ≤ ε * Real.exp (M * T) * (T * Real.exp (M * T)) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hC0 (norm_nonneg _)) fun p => ?_
  rw [_root_.sub_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  have hsplit : L₁ p.1 + p.2 • w₁ (Φ₁ (x, t)) - (L₂ p.1 + p.2 • w₂ (Φ₂ (x, t))) =
      (L₁ p.1 - L₂ p.1) + p.2 • (w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t))) := by
    rw [smul_sub]; abel
  rw [hsplit]
  -- the variational part
  obtain ⟨y₁, hy₁sol, hy₁t⟩ := hy₁ p.1
  obtain ⟨y₂, hy₂sol, hy₂t⟩ := hy₂ p.1
  have hB : ∀ s ∈ Icc (-T) T, ‖y₁ s‖ ≤ Real.exp (M * T) * ‖p.1‖ := by
    intro s hs
    have hsol' : IsVariationalSolutionOn (fun _ z => w₁ z) (fun s => Φ₁ (x, s)) p.1 0 y₁
        (Icc (0 - T) (0 + T)) := by
      rw [zero_sub, zero_add]
      exact hy₁sol
    have h := IsVariationalSolutionOn.norm_le_exp_of_mem_Icc hT.le M.coe_nonneg hsol'
      (fun τ hτ => hA₁ x hx' τ (by rw [zero_sub, zero_add] at hτ; exact hτ)) s
      (by rw [zero_sub, zero_add]; exact hs)
    rw [mul_comm]
    exact h
  have hlin := norm_sub_le_of_linear_odes (A₁ := fun s => fderiv ℝ w₁ (Φ₁ (x, s)))
    (A₂ := fun s => fderiv ℝ w₂ (Φ₂ (x, s))) ht₀ (M := M) (ε := ε)
    (B := Real.exp (M * T) * ‖p.1‖) hy₁sol.2 hy₂sol.2 (fun s hs => hA₂ x hx' s hs) hε hB
    (by rw [hy₁sol.1, hy₂sol.1]) t htI
  rw [sub_zero, hy₁t, hy₂t] at hlin
  have habs : |t| ≤ T := abs_le.mpr ⟨htI.1, htI.2⟩
  have hexp : Real.exp (M * |t|) ≤ Real.exp (M * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs M.coe_nonneg)
  have hvar : ‖L₁ p.1 - L₂ p.1‖ ≤ ε * Real.exp (M * T) * (T * Real.exp (M * T)) * ‖p‖ := by
    refine hlin.trans ?_
    have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    calc ε * (Real.exp (M * T) * ‖p.1‖) * |t| * Real.exp (M * |t|)
        ≤ ε * (Real.exp (M * T) * ‖p‖) * T * Real.exp (M * T) := by gcongr
      _ = ε * Real.exp (M * T) * (T * Real.exp (M * T)) * ‖p‖ := by ring
  have hfield : ‖p.2 • (w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t)))‖ ≤
      ‖w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t))‖ * ‖p‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_snd_le p) (norm_nonneg _)
  calc ‖(L₁ p.1 - L₂ p.1) + p.2 • (w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t)))‖
      ≤ ‖L₁ p.1 - L₂ p.1‖ + ‖p.2 • (w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t)))‖ := norm_add_le _ _
    _ ≤ ε * Real.exp (M * T) * (T * Real.exp (M * T)) * ‖p‖ +
        ‖w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t))‖ * ‖p‖ := add_le_add hvar hfield
    _ = (ε * Real.exp (M * T) * (T * Real.exp (M * T)) +
        ‖w₁ (Φ₁ (x, t)) - w₂ (Φ₂ (x, t))‖) * ‖p‖ := by ring

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
