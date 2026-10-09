import DifferentialGeometry.Analysis.ODE.GeodesicLimits.FlowComparison
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.DerivativeLimit
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic

/-!
# Common local flows of `C¹`-convergent fields (CM4.b, step 8)

The frozen interface `exists_common_local_flows_C1_tendsto` of D-FOUND (CM4.b, with the two
`ContDiffAt` clauses accepted by main): if `V i → V∞` in `C¹` on the compact subsets of an open set
`Ω` of a finite-dimensional space, then around every `z₀ ∈ Ω` the flows of `V i` (for a tail) and of
`V∞` exist on a common box `closedBall z₀ ρ × [-T, T]`, are `C¹` there, and converge in `C¹`.

* `mapCPConvergenceOn_one_of_forall_norm_sub_le`, `forall_norm_sub_le_of_mapCPConvergenceOn_one`:
  order-one map convergence in terms of values and first derivatives.
* `norm_bump_smul_le`: a cut-off by a function with values in `[0, 1]` keeps sup bounds.
* `flows_C1_tendsto_of_uniform`: the KERNEL for globally `C¹` fields with uniform bounds on a ball
  containing all orbits (C⁰ comparison by Grönwall with the limit field's Lipschitz constant,
  derivative comparison through the variational equations).
* `exists_common_local_flows_C1_tendsto`: the frozen theorem (cut-off `χ • V`, uniform constants,
  Picard–Lindelöf with uniform constants, kernel, field congruence back to `V`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.CheegerGromovCompactness

section Adapters

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The first derivative of a difference, in the form used by `mapDerivNorm`. -/
theorem mapDerivNorm_one_eq {f g : E → G} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    mapDerivNorm 1 f g x = ‖fderiv ℝ f x - fderiv ℝ g x‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y => f y - g y) (x := x) (n := 0)
  rw [norm_iteratedFDeriv_zero, fderiv_fun_sub hf hg] at h
  rw [mapDerivNorm, ← h]

/-- Order-one map convergence from uniform convergence of values and first derivatives. -/
theorem mapCPConvergenceOn_one_of_forall_norm_sub_le {K : Set E} {Φ : ℕ → E → G}
    {ΦInf : E → G} (hΦ : ∀ᶠ i in atTop, ∀ x ∈ K, DifferentiableAt ℝ (Φ i) x)
    (hΦInf : ∀ x ∈ K, DifferentiableAt ℝ ΦInf x)
    (h0 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ x ∈ K, ‖Φ i x - ΦInf x‖ ≤ ε)
    (h1 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ x ∈ K, ‖fderiv ℝ (Φ i) x - fderiv ℝ ΦInf x‖ ≤ ε) :
    MapCPConvergenceOn K 1 Φ ΦInf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp ((hΦ.and (h0 ε hε)).and (h1 ε hε))
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  obtain ⟨⟨hd, hb0⟩, hb1⟩ := hk0 k hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with rfl | rfl
  · rw [mapDerivNorm, norm_iteratedFDeriv_zero]
    exact hb0 x hx
  · rw [mapDerivNorm_one_eq (hd x hx) (hΦInf x hx)]
    exact hb1 x hx

/-- Values and first derivatives from order-one map convergence. -/
theorem forall_norm_sub_le_of_mapCPConvergenceOn_one {K : Set E} {Φ : ℕ → E → G}
    {ΦInf : E → G} (h : MapCPConvergenceOn K 1 Φ ΦInf)
    (hΦ : ∀ i, ∀ x ∈ K, DifferentiableAt ℝ (Φ i) x)
    (hΦInf : ∀ x ∈ K, DifferentiableAt ℝ ΦInf x) :
    ∀ ε > 0, ∀ᶠ i in atTop, ∀ x ∈ K,
      ‖Φ i x - ΦInf x‖ ≤ ε ∧ ‖fderiv ℝ (Φ i) x - fderiv ℝ ΦInf x‖ ≤ ε := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  filter_upwards [eventually_ge_atTop k0] with k hk x hx
  have h0 := hk0 k hk 0 (Nat.zero_le 1) x hx
  have h1 := hk0 k hk 1 le_rfl x hx
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at h0
  rw [mapDerivNorm_one_eq (hΦ k x hx) (hΦInf x hx)] at h1
  exact ⟨h0, h1⟩

end Adapters

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A cut-off by a function with values in `[0, 1]` vanishing off `s` keeps a bound valid on `s`. -/
theorem norm_bump_smul_le {χ : F → ℝ} (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) {s : Set F}
    (hχs : ∀ z ∉ s, χ z = 0) {V : F → F} {A : ℝ} (hA0 : 0 ≤ A) (hV : ∀ z ∈ s, ‖V z‖ ≤ A)
    (z : F) : ‖χ z • V z‖ ≤ A := by
  by_cases hz : z ∈ s
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 z)]
    calc χ z * ‖V z‖ ≤ 1 * A := mul_le_mul (hχ1 z) (hV z hz) (norm_nonneg _) zero_le_one
      _ = A := one_mul A
  · rw [hχs z hz, zero_smul, norm_zero]
    exact hA0

/-- **Kernel of CM4.b for globally `C¹` fields.** Local flows `Φ i` (for a tail) and `Φ∞` of
`W i`, `W∞` on `closedBall z₀ r × [-T, T]` with all orbits in `closedBall z₀ a`, uniform bounds
`‖DW i‖, ‖DW∞‖ ≤ M` on that ball, `M T < 1`, and `W i → W∞`, `DW i → DW∞` uniformly on it. Then on
every smaller box `closedBall z₀ ρ × [-T', T']` (`ρ < r/2`, `T' < T/2`) the flows are `C¹` and
`Φ i → Φ∞` in `C¹`. -/
theorem flows_C1_tendsto_of_uniform [FiniteDimensional ℝ F]
    {W : ℕ → F → F} {WInf : F → F} (hW : ∀ i, ContDiff ℝ 1 (W i)) (hWInf : ContDiff ℝ 1 WInf)
    {z₀ : F} {a r : ℝ≥0} {T : ℝ} {M : ℝ≥0} (hMT : M * T < 1)
    {Φ : ℕ → F × ℝ → F} {ΦInf : F × ℝ → F}
    (hΦ : ∀ᶠ i in atTop, IsLocalFlow (fun _ z => W i z) 0 z₀ r (-T) T (Φ i) ∧
      ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, Φ i (x, t) ∈ closedBall z₀ a)
    (hΦInf : IsLocalFlow (fun _ z => WInf z) 0 z₀ r (-T) T ΦInf)
    (hΦInfS : ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, ΦInf (x, t) ∈ closedBall z₀ a)
    (hDW : ∀ᶠ i in atTop, ∀ z ∈ closedBall z₀ a, ‖fderiv ℝ (W i) z‖ ≤ M)
    (hDWInf : ∀ z ∈ closedBall z₀ a, ‖fderiv ℝ WInf z‖ ≤ M)
    (h0 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ z ∈ closedBall z₀ a, ‖W i z - WInf z‖ ≤ ε)
    (h1 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ z ∈ closedBall z₀ a,
      ‖fderiv ℝ (W i) z - fderiv ℝ WInf z‖ ≤ ε)
    {ρ T' : ℝ} (hρ : ρ < (r : ℝ) / 2) (hT' : T' < T / 2) :
    (∀ q ∈ closedBall z₀ ρ ×ˢ Icc (-T') T', ContDiffAt ℝ 1 ΦInf q) ∧
      (∀ᶠ i in atTop, ∀ q ∈ closedBall z₀ ρ ×ˢ Icc (-T') T', ContDiffAt ℝ 1 (Φ i) q) ∧
      MapCPConvergenceOn (closedBall z₀ ρ ×ˢ Icc (-T') T') 1 Φ ΦInf := by
  set S : Set F := closedBall z₀ (a : ℝ) with hS_def
  set D : Set (F × ℝ) := closedBall z₀ (r : ℝ) ×ˢ Icc (-T) T with hD_def
  have hSc : IsCompact S := isCompact_closedBall z₀ a
  -- membership facts for the small box
  have hK : ∀ q ∈ closedBall z₀ ρ ×ˢ Icc (-T') T',
      q.1 ∈ ball z₀ ((r : ℝ) / 2) ∧ q.2 ∈ Ioo (-(T / 2)) (T / 2) ∧ q.1 ∈ ball z₀ (r : ℝ) ∧
        q.1 ∈ closedBall z₀ (r : ℝ) ∧ q.2 ∈ Ioo (-T) T := by
    intro q hq
    have hq1 : dist q.1 z₀ ≤ ρ := hq.1
    have hq2 := hq.2
    have hr0 : (0 : ℝ) ≤ r := r.coe_nonneg
    have hT0 : 0 < T := by linarith [hq2.1, hq2.2]
    refine ⟨mem_ball.mpr (by linarith), ⟨by linarith [hq2.1], by linarith [hq2.2]⟩,
      mem_ball.mpr (by linarith), mem_closedBall.mpr (by linarith),
      ⟨by linarith [hq2.1], by linarith [hq2.2]⟩⟩
  -- Lipschitz constant of the limit field
  have hlip : LipschitzOnWith M WInf S :=
    (convex_closedBall z₀ (a : ℝ)).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z _ => (hWInf.differentiable one_ne_zero) z)
      (fun z hz => by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact hDWInf z hz)
  -- C⁰ comparison on the whole box
  have hC0 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T) T,
      ‖Φ i (x, t) - ΦInf (x, t)‖ ≤ ε := by
    intro ε hε
    set C : ℝ := T * Real.exp (M * T) with hC_def
    filter_upwards [hΦ, h0 (ε / (|C| + 1)) (by positivity)] with i hi hi0 x hx t ht
    have h := norm_flow_sub_le hi.1 hΦInf hlip hi0 hi.2 hΦInfS hx ht
    have habs : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    have hexp : Real.exp (M * |t|) ≤ Real.exp (M * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs M.coe_nonneg)
    have hη0 : 0 ≤ ε / (|C| + 1) := by positivity
    have hT0 : 0 ≤ T := by linarith [ht.1, ht.2]
    calc ‖Φ i (x, t) - ΦInf (x, t)‖ ≤ ε / (|C| + 1) * |t| * Real.exp (M * |t|) := h
      _ ≤ ε / (|C| + 1) * T * Real.exp (M * T) :=
          mul_le_mul (mul_le_mul_of_nonneg_left habs hη0) hexp (Real.exp_pos _).le
            (mul_nonneg hη0 hT0)
      _ = ε / (|C| + 1) * C := by rw [hC_def]; ring
      _ ≤ ε / (|C| + 1) * (|C| + 1) := by gcongr; linarith [le_abs_self C]
      _ = ε := by field_simp
  have hTU : TendstoUniformlyOn Φ ΦInf atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hC0 (ε / 2) (by positivity)] with i hi q hq
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (hi q.1 hq.1 q.2 hq.2) (by linarith)
  have hInfD : ∀ q ∈ D, ΦInf q ∈ S := fun q hq => hΦInfS q.1 hq.1 q.2 hq.2
  -- the fields and their derivatives along the orbits
  have hWc := Metric.tendstoUniformlyOn_iff.mp (hTU.comp_continuousAt_of_isCompact hSc hInfD
    (fun y _ => hWInf.continuous.continuousAt))
  have hDc := Metric.tendstoUniformlyOn_iff.mp (hTU.comp_continuousAt_of_isCompact hSc hInfD
    (fun y _ => (hWInf.continuous_fderiv one_ne_zero).continuousAt))
  have hU1 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T) T,
      ‖W i (Φ i (x, t)) - WInf (ΦInf (x, t))‖ ≤ ε := by
    intro ε hε
    filter_upwards [hΦ, h0 (ε / 2) (by positivity), hWc (ε / 2) (by positivity)]
      with i hi hi0 hic x hx t ht
    have h1' := hi0 _ (hi.2 x hx t ht)
    have h2' := hic (x, t) ⟨hx, ht⟩
    rw [dist_eq_norm, norm_sub_rev] at h2'
    calc ‖W i (Φ i (x, t)) - WInf (ΦInf (x, t))‖
        = ‖(W i (Φ i (x, t)) - WInf (Φ i (x, t))) + (WInf (Φ i (x, t)) - WInf (ΦInf (x, t)))‖ := by
          congr 1; abel
      _ ≤ ‖W i (Φ i (x, t)) - WInf (Φ i (x, t))‖ + ‖WInf (Φ i (x, t)) - WInf (ΦInf (x, t))‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1' h2'.le
      _ = ε := by ring
  have hU2 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (W i) (Φ i (x, t)) - fderiv ℝ WInf (ΦInf (x, t))‖ ≤ ε := by
    intro ε hε
    filter_upwards [hΦ, h1 (ε / 2) (by positivity), hDc (ε / 2) (by positivity)]
      with i hi hi1 hic x hx t ht
    have h1' := hi1 _ (hi.2 x hx t ht)
    have h2' := hic (x, t) ⟨hx, ht⟩
    rw [dist_eq_norm (fderiv ℝ WInf (ΦInf (x, t))) (fderiv ℝ WInf (Φ i (x, t))),
      norm_sub_rev] at h2'
    calc ‖fderiv ℝ (W i) (Φ i (x, t)) - fderiv ℝ WInf (ΦInf (x, t))‖
        = ‖(fderiv ℝ (W i) (Φ i (x, t)) - fderiv ℝ WInf (Φ i (x, t))) +
            (fderiv ℝ WInf (Φ i (x, t)) - fderiv ℝ WInf (ΦInf (x, t)))‖ := by
          congr 1; abel
      _ ≤ ‖fderiv ℝ (W i) (Φ i (x, t)) - fderiv ℝ WInf (Φ i (x, t))‖ +
            ‖fderiv ℝ WInf (Φ i (x, t)) - fderiv ℝ WInf (ΦInf (x, t))‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1' h2'.le
      _ = ε := by ring
  -- derivative bounds along the orbits
  have hAInf : ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ WInf (ΦInf (x, t))‖ ≤ M := fun x hx t ht => hDWInf _ (hΦInfS x hx t ht)
  have hAi : ∀ᶠ i in atTop, ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (W i) (Φ i (x, t))‖ ≤ M := by
    filter_upwards [hΦ, hDW] with i hi hDi x hx t ht
    exact hDi _ (hi.2 x hx t ht)
  -- C¹ regularity on the small box
  have hCInf : ∀ q ∈ closedBall z₀ ρ ×ˢ Icc (-T') T', ContDiffAt ℝ 1 ΦInf q := by
    intro q hq
    obtain ⟨hq1, hq2, -, -, -⟩ := hK q hq
    exact contDiffAt_flow_of_mem hWInf hΦInf M.coe_nonneg hMT hAInf hq1 hq2
  have hCi : ∀ᶠ i in atTop, ∀ q ∈ closedBall z₀ ρ ×ˢ Icc (-T') T', ContDiffAt ℝ 1 (Φ i) q := by
    filter_upwards [hΦ, hAi] with i hi hAi' q hq
    obtain ⟨hq1, hq2, -, -, -⟩ := hK q hq
    exact contDiffAt_flow_of_mem (hW i) hi.1 M.coe_nonneg hMT hAi' hq1 hq2
  refine ⟨hCInf, hCi, ?_⟩
  refine mapCPConvergenceOn_one_of_forall_norm_sub_le ?_
    (fun q hq => (hCInf q hq).differentiableAt one_ne_zero) ?_ ?_
  · filter_upwards [hCi] with i hi q hq
    exact (hi q hq).differentiableAt one_ne_zero
  · intro ε hε
    filter_upwards [hC0 ε hε] with i hi q hq
    obtain ⟨-, -, -, hq4, hq5⟩ := hK q hq
    exact hi q.1 hq4 q.2 (Ioo_subset_Icc_self hq5)
  · intro ε hε
    set C : ℝ := Real.exp (M * T) * (T * Real.exp (M * T)) with hC_def
    filter_upwards [hΦ, hAi, hU2 (ε / (2 * (|C| + 1))) (by positivity), hU1 (ε / 2) (by positivity)]
      with i hi hAi' hu2 hu1 q hq
    obtain ⟨-, -, hq3, hq4, hq5⟩ := hK q hq
    have h := norm_fderiv_flow_sub_le (hW i) hWInf hi.1 hΦInf hMT hAi' hAInf hq3
      (fun s hs => hu2 q.1 hq4 s hs) hq5
    have hw := hu1 q.1 hq4 q.2 (Ioo_subset_Icc_self hq5)
    have hε' : 0 ≤ ε / (2 * (|C| + 1)) := by positivity
    calc ‖fderiv ℝ (Φ i) q - fderiv ℝ ΦInf q‖
        ≤ ε / (2 * (|C| + 1)) * Real.exp (M * T) * (T * Real.exp (M * T)) +
          ‖W i (Φ i (q.1, q.2)) - WInf (ΦInf (q.1, q.2))‖ := h
      _ = ε / (2 * (|C| + 1)) * C + ‖W i (Φ i (q.1, q.2)) - WInf (ΦInf (q.1, q.2))‖ := by
          rw [hC_def]; ring
      _ ≤ ε / (2 * (|C| + 1)) * (|C| + 1) + ε / 2 := by
          gcongr; linarith [le_abs_self C]
      _ = ε := by field_simp; ring

/-- **CM4.b (frozen interface of D-FOUND, with the `ContDiffAt` clauses).** If `V i → V∞` in `C¹`
on every compact subset of the open set `Ω`, then around every `z₀ ∈ Ω` there are `ρ, T > 0` and
local flows `Φ i` (for a tail of `i`) of `V i` and `Φ∞` of `V∞` on `closedBall z₀ ρ × [-T, T]`,
all `C¹` near every point of that box, with `Φ i → Φ∞` in `C¹` on it. -/
theorem exists_common_local_flows_C1_tendsto
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Ω : Set F} (hΩ : IsOpen Ω) (V : ℕ → F → F) (VInf : F → F)
    (hV : ∀ i, ContDiffOn ℝ 1 (V i) Ω) (hVInf : ContDiffOn ℝ 1 VInf Ω)
    (hconv : ∀ C, IsCompact C → C ⊆ Ω → MapCPConvergenceOn C 1 V VInf) {z₀ : F} (hz₀ : z₀ ∈ Ω) :
    ∃ (ρ : ℝ≥0) (T : ℝ) (Φ : ℕ → F × ℝ → F) (ΦInf : F × ℝ → F), 0 < (ρ : ℝ) ∧ 0 < T ∧
      IsLocalFlow (fun _ z => VInf z) 0 z₀ ρ (-T) T ΦInf ∧
      (∀ᶠ i in atTop, IsLocalFlow (fun _ z => V i z) 0 z₀ ρ (-T) T (Φ i)) ∧
      (∀ q ∈ closedBall z₀ ρ ×ˢ Icc (-T) T, ContDiffAt ℝ 1 ΦInf q) ∧
      (∀ᶠ i in atTop, ∀ q ∈ closedBall z₀ ρ ×ˢ Icc (-T) T, ContDiffAt ℝ 1 (Φ i) q) ∧
      MapCPConvergenceOn (closedBall z₀ ρ ×ˢ Icc (-T) T) 1 Φ ΦInf := by
  classical
  -- radii: `closedBall z₀ (3R) ⊆ Ω`
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
  set R : ℝ := ε / 4 with hR_def
  have hR : 0 < R := by positivity
  have h3R : closedBall z₀ (3 * R) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεΩ
  set S : Set F := closedBall z₀ R with hS_def
  have hSc : IsCompact S := isCompact_closedBall z₀ R
  have hS3 : S ⊆ closedBall z₀ (3 * R) := closedBall_subset_closedBall (by linarith)
  have hSΩ : S ⊆ Ω := hS3.trans h3R
  have hS2 : ∀ z ∈ S, z ∈ ball z₀ (2 * R) := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  -- cut-off
  let χ : ContDiffBump z₀ := ⟨2 * R, 3 * R, by positivity, by linarith⟩
  have hχΩ : tsupport χ ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact h3R
  have hχ0 : ∀ z, z ∉ ball z₀ (3 * R) → χ z = 0 := fun z hz =>
    χ.zero_of_le_dist (by
      rw [mem_ball, not_lt] at hz
      exact hz)
  set W : ℕ → F → F := fun i z => χ z • V i z with hW_def
  set WInf : F → F := fun z => χ z • VInf z with hWInf_def
  have hW : ∀ i, ContDiff ℝ 1 (W i) := fun i =>
    contDiff_smul_of_tsupport_subset hΩ χ.contDiff hχΩ (hV i)
  have hWInf : ContDiff ℝ 1 WInf := contDiff_smul_of_tsupport_subset hΩ χ.contDiff hχΩ hVInf
  have hWeq : ∀ i, ∀ z ∈ S, W i z = V i z := fun i z hz => by
    simp only [hW_def, χ.one_of_mem_closedBall (ball_subset_closedBall (hS2 z hz)), one_smul]
  have hWInfeq : ∀ z ∈ S, WInf z = VInf z := fun z hz => by
    simp only [hWInf_def, χ.one_of_mem_closedBall (ball_subset_closedBall (hS2 z hz)), one_smul]
  have hDWeq : ∀ i, ∀ z ∈ S, fderiv ℝ (W i) z = fderiv ℝ (V i) z := fun i z hz => by
    have h : W i =ᶠ[𝓝 z] V i := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball (hS2 z hz)] with y hy
      simp only [hW_def, hy, Pi.one_apply, one_smul]
    exact h.fderiv_eq
  have hDWInfeq : ∀ z ∈ S, fderiv ℝ WInf z = fderiv ℝ VInf z := fun z hz => by
    have h : WInf =ᶠ[𝓝 z] VInf := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball (hS2 z hz)] with y hy
      simp only [hWInf_def, hy, Pi.one_apply, one_smul]
    exact h.fderiv_eq
  -- uniform constants
  have hdV : ∀ i, ∀ z ∈ Ω, DifferentiableAt ℝ (V i) z := fun i z hz =>
    ((hV i).contDiffAt (hΩ.mem_nhds hz)).differentiableAt one_ne_zero
  have hdVInf : ∀ z ∈ Ω, DifferentiableAt ℝ VInf z := fun z hz =>
    (hVInf.contDiffAt (hΩ.mem_nhds hz)).differentiableAt one_ne_zero
  obtain ⟨A₀, hA₀⟩ := (isCompact_closedBall z₀ (3 * R)).exists_bound_of_continuousOn
    (hVInf.continuousOn.mono h3R)
  obtain ⟨M₀, hM₀⟩ := hSc.exists_bound_of_continuousOn
    ((hVInf.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hSΩ)
  set A : ℝ≥0 := ⟨max A₀ 0 + 1, by positivity⟩ with hA_def
  set M : ℝ≥0 := ⟨max M₀ 0 + 1, by positivity⟩ with hM_def
  have hA : (0 : ℝ) < A := by
    change (0 : ℝ) < max A₀ 0 + 1
    positivity
  have hM : (0 : ℝ) < M := by
    change (0 : ℝ) < max M₀ 0 + 1
    positivity
  have hA₀A : A₀ + 1 ≤ A := by
    change A₀ + 1 ≤ max A₀ 0 + 1
    linarith [le_max_left A₀ 0]
  have hM₀M : M₀ + 1 ≤ M := by
    change M₀ + 1 ≤ max M₀ 0 + 1
    linarith [le_max_left M₀ 0]
  have hconv3 := forall_norm_sub_le_of_mapCPConvergenceOn_one
    (hconv _ (isCompact_closedBall z₀ (3 * R)) h3R) (fun i z hz => hdV i z (h3R hz))
    (fun z hz => hdVInf z (h3R hz))
  have hχ01 : ∀ z, 0 ≤ χ z := fun z => χ.nonneg
  have hχle : ∀ z, χ z ≤ 1 := fun z => χ.le_one
  have hWbd : ∀ᶠ i in atTop, ∀ z, ‖W i z‖ ≤ A := by
    filter_upwards [hconv3 1 one_pos] with i hi z
    refine norm_bump_smul_le hχ01 hχle hχ0 hA.le (fun y hy => ?_) z
    have hy3 : y ∈ closedBall z₀ (3 * R) := ball_subset_closedBall hy
    calc ‖V i y‖ = ‖(V i y - VInf y) + VInf y‖ := by rw [sub_add_cancel]
      _ ≤ ‖V i y - VInf y‖ + ‖VInf y‖ := norm_add_le _ _
      _ ≤ 1 + A₀ := add_le_add (hi y hy3).1 (hA₀ y hy3)
      _ ≤ A := by linarith
  have hWInfbd : ∀ z, ‖WInf z‖ ≤ A := fun z =>
    norm_bump_smul_le hχ01 hχle hχ0 hA.le
      (fun y hy => (hA₀ y (ball_subset_closedBall hy)).trans (by linarith)) z
  have hDWbd : ∀ᶠ i in atTop, ∀ z ∈ S, ‖fderiv ℝ (W i) z‖ ≤ M := by
    filter_upwards [hconv3 1 one_pos] with i hi z hz
    rw [hDWeq i z hz]
    calc ‖fderiv ℝ (V i) z‖ = ‖(fderiv ℝ (V i) z - fderiv ℝ VInf z) + fderiv ℝ VInf z‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ (V i) z - fderiv ℝ VInf z‖ + ‖fderiv ℝ VInf z‖ := norm_add_le _ _
      _ ≤ 1 + M₀ := add_le_add (hi z (hS3 hz)).2 (hM₀ z hz)
      _ ≤ M := by linarith
  have hDWInfbd : ∀ z ∈ S, ‖fderiv ℝ WInf z‖ ≤ M := fun z hz => by
    rw [hDWInfeq z hz]
    exact (hM₀ z hz).trans (by linarith)
  have hW0 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ z ∈ S, ‖W i z - WInf z‖ ≤ ε := by
    intro ε hε
    filter_upwards [hconv3 ε hε] with i hi z hz
    rw [hWeq i z hz, hWInfeq z hz]
    exact (hi z (hS3 hz)).1
  have hW1 : ∀ ε > 0, ∀ᶠ i in atTop, ∀ z ∈ S, ‖fderiv ℝ (W i) z - fderiv ℝ WInf z‖ ≤ ε := by
    intro ε hε
    filter_upwards [hconv3 ε hε] with i hi z hz
    rw [hDWeq i z hz, hDWInfeq z hz]
    exact (hi z (hS3 hz)).2
  have hlipOf : ∀ w : F → F, ContDiff ℝ 1 w → (∀ z ∈ S, ‖fderiv ℝ w z‖ ≤ M) →
      LipschitzOnWith M w S := fun w hw hb =>
    (convex_closedBall z₀ R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z _ => (hw.differentiable one_ne_zero) z)
      (fun z hz => by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact hb z hz)
  -- common existence time
  set T₀ : ℝ := min (R / (2 * A)) (1 / (2 * M)) with hT₀_def
  have hT₀ : 0 < T₀ := lt_min (by positivity) (by positivity)
  have hAT : (A : ℝ) * T₀ ≤ R - R / 2 := by
    have h1 : (A : ℝ) * T₀ ≤ A * (R / (2 * A)) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hA.le
    have h2 : (A : ℝ) * (R / (2 * A)) = R / 2 := by field_simp
    linarith
  have hMT : (M : ℝ) * T₀ < 1 := by
    have h1 : (M : ℝ) * T₀ ≤ M * (1 / (2 * M)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
    have h2 : (M : ℝ) * (1 / (2 * M)) = 1 / 2 := by field_simp
    linarith
  set a : ℝ≥0 := ⟨R, hR.le⟩ with ha_def
  set r : ℝ≥0 := ⟨R / 2, by positivity⟩ with hr_def
  have hAT' : (A : ℝ) * T₀ ≤ a - r := hAT
  have hex : ∀ w : F → F, (∀ z, ‖w z‖ ≤ A) → LipschitzOnWith M w S →
      ∃ Ψ : F × ℝ → F, IsLocalFlow (fun _ z => w z) 0 z₀ r (-T₀) T₀ Ψ ∧
        ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T₀) T₀, Ψ (x, t) ∈ closedBall z₀ (a : ℝ) :=
    fun w hw hl => exists_isLocalFlow_mapsTo_of_norm_le hT₀.le hw hl hAT'
  -- the flows
  set Φ : ℕ → F × ℝ → F := fun i =>
    if h : ∃ Ψ : F × ℝ → F, IsLocalFlow (fun _ z => W i z) 0 z₀ r (-T₀) T₀ Ψ ∧
        ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T₀) T₀, Ψ (x, t) ∈ closedBall z₀ (a : ℝ)
    then h.choose else fun _ => 0 with hΦ_def
  have hΦ : ∀ᶠ i in atTop, IsLocalFlow (fun _ z => W i z) 0 z₀ r (-T₀) T₀ (Φ i) ∧
      ∀ x ∈ closedBall z₀ (r : ℝ), ∀ t ∈ Icc (-T₀) T₀, Φ i (x, t) ∈ closedBall z₀ (a : ℝ) := by
    filter_upwards [hWbd, hDWbd] with i hi hDi
    have hP := hex (W i) hi (hlipOf (W i) (hW i) hDi)
    simp only [hΦ_def, hP, ↓reduceDIte]
    exact hP.choose_spec
  obtain ⟨ΦInf, hΦInf, hΦInfS⟩ := hex WInf hWInfbd (hlipOf WInf hWInf hDWInfbd)
  -- final box
  set ρ : ℝ≥0 := ⟨R / 8, by positivity⟩ with hρ_def
  have hρr : (ρ : ℝ) < (r : ℝ) / 2 := by
    change R / 8 < R / 2 / 2
    linarith
  have hT' : T₀ / 4 < T₀ / 2 := by linarith
  obtain ⟨hCInf, hCi, hconvΦ⟩ := flows_C1_tendsto_of_uniform hW hWInf hMT hΦ hΦInf hΦInfS hDWbd
    hDWInfbd hW0 hW1 hρr hT'
  have hρsub : closedBall z₀ (ρ : ℝ) ⊆ closedBall z₀ (r : ℝ) :=
    closedBall_subset_closedBall (by
      change R / 8 ≤ R / 2
      linarith)
  have haS : ∀ y ∈ closedBall z₀ (a : ℝ), y ∈ S := fun y hy => hy
  refine ⟨ρ, T₀ / 4, Φ, ΦInf, by
    change (0 : ℝ) < R / 8
    positivity, by positivity, ?_, ?_, hCInf, hCi, hconvΦ⟩
  · refine ((hΦInf.congr_field (g := fun _ z => VInf z) fun x hx t ht =>
      hWInfeq _ (haS _ (hΦInfS x hx t ht))).restrict_center hρsub).mono_time
      (by linarith) (by linarith) (by linarith) (by linarith)
  · filter_upwards [hΦ] with i hi
    exact ((hi.1.congr_field (g := fun _ z => V i z) fun x hx t ht =>
      hWeq i _ (haS _ (hi.2 x hx t ht))).restrict_center hρsub).mono_time
      (by linarith) (by linarith) (by linarith) (by linarith)

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
