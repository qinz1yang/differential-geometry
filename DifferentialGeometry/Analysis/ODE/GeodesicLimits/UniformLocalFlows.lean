import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.ContDiffOnOne
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local flows with uniform constants (CM4.b, steps 2–5)

Steps 2–5 of `exists_common_local_flows_C1_tendsto` (lane CM-L3, successor of CM-L / CM-L2):

* `IsLocalFlow.congr_field`: a local flow of `f` is a local flow of every field agreeing with `f`
  along its orbits; `IsLocalFlow.mono_time`: restriction to a smaller time interval.
* `contDiff_smul_of_tsupport_subset`: a cut-off `χ • V` of a field that is `C^n` on an open set
  containing `tsupport χ` is `C^n` on the whole space.
* `exists_isLocalFlow_mapsTo_of_norm_le`: Picard–Lindelöf with UNIFORM constants: a field bounded by
  `A` everywhere and `M`-Lipschitz on `closedBall z₀ a` has a local flow on
  `closedBall z₀ r × [-T, T]` (as soon as `A T ≤ a - r`) whose orbits stay in `closedBall z₀ a`.
* `exists_hasFDerivAt_flow_coprod`: the derivative of the flow of a globally `C¹` field at
  `(x, t)` is `L.coprod (· • w (Φ (x, t)))`, where `L δ` is the value at `t` of a solution of the
  variational equation along the orbit of `x` starting at `δ` (no opaque proof terms in the
  statement).
* `contDiffAt_flow_of_mem`: the flow is `C¹` near every point of `ball z₀ (r/2) × (-T/2, T/2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.Analysis.ODE.Flow

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local flow of `f` is a local flow of any field `g` that agrees with `f` along the orbits. -/
theorem _root_.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.congr_field
    {f g : ℝ → F → F} {t₀ : ℝ} {x₀ : F} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : F × ℝ → F}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hfg : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc tmin tmax, f t (Φ (x, t)) = g t (Φ (x, t))) :
    IsLocalFlow g t₀ x₀ r tmin tmax Φ where
  minTime_le_initial := hΦ.minTime_le_initial
  initial_le_maxTime := hΦ.initial_le_maxTime
  apply_initial := hΦ.apply_initial
  hasDerivWithinAt := fun x hx t ht => by
    rw [← hfg x hx t ht]
    exact hΦ.hasDerivWithinAt x hx t ht
  continuousOn := hΦ.continuousOn
  exists_lipschitz := hΦ.exists_lipschitz

/-- Restriction of a local flow to a smaller time interval around the initial time. -/
theorem _root_.DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow.mono_time
    {f : ℝ → F → F} {t₀ : ℝ} {x₀ : F} {r : ℝ≥0} {tmin tmax tmin' tmax' : ℝ} {Φ : F × ℝ → F}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) (hmin : tmin ≤ tmin') (hmin' : tmin' ≤ t₀)
    (hmax' : t₀ ≤ tmax') (hmax : tmax' ≤ tmax) :
    IsLocalFlow f t₀ x₀ r tmin' tmax' Φ where
  minTime_le_initial := hmin'
  initial_le_maxTime := hmax'
  apply_initial := hΦ.apply_initial
  hasDerivWithinAt := fun x hx t ht =>
    (hΦ.hasDerivWithinAt x hx t (Icc_subset_Icc hmin hmax ht)).mono (Icc_subset_Icc hmin hmax)
  continuousOn := hΦ.continuousOn.mono (prod_mono subset_rfl (Icc_subset_Icc hmin hmax))
  exists_lipschitz := by
    obtain ⟨L, hL⟩ := hΦ.exists_lipschitz
    exact ⟨L, fun t ht => hL t (Icc_subset_Icc hmin hmax ht)⟩

/-- **Cut-off.** If `V` is `C^n` on an open set `Ω` containing the topological support of the
`C^n` function `χ`, then `χ • V` is `C^n` on the whole space. -/
theorem contDiff_smul_of_tsupport_subset {n : WithTop ℕ∞} {Ω : Set F} (hΩ : IsOpen Ω)
    {χ : F → ℝ} (hχ : ContDiff ℝ n χ) (hχΩ : tsupport χ ⊆ Ω) {V : F → F}
    (hV : ContDiffOn ℝ n V Ω) : ContDiff ℝ n (fun z => χ z • V z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Ω
  · exact hχ.contDiffAt.smul (hV.contDiffAt (hΩ.mem_nhds hz))
  · have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hχΩ h))
    have hzero : (fun y => χ y • V y) =ᶠ[𝓝 z] fun _ => (0 : F) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- **Uniform local flows.** A field bounded by `A` on the whole space and `M`-Lipschitz on
`closedBall z₀ a` has a local flow on `closedBall z₀ r × [-T, T]` whenever `A T ≤ a - r`; its orbits
stay in `closedBall z₀ a`. All constants are explicit, so the same `r, T` serve a whole sequence of
fields with common bounds. -/
theorem exists_isLocalFlow_mapsTo_of_norm_le [CompleteSpace F] {w : F → F} {z₀ : F}
    {a r A M : ℝ≥0} {T : ℝ} (hT : 0 ≤ T) (hw : ∀ z, ‖w z‖ ≤ A)
    (hlip : LipschitzOnWith M w (closedBall z₀ a)) (hAT : (A : ℝ) * T ≤ a - r) :
    ∃ Φ : F × ℝ → F, IsLocalFlow (fun _ z => w z) 0 z₀ r (-T) T Φ ∧
      ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, Φ (x, t) ∈ closedBall z₀ a := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hpl : IsPicardLindelof (fun _ z => w z) (tmin := -T) (tmax := T) ⟨0, h0⟩ z₀ a r A M := by
    refine IsPicardLindelof.of_time_independent (fun z _ => hw z) hlip ?_
    have hmax : max (T - ((⟨0, h0⟩ : Icc (-T) T) : ℝ)) (((⟨0, h0⟩ : Icc (-T) T) : ℝ) - -T) = T := by
      simp
    rw [hmax]
    exact hAT
  obtain ⟨α, hα, L', hL'⟩ := hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨uncurry α, ?_, ?_⟩
  · refine
      { minTime_le_initial := by linarith
        initial_le_maxTime := hT
        apply_initial := fun x hx => (hα x hx).1
        hasDerivWithinAt := fun x hx t ht => (hα x hx).2 t ht
        continuousOn := ?_
        exists_lipschitz := ⟨L', hL'⟩ }
    exact continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
      (fun x hx => HasDerivWithinAt.continuousOn (hα x hx).2) hL'
  · intro x hx t ht
    have hmv := (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := α x) (fun s hs => (hα x hx).2 s hs) (fun s _ => hw _) h0 ht
    have hinit : α x 0 = x := (hα x hx).1
    rw [hinit, sub_zero, Real.norm_eq_abs] at hmv
    have habs : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    have hAt : (A : ℝ) * |t| ≤ A * T := mul_le_mul_of_nonneg_left habs A.coe_nonneg
    rw [mem_closedBall] at hx ⊢
    have htri := dist_triangle (α x t) x z₀
    rw [dist_eq_norm (α x t) x] at htri
    change ‖α x t - x‖ ≤ (A : ℝ) * |t| at hmv
    simp only [uncurry_apply_pair]
    linarith

/-- **Derivative of a flow of a `C¹` field.** At `(x, t)` with `x ∈ ball z₀ r` and `|t| < T`, the
flow has derivative `L.coprod (· • w (Φ (x, t)))`, where `L δ` is the value at time `t` of a
solution of the variational equation along the orbit of `x` with initial value `δ`. -/
theorem exists_hasFDerivAt_flow_coprod [CompleteSpace F] {w : F → F} (hw : ContDiff ℝ 1 w)
    {z₀ : F} {r : ℝ≥0} {T : ℝ} {Φ : F × ℝ → F}
    (hΦ : IsLocalFlow (fun _ z => w z) 0 z₀ r (-T) T Φ) {M : ℝ} (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA : ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, ‖fderiv ℝ w (Φ (x, t))‖ ≤ M)
    {x : F} (hx : x ∈ ball z₀ r) {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    ∃ L : F →L[ℝ] F,
      HasFDerivAt Φ (L.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (w (Φ (x, t))))) (x, t) ∧
      ∀ δ : F, ∃ y : ℝ → F,
        IsVariationalSolutionOn (fun _ z => w z) (fun s => Φ (x, s)) δ 0 y (Icc (-T) T) ∧
          y t = L δ := by
  have hT : 0 < T := by linarith [ht.1, ht.2]
  have hxr : dist x z₀ < r := mem_ball.mp hx
  set r' : ℝ≥0 := ⟨(r : ℝ) - dist x z₀, by linarith⟩ with hr'_def
  have hr'pos : 0 < r' := by
    change (0 : ℝ) < (r : ℝ) - dist x z₀
    linarith
  have hΦx : IsLocalFlow (fun _ z => w z) 0 x r' (-T) T Φ :=
    hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
      change dist x z₀ + ((r : ℝ) - dist x z₀) ≤ r
      linarith)
  have hC1 : ContDiffOn ℝ 1 (uncurry fun (_ : ℝ) (z : F) => w z) univ :=
    (hw.comp contDiff_snd).contDiffOn
  have hsub : Icc (0 - T) (0 + T) ⊆ Icc (-T) T := by
    rw [zero_sub, zero_add]
  have hball : ∀ y ∈ closedBall x (r' : ℝ), y ∈ closedBall z₀ (r : ℝ) := by
    intro y hy
    rw [mem_closedBall] at hy ⊢
    have h1 : dist y x ≤ (r : ℝ) - dist x z₀ := hy
    linarith [dist_triangle y x z₀]
  have hx' : x ∈ closedBall z₀ (r : ℝ) := hball x (mem_closedBall_self hr'pos.le)
  have hAx : ∀ τ ∈ Icc (0 - T) (0 + T),
      ‖fderiv ℝ ((fun (_ : ℝ) (z : F) => w z) τ) (Φ ⟨x, τ⟩)‖ ≤ M :=
    fun τ hτ => hA x hx' τ (hsub hτ)
  have ht' : t ∈ Ioo (0 - T) (0 + T) := by
    rw [zero_sub, zero_add]
    exact ht
  have h := hasFDerivAt_flow_jointly_of_isLocalFlow hΦx hC1 hT hM hMT hsub hAx hr'pos ht'
  refine ⟨_, h, fun δ => ⟨variationalSolutionFun (f := fun _ z => w z)
    (α := fun s => Φ (x, s)) (t₀ := 0) hT hM hMT
    ((hΦx.continuousOn_fderiv_along_orbit hC1 x
      (Metric.mem_closedBall_self (le_of_lt (by exact_mod_cast hr'pos)))).mono hsub) hAx δ,
    ?_, rfl⟩⟩
  have hsol := variationalSolutionFun_isSolution (f := fun _ z => w z)
    (α := fun s => Φ (x, s)) (t₀ := 0) hT hM hMT
    ((hΦx.continuousOn_fderiv_along_orbit hC1 x
      (Metric.mem_closedBall_self (le_of_lt (by exact_mod_cast hr'pos)))).mono hsub) hAx δ
  exact hsol.mono (by rw [zero_sub, zero_add])

/-- **`C¹` regularity of a flow of a `C¹` field**, with explicit radii: the flow is `C¹` near every
point of `ball z₀ (r/2) × (-T/2, T/2)` once `‖Dw‖ ≤ M` along the orbits and `M T < 1`. -/
theorem contDiffAt_flow_of_mem [CompleteSpace F] {w : F → F} (hw : ContDiff ℝ 1 w)
    {z₀ : F} {r : ℝ≥0} {T : ℝ} {Φ : F × ℝ → F}
    (hΦ : IsLocalFlow (fun _ z => w z) 0 z₀ r (-T) T Φ) {M : ℝ} (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA : ∀ x ∈ closedBall z₀ r, ∀ t ∈ Icc (-T) T, ‖fderiv ℝ w (Φ (x, t))‖ ≤ M)
    {x : F} (hx : x ∈ ball z₀ ((r : ℝ) / 2)) {t : ℝ} (ht : t ∈ Ioo (-(T / 2)) (T / 2)) :
    ContDiffAt ℝ 1 Φ (x, t) := by
  have hT : 0 < T := by linarith [ht.1, ht.2]
  have hr : (0 : ℝ) < r := by
    have := mem_ball.mp hx
    linarith [dist_nonneg (x := x) (y := z₀)]
  have hC1 : ContDiffOn ℝ 1 (uncurry fun (_ : ℝ) (z : F) => w z) univ :=
    (hw.comp contDiff_snd).contDiffOn
  have hsub : Icc (0 - T) (0 + T) ⊆ Icc (-T) T := by
    rw [zero_sub, zero_add]
  have hMT' : M * (3 * T / 4) < 1 := by
    have : M * (3 * T / 4) ≤ M * T := mul_le_mul_of_nonneg_left (by linarith) hM
    linarith
  have hon := contDiffOn_flow_of_isLocalFlow hΦ hC1 (T_out := T) (T_mid := 3 * T / 4)
    (T := T / 2) (by linarith) (by linarith) (by linarith) hM hMT' hsub
    (ρ_out := r) (ρ_mid := 3 * r / 4) (ρ := r / 2) (r' := r / 4)
    (by
      change (0 : ℝ) < (r : ℝ) / 4
      linarith)
    (by
      change (r : ℝ) / 2 < 3 * (r : ℝ) / 4
      linarith)
    (by
      change 3 * (r : ℝ) / 4 < r
      linarith)
    (by
      change 3 * (r : ℝ) / 4 + (r : ℝ) / 4 ≤ r
      linarith)
    le_rfl
    (fun y hy τ hτ => hA y hy τ (hsub hτ))
  have hopen : IsOpen (ball z₀ (((r / 2 : ℝ≥0)) : ℝ) ×ˢ Ioo (0 - T / 2) (0 + T / 2)) :=
    isOpen_ball.prod isOpen_Ioo
  refine hon.contDiffAt (hopen.mem_nhds ⟨?_, ?_⟩)
  · change x ∈ ball z₀ ((r : ℝ) / 2)
    exact hx
  · rw [zero_sub, zero_add]
    exact ht

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
