import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.BlendKernel
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteRegularity
import DifferentialGeometry.Topology.VectorField.CollarExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Euclidean inputs of the collar straightening at a boundary point

* `exists_abs_deriv_collarTransition_le`, `deriv_collarTransition_eq_zero_of_one_le`: the cutoff
  `collarTransition` has bounded derivative, vanishing on `[1, ∞)`;
* `exists_pos_mul_norm_le_of_injective`: an injective linear map on a finite-dimensional space is
  bounded below;
* `eventually_norm_fderiv_sub_le_of_mapCPConvergenceOn`: `C¹` convergence on a closed ball makes
  the derivatives of the approximants uniformly close, near the centre, to the derivative of the
  limit at the centre;
* `collarJet_close`: the blend kernel (`collarBlend_close`) for the jet model
  `(y, t) ↦ a y + t • b y` on the half-ball region `ball y₀ r ×ˢ [0, r)`, with hypotheses only on
  the data `a`, `b` (the form in which they come from smooth approximation on the boundary).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Function
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.VectorField

theorem deriv_collarTransition_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv collarTransition t = 0 := by
  have h : collarTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < t by linarith)] with s hs
    exact collarTransition_eq_one hs.le
  rw [h.deriv_eq, deriv_const]

theorem exists_abs_deriv_collarTransition_le : ∃ C, ∀ t, |deriv collarTransition t| ≤ C := by
  have hc : Continuous (deriv collarTransition) :=
    contDiff_collarTransition.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv collarTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun t ht => ?_
    rcases not_and_or.mp ht with h | h
    · have h' : collarTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show t < 1 / 3 by linarith [not_le.mp h])] with s hs
        exact collarTransition_eq_zero hs.le
      rw [h'.deriv_eq, deriv_const]
    · exact deriv_collarTransition_eq_zero_of_one_le (not_le.mp h).le
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, fun t => by simpa [Real.norm_eq_abs] using hC t⟩

/-- An injective linear map on a finite-dimensional space is bounded below. -/
theorem exists_pos_mul_norm_le_of_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {L : E →L[ℝ] F}
    (hL : Injective L) : ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖L v‖ := by
  obtain ⟨K, hK, hKL⟩ :=
    (L : E →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
  have hK' : (0 : ℝ) < K := NNReal.coe_pos.mpr hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hK', fun v => ?_⟩
  have h := hKL.le_mul_norm_sub v 0
  rw [inv_mul_le_iff₀ hK']
  simpa using h

/-- `C¹` convergence on a closed ball: near the centre, the derivatives of the approximants are
uniformly close to the derivative of the limit at the centre. -/
theorem eventually_norm_fderiv_sub_le_of_mapCPConvergenceOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U)
    {y₀ : E} {r : ℝ} (hr : 0 < r) (hrU : closedBall y₀ r ⊆ U) {fs : ℕ → E → F} {f : E → F}
    (hconv : MapCPConvergenceOn (closedBall y₀ r) 1 fs f)
    (hfs : ∀ j, DifferentiableOn ℝ (fs j) U) (hf : ContDiffOn ℝ 1 f U) :
    ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r',
      ‖fderiv ℝ (fs j) y - fderiv ℝ f y₀‖ ≤ ε := by
  intro ε hε
  have hd : MapCPConvergenceOn (closedBall y₀ r) 0 (fun j => fderiv ℝ (fs j)) (fderiv ℝ f) := by
    refine MapCPConvergenceOn.fderiv (p := 0) hconv ?_ ?_
    · refine Eventually.of_forall fun j x hx => ?_
      filter_upwards [hU.mem_nhds (hrU hx)] with y hy
      exact (hfs j y hy).differentiableAt (hU.mem_nhds hy)
    · intro x hx
      filter_upwards [hU.mem_nhds (hrU hx)] with y hy
      exact (hf.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  obtain ⟨k₀, hk₀⟩ := hd (ε / 2) (half_pos hε)
  have hy₀ : y₀ ∈ U := hrU (mem_closedBall_self hr.le)
  have hcont : ContinuousAt (fderiv ℝ f) y₀ :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hy₀)
  obtain ⟨r₁, hr₁, hr₁c⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (half_pos hε)
  refine ⟨min r r₁, lt_min hr hr₁, ?_⟩
  filter_upwards [eventually_ge_atTop k₀] with j hj y hy
  have hyr : y ∈ closedBall y₀ r :=
    ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hy)
  have h1 : ‖fderiv ℝ (fs j) y - fderiv ℝ f y‖ ≤ ε / 2 := by
    have h := hk₀ j hj 0 le_rfl y hyr
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero] using h
  have h2 : ‖fderiv ℝ f y - fderiv ℝ f y₀‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    exact (hr₁c (lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _))).le
  calc ‖fderiv ℝ (fs j) y - fderiv ℝ f y₀‖
      = ‖(fderiv ℝ (fs j) y - fderiv ℝ f y) + (fderiv ℝ f y - fderiv ℝ f y₀)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖fderiv ℝ (fs j) y - fderiv ℝ f y‖ + ‖fderiv ℝ f y - fderiv ℝ f y₀‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := add_halves ε

variable {E₁ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Jet blend kernel on a half-ball.** For `G` that is `C¹` on `S = ball y₀ r ×ˢ [0, r)` and
data `a j`, `b j` with `a j ≈ G (·, 0)` at rate `o(δ j)`, `Da j ≈ ∂_y G (y₀, 0)`,
`b j ≈ ∂_t G (y₀, 0)` near `y₀`, and `Db j` bounded near `y₀`, the blends of the models
`a j y + t • b j y` with `G` have derivatives uniformly close to `DG (y₀, 0)` near `(y₀, 0)` and
are `o(δ j)`-close to `G`. -/
theorem collarJet_close {ρ : ℝ → ℝ} (hρd : Differentiable ℝ ρ) {Cρ : ℝ}
    (hρ' : ∀ t, |deriv ρ t| ≤ Cρ) (hρ1 : ∀ t, 1 ≤ t → ρ t = 1)
    (hρd1 : ∀ t, 1 ≤ t → deriv ρ t = 0) (hρ01 : ∀ t, ρ t ∈ Icc (0 : ℝ) 1)
    {y₀ : E₁} {r : ℝ} (hr : 0 < r) {G : E₁ × ℝ → F}
    (hG : ContDiffOn ℝ 1 G (ball y₀ r ×ˢ Ico 0 r))
    {a b : ℕ → E₁ → F} {a' b' : ℕ → E₁ → E₁ →L[ℝ] F}
    (had : ∀ j, ∀ y ∈ ball y₀ r, HasFDerivAt (a j) (a' j y) y)
    (hbd : ∀ j, ∀ y ∈ ball y₀ r, HasFDerivAt (b j) (b' j y) y)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ j, 0 < δ j)
    (ha : ∀ ε > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r, ‖a j y - G (y, 0)‖ ≤ ε * δ j)
    (ha' : ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r',
      ‖a' j y - (fderivWithin ℝ G (ball y₀ r ×ˢ Ico 0 r) (y₀, 0)).comp
        (ContinuousLinearMap.inl ℝ E₁ ℝ)‖ ≤ ε)
    (hb : ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r',
      ‖b j y - fderivWithin ℝ G (ball y₀ r ×ˢ Ico 0 r) (y₀, 0) (0, 1)‖ ≤ ε)
    (hb' : ∃ C, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r', ‖b' j y‖ ≤ C) :
    ∃ X' : ℕ → E₁ × ℝ → (E₁ × ℝ) →L[ℝ] F,
      (∀ j, ∀ z ∈ ball y₀ r ×ˢ Ico 0 r, HasFDerivWithinAt
        (collarBlend ρ (ContinuousLinearMap.snd ℝ E₁ ℝ) (δ j) (fun z => a j z.1 + z.2 • b j z.1) G)
        (X' j z) (ball y₀ r ×ˢ Ico 0 r) z) ∧
      ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ z ∈ (ball y₀ r ×ˢ Ico 0 r) ∩ ball (y₀, 0) r',
        ‖X' j z - fderivWithin ℝ G (ball y₀ r ×ˢ Ico 0 r) (y₀, 0)‖ ≤ ε ∧
        ‖collarBlend ρ (ContinuousLinearMap.snd ℝ E₁ ℝ) (δ j) (fun z => a j z.1 + z.2 • b j z.1) G z
          - G z‖ ≤ ε * δ j := by
  set S := ball y₀ r ×ˢ Ico 0 r with hS
  set G' := fderivWithin ℝ G S with hG'
  have hSu : UniqueDiffOn ℝ S := isOpen_ball.uniqueDiffOn.prod (uniqueDiffOn_Ico 0 r)
  have hz₀ : ((y₀, 0) : E₁ × ℝ) ∈ S := ⟨mem_ball_self hr, left_mem_Ico.2 hr⟩
  have hGd : ∀ z ∈ S, HasFDerivWithinAt G (G' z) S z := fun z hz =>
    ((hG.differentiableOn one_ne_zero) z hz).hasFDerivWithinAt
  have hG'c : ContinuousWithinAt G' S (y₀, 0) :=
    (hG.continuousOn_fderivWithin hSu le_rfl) _ hz₀
  -- the data in operator form
  set T : F →L[ℝ] (ℝ →L[ℝ] F) :=
    ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ) with hT
  have hTv : ∀ (c : F) (v : ℝ), T c v = v • c := fun c v => by simp [hT]
  have hTn : ∀ c : F, ‖T c‖ ≤ ‖c‖ := fun c =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) fun v => by
      rw [hTv, norm_smul, mul_comm]
  set B : ℕ → E₁ → ℝ →L[ℝ] F := fun j y => T (b j y) with hBdef
  set B' : ℕ → E₁ → E₁ →L[ℝ] (ℝ →L[ℝ] F) := fun j y => T.comp (b' j y) with hB'def
  have hBv : ∀ j y v, B j y v = v • b j y := fun j y v => hTv _ _
  have hBd : ∀ j, ∀ y ∈ ball y₀ r, HasFDerivAt (B j) (B' j y) y := fun j y hy =>
    T.hasFDerivAt.comp y (hbd j y hy)
  have hm : ∀ j, (fun z : E₁ × ℝ => a j z.1 + B j z.1 z.2) = fun z => a j z.1 + z.2 • b j z.1 :=
    fun j => funext fun z => by rw [hBv]
  have hinr : (G' (y₀, 0)).comp (ContinuousLinearMap.inr ℝ E₁ ℝ) = T (G' (y₀, 0) (0, 1)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hTv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      show ((0 : E₁), v) = v • ((0 : E₁), (1 : ℝ)) by simp, map_smul]
  have hB : ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r',
      ‖B j y - (G' (y₀, 0)).comp (ContinuousLinearMap.inr ℝ E₁ ℝ)‖ ≤ ε := by
    intro ε hε
    obtain ⟨r', hr', hev⟩ := hb ε hε
    refine ⟨r', hr', hev.mono fun j hj y hy => ?_⟩
    rw [hinr, hBdef, ← map_sub]
    exact (hTn _).trans (hj y hy)
  have hB' : ∃ C, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r', ‖B' j y‖ ≤ C := by
    obtain ⟨C, r', hr', hev⟩ := hb'
    refine ⟨C, r', hr', hev.mono fun j hj y hy => ?_⟩
    have hC : 0 ≤ C := (norm_nonneg _).trans (hj y hy)
    refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
    rw [hB'def, ContinuousLinearMap.comp_apply]
    exact (hTn _).trans (((b' j y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hj y hy) (norm_nonneg _)))
  -- jet estimate and blend kernel
  have hjet := collarBlend_hyp_of_jet (ContinuousLinearMap.id ℝ ℝ) (convex_Ico 0 r)
    (left_mem_Ico.2 hr) zero_le_one
    (fun v hv => by
      rw [one_mul, ContinuousLinearMap.id_apply, Real.norm_eq_abs, abs_of_nonneg hv.1])
    hGd hG'c hδ hδpos ha ha' hB hB'
  have hA : ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ z ∈ S ∩ ball (y₀, 0) r',
      (ContinuousLinearMap.snd ℝ E₁ ℝ) z < δ j →
      ‖jetModelDeriv (a' j z.1) (B j z.1) (B' j z.1) z.2 - G' (y₀, 0)‖ ≤ ε ∧
        ‖G z - (a j z.1 + z.2 • b j z.1)‖ ≤ ε * δ j := by
    intro ε hε
    obtain ⟨r', hr', hev⟩ := hjet ε hε
    refine ⟨r', hr', hev.mono fun j hj z hz hτ => ?_⟩
    have h := hj z hz hτ
    rw [hBv] at h
    exact h
  have hclose := collarBlend_close hρ' hρ1 hρd1 hρ01 (ContinuousLinearMap.snd ℝ E₁ ℝ)
    (S := S) (z₀ := (y₀, 0)) (G := G) (G' := G') hG'c
    (m := fun j z => a j z.1 + z.2 • b j z.1)
    (m' := fun j z => jetModelDeriv (a' j z.1) (B j z.1) (B' j z.1) z.2) hδpos hA
  refine ⟨fun j z => collarBlendDeriv ρ (ContinuousLinearMap.snd ℝ E₁ ℝ) (δ j)
    (fun z => a j z.1 + z.2 • b j z.1) G
    (fun z => jetModelDeriv (a' j z.1) (B j z.1) (B' j z.1) z.2) G' z, fun j z hz => ?_, hclose⟩
  have hmd : HasFDerivWithinAt (fun z : E₁ × ℝ => a j z.1 + z.2 • b j z.1)
      (jetModelDeriv (a' j z.1) (B j z.1) (B' j z.1) z.2) S z := by
    rw [← hm j]
    exact (hasFDerivAt_jetModel (had j z.1 hz.1) (hBd j z.1 hz.1)).hasFDerivWithinAt
  exact hasFDerivWithinAt_collarBlend hρd _ (δ j) hmd (hGd z hz)

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
