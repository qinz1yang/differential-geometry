import DifferentialGeometry.Analysis.ODE.GeodesicLimits.UniformInverse
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.SprayConvergence
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.SprayEstimates

/-!
# Uniform short joining geodesics in a chart (LFR09, chart kernel)

LFR09 (blueprint A:25443) in chart form, for Christoffel fields `Γ i → Γ∞` in `C¹` on the compact
subsets of an open set `U` of a finite-dimensional space (for `C²` metrics `h_i → g` in `C²` this
is the `C¹` convergence of `raisedKoszulOp (h_i ·) (fderiv h_i ·)`):

* `exists_local_short_geodesics`: around every `x₀ ∈ U` there are `b, τ, L > 0` such that, for a
  tail of `i`, any `x ∈ closedBall x₀ b` and `y` with `‖y - x‖ ≤ τ` are joined by a `Γ i`-geodesic
  `γ : [0, 1] → U` with `‖γ'‖ ≤ L ‖y - x‖`.
* `exists_short_geodesics_of_isCompact`: the same, uniformly for `x` in a compact `C ⊆ U`.

Route (blueprint proof): CM4.b for the geodesic sprays at `(x₀, 0)`; orbits confined near their
initial points on a common time `τ₀`; the spray estimates give `exp_x(0) = x` and
`D_w exp_{x₀}(0) = τ₀ · I` for the limit; the uniform inverse radius
(`exists_uniform_surjOn_of_mapCPConvergenceOn_one`) solves `exp_x^{i}(w) = y`; rescaling time by
`τ₀` gives the geodesic on `[0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric Asymptotics
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable local instance shortGeodBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance shortGeodBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

/-- **LFR09, local chart kernel.** -/
theorem exists_local_short_geodesics {U : Set E} (hU : IsOpen U)
    {Γ : ℕ → E → E →L[ℝ] E →L[ℝ] E} {ΓInf : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ∀ i, ContDiffOn ℝ 1 (Γ i) U) (hΓInf : ContDiffOn ℝ 1 ΓInf U)
    (hconv : ∀ C, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1 Γ ΓInf) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ b τ L : ℝ, 0 < b ∧ 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ closedBall x₀ b, ∀ y : E,
      ‖y - x‖ ≤ τ → ∃ γ γ' : ℝ → E, γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U ∧
        HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
        HasDerivWithinAt γ' (-(Γ i (γ t) (γ' t) (γ' t))) (Icc 0 1) t ∧ ‖γ' t‖ ≤ L * ‖y - x‖ := by
  classical
  have hUo : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  obtain ⟨ρ₀, T, Φ, ΦInf, hρ₀, hT, hΦInf, hΦ, hCInf, hCi, hconvΦ⟩ :=
    exists_common_local_flows_C1_tendsto hUo (fun i (q : E × E) => (q.2, -(Γ i q.1 q.2 q.2)))
      (fun q => (q.2, -(ΓInf q.1 q.2 q.2))) (fun i => contDiffOn_spray (hΓ i))
      (contDiffOn_spray hΓInf) (fun C hC hCU => mapCPConvergenceOn_spray hU hΓ hΓInf hconv hC hCU)
      (z₀ := (x₀, 0)) ⟨hx₀, mem_univ _⟩
  -- a compact ball in `U` and the radius of the initial box
  obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set r₁ : ℝ := ε₁ / 2 with hr₁_def
  have hr₁ : 0 < r₁ := by positivity
  have hK₁U : closedBall x₀ r₁ ⊆ U := (closedBall_subset_ball (by linarith)).trans hε₁U
  set ρ : ℝ := min (ρ₀ : ℝ) (r₁ / 2) with hρ_def
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  set B : Set (E × E) := closedBall x₀ ρ ×ˢ closedBall (0 : E) ρ with hB_def
  have hBc : IsCompact B := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hBρ₀ : B ⊆ closedBall (x₀, (0 : E)) (ρ₀ : ℝ) := by
    rw [← closedBall_prod_same]
    exact prod_mono (closedBall_subset_closedBall (min_le_left _ _))
      (closedBall_subset_closedBall (min_le_left _ _))
  have hBT : B ×ˢ Icc (-T) T ⊆ closedBall (x₀, (0 : E)) (ρ₀ : ℝ) ×ˢ Icc (-T) T :=
    prod_mono hBρ₀ subset_rfl
  -- confinement for a common short time
  set δ : ℝ := r₁ / 2 with hδ_def
  obtain ⟨τ₀, hτ₀, hτ₀T, hInfδ, hiδ⟩ := exists_time_dist_le_of_tendstoUniformlyOn hBc hT
    (hΦInf.continuousOn.mono hBT) (fun q hq => hΦInf.apply_initial q (hBρ₀ hq))
    ((tendstoUniformlyOn_of_cPConvergence (hconvΦ.mono_order (Nat.zero_le 1))).mono hBT)
    (δ := δ) (by positivity)
  set R' : ℝ := ρ + δ with hR'_def
  -- bounds for the Christoffel fields on `closedBall x₀ r₁`
  have hK₁ : IsCompact (closedBall x₀ r₁) := isCompact_closedBall _ _
  obtain ⟨G₀, hG₀⟩ := hK₁.exists_bound_of_continuousOn (hΓInf.continuousOn.mono hK₁U)
  set G : ℝ := max G₀ 0 + 1 with hG_def
  have hG : 0 < G := by positivity
  have hΓInfG : ∀ x ∈ closedBall x₀ r₁, ‖ΓInf x‖ ≤ G := fun x hx =>
    (hG₀ x hx).trans (by linarith [le_max_left G₀ 0])
  have hΓG : ∀ᶠ i in atTop, ∀ x ∈ closedBall x₀ r₁, ‖Γ i x‖ ≤ G := by
    have hu := tendstoUniformlyOn_of_cPConvergence ((hconv _ hK₁ hK₁U).mono_order (Nat.zero_le 1))
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 one_pos] with i hi x hx
    have h1 := hi x hx
    rw [dist_eq_norm] at h1
    calc ‖Γ i x‖ = ‖ΓInf x - (ΓInf x - Γ i x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖ΓInf x‖ + ‖ΓInf x - Γ i x‖ := norm_sub_le _ _
      _ ≤ G₀ + 1 := add_le_add (hG₀ x hx) h1.le
      _ ≤ G := by linarith [le_max_left G₀ 0]
  -- the spray estimates along confined orbits
  have hest : ∀ (Θ : E → E →L[ℝ] E →L[ℝ] E) (Ψ : (E × E) × ℝ → E × E),
      IsLocalFlow (fun _ (z : E × E) => (z.2, -(Θ z.1 z.2 z.2))) 0 (x₀, 0) ρ₀ (-T) T Ψ →
      (∀ q ∈ B, ∀ s ∈ Icc (-τ₀) τ₀, dist (Ψ (q, s)) q < δ) →
      (∀ x ∈ closedBall x₀ r₁, ‖Θ x‖ ≤ G) → ∀ q ∈ B,
      (∀ t ∈ Icc 0 τ₀, (Ψ (q, t)).1 ∈ closedBall x₀ r₁ ∧
        ‖(Ψ (q, t)).2‖ ≤ ‖q.2‖ * Real.exp (G * R' * τ₀)) ∧
      ‖(Ψ (q, τ₀)).1 - q.1 - τ₀ • q.2‖ ≤ G * (‖q.2‖ * Real.exp (G * R' * τ₀)) ^ 2 * τ₀ ^ 2 := by
    intro Θ Ψ hΨ hΨδ hΘ q hq
    have hsub : Icc 0 τ₀ ⊆ Icc (-T) T := Icc_subset_Icc (by linarith) hτ₀T
    have hsub' : Icc 0 τ₀ ⊆ Icc (-τ₀) τ₀ := Icc_subset_Icc (by linarith) le_rfl
    have hconf : ∀ t ∈ Icc 0 τ₀, (Ψ (q, t)).1 ∈ closedBall x₀ r₁ ∧ ‖(Ψ (q, t)).2‖ ≤ R' := by
      intro t ht
      have hd := hΨδ q hq t (hsub' ht)
      rw [Prod.dist_eq] at hd
      have hd1 : dist (Ψ (q, t)).1 q.1 < δ := lt_of_le_of_lt (le_max_left _ _) hd
      have hd2 : dist (Ψ (q, t)).2 q.2 < δ := lt_of_le_of_lt (le_max_right _ _) hd
      have hq1 : dist q.1 x₀ ≤ ρ := hq.1
      have hq2 : ‖q.2‖ ≤ ρ := by simpa using hq.2
      have hρr : ρ ≤ r₁ / 2 := min_le_right _ _
      refine ⟨mem_closedBall.mpr ?_, ?_⟩
      · linarith [dist_triangle (Ψ (q, t)).1 q.1 x₀]
      · rw [dist_eq_norm] at hd2
        calc ‖(Ψ (q, t)).2‖ = ‖((Ψ (q, t)).2 - q.2) + q.2‖ := by rw [sub_add_cancel]
          _ ≤ ‖(Ψ (q, t)).2 - q.2‖ + ‖q.2‖ := norm_add_le _ _
          _ ≤ R' := by rw [hR'_def]; linarith
    have hqb : q ∈ closedBall (x₀, (0 : E)) (ρ₀ : ℝ) := hBρ₀ hq
    have horb : ∀ t ∈ Icc 0 τ₀, HasDerivWithinAt (fun s => Ψ (q, s))
        ((Ψ (q, t)).2, -(Θ (Ψ (q, t)).1 (Ψ (q, t)).2 (Ψ (q, t)).2)) (Icc 0 τ₀) t :=
      fun t ht => (hΨ.hasDerivWithinAt q hqb t (hsub ht)).mono hsub
    have hγ : ∀ t ∈ Icc 0 τ₀, HasDerivWithinAt (fun s => (Ψ (q, s)).1) (Ψ (q, t)).2
        (Icc 0 τ₀) t := fun t ht =>
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t (horb t ht)
    have hv : ∀ t ∈ Icc 0 τ₀, HasDerivWithinAt (fun s => (Ψ (q, s)).2)
        (-(Θ (Ψ (q, t)).1 (Ψ (q, t)).2 (Ψ (q, t)).2)) (Icc 0 τ₀) t := fun t ht =>
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t (horb t ht)
    obtain ⟨h1, h2⟩ := spray_estimates hτ₀.le hγ hv (fun t ht => hΘ _ (hconf t ht).1)
      (fun t ht => (hconf t ht).2)
    have hinit : Ψ (q, 0) = q := hΨ.apply_initial q hqb
    simp only [hinit] at h1 h2
    exact ⟨fun t ht => ⟨(hconf t ht).1, h1 t ht⟩, h2⟩
  -- the exponential maps at time `τ₀`
  have hτ₀I : τ₀ ∈ Icc (-T) T := ⟨by linarith, hτ₀T⟩
  have hBmem : ∀ p ∈ B, (p, τ₀) ∈ closedBall (x₀, (0 : E)) (ρ₀ : ℝ) ×ˢ Icc (-T) T :=
    fun p hp => ⟨hBρ₀ hp, hτ₀I⟩
  have hslice : ∀ {Ψ : (E × E) × ℝ → E × E} {p : E × E}, ContDiffAt ℝ 1 Ψ (p, τ₀) →
      ContDiffAt ℝ 1 (fun p : E × E => (Ψ (p, τ₀)).1) p := fun {Ψ} {p} hΨ =>
    (ContDiffAt.comp (g := Ψ) (f := fun p : E × E => (p, τ₀)) p hΨ
      (contDiffAt_id.prodMk contDiffAt_const)).fst
  have hconvG := mapCPConvergenceOn_one_comp_time hτ₀I (hconvΦ.mono_set hBT)
    (by
      filter_upwards [hCi] with i hi p hp
      exact (hi _ (hBmem p hp)).differentiableAt one_ne_zero)
    (fun p hp => (hCInf _ (hBmem p hp)).differentiableAt one_ne_zero)
    (ContinuousLinearMap.fst ℝ E E)
  -- derivative of the limit exponential map at zero velocity
  have hx₀B : ((x₀, (0 : E)) : E × E) ∈ B := ⟨mem_closedBall_self hρ.le, mem_closedBall_self hρ.le⟩
  have hGInf : ContDiffAt ℝ 1 (fun p : E × E => (ΦInf (p, τ₀)).1) (x₀, 0) :=
    hslice (hCInf _ (hBmem _ hx₀B))
  have hInfest := hest ΓInf ΦInf hΦInf hInfδ hΓInfG
  have hdA : HasFDerivAt (fun w : E => (ΦInf ((x₀, w), τ₀)).1) (τ₀ • ContinuousLinearMap.id ℝ E)
      0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have h0 : (ΦInf ((x₀, 0), τ₀)).1 = x₀ := by
      have h := (hInfest _ hx₀B).2
      simp only [norm_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, smul_zero, sub_zero, norm_le_zero_iff, sub_eq_zero] at h
      exact h
    refine IsBigO.trans_isLittleO (g := fun w : E => ‖w‖ ^ 2) ?_ (isLittleO_norm_pow_id one_lt_two)
    refine IsBigO.of_bound (G * Real.exp (G * R' * τ₀) ^ 2 * τ₀ ^ 2) ?_
    filter_upwards [closedBall_mem_nhds (0 : E) hρ] with w hw
    have hwB : ((x₀, w) : E × E) ∈ B := ⟨mem_closedBall_self hρ.le, hw⟩
    have h := (hInfest _ hwB).2
    simp only [zero_add, h0, smul_apply, ContinuousLinearMap.id_apply,
      norm_pow, norm_norm]
    calc ‖(ΦInf ((x₀, w), τ₀)).1 - x₀ - τ₀ • w‖
        ≤ G * (‖w‖ * Real.exp (G * R' * τ₀)) ^ 2 * τ₀ ^ 2 := h
      _ = G * Real.exp (G * R' * τ₀) ^ 2 * τ₀ ^ 2 * ‖w‖ ^ 2 := by ring
  have hdB : HasFDerivAt (fun w : E => (ΦInf ((x₀, w), τ₀)).1)
      ((fderiv ℝ (fun p : E × E => (ΦInf (p, τ₀)).1) (x₀, 0)).comp
        (ContinuousLinearMap.inr ℝ E E)) 0 :=
    (hGInf.differentiableAt one_ne_zero).hasFDerivAt.comp (0 : E) (hasFDerivAt_prodMk_right x₀ 0)
  have hτ₀ne : τ₀ ≠ 0 := hτ₀.ne'
  let A : E ≃L[ℝ] E :=
    { toLinearEquiv := LinearEquiv.smulOfNeZero ℝ E τ₀ hτ₀ne
      continuous_toFun := continuous_const_smul τ₀
      continuous_invFun := continuous_const_smul τ₀⁻¹ }
  have hA : (fderiv ℝ (fun p : E × E => (ΦInf (p, τ₀)).1) (x₀, 0)).comp
      (ContinuousLinearMap.inr ℝ E E) = (A : E →L[ℝ] E) := by
    rw [hdB.unique hdA]
    ext w
    rfl
  obtain ⟨b, c, K, hb, hc, hK, hsurj⟩ := exists_uniform_surjOn_of_mapCPConvergenceOn_one
    (G := fun i (p : E × E) => (Φ i (p, τ₀)).1) (GInf := fun p => (ΦInf (p, τ₀)).1) hconvG
    (by
      filter_upwards [hCi] with i hi p hp
      exact (hslice (hi _ (hBmem p hp))).differentiableAt one_ne_zero)
    (fun p hp => (hslice (hCInf _ (hBmem p hp))).differentiableAt one_ne_zero)
    (hGInf.continuousAt_fderiv one_ne_zero) hρ A hA
  -- final constants
  set b' : ℝ := min b ρ with hb'_def
  set c' : ℝ := min c (ρ / K) with hc'_def
  set L : ℝ := τ₀ * Real.exp (G * R' * τ₀) * K with hL_def
  refine ⟨b', c', L, lt_min hb hρ, lt_min hc (by positivity), by positivity, ?_⟩
  filter_upwards [hsurj, hΦ, hiδ, hΓG] with i hi hΦi hiδ' hΓi x hx y hy
  have hxb : x ∈ closedBall x₀ b := closedBall_subset_closedBall (min_le_left _ _) hx
  have hxρ : x ∈ closedBall x₀ ρ := closedBall_subset_closedBall (min_le_right _ _) hx
  have hiest := hest (Γ i) (Φ i) hΦi hiδ' hΓi
  -- `exp_x^{i}(0) = x`
  have hx0B : ((x, (0 : E)) : E × E) ∈ B := ⟨hxρ, mem_closedBall_self hρ.le⟩
  have hGx : (Φ i ((x, 0), τ₀)).1 = x := by
    have h := (hiest _ hx0B).2
    simp only [norm_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, smul_zero, sub_zero, norm_le_zero_iff, sub_eq_zero] at h
    exact h
  have hyc : ‖y - (Φ i ((x, 0), τ₀)).1‖ ≤ c := by
    rw [hGx]
    exact hy.trans (min_le_left _ _)
  obtain ⟨w, -, hwy, hwK⟩ := hi x hxb y hyc
  rw [hGx, sub_zero] at hwK
  have hwρ : ‖w‖ ≤ ρ := by
    refine hwK.trans ?_
    calc K * ‖y - x‖ ≤ K * (ρ / K) := mul_le_mul_of_nonneg_left (hy.trans (min_le_right _ _))
          hK.le
      _ = ρ := by field_simp
  have hwB : ((x, w) : E × E) ∈ B := ⟨hxρ, by simpa using hwρ⟩
  have hwest := (hiest _ hwB).1
  have hqb : ((x, w) : E × E) ∈ closedBall (x₀, (0 : E)) (ρ₀ : ℝ) := hBρ₀ hwB
  -- the rescaled geodesic
  refine ⟨fun t => (Φ i ((x, w), τ₀ * t)).1, fun t => τ₀ • (Φ i ((x, w), τ₀ * t)).2, ?_, ?_, ?_⟩
  · simp only [mul_zero]
    rw [hΦi.apply_initial _ hqb]
  · simp only [mul_one]
    exact hwy
  intro t ht
  have hs : τ₀ * t ∈ Icc 0 τ₀ := ⟨mul_nonneg hτ₀.le ht.1, by nlinarith [ht.2]⟩
  have hsT : τ₀ * t ∈ Icc (-T) T := ⟨by linarith [hs.1], hs.2.trans hτ₀T⟩
  have hmaps : MapsTo (fun t : ℝ => τ₀ * t) (Icc 0 1) (Icc (-T) T) := fun u hu =>
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have horb := (hΦi.hasDerivWithinAt _ hqb _ hsT).scomp t
    (((hasDerivAt_id t).const_mul τ₀).hasDerivWithinAt (s := Icc 0 1)) hmaps
  have hfst := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t horb
  have hsnd := ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t horb).const_smul
    τ₀
  refine ⟨hK₁U (hwest _ hs).1, ?_, ?_, ?_⟩
  · refine hfst.congr_deriv ?_
    simp
  · refine hsnd.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_snd', mul_one, smul_neg, map_smul, smul_apply, smul_smul]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ₀]
    calc τ₀ * ‖(Φ i ((x, w), τ₀ * t)).2‖ ≤ τ₀ * (‖w‖ * Real.exp (G * R' * τ₀)) :=
          mul_le_mul_of_nonneg_left (hwest _ hs).2 hτ₀.le
      _ ≤ τ₀ * (K * ‖y - x‖ * Real.exp (G * R' * τ₀)) := by gcongr
      _ = L * ‖y - x‖ := by rw [hL_def]; ring

/-- **LFR09, chart kernel, uniform over a compact set.** For Christoffel fields `Γ i → Γ∞` in `C¹` on
the compact subsets of `U` and a compact `C ⊆ U` there are `τ, L > 0` such that, for a tail of `i`,
any `x ∈ C` and `y` with `‖y - x‖ ≤ τ` are joined by a `Γ i`-geodesic `γ : [0, 1] → U` with
`‖γ'‖ ≤ L ‖y - x‖` (so its length in any metric bounded on `U`-compacts is `O(‖y - x‖)`). -/
theorem exists_short_geodesics_of_isCompact {U : Set E} (hU : IsOpen U)
    {Γ : ℕ → E → E →L[ℝ] E →L[ℝ] E} {ΓInf : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ∀ i, ContDiffOn ℝ 1 (Γ i) U) (hΓInf : ContDiffOn ℝ 1 ΓInf U)
    (hconv : ∀ C, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1 Γ ΓInf) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y : E,
      ‖y - x‖ ≤ τ → ∃ γ γ' : ℝ → E, γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U ∧
        HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
        HasDerivWithinAt γ' (-(Γ i (γ t) (γ' t) (γ' t))) (Icc 0 1) t ∧ ‖γ' t‖ ≤ L * ‖y - x‖ := by
  classical
  choose! b τ L hb hτ hL hev using fun x₀ (hx₀ : x₀ ∈ C) =>
    exists_local_short_geodesics hU hΓ hΓInf hconv (hCU hx₀)
  obtain ⟨t, htC, hCt⟩ := hC.elim_nhds_subcover (fun x => ball x (b x))
    (fun x hx => ball_mem_nhds x (hb x hx))
  obtain ⟨τm, hτm, hτmle⟩ : ∃ τm : ℝ, 0 < τm ∧ ∀ x ∈ t, τm ≤ τ x := by
    by_cases ht : t.Nonempty
    · obtain ⟨x₁, hx₁, hmin⟩ := t.exists_min_image τ ht
      exact ⟨τ x₁, hτ x₁ (htC x₁ hx₁), hmin⟩
    · refine ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ ht⟩
  set Lm : ℝ := 1 + ∑ x ∈ t, L x with hLm_def
  have hLpos : ∀ x ∈ t, 0 ≤ L x := fun x hx => (hL x (htC x hx)).le
  have hLm : 0 < Lm := by
    have := Finset.sum_nonneg hLpos
    linarith
  have hLle : ∀ x ∈ t, L x ≤ Lm := fun x hx => by
    have := Finset.single_le_sum hLpos hx
    linarith
  refine ⟨τm, Lm, hτm, hLm, ?_⟩
  filter_upwards [(Filter.eventually_all_finset t).2 fun x hx => hev x (htC x hx)] with i hi
    x hx y hy
  obtain ⟨x₀, hx₀t, hxx₀⟩ := mem_iUnion₂.mp (hCt hx)
  obtain ⟨γ, γ', h0, h1, hγ⟩ := hi x₀ hx₀t x (ball_subset_closedBall hxx₀) y
    (hy.trans (hτmle x₀ hx₀t))
  refine ⟨γ, γ', h0, h1, fun s hs => ?_⟩
  obtain ⟨hU', hd, hd', hb'⟩ := hγ s hs
  exact ⟨hU', hd, hd', hb'.trans (mul_le_mul_of_nonneg_right (hLle x₀ hx₀t) (norm_nonneg _))⟩

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
