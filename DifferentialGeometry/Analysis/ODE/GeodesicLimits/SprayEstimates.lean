import DifferentialGeometry.Analysis.ODE.GeodesicLimits.CommonLocalFlows

/-!
# Estimates for geodesic sprays and for limits of local flows (LFR09 kernel)

* `spray_estimates`: a solution `γ' = v`, `v' = -Γ(γ)(v, v)` on `[0, τ]` with `‖Γ(γ)‖ ≤ G`,
  `‖v‖ ≤ R` satisfies `‖v t‖ ≤ ‖v 0‖ e^{GRτ}` and
  `‖γ τ - γ 0 - τ v 0‖ ≤ G (‖v 0‖ e^{GRτ})² τ²` (zero initial velocity gives a constant curve, and
  the exponential map has derivative `τ · I` at the zero velocity — no ODE uniqueness theorem
  is used).
* `exists_time_dist_le_of_tendstoUniformlyOn`: orbits of uniformly convergent local flows stay
  `δ`-close to their initial points on a common short time interval.
* `mapCPConvergenceOn_one_comp_time`: order-one convergence of flows gives order-one convergence of
  `p ↦ L (Φ i (p, τ))` for a fixed time `τ` and a continuous linear map `L`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance sprayEstBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance sprayEstBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

/-- **Spray estimates.** -/
theorem spray_estimates {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ v : ℝ → E} {τ G R : ℝ} (hτ : 0 ≤ τ)
    (hγ : ∀ t ∈ Icc 0 τ, HasDerivWithinAt γ (v t) (Icc 0 τ) t)
    (hv : ∀ t ∈ Icc 0 τ, HasDerivWithinAt v (-(Γ (γ t) (v t) (v t))) (Icc 0 τ) t)
    (hG : ∀ t ∈ Icc 0 τ, ‖Γ (γ t)‖ ≤ G) (hR : ∀ t ∈ Icc 0 τ, ‖v t‖ ≤ R) :
    (∀ t ∈ Icc 0 τ, ‖v t‖ ≤ ‖v 0‖ * Real.exp (G * R * τ)) ∧
      ‖γ τ - γ 0 - τ • v 0‖ ≤ G * (‖v 0‖ * Real.exp (G * R * τ)) ^ 2 * τ ^ 2 := by
  have h0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ⟩
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0 h0)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 h0)
  have hquad : ∀ t ∈ Icc 0 τ, ‖Γ (γ t) (v t) (v t)‖ ≤ G * ‖v t‖ * ‖v t‖ := fun t ht =>
    ((Γ (γ t) (v t)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (((Γ (γ t)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hG t ht) (norm_nonneg _)))
      (norm_nonneg _))
  -- (i) velocity bound
  have hvel : ∀ t ∈ Icc 0 τ, ‖v t‖ ≤ ‖v 0‖ * Real.exp (G * R * t) := by
    intro t ht
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := v)
      (f' := fun s => -(Γ (γ s) (v s) (v s))) (δ := ‖v 0‖) (K := G * R) (ε := 0) (a := 0) (b := τ)
      (fun s hs => (hv s hs).continuousWithinAt)
      (fun s hs => (hv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hs.1, hs.2⟩) |>.mono_of_mem_nhdsWithin (self_mem_nhdsWithin))
      le_rfl
      (fun s hs => by
        rw [norm_neg, add_zero]
        have hsI := Ico_subset_Icc_self hs
        calc ‖Γ (γ s) (v s) (v s)‖ ≤ G * ‖v s‖ * ‖v s‖ := hquad s hsI
          _ ≤ G * R * ‖v s‖ := by gcongr; exact hR s hsI)
      t ht
    rwa [gronwallBound_ε0, sub_zero] at h
  have hvelτ : ∀ t ∈ Icc 0 τ, ‖v t‖ ≤ ‖v 0‖ * Real.exp (G * R * τ) := fun t ht =>
    (hvel t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hG0 hR0))) (norm_nonneg _))
  refine ⟨hvelτ, ?_⟩
  set B : ℝ := ‖v 0‖ * Real.exp (G * R * τ) with hB_def
  -- (ii) velocity drift
  have hdrift : ∀ t ∈ Icc 0 τ, ‖v t - v 0‖ ≤ G * B ^ 2 * t := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := v) (a := 0) (b := τ)
      (f' := fun s => -(Γ (γ s) (v s) (v s))) (C := G * B ^ 2) hv (fun s hs => by
        have hsI := Ico_subset_Icc_self hs
        rw [norm_neg]
        calc ‖Γ (γ s) (v s) (v s)‖ ≤ G * ‖v s‖ * ‖v s‖ := hquad s hsI
          _ ≤ G * B * B := by gcongr <;> exact hvelτ s hsI
          _ = G * B ^ 2 := by ring)
    intro t ht
    simpa using h t ht
  -- (iii) position
  have hpos := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => γ t - t • v 0)
    (a := 0) (b := τ) (f' := fun s => v s - v 0) (C := G * B ^ 2 * τ)
    (fun s hs => by
      have h1 := (hγ s hs).fun_sub ((hasDerivAt_id s).smul_const (v 0)).hasDerivWithinAt
      simpa using h1)
    (fun s hs => (hdrift s (Ico_subset_Icc_self hs)).trans
      (mul_le_mul_of_nonneg_left hs.2.le (by positivity)))
    τ ⟨hτ, le_rfl⟩
  simp only [zero_smul, sub_zero] at hpos
  calc ‖γ τ - γ 0 - τ • v 0‖ = ‖γ τ - τ • v 0 - γ 0‖ := by congr 1; abel
    _ ≤ G * B ^ 2 * τ * τ := hpos
    _ = G * B ^ 2 * τ ^ 2 := by ring

/-- **Orbits stay close to their initial points for a common short time.** -/
theorem exists_time_dist_le_of_tendstoUniformlyOn {P : Type*} [MetricSpace P] {B : Set P}
    (hB : IsCompact B) {T : ℝ} (hT : 0 < T) {Φ : ℕ → P × ℝ → P} {ΦInf : P × ℝ → P}
    (hcont : ContinuousOn ΦInf (B ×ˢ Icc (-T) T)) (h0 : ∀ q ∈ B, ΦInf (q, 0) = q)
    (hconv : TendstoUniformlyOn Φ ΦInf atTop (B ×ˢ Icc (-T) T)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧ (∀ q ∈ B, ∀ s ∈ Icc (-τ) τ, dist (ΦInf (q, s)) q < δ) ∧
      ∀ᶠ i in atTop, ∀ q ∈ B, ∀ s ∈ Icc (-τ) τ, dist (Φ i (q, s)) q < δ := by
  have hK : IsCompact (B ×ˢ Icc (-T) T) := hB.prod isCompact_Icc
  obtain ⟨η, hη, hηU⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hcont) (δ / 2) (by positivity)
  set τ : ℝ := min T (η / 2) with hτ_def
  have hτ : 0 < τ := lt_min hT (by positivity)
  have hτT : τ ≤ T := min_le_left _ _
  have hτη : τ < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmem : ∀ q ∈ B, ∀ s ∈ Icc (-τ) τ, (q, s) ∈ B ×ˢ Icc (-T) T :=
    fun q hq s hs => ⟨hq, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
  have hInf : ∀ q ∈ B, ∀ s ∈ Icc (-τ) τ, dist (ΦInf (q, s)) q < δ / 2 := by
    intro q hq s hs
    have hd : dist (q, s) (q, (0 : ℝ)) < η := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
      exact lt_of_le_of_lt (max_le hτ.le (abs_le.mpr ⟨hs.1, hs.2⟩)) hτη
    have h := hηU _ (hmem q hq s hs) _ (hmem q hq 0 ⟨by linarith, hτ.le⟩) hd
    rwa [h0 q hq] at h
  refine ⟨τ, hτ, hτT, fun q hq s hs => (hInf q hq s hs).trans (by linarith), ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (δ / 2) (by positivity)] with i hi q hq s hs
  calc dist (Φ i (q, s)) q ≤ dist (Φ i (q, s)) (ΦInf (q, s)) + dist (ΦInf (q, s)) q :=
        dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := by
        refine add_lt_add ?_ (hInf q hq s hs)
        rw [dist_comm]
        exact hi _ (hmem q hq s hs)
    _ = δ := by ring

/-- **Fixed-time slices of `C¹`-convergent flows**, post-composed with a continuous linear map. -/
theorem mapCPConvergenceOn_one_comp_time {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {B : Set P} {T τ : ℝ} (hτ : τ ∈ Icc (-T) T)
    {Φ : ℕ → P × ℝ → P} {ΦInf : P × ℝ → P}
    (hconv : MapCPConvergenceOn (B ×ˢ Icc (-T) T) 1 Φ ΦInf)
    (hΦ : ∀ᶠ i in atTop, ∀ p ∈ B, DifferentiableAt ℝ (Φ i) (p, τ))
    (hΦInf : ∀ p ∈ B, DifferentiableAt ℝ ΦInf (p, τ)) (L : P →L[ℝ] F) :
    MapCPConvergenceOn B 1 (fun i p => L (Φ i (p, τ))) (fun p => L (ΦInf (p, τ))) := by
  have hι : ∀ p : P, HasFDerivAt (fun p : P => (p, τ)) (ContinuousLinearMap.inl ℝ P ℝ) p :=
    fun p => hasFDerivAt_prodMk_left p τ
  have hdiff : ∀ {Ψ : P × ℝ → P} {p : P}, DifferentiableAt ℝ Ψ (p, τ) →
      HasFDerivAt (fun p => L (Ψ (p, τ))) (L.comp ((fderiv ℝ Ψ (p, τ)).comp
        (ContinuousLinearMap.inl ℝ P ℝ))) p := fun {_} {p} hΨ =>
    L.hasFDerivAt.comp p (hΨ.hasFDerivAt.comp p (hι p))
  intro ε hε
  set c : ℝ := ε / (‖L‖ + 1) with hc_def
  obtain ⟨k0, hk0⟩ := hconv c (by positivity)
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp hΦ
  refine ⟨max k0 k1, fun k hk r hr p hp => ?_⟩
  have hk0' : k0 ≤ k := le_of_max_le_left hk
  have hk1' := hk1 k (le_of_max_le_right hk)
  have hpm : (p, τ) ∈ B ×ˢ Icc (-T) T := ⟨hp, hτ⟩
  have hLc : ‖L‖ * c ≤ ε := by
    rw [hc_def, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg L]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with rfl | rfl
  · have h := hk0 k hk0' 0 (Nat.zero_le 1) _ hpm
    rw [mapDerivNorm, norm_iteratedFDeriv_zero] at h ⊢
    rw [← map_sub]
    exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans hLc)
  · have h := hk0 k hk0' 1 le_rfl _ hpm
    rw [mapDerivNorm_one_eq (hk1' p hp) (hΦInf p hp)] at h
    rw [mapDerivNorm_one_eq (hdiff (hk1' p hp)).differentiableAt
      (hdiff (hΦInf p hp)).differentiableAt, (hdiff (hk1' p hp)).fderiv,
      (hdiff (hΦInf p hp)).fderiv, ← ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.sub_comp]
    calc ‖L.comp ((fderiv ℝ (Φ k) (p, τ) - fderiv ℝ ΦInf (p, τ)).comp
          (ContinuousLinearMap.inl ℝ P ℝ))‖
        ≤ ‖L‖ * (‖fderiv ℝ (Φ k) (p, τ) - fderiv ℝ ΦInf (p, τ)‖ *
          ‖ContinuousLinearMap.inl ℝ P ℝ‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖L‖ * (c * 1) := by
          gcongr
          exact ContinuousLinearMap.norm_inl_le_one ℝ P ℝ
      _ ≤ ε := by rw [mul_one]; exact hLc

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
