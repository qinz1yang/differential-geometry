import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.FrozenReplacement
import DifferentialGeometry.Analysis.Integration.Integral.MeanSquareDeviation

noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff InnerProductSpace ENNReal

namespace DifferentialGeometry.Analysis

open DeGiorgi Parabolic.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem smoothGradField_eq_gradient (v : E → ℝ) (x : E) :
    smoothGradField v x = gradient v x := by
  ext i
  change fderiv ℝ v x (EuclideanSpace.single i 1) = gradient v x i
  rw [← inner_gradient_left (f := v) (x := x), EuclideanSpace.inner_single_right]
  simp only [conj_trivial, one_mul]

private theorem smoothGradField_comp_spdSqrt
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) (v : E → ℝ) (x : E) :
    smoothGradField (v ∘ spdSqrtEquiv K hK) x =
      spdSqrtEquiv K hK (smoothGradField v (spdSqrtEquiv K hK x)) := by
  let L := spdSqrtEquiv K hK
  ext i
  change fderiv ℝ (v ∘ L) x (EuclideanSpace.single i 1) = _
  rw [L.comp_right_fderiv]
  change fderiv ℝ v (L x) (L (EuclideanSpace.single i 1)) = _
  rw [smoothGradField_eq_gradient]
  calc
    _ = inner ℝ (gradient v (L x)) (L (EuclideanSpace.single i 1)) :=
      (inner_gradient_left (f := v) (x := L x)).symm
    _ = inner ℝ (L (gradient v (L x))) (EuclideanSpace.single i 1) :=
      ((spdSqrt_selfAdj K hK).isSymmetric _ _).symm
    _ = _ := by
      change inner ℝ (L (gradient v (L x))) (EuclideanSpace.single i 1) =
        (L (gradient v (L x))) i
      rw [EuclideanSpace.inner_single_right]
      simp only [conj_trivial, one_mul]

private theorem measurePreserving_spdSqrt_of_det_one
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) (hdet : K.det = 1) :
    MeasurePreserving (spdSqrtEquiv K hK) volume volume := by
  let L := spdSqrtEquiv K hK
  have hd : LinearMap.det (L : E →ₗ[ℝ] E) = 1 := by
    simpa only [L, hdet, Real.sqrt_one] using! spdSqrt_det K hK
  change MeasurePreserving L volume volume
  refine ⟨L.continuous.measurable, ?_⟩
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure E) (show LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 by
      rw [hd]
      exact one_ne_zero)
  simpa only [hd, abs_one, inv_one, ENNReal.ofReal_one, one_smul] using! hm

private theorem transformed_gradient_sub_memLp
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) (hdet : K.det = 1)
    {c : E} {R : ℝ} {v : E → ℝ}
    (hgradLp : MemLp (smoothGradField v) 2 (volume.restrict (Metric.ball c R))) (q : E) :
    MemLp (fun y => smoothGradField (v ∘ spdSqrtEquiv K hK) y - spdSqrtEquiv K hK q) 2
      (volume.restrict (spdSqrtEquiv K hK ⁻¹' Metric.ball c R)) := by
  let L := spdSqrtEquiv K hK
  let : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hmp := (measurePreserving_spdSqrt_of_det_one K hK hdet).restrict_preimage_emb
    L.toHomeomorph.measurableEmbedding (Metric.ball c R)
  have hh := ((hgradLp.sub (memLp_const q)).comp_measurePreserving hmp).continuousLinearMap_comp
    (L : E →L[ℝ] E)
  simpa only [L, Function.comp_apply, Pi.sub_apply, smoothGradField_comp_spdSqrt, map_sub]
    using! hh

private theorem norm_smoothGradField_sub_sq (v : E → ℝ) (y q : E) :
    ‖smoothGradField v y - q‖ ^ 2 =
      ∑ j : Fin 2, (fderiv ℝ v y (EuclideanSpace.single j 1) - q j) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, smoothGradField]

private theorem norm_smoothGradField_sq (v : E → ℝ) (y : E) :
    ‖smoothGradField v y‖ ^ 2 =
      ∑ j : Fin 2, (fderiv ℝ v y (EuclideanSpace.single j 1)) ^ 2 := by
  simpa only [sub_zero, PiLp.zero_apply] using norm_smoothGradField_sub_sq v y 0

private theorem norm_sq_le_inverse_norm_sq
    (L : E ≃L[ℝ] E) {N : ℝ} (hN : 0 ≤ N)
    (hLN : ‖(L.symm : E →L[ℝ] E)‖ ≤ N) (z : E) :
    ‖z‖ ^ 2 ≤ N ^ 2 * ‖L z‖ ^ 2 := by
  have hn : ‖z‖ ≤ N * ‖L z‖ := by
    calc
      ‖z‖ = ‖L.symm (L z)‖ := by rw [L.symm_apply_apply]
      _ ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖L z‖ := (L.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right hLN (norm_nonneg _)
  simpa only [mul_pow] using! (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hN (norm_nonneg _))).2 hn

private theorem norm_sq_map_le
    (L : E ≃L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hLM : ‖(L : E →L[ℝ] E)‖ ≤ M) (z : E) :
    ‖L z‖ ^ 2 ≤ M ^ 2 * ‖z‖ ^ 2 := by
  have hn := ((L : E →L[ℝ] E).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hLM (norm_nonneg z))
  simpa only [mul_pow] using! (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).2 hn

private theorem transfer_gradient_integral_bound
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) (hdet : K.det = 1)
    {c : E} {r R M N : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hLM : ‖(spdSqrtEquiv K hK : E →L[ℝ] E)‖ ≤ M)
    (hLN : ‖((spdSqrtEquiv K hK).symm : E →L[ℝ] E)‖ ≤ N)
    (hrR : r ≤ R / (8 * M * N))
    {v : E → ℝ}
    (hgradLp : MemLp (smoothGradField v) 2 (volume.restrict (Metric.ball c R)))
    (q p : E) (D : ℝ) (n : ℕ) (hD : 0 ≤ D)
    (hdecay : ∀ {s t : ℝ}, 0 < s → 0 ≤ t → t ≤ s / 4 →
      Metric.closedBall ((spdSqrtEquiv K hK).symm c) s ⊆
        spdSqrtEquiv K hK ⁻¹' Metric.ball c R →
      (∫ y in Metric.ball ((spdSqrtEquiv K hK).symm c) t,
        ‖smoothGradField (v ∘ spdSqrtEquiv K hK) y - spdSqrtEquiv K hK q‖ ^ 2) ≤
        D * (t / s) ^ n * ∫ y in Metric.ball ((spdSqrtEquiv K hK).symm c) s,
          ‖smoothGradField (v ∘ spdSqrtEquiv K hK) y - spdSqrtEquiv K hK p‖ ^ 2) :
    (∫ x in Metric.ball c r, ‖smoothGradField v x - q‖ ^ 2) ≤
      (N ^ 2 * (D * (N * r / (R / (2 * M))) ^ n * M ^ 2)) *
        ∫ x in Metric.ball c R, ‖smoothGradField v x - p‖ ^ 2 := by
  let L := spdSqrtEquiv K hK
  let b := L.symm c
  let S := R / (2 * M)
  let g := v ∘ L
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hS : 0 < S := div_pos hR (mul_pos (by norm_num) hM0)
  have hrS : N * r ≤ S / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hM0)).2
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * M * N)).1 hrR
    nlinarith
  have hclosed : Metric.closedBall b S ⊆ L ⁻¹' Metric.ball c R := by
    intro y hy
    have hy' : ‖y - b‖ ≤ S := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    have hMS : M * S = R / 2 := by dsimp only [S]; field_simp [ne_of_gt hM0]
    have hn : ‖L (y - b)‖ ≤ M * S :=
      ((L : E →L[ℝ] E).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right hLM (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hy' hM0.le))
    change dist (L y) c < R
    rw [dist_eq_norm, ← show L (y - b) = L y - c by simp only [map_sub, b, L.apply_symm_apply]]
    rw [hMS] at hn
    linarith
  have hpre : L ⁻¹' Metric.ball c r ⊆ Metric.ball b (N * r) := by
    intro y hy
    have hy' : ‖L y - c‖ < r := by simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hy
    have hn : ‖y - b‖ ≤ N * ‖L y - c‖ := by
      calc
        ‖y - b‖ = ‖L.symm (L y - c)‖ := by simp only [map_sub, L.symm_apply_apply, b]
        _ ≤ ‖(L.symm : E →L[ℝ] E)‖ * ‖L y - c‖ := (L.symm : E →L[ℝ] E).le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_right hLN (norm_nonneg _)
    exact Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hn.trans_lt (mul_lt_mul_of_pos_left hy' hN0))
  have hsmall : Metric.ball b (N * r) ⊆ L ⁻¹' Metric.ball c R :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hclosed
  have hmp := measurePreserving_spdSqrt_of_det_one K hK hdet
  have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have hmpR := hmp.restrict_preimage_emb hemb (Metric.ball c R)
  have hmpr := hmp.restrict_preimage_emb hemb (Metric.ball c r)
  let : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpull (q : E) : MemLp (fun y => smoothGradField v (L y) - q) 2
      (volume.restrict (L ⁻¹' Metric.ball c R)) :=
    (hgradLp.sub (memLp_const q)).comp_measurePreserving hmpR
  have hgdiff (q : E) : MemLp (fun y => smoothGradField g y - L q) 2
      (volume.restrict (L ⁻¹' Metric.ball c R)) := by
    simpa only [g, L, smoothGradField_comp_spdSqrt, map_sub] using!
      (hpull q).continuousLinearMap_comp (L : E →L[ℝ] E)
  have hinner : (∫ x in Metric.ball c r, ‖smoothGradField v x - q‖ ^ 2) ≤
      N ^ 2 * ∫ y in Metric.ball b (N * r), ‖smoothGradField g y - L q‖ ^ 2 := by
    rw [← hmpr.integral_comp hemb (fun x => ‖smoothGradField v x - q‖ ^ 2)]
    have hsubset := hpre.trans hsmall
    have hleft := (hpull q).mono_measure (Measure.restrict_mono_set volume hsubset)
    have hright := (hgdiff q).mono_measure (Measure.restrict_mono_set volume hsubset)
    have hrightSmall := (hgdiff q).mono_measure (Measure.restrict_mono_set volume hsmall)
    calc
      _ ≤ N ^ 2 * ∫ y in L ⁻¹' Metric.ball c r,
          ‖smoothGradField g y - L q‖ ^ 2 := by
        rw [← integral_const_mul]
        apply integral_mono_ae hleft.norm.integrable_sq (hright.norm.integrable_sq.const_mul _)
        filter_upwards with y
        simpa only [g, L, smoothGradField_comp_spdSqrt, ← map_sub] using
          norm_sq_le_inverse_norm_sq L hN0.le hLN (smoothGradField v (L y) - q)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hrightSmall.norm.integrable_sq
          (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hpre)) (sq_nonneg N)
  have houter : (∫ y in Metric.ball b S, ‖smoothGradField g y - L p‖ ^ 2) ≤
      M ^ 2 * ∫ x in Metric.ball c R, ‖smoothGradField v x - p‖ ^ 2 := by
    have hs := Metric.ball_subset_closedBall.trans hclosed
    have hleft := (hgdiff p).mono_measure (Measure.restrict_mono_set volume hs)
    have hright := (hpull p).mono_measure (Measure.restrict_mono_set volume hs)
    rw [← hmpR.integral_comp hemb (fun x => ‖smoothGradField v x - p‖ ^ 2)]
    calc
      _ ≤ M ^ 2 * ∫ y in Metric.ball b S, ‖smoothGradField v (L y) - p‖ ^ 2 := by
        rw [← integral_const_mul]
        apply integral_mono_ae hleft.norm.integrable_sq (hright.norm.integrable_sq.const_mul _)
        filter_upwards with y
        simpa only [g, L, smoothGradField_comp_spdSqrt, ← map_sub] using
          norm_sq_map_le L hM0.le hLM (smoothGradField v (L y) - p)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set (hpull p).norm.integrable_sq
          (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hs)) (sq_nonneg M)
  have hdecayApply := hdecay hS (mul_pos hN0 hr).le hrS hclosed
  calc
    _ ≤ N ^ 2 * (D * (N * r / S) ^ n *
        ∫ y in Metric.ball b S, ‖smoothGradField g y - L p‖ ^ 2) :=
      hinner.trans (mul_le_mul_of_nonneg_left hdecayApply (sq_nonneg N))
    _ ≤ N ^ 2 * (D * (N * r / S) ^ n *
        (M ^ 2 * ∫ x in Metric.ball c R, ‖smoothGradField v x - p‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left houter (by positivity)) (sq_nonneg N)
    _ = _ := by dsimp only [S]; ring

/-- Physical-ball excess of the exact smooth representative returned by
`exists_frozen_harmonic_replacement_with_gradient_comparison`. The transformed
harmonicity premise is that producer's conclusion for the same `v`. -/
theorem frozen_harmonic_physical_gradient_excess
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) (hdet : K.det = 1)
    {c : E} {r R M N : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hLM : ‖(spdSqrtEquiv K hK : E →L[ℝ] E)‖ ≤ M)
    (hLN : ‖((spdSqrtEquiv K hK).symm : E →L[ℝ] E)‖ ≤ N)
    (hrR : r ≤ R / (8 * M * N))
    {v : E → ℝ}
    (hgradLp : MemLp (smoothGradField v) 2 (volume.restrict (Metric.ball c R)))
    (hharm : HarmonicOnNhd (v ∘ spdSqrtEquiv K hK)
      (spdSqrtEquiv K hK ⁻¹' Metric.ball c R)) (p : E) :
    (∫ x in Metric.ball c r, ‖smoothGradField v x - smoothGradField v c‖ ^ 2) ≤
      (4096 * (M * N) ^ 6) * (r / R) ^ 4 *
        ∫ x in Metric.ball c R, ‖smoothGradField v x - p‖ ^ 2 := by
  let L := spdSqrtEquiv K hK
  let g := v ∘ L
  have he := transfer_gradient_integral_bound K hK hdet hR hr hM hN hLM hLN hrR
    hgradLp (smoothGradField v c) p 256 4 (by norm_num) (by
      intro s t hs ht hts hsub
      have hi := ((transformed_gradient_sub_memLp K hK hdet hgradLp p).mono_measure
        (Measure.restrict_mono_set volume (Metric.ball_subset_closedBall.trans hsub))).norm.integrable_sq
      have hi' : IntegrableOn (fun y => ∑ j : Fin 2,
          (fderiv ℝ g y (EuclideanSpace.single j 1) - (L p) j) ^ 2)
          (Metric.ball (L.symm c) s) := by
        simpa only [g, L, norm_smoothGradField_sub_sq] using! hi
      have hh := harmonic_integral_gradient_sub_center_sq_le_radius_ratio_pow_four hs ht hts
        (hharm.mono (Metric.ball_subset_closedBall.trans hsub)) (L p) hi'
      have hcenter : smoothGradField g (L.symm c) = L (smoothGradField v c) := by
        simp only [g, L, smoothGradField_comp_spdSqrt, ContinuousLinearEquiv.apply_symm_apply]
      rw [← hcenter]
      simp only [norm_smoothGradField_sub_sq]
      simpa only [g, L, smoothGradField] using! hh)
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hscale : N ^ 2 * (256 * (N * r / (R / (2 * M))) ^ 4 * M ^ 2) =
      (4096 * (M * N) ^ 6) * (r / R) ^ 4 := by
    field_simp [ne_of_gt hR, ne_of_gt hM0]
    ring
  rwa [hscale] at he

/-- Companion physical-ball energy decay for the same frozen comparator. -/
theorem frozen_harmonic_physical_gradient_energy
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef) (hdet : K.det = 1)
    {c : E} {r R M N : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hLM : ‖(spdSqrtEquiv K hK : E →L[ℝ] E)‖ ≤ M)
    (hLN : ‖((spdSqrtEquiv K hK).symm : E →L[ℝ] E)‖ ≤ N)
    (hrR : r ≤ R / (8 * M * N))
    {v : E → ℝ}
    (hgradLp : MemLp (smoothGradField v) 2 (volume.restrict (Metric.ball c R)))
    (hharm : HarmonicOnNhd (v ∘ spdSqrtEquiv K hK)
      (spdSqrtEquiv K hK ⁻¹' Metric.ball c R)) :
    (∫ x in Metric.ball c r, ‖smoothGradField v x‖ ^ 2) ≤
      (64 * (M * N) ^ 4) * (r / R) ^ 2 *
        ∫ x in Metric.ball c R, ‖smoothGradField v x‖ ^ 2 := by
  let L := spdSqrtEquiv K hK
  let g := v ∘ L
  have he := transfer_gradient_integral_bound K hK hdet hR hr hM hN hLM hLN hrR
    hgradLp 0 0 16 2 (by norm_num) (by
      intro s t hs ht hts hsub
      have hi := ((transformed_gradient_sub_memLp K hK hdet hgradLp 0).mono_measure
        (Measure.restrict_mono_set volume (Metric.ball_subset_closedBall.trans hsub))).norm.integrable_sq
      have hi' : IntegrableOn (fun y => ∑ j : Fin 2,
          (fderiv ℝ g y (EuclideanSpace.single j 1)) ^ 2)
          (Metric.ball (L.symm c) s) := by
        simpa only [g, L, map_zero, sub_zero, norm_smoothGradField_sq] using! hi
      have hh := harmonic_integral_gradient_sq_le_radius_ratio_sq hs ht (by linarith)
        (hharm.mono (Metric.ball_subset_closedBall.trans hsub)) hi'
      simpa only [g, L, map_zero, sub_zero, norm_smoothGradField_sq] using! hh)
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hscale : N ^ 2 * (16 * (N * r / (R / (2 * M))) ^ 2 * M ^ 2) =
      (64 * (M * N) ^ 4) * (r / R) ^ 2 := by
    field_simp [ne_of_gt hR, ne_of_gt hM0]
    ring
  simpa only [hscale, sub_zero] using he

private theorem frozen_comparison_error_sq
    {Ω : Set E} (hΩ : IsOpen Ω) (A B : EllipticCoeff 2 Ω)
    {u h : E → ℝ} (hu : IsHomogeneousWeakSolution A u)
    (hh : IsHomogeneousWeakSolution B h)
    (htrace : MemW01p 2 (fun x => h x - u x) Ω)
    (wu : MemW1pWitness 2 u Ω) (wh : MemW1pWitness 2 h Ω)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (B.a x) ξ‖ ≤ ε * ‖ξ‖) :
    (∫ x in Ω, ‖wh.weakGrad x - wu.weakGrad x‖ ^ 2) ≤
      (ε / B.lam) ^ 2 * ∫ x in Ω, ‖wu.weakGrad x‖ ^ 2 := by
  have hc := weakGrad_l2_sub_le_of_coefficient_oscillation hΩ A B hu hh htrace wu wh hε hosc
  simp only [Real.rpow_ofNat, ← Real.sqrt_eq_rpow] at hc
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (div_nonneg hε B.lam_nonneg) (Real.sqrt_nonneg _))).2 hc
  have hE : 0 ≤ ∫ x in Ω, ‖wh.weakGrad x - wu.weakGrad x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hU : 0 ≤ ∫ x in Ω, ‖wu.weakGrad x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rwa [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hU] at hs

/-- Energy and mean-gradient excess decay for the same original weak solution.
The comparator's smooth gradient is identified a.e. with the supplied `wh`, and
its transformed harmonicity is the literal conclusion of `FrozenReplacement`.
The coercivity divisor remains exactly `B.lam`. No C1 representative is assumed. -/
theorem weakGrad_energy_and_excess_le_of_frozen_replacement
    {c : E} {r R M N : ℝ} (hR : 0 < R) (hr : 0 < r)
    (A B : EllipticCoeff 2 (Metric.ball c R))
    (hB : B.a = fun _ => A.a c) (hAc : (A.a c).PosDef) (hdet : (A.a c).det = 1)
    (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hLM : ‖(spdSqrtEquiv (A.a c) hAc : E →L[ℝ] E)‖ ≤ M)
    (hLN : ‖((spdSqrtEquiv (A.a c) hAc).symm : E →L[ℝ] E)‖ ≤ N)
    (hrR : r ≤ R / (8 * M * N))
    {u h v : E → ℝ} (hu : IsHomogeneousWeakSolution A u)
    (hh : IsHomogeneousWeakSolution B h)
    (htrace : MemW01p 2 (fun x => h x - u x) (Metric.ball c R))
    (wu : MemW1pWitness 2 u (Metric.ball c R))
    (wh : MemW1pWitness 2 h (Metric.ball c R))
    (hgradient : wh.weakGrad =ᵐ[volume.restrict (Metric.ball c R)] smoothGradField v)
    (hharm : HarmonicOnNhd (v ∘ spdSqrtEquiv (A.a c) hAc)
      (spdSqrtEquiv (A.a c) hAc ⁻¹' Metric.ball c R))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ᵐ x ∂volume.restrict (Metric.ball c R), ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (A.a c) ξ‖ ≤ ε * ‖ξ‖) :
    (∫ x in Metric.ball c r, ‖wu.weakGrad x‖ ^ 2) ≤
      ((256 * (M * N) ^ 4) * (r / R) ^ 2 +
        (2 + (256 * (M * N) ^ 4) * (r / R) ^ 2) * (ε / B.lam) ^ 2) *
          ∫ x in Metric.ball c R, ‖wu.weakGrad x‖ ^ 2 ∧
    (∫ x in Metric.ball c r,
      ‖wu.weakGrad x - ⨍ y in Metric.ball c r, wu.weakGrad y‖ ^ 2) ≤
      (16384 * (M * N) ^ 6) * (r / R) ^ 4 *
        (∫ x in Metric.ball c R,
          ‖wu.weakGrad x - ⨍ y in Metric.ball c R, wu.weakGrad y‖ ^ 2) +
      (2 + (16384 * (M * N) ^ 6) * (r / R) ^ 4) * (ε / B.lam) ^ 2 *
        ∫ x in Metric.ball c R, ‖wu.weakGrad x‖ ^ 2 := by
  let F := wu.weakGrad
  let G := smoothGradField v
  let E0 := ∫ x in Metric.ball c R, ‖F x‖ ^ 2
  let Err := ∫ x in Metric.ball c R, ‖F x - G x‖ ^ 2
  let p := ⨍ y in Metric.ball c R, F y
  let Ex := ∫ x in Metric.ball c R, ‖F x - p‖ ^ 2
  let CE := (64 * (M * N) ^ 4) * (r / R) ^ 2
  let CX := (4096 * (M * N) ^ 6) * (r / R) ^ 4
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hMN : 1 ≤ M * N := by
    simpa only [one_mul] using mul_le_mul hM hN zero_le_one hM0.le
  have hden : 1 ≤ 8 * M * N := by nlinarith
  have hrle : r ≤ R := by
    have hh' := (le_div_iff₀ (by positivity : 0 < 8 * M * N)).1 hrR
    have hrr := mul_le_mul_of_nonneg_left hden hr.le
    nlinarith
  have hsub : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrle
  let : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hF : MemLp F 2 (volume.restrict (Metric.ball c R)) := wu.weakGrad_memLp
  have hG : MemLp G 2 (volume.restrict (Metric.ball c R)) := wh.weakGrad_memLp.ae_eq hgradient
  have hFr := hF.mono_measure (Measure.restrict_mono_set volume hsub)
  have hGr := hG.mono_measure (Measure.restrict_mono_set volume hsub)
  have hoscB : ∀ᵐ x ∂volume.restrict (Metric.ball c R), ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (B.a x) ξ‖ ≤ ε * ‖ξ‖ := by
    simpa only [hB] using hosc
  have hErr : Err ≤ (ε / B.lam) ^ 2 * E0 := by
    have heq : Err = ∫ x in Metric.ball c R, ‖wh.weakGrad x - wu.weakGrad x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hgradient] with x hx
      dsimp only [F, G]
      rw [← hx, norm_sub_rev]
    rw [heq]
    exact frozen_comparison_error_sq Metric.isOpen_ball A B hu hh htrace wu wh hε hoscB
  have hErrr : (∫ x in Metric.ball c r, ‖F x - G x‖ ^ 2) ≤ Err :=
    setIntegral_mono_set (hF.sub hG).norm.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub)
  have hreverse (q : E) : (∫ x in Metric.ball c R, ‖G x - q‖ ^ 2) ≤
      2 * Err + 2 * ∫ x in Metric.ball c R, ‖F x - q‖ ^ 2 := by
    have hh' := integral_norm_sub_const_sq_le_two_difference_add hG hF q
    have heq : (∫ x in Metric.ball c R, ‖G x - F x‖ ^ 2) = Err := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [Err]; rw [norm_sub_rev]
    rw [heq] at hh'
    exact hh'
  have hCE : 0 ≤ CE := by positivity
  have hCX : 0 ≤ CX := by positivity
  have henergy := frozen_harmonic_physical_gradient_energy (A.a c) hAc hdet
    hR hr hM hN hLM hLN hrR hG hharm
  have hexcess := frozen_harmonic_physical_gradient_excess (A.a c) hAc hdet
    hR hr hM hN hLM hLN hrR hG hharm p
  constructor
  · have hsplit := integral_norm_sub_const_sq_le_two_difference_add hFr hGr (0 : E)
    have hrev := hreverse (0 : E)
    simp only [sub_zero] at hsplit hrev
    have hm := mul_le_mul_of_nonneg_left hrev (show 0 ≤ 2 * CE by positivity)
    have he := mul_le_mul_of_nonneg_left hErr (show 0 ≤ 2 + 4 * CE by positivity)
    change (∫ x in Metric.ball c r, ‖G x‖ ^ 2) ≤ CE * _ at henergy
    have hgoal : (∫ x in Metric.ball c r, ‖F x‖ ^ 2) ≤
        (4 * CE + (2 + 4 * CE) * (ε / B.lam) ^ 2) * E0 := by
      nlinarith
    have hcoef : 4 * CE = (256 * (M * N) ^ 4) * (r / R) ^ 2 := by
      dsimp only [CE]
      ring
    rw [hcoef] at hgoal
    exact hgoal
  · have hmin := integral_norm_sub_average_sq_le_integral_norm_sub_sq hFr (G c)
    have hsplit := integral_norm_sub_const_sq_le_two_difference_add hFr hGr (G c)
    have hrev := hreverse p
    have hm := mul_le_mul_of_nonneg_left hrev (show 0 ≤ 2 * CX by positivity)
    have he := mul_le_mul_of_nonneg_left hErr (show 0 ≤ 2 + 4 * CX by positivity)
    change (∫ x in Metric.ball c r, ‖G x - G c‖ ^ 2) ≤ CX * _ at hexcess
    have hgoal : (∫ x in Metric.ball c r, ‖F x - ⨍ y in Metric.ball c r, F y‖ ^ 2) ≤
        4 * CX * Ex + (2 + 4 * CX) * (ε / B.lam) ^ 2 * E0 := by
      nlinarith
    have hcoef : 4 * CX = (16384 * (M * N) ^ 6) * (r / R) ^ 4 := by
      dsimp only [CX]
      ring
    rw [hcoef] at hgoal
    exact hgoal

end DifferentialGeometry.Analysis
