import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakDerivative

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

private theorem compact_diffQuot_integral_sq_le
    {d : ℕ} {u g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u univ)
    (hucompact : HasCompactSupport u) (h : ℝ) :
    (∫ x, (diffQuot k h u x)^2) ≤ ∫ x, (g x)^2 := by
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero]
    exact integral_nonneg (fun x => sq_nonneg (g x))
  let K := cthickening |h| (tsupport u)
  have hKc : IsCompact K := hucompact.isCompact.cthickening
  have hsupport : Function.support (diffQuot k h u) ⊆ K := by
    intro x hx
    by_contra hxK
    have hx0 : u x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hxu => hxK (self_subset_cthickening (tsupport u) hxu))
    have hshift : u (x + h • EuclideanSpace.single k 1) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxu
      apply hxK
      apply closedBall_subset_cthickening hxu |h|
      rw [mem_closedBall, dist_eq_norm]
      have heq : x - (x + h • EuclideanSpace.single k 1) =
          (-h) • EuclideanSpace.single k 1 := by module
      rw [heq, norm_smul]
      simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_neg, le_refl]
    change diffQuot k h u x ≠ 0 at hx
    exact hx (by simp [diffQuot, hx0, hshift])
  have hbound := integral_sq_diffQuot_le_integral_sq_weakPartial_meas hu hg k hweak
    MeasurableSet.univ hKc.measurableSet
    (by simpa only [hKc.isClosed.closure_eq] using hKc)
    (show 0 < |h| + 1 by positivity)
    (subset_univ (cthickening (|h| + 1) (closure K))) hh
    (show |h| ≤ |h| + 1 by linarith)
  rw [Measure.restrict_univ] at hbound
  have heq : (∫ x in K, (diffQuot k h u x)^2) = ∫ x, (diffQuot k h u x)^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : diffQuot k h u x = 0 := by
      by_contra hn
      exact hx (hsupport hn)
    rw [hz, zero_pow (by norm_num)]
  rwa [heq] at hbound

private theorem integral_sq_nirenbergTestFunction_le
    {d : ℕ} {u g η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u univ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    (h : ℝ) :
    (∫ x, (nirenbergTestFunction k h η u x)^2) ≤
      2 * (∫ x, (η x * diffQuot k h g x)^2) +
        8 * N^2 * ∫ x in tsupport η, (diffQuot k h u x)^2 := by
  let F := fun x => (η x)^2 * diffQuot k h u x
  let G := fun x => (η x)^2 * diffQuot k h g x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1) * diffQuot k h u x
  have hdqu := memLp_diffQuot_two k h hu
  have hdqg := memLp_diffQuot_two k h hg
  have hηsq := hη.pow 2
  have hηsqc : HasCompactSupport (fun x => (η x)^2) :=
    hηc.comp_left (g := fun y : ℝ => y^2) (by simp)
  have hηsqLp : MemLp (fun x => (η x)^2) ∞ volume := hηsq.continuous.memLp_of_hasCompactSupport hηsqc
  have hFLp : MemLp F 2 volume := hdqu.mul' hηsqLp
  have hDη := (hη.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => EuclideanSpace.single k (1 : ℝ)))
  have hcoef : MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1)) ∞ volume :=
    ((continuous_const.mul hη.continuous).mul hDη).memLp_of_hasCompactSupport
      ((hηc.mul_left).mul_right)
  have hGLp : MemLp G 2 volume :=
    (hdqg.mul' hηsqLp).add (hdqu.mul' hcoef)
  have hFweak : DeGiorgi.HasWeakPartialDeriv k G F univ := by
    have h0 := hasWeakPartialDeriv_cutoff_sq_mul_diffQuot k k h hη
      (by simpa only [Measure.restrict_univ] using hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (by simpa only [Measure.restrict_univ] using hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hweak
    have hd (x : EuclideanSpace ℝ (Fin d)) :
        fderiv ℝ (fun z => (η z)^2) x (EuclideanSpace.single k 1) =
          2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1) := by
      rw [fderiv_fun_pow 2 (hη.differentiable (by simp) x)]
      simp only [smul_apply, smul_eq_mul]
      norm_num
    simpa only [hd] using h0
  have hbound := compact_diffQuot_integral_sq_le hFLp hGLp k hFweak
    hηsqc.mul_right (-h)
  change (∫ x, (nirenbergTestFunction k h η u x)^2) ≤ ∫ x, (G x)^2 at hbound
  have hηLp : MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hmainLp : MemLp (fun x => η x * diffQuot k h g x) 2 volume := hdqg.mul' hηLp
  have hduLp : MemLp ((tsupport η).indicator (diffQuot k h u)) 2 volume := hdqu.indicator (isClosed_tsupport η).measurableSet
  have hp (x : EuclideanSpace ℝ (Fin d)) :
      (G x)^2 ≤ 2 * (η x * diffQuot k h g x)^2 +
        8 * N^2 * ((tsupport η).indicator (diffQuot k h u) x)^2 := by
    by_cases hx : x ∈ tsupport η
    · rw [indicator_of_mem hx]
      have he : (η x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one (η x)).mpr (hηb x)
      have hd : (fderiv ℝ η x (EuclideanSpace.single k 1))^2 ≤ N^2 :=
        by nlinarith [abs_le.mp (hηd x)]
      have h1 := mul_le_mul_of_nonneg_right he (sq_nonneg (η x * diffQuot k h g x))
      have h2 := mul_le_mul_of_nonneg_right he (sq_nonneg (fderiv ℝ η x (EuclideanSpace.single k 1) * diffQuot k h u x))
      have h3 := mul_le_mul_of_nonneg_right hd (sq_nonneg (diffQuot k h u x))
      dsimp only [G]
      nlinarith [sq_nonneg ((η x)^2 * diffQuot k h g x -
        2 * η x * fderiv ℝ η x (EuclideanSpace.single k 1) * diffQuot k h u x)]
    · have he : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [G, he, hx]
  have hfinal := integral_mono_ae hGLp.integrable_sq
    ((hmainLp.integrable_sq.const_mul 2).add (hduLp.integrable_sq.const_mul (8 * N^2)))
    (Eventually.of_forall hp)
  simp only [Pi.add_apply] at hfinal
  rw [integral_add (hmainLp.integrable_sq.const_mul 2) (hduLp.integrable_sq.const_mul (8 * N^2)),
    integral_const_mul, integral_const_mul] at hfinal
  have hind : (∫ x, ((tsupport η).indicator (diffQuot k h u) x)^2) =
      ∫ x in tsupport η, (diffQuot k h u x)^2 := by
    rw [← integral_indicator (isClosed_tsupport η).measurableSet]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport η <;> simp [hx]
  rw [hind] at hfinal
  exact hbound.trans hfinal

private theorem abs_integral_mul_nirenbergTestFunction_le
    {d : ℕ} {u g η f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) (hf : MemLp f 2 volume)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u univ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) :
    |∫ x, f x * nirenbergTestFunction k h η u x| ≤
      ε * (∫ x, (η x * diffQuot k h g x)^2) +
      (2 * ε)⁻¹ * (∫ x, f x ^ 2) +
      4 * ε * N^2 * (∫ x in tsupport η, (diffQuot k h u x)^2) := by
  let v := nirenbergTestFunction k h η u
  have hηsqc : HasCompactSupport (fun x => (η x)^2) :=
    hηc.comp_left (g := fun y : ℝ => y^2) (by simp)
  have hηsqLp : MemLp (fun x => (η x)^2) ∞ volume :=
    (hη.pow 2).continuous.memLp_of_hasCompactSupport hηsqc
  have hv : MemLp v 2 volume :=
    memLp_diffQuot_two k (-h) ((memLp_diffQuot_two k h hu).mul' hηsqLp)
  have hp : Integrable (fun x => f x * v x) volume := hf.integrable_mul hv
  have hy : (∫ x, |f x * v x|) ≤
      (ε / 2) * (∫ x, (v x)^2) + (2 * ε)⁻¹ * (∫ x, (f x)^2) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hv.integrable_sq.const_mul (ε / 2))
        (hf.integrable_sq.const_mul ((2 * ε)⁻¹))]
    apply integral_mono_ae hp.abs
      ((hv.integrable_sq.const_mul (ε / 2)).add (hf.integrable_sq.const_mul ((2 * ε)⁻¹)))
    filter_upwards [] with x
    have hpoint := two_mul_le_add_mul_sq (a := |v x|) (b := |f x|) hε
    rw [sq_abs, sq_abs] at hpoint
    have heq : ε⁻¹ = 2 * (2 * ε)⁻¹ := by
      field_simp
    rw [heq] at hpoint
    rw [abs_mul]
    simp only [Pi.add_apply]
    nlinarith only [hpoint]
  have hn := integral_sq_nirenbergTestFunction_le hu hg k hweak hη hηc hηb hηd h
  have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ ε / 2 by positivity)
  have habs : |∫ x, f x * v x| ≤ ∫ x, |f x * v x| :=
    abs_integral_le_integral_abs
  change |∫ x, f x * v x| ≤ _
  have h := habs.trans hy
  dsimp only [v] at h
  nlinarith only [h, hm]

private theorem memLp_cutoff_product_local
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u χ : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω) :
    MemLp (fun x => χ x * u x) 2 volume := by
  have hm : MemLp (fun x => χ x * u x) 2 (volume.restrict Ω) :=
    hu.mul' ((hχ.memLp_of_hasCompactSupport hχc : MemLp χ ∞ volume).restrict Ω)
  have hi := (memLp_indicator_iff_restrict hΩ.measurableSet).mpr hm
  have heq : Ω.indicator (fun x => χ x * u x) = fun x => χ x * u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hs => hx (hχs hs)), zero_mul]
  rwa [heq] at hi

private theorem exists_lp_weak_partial_extension
    {d : ℕ} {Ω K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω) :
    ∃ v w : EuclideanSpace ℝ (Fin d) → ℝ, MemLp v 2 volume ∧ MemLp w 2 volume ∧
      DeGiorgi.HasWeakPartialDeriv k w v univ ∧ EqOn v u K ∧ EqOn w g K := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    Euclidean.exists_smooth_cutoff_with_neighborhood hK hΩ hKΩ
  let v := fun x => χ x * u x
  let w := fun x => χ x * g x + fderiv ℝ χ x (EuclideanSpace.single k 1) * u x
  have hv : MemLp v 2 volume := memLp_cutoff_product_local hΩ hu hχ.continuous hχc hχs
  have hDχ := (hχ.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => EuclideanSpace.single k (1 : ℝ)))
  have hw : MemLp w 2 volume :=
    (memLp_cutoff_product_local hΩ hg hχ.continuous hχc hχs).add
      (memLp_cutoff_product_local hΩ hu hDχ (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1)).trans hχs))
  refine ⟨v, w, hv, hw, hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hg k hweak hχ hχc hχs, ?_, ?_⟩
  · intro x hx
    simp only [v, hχone x (self_subset_cthickening K hx), one_mul]
  · intro x hx
    simp only [w, hχone x (self_subset_cthickening K hx), one_mul,
      Euclidean.fderiv_cutoff_apply_zero_on_cthickening hδ hχone hx k, zero_mul, add_zero]

private theorem diffQuot_eqOn_tsupport
    {d : ℕ} (k : Fin d) (h : ℝ) {η u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (heq : EqOn u v (cthickening |h| (tsupport η))) :
    EqOn (diffQuot k h u) (diffQuot k h v) (tsupport η) := by
  intro x hx
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h, Pi.zero_apply]
  have hbase := heq (self_subset_cthickening _ hx)
  have hshift : u (x + h • EuclideanSpace.single k (1 : ℝ)) =
      v (x + h • EuclideanSpace.single k (1 : ℝ)) := by
    apply heq
    apply closedBall_subset_cthickening hx |h|
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [diffQuot_apply_of_ne k hh, hbase, hshift]

theorem integral_sq_nirenbergTestFunction_le_local
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u g η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    (h : ℝ) (hroom : cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x, (nirenbergTestFunction k h η u x)^2) ≤
      2 * (∫ x, (η x * diffQuot k h g x)^2) +
        8 * N^2 * ∫ x in tsupport η, (diffQuot k h u x)^2 := by
  obtain ⟨v, w, hv, hw, hweak', heqv, heqw⟩ :=
    exists_lp_weak_partial_extension hΩ (hηc.cthickening (r := |h|)) hroom hu hg k hweak
  have htest := nirenbergTestFunction_congr_of_eqOn_cthickening k h heqv
  have hmain : (fun x => η x * diffQuot k h w x) = fun x => η x * diffQuot k h g x := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [diffQuot_eqOn_tsupport k h heqw hx]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hlower : (∫ x in tsupport η, (diffQuot k h v x)^2) =
      ∫ x in tsupport η, (diffQuot k h u x)^2 := by
    apply setIntegral_congr_fun (isClosed_tsupport η).measurableSet
    intro x hx
    exact congrArg (fun r : ℝ => r^2) (diffQuot_eqOn_tsupport k h heqv hx)
  have hb := integral_sq_nirenbergTestFunction_le hv hw k hweak' hη hηc hηb hηd h
  rw [htest, hlower] at hb
  change (∫ x, (nirenbergTestFunction k h η u x)^2) ≤
      2 * (∫ x, ((fun x => η x * diffQuot k h w x) x)^2) + _ at hb
  rw [hmain] at hb
  exact hb

theorem abs_integral_mul_nirenbergTestFunction_le_local
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {u g η f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hf : MemLp f 2 (volume.restrict Ω))
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : cthickening |h| (tsupport η) ⊆ Ω) :
    |∫ x in Ω, f x * nirenbergTestFunction k h η u x| ≤
      ε * (∫ x, (η x * diffQuot k h g x)^2) +
      (2 * ε)⁻¹ * (∫ x in Ω, f x ^ 2) +
      4 * ε * N^2 * (∫ x in tsupport η, (diffQuot k h u x)^2) := by
  obtain ⟨v, w, hv, hw, hweak', heqv, heqw⟩ :=
    exists_lp_weak_partial_extension hΩ (hηc.cthickening (r := |h|)) hroom hu hg k hweak
  have htest := nirenbergTestFunction_congr_of_eqOn_cthickening k h heqv
  have hmain : (fun x => η x * diffQuot k h w x) = fun x => η x * diffQuot k h g x := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [diffQuot_eqOn_tsupport k h heqw hx]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hlower : (∫ x in tsupport η, (diffQuot k h v x)^2) =
      ∫ x in tsupport η, (diffQuot k h u x)^2 := by
    apply setIntegral_congr_fun (isClosed_tsupport η).measurableSet
    intro x hx
    exact congrArg (fun r : ℝ => r^2) (diffQuot_eqOn_tsupport k h heqv hx)
  have hfglobal : MemLp (Ω.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet).mpr hf
  have hb := abs_integral_mul_nirenbergTestFunction_le hv hw hfglobal k hweak' hη hηc hηb hηd hε h
  rw [htest, hlower] at hb
  change |∫ x, Ω.indicator f x * nirenbergTestFunction k h η u x| ≤
    (ε * (∫ x, ((fun x => η x * diffQuot k h w x) x)^2) + _) + _ at hb
  rw [hmain] at hb
  have hforce : (∫ x, Ω.indicator f x * nirenbergTestFunction k h η u x) =
      ∫ x in Ω, f x * nirenbergTestFunction k h η u x := by
    rw [← integral_indicator hΩ.measurableSet]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hforceSq : (∫ x, (Ω.indicator f x)^2) = ∫ x in Ω, (f x)^2 := by
    rw [← integral_indicator hΩ.measurableSet]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rwa [hforce, hforceSq] at hb

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
