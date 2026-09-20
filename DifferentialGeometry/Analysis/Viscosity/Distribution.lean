import DifferentialGeometry.Analysis.Convex.Distribution
import DifferentialGeometry.Analysis.Viscosity.Differentiability
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts
import DifferentialGeometry.Analysis.Integration.Integral.CompactSupport
import DifferentialGeometry.Analysis.Integration.Lp.Lipschitz

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Viscosity

theorem distribution_le_of_upper_tests_of_locallyLipschitzOn_fderiv
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    [Fintype ι] [Fintype κ] {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u Ω) (hdu : LocallyLipschitzOn Ω (fderiv ℝ u))
    {a : ι → E → ℝ} {b : κ → E → ℝ} {c r : E → ℝ}
    (ha : ∀ i, ContDiffOn ℝ 2 (a i) Ω) (hb : ∀ j, ContDiffOn ℝ 1 (b j) Ω)
    (hc : LocallyIntegrableOn c Ω μ) (hr : LocallyIntegrableOn r Ω μ) (v w : ι → E) (z : κ → E)
    (hsub : ∀ x ∈ Ω, ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => u y - ψ y) x →
      -(∑ i, a i x * fderiv ℝ (fderiv ℝ ψ) x (v i) (w i)) +
        (∑ j, b j x * fderiv ℝ ψ x (z j)) + c x * u x ≤ r x)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) :
    -(∑ i, ∫ x in Ω, u x * fderiv ℝ (fderiv ℝ (fun y => a i y * φ y)) x (w i) (v i) ∂μ) -
      (∑ j, ∫ x in Ω, u x * fderiv ℝ (fun y => b j y * φ y) x (z j) ∂μ) +
      (∫ x in Ω, (c x * u x - r x) * φ x ∂μ) ≤ 0 := by
  have hu1 : ContDiffOn ℝ 1 u Ω := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).mpr
    exact ⟨hu, by norm_num, contDiffOn_zero.mpr hdu.continuousOn⟩
  have htesta (i : ι) : ContDiff ℝ 2 (fun x => a i x * φ x) :=
    ((ha i).mul hφ.contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  have htestb (j : κ) : ContDiff ℝ 1 (fun x => b j x * φ x) :=
    ((hb j).mul (hφ.of_le (by norm_num)).contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  have hAe : ∀ᵐ x ∂μ.restrict Ω,
      -(∑ i, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i)) +
        (∑ j, b j x * fderiv ℝ u x (z j)) + c x * u x - r x ≤ 0 := by
    apply ae_second_order_le_zero_of_upper_tests_of_locallyLipschitzOn_fderiv hΩ hu hdu
      (H := fun x p B => -(∑ i, a i x * B (v i) (w i)) + (∑ j, b j x * p (z j)) +
        c x * u x - r x)
    · intro x hx ψ hψ hm
      exact sub_nonpos.mpr (hsub x hx ψ hψ hm)
    · intro x hx
      exact (by fun_prop : Continuous (fun pair : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) =>
        -(∑ i, a i x * pair.2 (v i) (w i)) + (∑ j, b j x * pair.1 (z j)) +
          c x * u x - r x)).lowerSemicontinuous
  have hintA (i : ι) : IntegrableOn
      (fun x => a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x) Ω μ := by
    have h := (hdu.integrable_fderiv_fderiv_mul_of_hasCompactSupport (μ := μ) hΩ
      (htesta i).continuous hφc.mul_left (tsupport_mul_subset_right.trans hφs) (v i) (w i)).integrableOn (s := Ω)
    convert h using 1
    ext x
    ring
  have hintB (j : κ) : IntegrableOn (fun x => b j x * fderiv ℝ u x (z j) * φ x) Ω μ := by
    have hcont : ContinuousOn (fun x => b j x * fderiv ℝ u x (z j)) Ω :=
      (hb j).continuousOn.mul (hdu.continuousOn.clm_apply continuousOn_const)
    exact ((hcont.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport
        hφc.mul_left |>.integrableOn
  have hintC : IntegrableOn (fun x => (c x * u x - r x) * φ x) Ω μ := by
    have hup : Continuous (fun x => u x * φ x) :=
      (hu.continuousOn.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans hφs)
    have h₁ := hc.integrable_smul_right_of_hasCompactSupport hup hφc.mul_left
      (tsupport_mul_subset_right.trans hφs)
    have h₂ := hr.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc hφs
    convert (h₁.sub h₂).integrableOn using 1
    ext x
    simp only [Pi.sub_apply, smul_eq_mul]
    ring
  have hineq : -(∑ i, ∫ x in Ω, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x ∂μ) +
      (∑ j, ∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ) +
      (∫ x in Ω, (c x * u x - r x) * φ x ∂μ) ≤ 0 := by
    have hsA := integrable_finsetSum Finset.univ (fun i _ => hintA i)
    have hsB := integrable_finsetSum Finset.univ (fun j _ => hintB j)
    have heq : (∫ x in Ω,
        (-(∑ i, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x) +
          (∑ j, b j x * fderiv ℝ u x (z j) * φ x)) + (c x * u x - r x) * φ x ∂μ) =
        -(∑ i, ∫ x in Ω, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x ∂μ) +
          (∑ j, ∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ) +
          (∫ x in Ω, (c x * u x - r x) * φ x ∂μ) := by
      have h₁ := integral_add (hsA.neg.add hsB) hintC
      have h₂ := integral_add hsA.neg hsB
      simp only [Pi.add_apply, Pi.neg_apply] at h₁ h₂
      rw [h₁, h₂, integral_neg, integral_finsetSum Finset.univ (fun i _ => hintA i),
        integral_finsetSum Finset.univ (fun j _ => hintB j)]
    rw [← heq]
    apply integral_nonpos_of_ae
    filter_upwards [hAe] with x hx
    have h := mul_nonpos_of_nonpos_of_nonneg hx (hφ0 x)
    simp only [Pi.zero_apply, sub_mul]
    simp only [add_mul, sub_mul, neg_mul, Finset.sum_mul] at h
    linarith
  have hA (i : ι) : (∫ x in Ω, a i x * fderiv ℝ (fderiv ℝ u) x (v i) (w i) * φ x ∂μ) =
      ∫ x in Ω, u x * fderiv ℝ (fderiv ℝ (fun y => a i y * φ y)) x (w i) (v i) ∂μ := by
    convert integral_fderiv_fderiv_mul_eq_of_locallyLipschitzOn_fderiv (μ := μ) hΩ hu hdu
      (htesta i) hφc.mul_left (tsupport_mul_subset_right.trans hφs) (v i) (w i) using 1
    congr 1
    ext x
    ring
  have hB (j : κ) : (∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ) =
      -∫ x in Ω, u x * fderiv ℝ (fun y => b j y * φ y) x (z j) ∂μ := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn (μ := μ) hΩ hu1
      (htestb j) hφc.mul_left (tsupport_mul_subset_right.trans hφs) (z j)
    have heq : (∫ x in Ω, fderiv ℝ u x (z j) * (b j x * φ x) ∂μ) =
        ∫ x in Ω, b j x * fderiv ℝ u x (z j) * φ x ∂μ := by
      congr 1
      ext x
      ring
    rw [heq] at h
    linarith
  simp_rw [hA, hB, Finset.sum_neg_distrib] at hineq
  simpa only [sub_eq_add_neg] using hineq

theorem distribution_le_of_upper_tests_of_convexOn_add_quadratic
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype κ]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    (e : Module.Basis ι ℝ E) {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {Ω : Set E} (hΩ : IsOpen Ω) {V : κ → E → E} {W : E → E} {c r : E → ℝ}
    (hV : ∀ k, ContDiffOn ℝ 2 (V k) Ω) (hW : ContDiffOn ℝ 1 W Ω)
    (hc : LocallyIntegrableOn c Ω μ) (hr : LocallyIntegrableOn r Ω μ)
    (hsub : ∀ x ∈ Ω, ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => u y - ψ y) x →
      -(∑ k, fderiv ℝ (fderiv ℝ ψ) x (V k x) (V k x)) +
        fderiv ℝ ψ x (W x) + c x * u x ≤ r x)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) :
    -(∑ k, ∑ i, ∑ j, ∫ x, u x * fderiv ℝ
        (fderiv ℝ (fun y => e.repr (V k y) i * e.repr (V k y) j * φ y)) x (e j) (e i) ∂μ) -
      (∑ i, ∫ x, u x * fderiv ℝ (fun y => e.repr (W y) i * φ y) x (e i) ∂μ) +
      (∫ x, (c x * u x - r x) * φ x ∂μ) ≤ 0 := by
  classical
  let : FiniteDimensional ℝ E := e.finiteDimensional_of_finite
  have hQ : ContDiff ℝ 2 (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
  have hlip : LocallyLipschitzOn univ u := by
    have h := (hu.locallyLipschitzOn isOpen_univ).sub
      (hQ.of_le (by norm_num)).locallyLipschitz.locallyLipschitzOn
    simpa only [add_sub_cancel_right] using h
  have huc : Continuous u := continuousOn_univ.mp hlip.continuousOn
  have hj : ∀ᵐ x ∂μ, DifferentiableAt ℝ u x ∧ ∃ B : E →L[ℝ] E →L[ℝ] ℝ,
      B.flip = B ∧ (fun y => u y - u x - fderiv ℝ u x (y - x) -
        (1 / 2 : ℝ) * B (y - x) (y - x)) =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    have heq : (fun x => u x + (1 / 2 : ℝ) * A x x) -
        (fun x => (1 / 2 : ℝ) * A x x) = u := by funext x; simp
    simpa only [interior_univ, Measure.restrict_univ, heq] using
      hu.alexandrov_sub_contDiffOn (μ := μ) hQ.contDiffOn
  let B (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
    if h : ∃ B : E →L[ℝ] E →L[ℝ] ℝ, B.flip = B ∧
        (fun y => u y - u x - fderiv ℝ u x (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
          =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) then h.choose else 0
  have hjet : ∀ᵐ x ∂μ, DifferentiableAt ℝ u x ∧ (B x).flip = B x ∧
      (fun y => u y - u x - fderiv ℝ u x (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    filter_upwards [hj] with x hx
    refine ⟨hx.1, ?_⟩
    dsimp only [B]
    rw [dif_pos hx.2]
    exact hx.2.choose_spec
  have hBAE : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    filter_upwards [hjet] with x hx
    exact ⟨hx.2.1, fderiv ℝ u x, hx.2.2⟩
  have hprincipal (k : κ) := hu.integral_hessian_vector_field_le (μ := μ)
    e A hA hBAE hΩ hφ hφc hφs hφ0 (hV k)
  let ψ (i : ι) : E → ℝ := fun x => e.repr (W x) i * φ x
  have hψ (i : ι) : ContDiff ℝ 1 (ψ i) :=
    (((e.coord i).toContinuousLinearMap.contDiff.comp_contDiffOn hW).mul
      (hφ.of_le (by norm_num)).contDiffOn).contDiff_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans hφs)
  have hψc (i : ι) : HasCompactSupport (ψ i) := hφc.mul_left
  have hψs (i : ι) : tsupport (ψ i) ⊆ Ω := tsupport_mul_subset_right.trans hφs
  have hiB (i : ι) : Integrable (fun x => fderiv ℝ u x (e i) * ψ i x) μ := by
    apply (hlip.integrable_lineDeriv_mul_of_hasCompactSupport
      (hψ i).continuous (hψc i) (subset_univ _) (e i)).congr
    filter_upwards [hjet] with x hx
    rw [hx.1.lineDeriv_eq_fderiv]
  have hIBP (i : ι) : (∫ x, fderiv ℝ u x (e i) * ψ i x ∂μ) =
      -∫ x, u x * fderiv ℝ (ψ i) x (e i) ∂μ := by
    have h := integral_mul_fderiv_eq_neg_lineDeriv_mul_of_locallyLipschitzOn
      (μ := μ) (hlip.mono (subset_univ Ω)) (hψ i) (hψc i) (hψs i) (e i)
    have hz₁ (x : E) (hx : x ∉ Ω) : u x * fderiv ℝ (ψ i) x (e i) = 0 := by
      rw [image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ (ψ i) x (e i))
        (fun h => hx (((tsupport_fderiv_apply_subset ℝ (e i)).trans (hψs i)) h)), mul_zero]
    have hz₂ (x : E) (hx : x ∉ Ω) : lineDeriv ℝ u x (e i) * ψ i x = 0 := by
      rw [image_eq_zero_of_notMem_tsupport (f := ψ i) (fun h => hx (hψs i h)), mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz₁,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz₂] at h
    have heq : (∫ x, lineDeriv ℝ u x (e i) * ψ i x ∂μ) =
        ∫ x, fderiv ℝ u x (e i) * ψ i x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hjet] with x hx
      rw [hx.1.lineDeriv_eq_fderiv]
    rw [heq] at h
    linarith
  have hiC : Integrable (fun x => (c x * u x - r x) * φ x) μ := by
    have h₁ := hc.integrable_smul_right_of_hasCompactSupport (huc.mul hφ.continuous)
      hφc.mul_left (tsupport_mul_subset_right.trans hφs)
    have h₂ := hr.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc hφs
    convert h₁.sub h₂ using 1
    ext x
    simp only [Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hexp (x : E) : fderiv ℝ u x (W x) * φ x =
      ∑ i, fderiv ℝ u x (e i) * ψ i x := by
    conv_lhs => rw [← e.sum_repr (W x)]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [ψ]
    ring
  have hpoint : ∀ᵐ x ∂μ, (-(∑ k, B x (V k x) (V k x)) +
      fderiv ℝ u x (W x) + c x * u x - r x) * φ x ≤ 0 := by
    filter_upwards [hjet] with x hx
    by_cases hxs : x ∈ Ω
    · have h := second_order_le_zero_of_upper_tests_of_isLittleO hx.2.1 hx.2.2
        (H := fun p C => -(∑ k, C (V k x) (V k x)) + p (W x) + c x * u x - r x)
        (fun f hf hm => sub_nonpos.mpr (hsub x hxs f hf hm))
        (by exact (by fun_prop : Continuous
          (fun z : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) =>
            -(∑ k, z.2 (V k x) (V k x)) + z.1 (W x) + c x * u x - r x)).lowerSemicontinuous.lowerSemicontinuousAt _)
      exact mul_nonpos_of_nonpos_of_nonneg h (hφ0 x)
    · rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hxs (hφs h)), mul_zero]
  have hineq : -(∑ k, ∫ x, B x (V k x) (V k x) * φ x ∂μ) +
      (∑ i, ∫ x, fderiv ℝ u x (e i) * ψ i x ∂μ) +
      (∫ x, (c x * u x - r x) * φ x ∂μ) ≤ 0 := by
    have hsA := integrable_finsetSum Finset.univ (fun k _ => (hprincipal k).1)
    have hsB := integrable_finsetSum Finset.univ (fun i _ => hiB i)
    have heq : (∫ x, (-(∑ k, B x (V k x) (V k x) * φ x) +
        (∑ i, fderiv ℝ u x (e i) * ψ i x)) + (c x * u x - r x) * φ x ∂μ) =
        -(∑ k, ∫ x, B x (V k x) (V k x) * φ x ∂μ) +
        (∑ i, ∫ x, fderiv ℝ u x (e i) * ψ i x ∂μ) +
        (∫ x, (c x * u x - r x) * φ x ∂μ) := by
      have h₁ := integral_add (hsA.neg.add hsB) hiC
      have h₂ := integral_add hsA.neg hsB
      simp only [Pi.add_apply, Pi.neg_apply] at h₁ h₂
      rw [h₁, h₂, integral_neg, integral_finsetSum Finset.univ (fun k _ => (hprincipal k).1),
        integral_finsetSum Finset.univ (fun i _ => hiB i)]
    rw [← heq]
    apply integral_nonpos_of_ae
    filter_upwards [hpoint] with x hx
    rw [sub_mul, add_mul, add_mul, neg_mul, Finset.sum_mul, hexp] at hx
    simp only [Pi.zero_apply, sub_mul]
    linarith
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun k _ => (hprincipal k).2)
  simp_rw [hIBP, Finset.sum_neg_distrib] at hineq
  change -(∑ k, ∑ i, ∑ j, ∫ x, u x * fderiv ℝ
      (fderiv ℝ (fun y => e.repr (V k y) i * e.repr (V k y) j * φ y)) x (e j) (e i) ∂μ) -
    (∑ i, ∫ x, u x * fderiv ℝ (ψ i) x (e i) ∂μ) +
    (∫ x, (c x * u x - r x) * φ x ∂μ) ≤ 0
  linarith

end DifferentialGeometry.Analysis.Viscosity
