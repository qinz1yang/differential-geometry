import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import DifferentialGeometry.Analysis.Integration.Lp.ProductL2
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakFTC

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ν : Measure E} [IsLocallyFiniteMeasure ν] {Ω : Set E}

private theorem lp_eq_zero_of_integral_test_eq_zero
    (hΩ : IsOpen Ω) (w : Lp ℝ 2 (ν.restrict Ω))
    (h : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → ∫ x in Ω, w x * ψ x ∂ν = 0) : w = 0 := by
  apply Lp.ext
  have hw : LocallyIntegrableOn (fun x => w x) Ω ν :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp w).locallyIntegrable (by norm_num))
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw (by
    intro ψ hψ hψc hψs
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hψs hmem)), zero_smul])]
    simpa only [smul_eq_mul, mul_comm] using h ψ hψ hψc hψs)
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem hΩ.measurableSet, Lp.coeFn_zero ℝ 2 (ν.restrict Ω)] with x hx hxΩ hx0
  rw [hx0]
  exact hx hxΩ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem tsupport_tensor_mul_subset {η : ℝ → ℝ} {ψ : E → ℝ} :
    tsupport (fun p : ℝ × E => η p.1 * ψ p.2) ⊆ tsupport η ×ˢ tsupport ψ := by
  apply closure_minimal
  · intro p hp
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
    exact ⟨subset_tsupport η hp.1, subset_tsupport ψ hp.2⟩
  · exact (isClosed_tsupport η).prod (isClosed_tsupport ψ)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem hasCompactSupport_tensor_mul {η : ℝ → ℝ} {ψ : E → ℝ}
    (hη : HasCompactSupport η) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : ℝ × E => η p.1 * ψ p.2) :=
  (hη.isCompact.prod hψ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    tsupport_tensor_mul_subset

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem fderiv_tensor_mul_time {η : ℝ → ℝ} {ψ : E → ℝ}
    (hη : Differentiable ℝ η) (hψ : Differentiable ℝ ψ) (p : ℝ × E) :
    fderiv ℝ (fun p : ℝ × E => η p.1 * ψ p.2) p (1, 0) =
      deriv η p.1 * ψ p.2 := by
  have hηp : DifferentiableAt ℝ (fun p : ℝ × E => η p.1) p := hη.differentiableAt.comp p differentiableAt_fst
  have hψp : DifferentiableAt ℝ (fun p : ℝ × E => ψ p.2) p := hψ.differentiableAt.comp p differentiableAt_snd
  rw [fderiv_fun_mul hηp hψp]
  change η p.1 * (fderiv ℝ (ψ ∘ Prod.snd) p) (1, 0) +
    ψ p.2 * (fderiv ℝ (η ∘ Prod.fst) p) (1, 0) = _
  rw [fderiv_comp p hψ.differentiableAt differentiableAt_snd,
    fderiv_comp p hη.differentiableAt differentiableAt_fst]
  rw [fderiv_snd, fderiv_fst]
  change η p.1 * fderiv ℝ ψ p.2 0 + ψ p.2 * fderiv ℝ η p.1 1 = _
  simp only [map_zero, mul_zero, zero_add]
  rw [fderiv_apply_one_eq_deriv]
  exact mul_comm _ _


variable {a b : ℝ}

private theorem weak_deriv_of_spacetime_test_identity
    (hΩ : IsOpen Ω)
    (P : Lp (Lp ℝ 2 (ν.restrict Ω)) 2 (volume.restrict (Icc a b)))
    (R : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (ν.restrict Ω)))
    (hweak : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω)) =
      -(∫ p, R p * φ p ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω))) :
    let Q := (Lp.uncurry (μ := volume.restrict (Icc a b)) (ν := ν.restrict Ω)
      (E := ℝ) ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.adjoint R
    ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b →
      ∫ t in Ioo a b, deriv η t • P t = -∫ t in Ioo a b, η t • Q t := by
  intro Q η hη hηc hηs
  let μ := volume.restrict (Icc a b)
  have hηmem : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
  have hdηmem : MemLp (deriv η) 2 μ :=
    (hη.continuous_deriv (by norm_cast)).memLp_of_hasCompactSupport hηc.deriv
  have hPint : Integrable (fun t => deriv η t • P t) μ :=
    (Lp.memLp P).smul (r := 1) hdηmem |>.integrable (by norm_num)
  have hQint : Integrable (fun t => η t • Q t) μ :=
    (Lp.memLp Q).smul (r := 1) hηmem |>.integrable (by norm_num)
  have hspace : (∫ t, deriv η t • P t ∂μ) + (∫ t, η t • Q t ∂μ) = 0 := by
    apply lp_eq_zero_of_integral_test_eq_zero hΩ
    intro ψ hψ hψc hψs
    have hψmem : MemLp ψ 2 (ν.restrict Ω) :=
      hψ.continuous.memLp_of_hasCompactSupport hψc
    let Ψ := hψmem.toLp ψ
    have htensor := hweak (fun p => η p.1 * ψ p.2)
      ((hη.comp contDiff_fst).mul (hψ.comp contDiff_snd))
      (hasCompactSupport_tensor_mul hηc hψc)
      (tsupport_tensor_mul_subset.trans (Set.prod_mono hηs hψs))
    have hproduct (F : Lp ℝ 2 (μ.prod (ν.restrict Ω)))
        (ζ : ℝ → ℝ) (hζ : MemLp ζ 2 μ) :
        (∫ p, (hζ.toLp ζ) p.1 * inner ℝ (F p) (Ψ p.2) ∂μ.prod (ν.restrict Ω)) =
          ∫ p, F p * ζ p.1 * ψ p.2 ∂μ.prod (ν.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν.restrict Ω)).ae (MemLp.coeFn_toLp hζ),
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν.restrict Ω)).ae (MemLp.coeFn_toLp hψmem)] with p hp₁ hp₂
      simp only [hp₁, Ψ, hp₂, RCLike.inner_apply, conj_trivial]
      ring
    have hleft := Lp.integral_inner_eq_integral_uncurry_mul P (hdηmem.toLp (deriv η)) Ψ
    have hright := Lp.integral_inner_uncurryAdjoint_eq_integral_mul R (hηmem.toLp η) Ψ
    rw [hproduct _ _ hdηmem] at hleft
    rw [hproduct _ _ hηmem] at hright
    have hleft' : (∫ t, deriv η t * inner ℝ (P t) Ψ ∂μ) =
        ∫ p, (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) p *
          deriv η p.1 * ψ p.2 ∂μ.prod (ν.restrict Ω) := by
      rw [← hleft]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hdηmem] with t ht
      rw [ht]
    have hright' : (∫ t, η t * inner ℝ (Q t) Ψ ∂μ) =
        ∫ p, R p * η p.1 * ψ p.2 ∂μ.prod (ν.restrict Ω) := by
      rw [← hright]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hηmem] with t ht
      rw [ht]
    have hinner : inner ℝ Ψ ((∫ t, deriv η t • P t ∂μ) +
        (∫ t, η t • Q t ∂μ)) = 0 := by
      rw [inner_add_right, ← integral_inner hPint, ← integral_inner hQint]
      simp_rw [inner_smul_right, ← real_inner_comm Ψ]
      rw [hleft', hright']
      have heq : (∫ p, (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) p *
          deriv η p.1 * ψ p.2 ∂μ.prod (ν.restrict Ω)) =
          -(∫ p, R p * η p.1 * ψ p.2 ∂μ.prod (ν.restrict Ω)) := by
        simpa only [fderiv_tensor_mul_time (hη.differentiable (by norm_cast))
          (hψ.differentiable (by norm_cast)), mul_assoc] using htensor
      rw [heq, neg_add_cancel]
    rw [L2.inner_def] at hinner
    rw [← hinner]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hψmem] with x hx
    simp only [Ψ, hx, RCLike.inner_apply, conj_trivial]
  have hset (f : ℝ → Lp ℝ 2 (ν.restrict Ω)) :
      (∫ t in Ioo a b, f t) = ∫ t, f t ∂μ :=
    setIntegral_congr_set Ioo_ae_eq_Icc
  rw [hset, hset]
  exact eq_neg_of_add_eq_zero_left hspace

theorem exists_timeH1_of_spacetime_weak_deriv_on
    (hab : a < b) (hΩ : IsOpen Ω)
    (P : Lp (Lp ℝ 2 (ν.restrict Ω)) 2 (volume.restrict (Icc a b)))
    (R : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (ν.restrict Ω)))
    (hweak : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω)) =
      -(∫ p, R p * φ p ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω))) :
    let Q := (Lp.uncurry (μ := volume.restrict (Icc a b)) (ν := ν.restrict Ω)
      (E := ℝ) ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.adjoint R
    ∃ w : timeH1 (Lp ℝ 2 (ν.restrict Ω)) (b - a),
      (fun t => P (a + t)) =ᵐ[timeMeasure (b - a)] w.toFun ∧
      w.deriv =ᵐ[timeMeasure (b - a)] fun t => Q (a + t) := by
  intro Q
  exact exists_timeH1_of_weak_deriv_on hab (Lp.memLp P) (Lp.memLp Q)
    (weak_deriv_of_spacetime_test_identity hΩ P R hweak)

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
