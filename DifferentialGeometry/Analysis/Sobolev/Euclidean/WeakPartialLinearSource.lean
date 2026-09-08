import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeUniqueness

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem ae_eq_weak_partial_linear_source
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {Ω : Set E} (hΩ : IsOpen Ω)
    (hp : (1 : ℝ≥0∞) ≤ 2) (k : Fin d)
    (U : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (V : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hUweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V k (t, x)) (fun x => U (t, x)) Ω)
    (hVweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => H i (t, x)) (fun x => V i (t, x)) Ω)
    (C : Fin d → ℝ × E → ℝ) (C0 : ℝ × E → ℝ)
    (hC : ∀ i, MemLp (C i) ∞ (μ.prod (volume.restrict Ω)))
    (hDC : ∀ i, MemLp
      (fun p => fderiv ℝ (fun x => C i (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hCs : ∀ i, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => C i (t, x)) Ω)
    (hC0 : MemLp C0 ∞ (μ.prod (volume.restrict Ω)))
    (hDC0 : MemLp
      (fun p => fderiv ℝ (fun x => C0 (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hC0s : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => C0 (t, x)) Ω)
    {Flower : Lp ℝ 2 (μ.prod (volume.restrict Ω))}
    (hFlower : ∀ (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (Set.univ : Set ℝ) ×ˢ Ω →
      (∫ p, ((∑ i, C i p * V i p) + C0 p * U p) *
          fderiv ℝ φ p (0, EuclideanSpace.single k 1)
          ∂μ.prod (volume.restrict Ω)) =
        -(∫ p, Flower p * φ p ∂μ.prod (volume.restrict Ω))) :
    Flower =ᵐ[μ.prod (volume.restrict Ω)] fun p =>
      (∑ i, (C i p * H i p +
        fderiv ℝ (fun x => C i (p.1, x)) p.2 (EuclideanSpace.single k 1) * V i p)) +
      (C0 p * V k p +
      fderiv ℝ (fun x => C0 (p.1, x)) p.2 (EuclideanSpace.single k 1) * U p) := by
  classical
  let ν := μ.prod (volume.restrict Ω)
  choose Fi hFi using fun i =>
    exists_lp_product_weakPartial hp hΩ k (V i) (H i) (hC i) (hDC i) (hCs i) (hVweak i)
  obtain ⟨F0, hF0, hF0weak⟩ :=
    exists_lp_product_weakPartial hp hΩ k U (V k) hC0 hDC0 hC0s hUweak
  let Fsum : Lp ℝ 2 ν := (Finset.univ.sum Fi) + F0
  have hsum : ∀ (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (Set.univ : Set ℝ) ×ˢ Ω →
      (∫ p, ((∑ i, C i p * V i p) + C0 p * U p) *
          fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂ν) =
        -(∫ p, Fsum p * φ p ∂ν) := by
    intro φ hφ hφc hφs
    let dφ : ℝ × E → ℝ := fun p => fderiv ℝ φ p (0, EuclideanSpace.single k 1)
    have hdφ : Continuous dφ :=
      (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
    have hdφc : HasCompactSupport dφ := hφc.fderiv_apply (𝕜 := ℝ) (0, EuclideanSpace.single k 1)
    have hI (i) : Integrable (fun p => C i p * V i p * dφ p) ν :=
      ((Lp.memLp (V i)).mul (r := 2) (hC i)).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hdφ hdφc
    have hI0 : Integrable (fun p => C0 p * U p * dφ p) ν :=
      ((Lp.memLp U).mul (r := 2) hC0).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hdφ hdφc
    have hFI (i) : Integrable (fun p => Fi i p * φ p) ν :=
      (Lp.memLp (Fi i)).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    have hF0I : Integrable (fun p => F0 p * φ p) ν :=
      (Lp.memLp F0).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    have hleft :
        (∫ p, ((∑ i, C i p * V i p) + C0 p * U p) * dφ p ∂ν) =
          (∑ i, ∫ p, C i p * V i p * dφ p ∂ν) +
            ∫ p, C0 p * U p * dφ p ∂ν := by
      simp_rw [add_mul, Finset.sum_mul]
      rw [integral_add (integrable_finsetSum _ (fun i _ => hI i)) hI0,
        integral_finsetSum _ (fun i _ => hI i)]
    have hright :
        (∫ p, Fsum p * φ p ∂ν) =
          (∑ i, ∫ p, Fi i p * φ p ∂ν) + ∫ p, F0 p * φ p ∂ν := by
      calc
        _ = ∫ p, ((∑ i, Fi i p) + F0 p) * φ p ∂ν := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_add (Finset.univ.sum Fi) F0,
            Lp.coeFn_finsetSum Finset.univ Fi] with p hp hsum
          change ((Finset.univ.sum Fi + F0 : Lp ℝ 2 ν) p) * φ p = _
          rw [hp]
          change ((Finset.univ.sum Fi) p + F0 p) * φ p = _
          rw [hsum]
          simp only [Finset.sum_apply]
        _ = (∫ p, (∑ i, Fi i p) * φ p ∂ν) + ∫ p, F0 p * φ p ∂ν := by
          have hsumI : Integrable (fun p => (∑ i, Fi i p) * φ p) ν := by
            simp_rw [Finset.sum_mul]
            exact integrable_finsetSum _ (fun i _ => hFI i)
          simp only [add_mul]
          exact integral_add hsumI hF0I
        _ = _ := by
          simp_rw [Finset.sum_mul]
          rw [integral_finsetSum _ (fun i _ => hFI i)]
    rw [hleft]
    have hFi' (i) := integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (((Lp.memLp (V i)).mul (r := 2) (hC i)).locallyIntegrable (by norm_num))
      ((Lp.memLp (Fi i)).locallyIntegrable (by norm_num)) k (hFi i).2 φ hφ hφc hφs
    have hF0' := integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (((Lp.memLp U).mul (r := 2) hC0).locallyIntegrable (by norm_num))
      ((Lp.memLp F0).locallyIntegrable (by norm_num)) k hF0weak φ hφ hφc hφs
    have hFi'' (i) : (∫ p, C i p * V i p * dφ p ∂ν) =
        -∫ p, Fi i p * φ p ∂ν := by simpa [dφ] using hFi' i
    have hF0'' : (∫ p, C0 p * U p * dφ p ∂ν) =
        -∫ p, F0 p * φ p ∂ν := by simpa [dφ] using hF0'
    calc
      (∑ i, ∫ p, C i p * V i p * dφ p ∂ν) + ∫ p, C0 p * U p * dφ p ∂ν
          = (∑ i, -(∫ p, Fi i p * φ p ∂ν)) + -(∫ p, F0 p * φ p ∂ν) := by
            rw [show (∑ i, ∫ p, C i p * V i p * dφ p ∂ν) =
                ∑ i, -(∫ p, Fi i p * φ p ∂ν) by
              apply Finset.sum_congr rfl; intro i hi; exact hFi'' i,
              hF0'']
      _ = -∫ p, Fsum p * φ p ∂ν := by
        rw [hright]
        simp only [Finset.sum_neg_distrib]
        ring
  have hmem : ∀ᵐ p ∂ν, p ∈ (Set.univ : Set ℝ) ×ˢ Ω := by
    apply (Measure.ae_prod_iff_ae_ae (MeasurableSet.univ.prod hΩ.measurableSet)).mpr
    filter_upwards with t
    exact (ae_restrict_mem hΩ.measurableSet).mono fun _ hx => ⟨Set.mem_univ _, hx⟩
  have heq : Flower = Fsum := lp_eq_of_integral_contDiff_mul_eq_on
    (isOpen_univ.prod hΩ) hmem hp (fun φ hφ hφc hφs => by
      have h1 := hFlower φ hφ hφc hφs
      have h2 := hsum φ hφ hφc hφs
      exact neg_injective (h1.symm.trans h2))
  filter_upwards [show Flower =ᵐ[ν] Fsum from (Lp.ext_iff.mp heq),
    Lp.coeFn_add (Finset.univ.sum Fi) F0,
    Lp.coeFn_finsetSum Finset.univ Fi,
    ae_all_iff.mpr (fun i => (hFi i).1),
    hF0] with p hp hsumco hsumFns hFiEq hF0Eq
  change Flower p = Fsum p at hp
  change Flower p = ((Finset.univ.sum Fi + F0 : Lp ℝ 2 ν) p) at hp
  rw [hsumco] at hp
  change Flower p = (Finset.univ.sum Fi) p + F0 p at hp
  rw [hsumFns] at hp
  simp only [Finset.sum_apply] at hp
  rw [hp]
  apply congrArg₂ (fun a b => a + b) ?_ ?_
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hFiEq i]
  · rw [hF0Eq]


end DifferentialGeometry.Analysis.Sobolev.Euclidean
