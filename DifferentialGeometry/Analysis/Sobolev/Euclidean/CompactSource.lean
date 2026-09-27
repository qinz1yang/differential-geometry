import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem tsupport_tensor_mul_subset {E : Type*} [TopologicalSpace E]
    {τ : ℝ → ℝ} {ψ : E → ℝ} :
    tsupport (fun p : ℝ × E => τ p.1 * ψ p.2) ⊆ tsupport τ ×ˢ tsupport ψ := by
  apply closure_minimal
  · intro p hp
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
    exact ⟨subset_tsupport τ hp.1, subset_tsupport ψ hp.2⟩
  · exact (isClosed_tsupport τ).prod (isClosed_tsupport ψ)

private theorem hasCompactSupport_tensor_mul {E : Type*} [TopologicalSpace E]
    {τ : ℝ → ℝ} {ψ : E → ℝ}
    (hτ : HasCompactSupport τ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : ℝ × E => τ p.1 * ψ p.2) :=
  (hτ.isCompact.prod hψ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    tsupport_tensor_mul_subset

private theorem fderiv_tensor_mul_space {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : ℝ → ℝ} {ψ : E → ℝ}
    (hτ : Differentiable ℝ τ) (hψ : Differentiable ℝ ψ) (p : ℝ × E) (v : E) :
    fderiv ℝ (fun p : ℝ × E => τ p.1 * ψ p.2) p (0, v) =
      τ p.1 * fderiv ℝ ψ p.2 v := by
  have hτp : DifferentiableAt ℝ (fun p : ℝ × E => τ p.1) p :=
    hτ.differentiableAt.comp p differentiableAt_fst
  have hψp : DifferentiableAt ℝ (fun p : ℝ × E => ψ p.2) p :=
    hψ.differentiableAt.comp p differentiableAt_snd
  rw [fderiv_fun_mul hτp hψp]
  change τ p.1 * (fderiv ℝ (ψ ∘ Prod.snd) p) (0, v) +
    ψ p.2 * (fderiv ℝ (τ ∘ Prod.fst) p) (0, v) = _
  rw [fderiv_comp p hψ.differentiableAt differentiableAt_snd,
    fderiv_comp p hτ.differentiableAt differentiableAt_fst,
    fderiv_snd, fderiv_fst]
  change τ p.1 * fderiv ℝ ψ p.2 v + ψ p.2 * fderiv ℝ τ p.1 0 = _
  simp only [map_zero, mul_zero, add_zero]

theorem integral_tensor_of_compact_source_support
    {d : ℕ} {Ω K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKs : K ⊆ Ω)
    {ν : Measure (ℝ × EuclideanSpace ℝ (Fin d))}
    {S : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    {P : Fin d → ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hS : ∀ᵐ p ∂ν, p.2 ∉ K → S p = 0)
    (hP : ∀ j, ∀ᵐ p ∂ν, p.2 ∉ K → P j p = 0)
    (htest : ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
      (∫ p, S p * φ p ∂ν) =
        ∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ Ω)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hτc : HasCompactSupport τ) :
    (∫ p, τ p.1 * S p * ψ p.2 ∂ν) =
      ∑ j, ∫ p, τ p.1 * P j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hK hΩ hKs
  have hχψs : tsupport (fun x => χ x * ψ x) ⊆ Ω := tsupport_mul_subset_left.trans hχs
  have hχψ : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * ψ x) :=
    (hχ.contDiffOn.mul hψ).contDiff_of_tsupport_subset hΩ hχψs
  have hlocal {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ K) :
      (fun x => χ x * ψ x) =ᶠ[𝓝 x] ψ := by
    filter_upwards [Metric.isOpen_thickening.mem_nhds
      (Metric.self_subset_thickening hδ K hx)] with y hy
    rw [hχone y (Metric.thickening_subset_cthickening δ K hy), one_mul]
  have h := htest (fun p => τ p.1 * (χ p.2 * ψ p.2))
    ((hτ.comp contDiff_fst).mul (hχψ.comp contDiff_snd))
    (hasCompactSupport_tensor_mul hτc hχc.mul_right)
    (tsupport_tensor_mul_subset.trans (prod_mono (subset_univ _) hχψs))
  have hleft : (∫ p, S p * (τ p.1 * (χ p.2 * ψ p.2)) ∂ν) =
      ∫ p, τ p.1 * S p * ψ p.2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hS] with p hp
    by_cases hx : p.2 ∈ K
    · rw [(hlocal hx).eq_of_nhds]
      ring
    · rw [hp hx]
      ring
  have hright : (∑ j, ∫ p, P j p *
      fderiv ℝ (fun p => τ p.1 * (χ p.2 * ψ p.2)) p (0, EuclideanSpace.single j 1) ∂ν) =
      ∑ j, ∫ p, τ p.1 * P j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν := by
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hP j] with p hp
    by_cases hx : p.2 ∈ K
    · rw [fderiv_tensor_mul_space (hτ.differentiable (by simp))
        (hχψ.differentiable (by simp)), (hlocal hx).fderiv_eq]
      ring
    · rw [hp hx]
      ring
  exact hleft.symm.trans (h.trans hright)

theorem integral_source_tensor_eq_of_compact_flux_support
    {d : ℕ} {Ω K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKs : K ⊆ Ω)
    {ν : Measure (ℝ × EuclideanSpace ℝ (Fin d))}
    {f B : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    {P : Fin d → ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : LocallyIntegrable f ν) (hB : LocallyIntegrable B ν)
    (hS : ∀ᵐ p ∂ν, p.2 ∉ K → f p - B p = 0)
    (hP : ∀ j, ∀ᵐ p ∂ν, p.2 ∉ K → P j p = 0)
    (htest : ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
      (∫ p, f p * φ p ∂ν) = (∫ p, B p * φ p ∂ν) +
        ∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ Ω)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hτc : HasCompactSupport τ)
    (hft : Integrable (fun p => τ p.1 * f p * ψ p.2) ν)
    (hBt : Integrable (fun p => τ p.1 * B p * ψ p.2) ν) :
    (∫ p, τ p.1 * f p * ψ p.2 ∂ν) = (∫ p, τ p.1 * B p * ψ p.2 ∂ν) +
      ∑ j, ∫ p, τ p.1 * P j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν := by
  have hs : ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
      (∫ p, (f p - B p) * φ p ∂ν) =
        ∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
    intro φ hφ hφc hφs
    have hfi : Integrable (fun p => f p * φ p) ν :=
      hf.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have hBi : Integrable (fun p => B p * φ p) ν :=
      hB.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    simp_rw [sub_mul]
    rw [integral_sub hfi hBi, htest φ hφ hφc hφs]
    ring
  have h := integral_tensor_of_compact_source_support hΩ hK hKs hS hP hs hψ hτ hτc
  simp_rw [mul_sub, sub_mul] at h
  rw [integral_sub hft hBt] at h
  linarith only [h]

end DifferentialGeometry.Analysis.Sobolev.Euclidean
