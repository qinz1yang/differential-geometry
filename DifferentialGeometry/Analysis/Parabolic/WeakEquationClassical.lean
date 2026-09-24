import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeClassical
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weighted_divergence_eq_of_contDiffOn_ae_eq_of_locallyIntegrableOn
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {U u ρ F : ℝ × E → ℝ}
    {K : Fin d → ℝ × E → ℝ} {A : Fin d → Fin d → ℝ × E → ℝ}
    (hK : ∀ i, LocallyIntegrableOn (K i) (J ×ˢ Ω) (volume.prod volume))
    (hKw : ∀ i, ∀ᵐ t ∂volume.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => U (t, z)) Ω)
    (hu : ContDiffOn ℝ 2 u (J ×ˢ Ω))
    (hUu : U =ᵐ[(volume.restrict J).prod (volume.restrict Ω)] u)
    (hρ : ContDiffOn ℝ 1 ρ (J ×ˢ Ω))
    (hA : ∀ i j, ContDiffOn ℝ 1 (A i j) (J ×ˢ Ω)) (hF : ContinuousOn F (J ×ˢ Ω))
    (hweak : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ x, ρ x * U x * fderiv ℝ φ x (1, 0) ∂(volume.restrict J).prod (volume.restrict Ω)) =
        (∑ i, ∑ j, ∫ x, A i j x * K i x * fderiv ℝ φ x (0, EuclideanSpace.single j 1)
          ∂(volume.restrict J).prod (volume.restrict Ω)) -
            ∫ x, F x * φ x ∂(volume.restrict J).prod (volume.restrict Ω)) :
    ∀ x ∈ J ×ˢ Ω, fderiv ℝ (fun y => ρ y * u y) x (1, 0) =
      (∑ i, ∑ j, fderiv ℝ (fun y => A i j y * fderiv ℝ u y (0, EuclideanSpace.single i 1))
        x (0, EuclideanSpace.single j 1)) + F x := by
  let ν : Measure (ℝ × E) := (volume : Measure ℝ).prod volume
  have hO := hJ.prod hΩ
  have hU : LocallyIntegrableOn U (J ×ˢ Ω) (volume.prod volume) :=
    LocallyIntegrableOn.congr (by simpa only [Measure.prod_restrict] using hUu.symm)
      (hu.continuousOn.locallyIntegrableOn hO.measurableSet)
  have hu₁ : ContDiffOn ℝ 1 u (J ×ˢ Ω) := hu.of_le (by norm_num)
  have hgrad (i) : K i =ᵐ[(volume.restrict J).prod (volume.restrict Ω)]
      fun x => fderiv ℝ u x (0, EuclideanSpace.single i 1) := by
    have h := ae_eq_fderiv_of_weak_deriv_of_contDiffOn (μ := ν) hO
      (0, EuclideanSpace.single i 1) hu₁ (hK i) (by
        intro φ hφ hφc hφs
        rw [← Measure.prod_restrict]
        refine (integral_congr_ae ?_).trans
          (integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv_of_locallyIntegrableOn
            hU (hK i) i (hKw i) φ hφ hφc hφs)
        filter_upwards [hUu] with x hx
        exact congrArg (fun z => z * fderiv ℝ φ x (0, EuclideanSpace.single i 1)) hx.symm)
    simpa only [ν, Measure.prod_restrict] using h
  have hDu (i) : ContDiffOn ℝ 1 (fun x => fderiv ℝ u x (0, EuclideanSpace.single i 1)) (J ×ˢ Ω) :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  have h := fderiv_eq_sum_fderiv_add_of_weak_divergence (μ := ν) hO
    (Finset.univ : Finset (Fin d × Fin d)) (1, 0)
    (fun ij => (0, EuclideanSpace.single ij.2 1))
    (hρ.mul hu₁) (fun ij _ => (hA ij.1 ij.2).mul (hDu ij.1)) hF (by
      intro φ hφ hφc hφs
      rw [← Measure.prod_restrict]
      simp only [Fintype.sum_prod_type]
      have hleft : (∫ x, ρ x * u x * fderiv ℝ φ x (1, 0)
          ∂(volume.restrict J).prod (volume.restrict Ω)) =
          ∫ x, ρ x * U x * fderiv ℝ φ x (1, 0) ∂(volume.restrict J).prod (volume.restrict Ω) := by
        apply integral_congr_ae
        filter_upwards [hUu] with x hx
        rw [hx]
      rw [hleft, hweak φ hφ hφc hφs]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [hgrad i] with x hx
      rw [hx])
  simpa only [Fintype.sum_prod_type] using h

theorem weighted_divergence_eq_of_contDiffOn_ae_eq
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {U u ρ F : ℝ × E → ℝ}
    {K : Fin d → ℝ × E → ℝ} {A : Fin d → Fin d → ℝ × E → ℝ}
    (hK : ∀ i, MemLp (K i) p ((volume.restrict J).prod (volume.restrict Ω)))
    (hKw : ∀ i, ∀ᵐ t ∂volume.restrict J, DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => U (t, z)) Ω)
    (hu : ContDiffOn ℝ 2 u (J ×ˢ Ω))
    (hUu : U =ᵐ[(volume.restrict J).prod (volume.restrict Ω)] u)
    (hρ : ContDiffOn ℝ 1 ρ (J ×ˢ Ω))
    (hA : ∀ i j, ContDiffOn ℝ 1 (A i j) (J ×ˢ Ω)) (hF : ContinuousOn F (J ×ˢ Ω))
    (hweak : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ x, ρ x * U x * fderiv ℝ φ x (1, 0) ∂(volume.restrict J).prod (volume.restrict Ω)) =
        (∑ i, ∑ j, ∫ x, A i j x * K i x * fderiv ℝ φ x (0, EuclideanSpace.single j 1)
          ∂(volume.restrict J).prod (volume.restrict Ω)) -
            ∫ x, F x * φ x ∂(volume.restrict J).prod (volume.restrict Ω)) :
    ∀ x ∈ J ×ˢ Ω, fderiv ℝ (fun y => ρ y * u y) x (1, 0) =
      (∑ i, ∑ j, fderiv ℝ (fun y => A i j y * fderiv ℝ u y (0, EuclideanSpace.single i 1))
        x (0, EuclideanSpace.single j 1)) + F x := by
  refine weighted_divergence_eq_of_contDiffOn_ae_eq_of_locallyIntegrableOn hJ hΩ
    ?_ hKw hu hUu hρ hA hF hweak
  intro i
  apply locallyIntegrableOn_of_locallyIntegrable_restrict
  simpa only [Measure.prod_restrict] using (hK i).locallyIntegrable hp

end DifferentialGeometry.Analysis.Parabolic
