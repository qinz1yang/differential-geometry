import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_mul_sum_fderiv_eq_neg_sum_integral
    {Ω : Set E} {u : E → ℝ} {Du F : Fin d → E → ℝ}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hDu : ∀ i, DeGiorgi.HasWeakPartialDeriv i (Du i) u Ω)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hFc : ∀ i, HasCompactSupport (F i)) (hFs : ∀ i, tsupport (F i) ⊆ Ω) :
    (∫ x in Ω, u x * ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) =
      -∑ i, ∫ x in Ω, Du i x * F i x := by
  have hint (i : Fin d) : Integrable
      (fun x => u x * fderiv ℝ (F i) x (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
    exact hu.integrable_smul_right_of_hasCompactSupport
      (((hF i).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hFc i).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [hDu _ _ (hF _) (hFc _) (hFs _), Finset.sum_neg_distrib]

theorem integral_mul_sum_fderiv_mul_eq_neg_sum_integral
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} {Du : Fin d → E → ℝ}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hDu : ∀ i, DeGiorgi.HasWeakPartialDeriv i (Du i) u Ω)
    {C : Fin d → Fin d → E → ℝ} (hC : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    (∫ x in Ω, u x * ∑ i, fderiv ℝ
      (fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) =
      -∑ i, ∫ x in Ω, Du i x * ∑ j, C i j x * fderiv ℝ ψ x (EuclideanSpace.single j 1) := by
  let F := fun i y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)
  have hFs (i : Fin d) : tsupport (F i) ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro x hx
    by_contra hxψ
    have hz (j : Fin d) : fderiv ℝ ψ x (EuclideanSpace.single j 1) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ ψ y (EuclideanSpace.single j 1))
        (fun hy => hxψ (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1) hy))
    exact hx (by simp [F, hz])
  have hFc (i : Fin d) : HasCompactSupport (F i) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) (hFs i)
  have hF (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (F i) := by
    apply ContDiffOn.contDiff_of_tsupport_subset (s := Ω) _ hΩ ((hFs i).trans hψs)
    apply ContDiffOn.sum
    intro j _
    exact (hC i j).mul
      ((hψ.fderiv_right (by simp)).clm_apply contDiff_const).contDiffOn
  exact integral_mul_sum_fderiv_eq_neg_sum_integral hu hDu hF hFc
    (fun i => (hFs i).trans hψs)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
