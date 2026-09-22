import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeAffine
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Determinant

noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Sobolev

theorem weak_divergence_comp_spatial_affineEquiv
    {d m : ℕ} (e : EuclideanSpace ℝ (Fin d) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin m))
    {J : Set ℝ} {Ω : Set (EuclideanSpace ℝ (Fin m))}
    {U R : ℝ × EuclideanSpace ℝ (Fin m) → ℝ}
    {V : Fin m → ℝ × EuclideanSpace ℝ (Fin m) → ℝ}
    (hV : ∀ i, LocallyIntegrableOn (V i) (J ×ˢ Ω)
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))))
    (hweak : ∀ φ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
      (∫ p in J ×ˢ Ω, U p * fderiv ℝ φ p (1, 0) ∂volume.prod volume) =
        (∑ i, ∫ p in J ×ˢ Ω, V i p * fderiv ℝ φ p (0, EuclideanSpace.single i 1)
          ∂volume.prod volume) - ∫ p in J ×ˢ Ω, R p * φ p ∂volume.prod volume) :
    ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ (e ⁻¹' Ω) →
      (∫ p in J ×ˢ (e ⁻¹' Ω), U (p.1, e p.2) * fderiv ℝ φ p (1, 0) ∂volume.prod volume) =
        (∑ j, ∫ p in J ×ˢ (e ⁻¹' Ω),
          (∑ i, e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1) j * V i (p.1, e p.2)) *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod volume) -
        ∫ p in J ×ˢ (e ⁻¹' Ω), R (p.1, e p.2) * φ p ∂volume.prod volume := by
  let ep := (ContinuousAffineEquiv.refl ℝ ℝ).prodCongr e
  let μ : Measure (ℝ × EuclideanSpace ℝ (Fin d)) := volume.prod volume
  let ν : Measure (ℝ × EuclideanSpace ℝ (Fin m)) := volume.prod volume
  let W := fun i j => e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1) j
  have hpre : ep ⁻¹' (J ×ˢ Ω) = J ×ˢ (e ⁻¹' Ω) := rfl
  have htime : ep.toAffineEquiv.linear (1, 0) = (1, 0) := by
    change ((1 : ℝ), e.toAffineEquiv.linear 0) = (1, 0)
    rw [map_zero]
  have hspace (i : Fin m) : ep.toAffineEquiv.linear
      (0, e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1)) = (0, EuclideanSpace.single i 1) := by
    change ((0 : ℝ), e.toAffineEquiv.linear
      (e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1))) = (0, EuclideanSpace.single i 1)
    rw [LinearEquiv.apply_symm_apply]
  have ht := weak_divergence_comp_affineEquiv ep (μ := μ) (ν := ν) Finset.univ (1, 0)
    (fun i : Fin m => (0, e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1)))
    (U := U) (V := V) (R := R)
    (fun φ hφ hφc hφs => by simpa only [htime, hspace] using hweak φ hφ hφc hφs)
  intro φ hφ hφc hφs
  have hbase := ht φ hφ hφc (hpre.symm ▸ hφs)
  change (∫ p in J ×ˢ (e ⁻¹' Ω), U (ep p) * fderiv ℝ φ p (1, 0) ∂μ) = _
  rw [hpre] at hbase
  rw [hbase]
  congr 1
  have hdir (p : ℝ × EuclideanSpace ℝ (Fin d)) (i : Fin m) :
      fderiv ℝ φ p (0, e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1)) =
        ∑ j, W i j * fderiv ℝ φ p (0, EuclideanSpace.single j 1) := by
    have hv : (∑ j, W i j • EuclideanSpace.single j 1) =
        e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1) := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr
          (e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1))
    have hp : (∑ j, W i j • ((0 : ℝ), EuclideanSpace.single j 1)) =
        (0, e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1)) := by
      simpa only [map_sum, map_smul, ContinuousLinearMap.inr_apply] using
        congrArg (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) hv
    conv_lhs => rw [← hp]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hVp (i) : LocallyIntegrableOn (V i ∘ ep) (J ×ˢ (e ⁻¹' Ω)) μ := by
    simpa only [hpre] using (hV i).comp_affineEquiv ep (μ := μ)
  have hint (i : Fin m) (j : Fin d) : Integrable
      (fun p => V i (ep p) * fderiv ℝ φ p (0, EuclideanSpace.single j 1))
      (μ.restrict (J ×ˢ (e ⁻¹' Ω))) := by
    let ψ := fun p => fderiv ℝ φ p (0, EuclideanSpace.single j 1)
    have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψc : HasCompactSupport ψ := hφc.fderiv_apply (𝕜 := ℝ) _
    have hψs : tsupport ψ ⊆ J ×ˢ (e ⁻¹' Ω) := (tsupport_fderiv_apply_subset ℝ _).trans hφs
    apply Integrable.mono_measure _ Measure.restrict_le_self
    apply (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport (fun p => V i (ep p) * ψ p)).trans tsupport_mul_subset_right)).mp
    exact ((hVp i).integrableOn_compact_subset hψs hψc).mul_continuousOn hψ.continuousOn hψc
  have hl (i j p) : V i (ep p) * (W i j * fderiv ℝ φ p (0, EuclideanSpace.single j 1)) =
      W i j * (V i (ep p) * fderiv ℝ φ p (0, EuclideanSpace.single j 1)) := by ring
  simp only [hdir, Finset.mul_sum, hl, Finset.sum_mul, mul_assoc]
  have hsleft (i) :
      (∫ p in J ×ˢ (e ⁻¹' Ω), ∑ j, W i j * (V i (ep p) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∂μ) =
      ∑ j, ∫ p in J ×ˢ (e ⁻¹' Ω), W i j * (V i (ep p) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∂μ :=
    integral_finsetSum _ (fun j _ => (hint i j).const_mul (W i j))
  have hsright (j) :
      (∫ p in J ×ˢ (e ⁻¹' Ω), ∑ i, W i j * (V i (ep p) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∂μ) =
      ∑ i, ∫ p in J ×ˢ (e ⁻¹' Ω), W i j * (V i (ep p) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∂μ :=
    integral_finsetSum _ (fun i _ => (hint i j).const_mul (W i j))
  change (∑ i, ∫ p in J ×ˢ (e ⁻¹' Ω), ∑ j, W i j * (V i (ep p) *
    fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∂μ) =
      ∑ j, ∫ p in J ×ˢ (e ⁻¹' Ω), ∑ i, W i j * (V i (ep p) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∂μ
  simp only [hsleft, hsright]
  exact Finset.sum_comm

theorem weighted_divergence_comp_spatial_affineEquiv
    {d : ℕ} (e : EuclideanSpace ℝ (Fin d) ≃ᴬ[ℝ] EuclideanSpace ℝ (Fin d))
    {J : Set ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ρ U R : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    {K : ℝ × EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {A : ℝ × EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    (hV : ∀ j, LocallyIntegrableOn (fun p => ((A p).transpose *ᵥ K p) j) (J ×ˢ Ω)
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))))
    (hweak : ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
      (∫ p in J ×ˢ Ω, ρ p * U p * fderiv ℝ φ p (1, 0) ∂volume.prod volume) =
        (∑ j, ∫ p in J ×ˢ Ω, ((A p).transpose *ᵥ K p) j *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod volume) -
        ∫ p in J ×ˢ Ω, R p * φ p ∂volume.prod volume) :
    let C := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis e.toAffineEquiv.linear.toLinearMap
    let c := |e.toAffineEquiv.linear.toLinearMap.det|
    let ρ' := fun p : ℝ × EuclideanSpace ℝ (Fin d) => c * ρ (p.1, e p.2)
    let K' := fun p : ℝ × EuclideanSpace ℝ (Fin d) => C.transpose *ᵥ K (p.1, e p.2)
    let A' := fun p : ℝ × EuclideanSpace ℝ (Fin d) => c • (C⁻¹ * A (p.1, e p.2) * C⁻¹.transpose)
    ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ J ×ˢ (e ⁻¹' Ω) →
      (∫ p in J ×ˢ (e ⁻¹' Ω), ρ' p * U (p.1, e p.2) * fderiv ℝ φ p (1, 0)
        ∂volume.prod volume) =
        (∑ j, ∫ p in J ×ˢ (e ⁻¹' Ω), ((A' p).transpose *ᵥ K' p) j *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂volume.prod volume) -
        ∫ p in J ×ˢ (e ⁻¹' Ω), c * R (p.1, e p.2) * φ p ∂volume.prod volume := by
  intro C c ρ' K' A' φ hφ hφc hφs
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hC : IsUnit C.det := e.toAffineEquiv.linear.isUnit_det b b
  have hCi : C⁻¹ = LinearMap.toMatrix b b e.toAffineEquiv.linear.symm.toLinearMap := by
    apply Matrix.inv_eq_left_inv
    simpa only [LinearEquiv.symm_comp, LinearMap.toMatrix_id] using
      (LinearMap.toMatrix_comp b b b e.toAffineEquiv.linear.symm.toLinearMap
        e.toAffineEquiv.linear.toLinearMap).symm
  have hCi_apply (i j) : C⁻¹ i j =
      e.toAffineEquiv.linear.symm (EuclideanSpace.single j 1) i := by
    rw [hCi]
    simp only [LinearMap.toMatrix_apply, b, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, LinearEquiv.coe_coe]
  have hflux (p : ℝ × EuclideanSpace ℝ (Fin d)) :
      (A' p).transpose *ᵥ K' p =
        c • (C⁻¹ *ᵥ ((A (p.1, e p.2)).transpose *ᵥ K (p.1, e p.2))) := by
    dsimp only [A', K']
    rw [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv C hC, Matrix.transpose_one, Matrix.mul_one]
  have h := weak_divergence_comp_spatial_affineEquiv e (U := fun p => ρ p * U p)
    (V := fun j p => ((A p).transpose *ᵥ K p) j) (R := R) hV hweak φ hφ hφc hφs
  have hi (p : ℝ × EuclideanSpace ℝ (Fin d)) (j) :
      ((A' p).transpose *ᵥ K' p) j =
        c * ∑ i, e.toAffineEquiv.linear.symm (EuclideanSpace.single i 1) j *
          ((A (p.1, e p.2)).transpose *ᵥ K (p.1, e p.2)) i := by
    rw [hflux]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hCi_apply]
  simp only [ρ', hi, mul_assoc, integral_const_mul, ← Finset.mul_sum]
  simpa only [mul_assoc, mul_sub] using congrArg (fun x : ℝ => c * x) h

end DifferentialGeometry.Analysis.Parabolic
