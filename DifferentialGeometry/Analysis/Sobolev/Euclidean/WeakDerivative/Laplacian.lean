import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Analysis.Integration.Integral.Laplacian
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem laplacian_eq_sum_euclidean_fderiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian f x = ∑ j : Fin d,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)) (differentiableAt_const _)]
  simp [iteratedFDeriv_two_apply]

theorem integral_mul_laplacian_eq_neg_integral_weak_gradient
    {Ω : Set E} {u : E → ℝ} {G : E → E}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hG : ∀ j, LocallyIntegrable (fun x => G x j) (volume.restrict Ω))
    (hgrad : DeGiorgi.HasWeakGrad G u Ω)
    {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, u x * Laplacian.laplacian φ x) =
      -∫ x in Ω, inner ℝ (G x) (DeGiorgi.smoothGradField φ x) := by
  let D (j : Fin d) (x : E) := fderiv ℝ φ x (EuclideanSpace.single j 1)
  have hD (j : Fin d) : ContDiff ℝ ∞ (D j) :=
    (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc (j : Fin d) : HasCompactSupport (D j) := hφ.2.1.fderiv_apply ℝ _
  have hDs (j : Fin d) : tsupport (D j) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2
  have hweak (j : Fin d) := hgrad j (D j) (hD j) (hDc j) (hDs j)
  have hleftI (j : Fin d) : IntegrableOn
      (fun x => u x * fderiv ℝ (D j) x (EuclideanSpace.single j 1)) Ω := by
    exact hu.integrable_smul_right_of_hasCompactSupport
      (((hD j).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hDc j).fderiv_apply ℝ _)
  have hrightI (j : Fin d) : IntegrableOn (fun x => G x j * D j x) Ω := by
    have hi := hG j
    exact hi.integrable_smul_right_of_hasCompactSupport (hD j).continuous (hDc j)
  have hEq : (∫ x in Ω, u x * Laplacian.laplacian φ x) =
      -∫ x in Ω, inner ℝ (G x) (DeGiorgi.smoothGradField φ x) := by
    simp_rw [laplacian_eq_sum_euclidean_fderiv (hφ.1.contDiffAt.of_le (by norm_cast)),
      Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ => hleftI j)]
    simp_rw [hweak]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hrightI j)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      DeGiorgi.smoothGradField, D, mul_comm]
  exact hEq


theorem integral_mul_laplacian_eq_of_hasWeakDiv
    {Ω : Set E} {u f : E → ℝ} {G : E → E}
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hG : ∀ j, LocallyIntegrable (fun x => G x j) (volume.restrict Ω))
    (hgrad : DeGiorgi.HasWeakGrad G u Ω) (hdiv : DeGiorgi.HasWeakDiv f G Ω)
    {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, u x * Laplacian.laplacian φ x) = ∫ x in Ω, f x * φ x := by
  rw [integral_mul_laplacian_eq_neg_integral_weak_gradient hu hG hgrad hφ]
  have hh := hdiv φ hφ.1 hφ.2.1 hφ.2.2
  have heq : (∫ x in Ω, inner ℝ (G x) (DeGiorgi.smoothGradField φ x)) =
      ∫ x in Ω, ∑ j, G x j * fderiv ℝ φ x (EuclideanSpace.single j 1) := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      DeGiorgi.smoothGradField, mul_comm]
  rw [heq, hh, neg_neg]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integrable_mul_test
    {Ω : Set E} {u ψ : E → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    IntegrableOn (fun x => u x * ψ x) Ω := by
  have hi : IntegrableOn (fun x => u x * ψ x) (tsupport ψ) :=
    (hu.integrableOn_compact_subset hs hc).mul_continuousOn hψ.continuousOn hc
  have hg : Integrable (fun x => u x * ψ x) volume :=
    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right u ψ).trans (subset_tsupport ψ))).mp hi
  exact hg.restrict

theorem integral_mul_laplacian_eq_neg_integral_weak_gradient_of_locallyIntegrableOn
    {Ω : Set E} {u : E → ℝ} {G : E → E}
    (hu : LocallyIntegrableOn u Ω volume)
    (hG : ∀ j, LocallyIntegrableOn (fun x => G x j) Ω volume)
    (hgrad : DeGiorgi.HasWeakGrad G u Ω)
    {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, u x * Laplacian.laplacian φ x) =
      -∫ x in Ω, inner ℝ (G x) (DeGiorgi.smoothGradField φ x) := by
  let D (j : Fin d) (x : E) := fderiv ℝ φ x (EuclideanSpace.single j 1)
  have hD (j : Fin d) : ContDiff ℝ ∞ (D j) :=
    (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc (j : Fin d) : HasCompactSupport (D j) := hφ.2.1.fderiv_apply ℝ _
  have hDs (j : Fin d) : tsupport (D j) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2
  have hweak (j : Fin d) := hgrad j (D j) (hD j) (hDc j) (hDs j)
  have hleftI (j : Fin d) : IntegrableOn
      (fun x => u x * fderiv ℝ (D j) x (EuclideanSpace.single j 1)) Ω :=
    integrable_mul_test hu
      (((hD j).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hDc j).fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans (hDs j))
  have hrightI (j : Fin d) : IntegrableOn (fun x => G x j * D j x) Ω :=
    integrable_mul_test (hG j) (hD j).continuous (hDc j) (hDs j)
  have hEq : (∫ x in Ω, u x * Laplacian.laplacian φ x) =
      -∫ x in Ω, inner ℝ (G x) (DeGiorgi.smoothGradField φ x) := by
    simp_rw [laplacian_eq_sum_euclidean_fderiv (hφ.1.contDiffAt.of_le (by norm_cast)),
      Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ => hleftI j)]
    simp_rw [hweak]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hrightI j)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      DeGiorgi.smoothGradField, D, mul_comm]
  exact hEq


theorem integral_mul_laplacian_eq_of_hasWeakDiv_of_locallyIntegrableOn
    {Ω : Set E} {u f : E → ℝ} {G : E → E}
    (hu : LocallyIntegrableOn u Ω volume)
    (hG : ∀ j, LocallyIntegrableOn (fun x => G x j) Ω volume)
    (hgrad : DeGiorgi.HasWeakGrad G u Ω) (hdiv : DeGiorgi.HasWeakDiv f G Ω)
    {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, u x * Laplacian.laplacian φ x) = ∫ x in Ω, f x * φ x := by
  rw [integral_mul_laplacian_eq_neg_integral_weak_gradient_of_locallyIntegrableOn hu hG hgrad hφ]
  have hh := hdiv φ hφ.1 hφ.2.1 hφ.2.2
  have heq : (∫ x in Ω, inner ℝ (G x) (DeGiorgi.smoothGradField φ x)) =
      ∫ x in Ω, ∑ j, G x j * fderiv ℝ φ x (EuclideanSpace.single j 1) := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      DeGiorgi.smoothGradField, mul_comm]
  rw [heq, hh, neg_neg]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem laplacian_eq_of_contDiffOn_of_hasWeakDiv
    {Ω : Set V} (hΩ : IsOpen Ω) {u f : V → ℝ}
    (hu2 : ContDiffOn ℝ 2 u Ω) (hf : ContinuousOn f Ω) {G : V → V}
    (hG : ∀ j, LocallyIntegrableOn (fun x => G x j) Ω volume)
    (hgrad : DeGiorgi.HasWeakGrad G u Ω) (hdiv : DeGiorgi.HasWeakDiv f G Ω) :
    EqOn (Laplacian.laplacian u) f Ω := by
  have hΔc : ContinuousOn (Laplacian.laplacian u) Ω := fun x hx =>
    ((hu2.contDiffAt (hΩ.mem_nhds hx)).continuousAt_laplacian).continuousWithinAt
  have hzero : ∀ᵐ x ∂volume, x ∈ Ω → Laplacian.laplacian u x - f x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hΔc.sub hf).locallyIntegrableOn hΩ.measurableSet)
    intro φ hφ hφc hφs
    have hd := integral_mul_laplacian_eq_of_hasWeakDiv_of_locallyIntegrableOn
      (hu2.continuousOn.locallyIntegrableOn hΩ.measurableSet) hG hgrad hdiv
      (show DeGiorgi.IsSmoothTestOn Ω φ from ⟨hφ, hφc, hφs⟩)
    have hI {a : V → ℝ} (ha : ContinuousOn a Ω) : Integrable (fun x => φ x * a x) volume :=
      ((hφ.continuous.continuousOn.mul ha).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_left.trans hφs)).integrable_of_hasCompactSupport hφc.mul_right
    have hΔs : tsupport (Laplacian.laplacian φ) ⊆ Ω := (tsupport_laplacian_subset _).trans hφs
    have hleft : (∫ x in Ω, u x * Laplacian.laplacian φ x) =
        ∫ x, Laplacian.laplacian φ x * u x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hΔs ht)), mul_zero]
    have hright : (∫ x in Ω, f x * φ x) = ∫ x, φ x * f x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hφs ht)), mul_zero]
    rw [hleft, hright] at hd
    have hgreen := DifferentialGeometry.Analysis.integral_smul_laplacian_eq_integral_laplacian_smul
      (μ := volume)
      (hφ.of_le (by norm_cast) : ContDiff ℝ 2 φ) hφc
      (fun x hx => hu2.contDiffAt (hΩ.mem_nhds (hφs hx)))
    simp only [smul_eq_mul] at hgreen ⊢
    change (∫ x, φ x * (Laplacian.laplacian u x - f x)) = 0
    simp_rw [mul_sub]
    rw [integral_sub (hI hΔc) (hI hf), hgreen, hd, sub_self]
  have hae : Laplacian.laplacian u =ᵐ[volume.restrict Ω] f := by
    change ∀ᵐ x ∂volume.restrict Ω, Laplacian.laplacian u x = f x
    rw [ae_restrict_iff' hΩ.measurableSet]
    exact hzero.mono fun x hx hxm => sub_eq_zero.mp (hx hxm)
  exact volume.eqOn_open_of_ae_eq hae hΩ hΔc hf

theorem laplacian_eq_of_contDiffOn_of_memW1p_hasWeakDiv
    {Ω : Set V} (hΩ : IsOpen Ω) {u f : V → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hu : DeGiorgi.MemW1pWitness p u Ω) (hu2 : ContDiffOn ℝ 2 u Ω)
    (hf : ContinuousOn f Ω) (hdiv : DeGiorgi.HasWeakDiv f hu.weakGrad Ω) :
    EqOn (Laplacian.laplacian u) f Ω :=
  laplacian_eq_of_contDiffOn_of_hasWeakDiv hΩ hu2 hf
    (fun j => locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hu.weakGrad_component_memLp j).locallyIntegrable hp)) hu.isWeakGrad hdiv

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
