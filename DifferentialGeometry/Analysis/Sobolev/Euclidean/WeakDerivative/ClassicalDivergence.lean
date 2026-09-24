import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import Mathlib.MeasureTheory.Measure.OpenPos

section

noncomputable section

open MeasureTheory Set

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integrable_mul_test
    {Ω : Set E} (hΩ : IsOpen Ω) {f φ : E → ℝ}
    (hf : ContinuousOn f Ω) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    Integrable (fun x => f x * φ x) :=
  ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hΩ
    (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left

theorem hasWeakDiv_of_contDiffOn
    {Ω : Set E} (hΩ : IsOpen Ω) {F : E → E}
    (hF : ∀ i : Fin d, ContDiffOn ℝ 1 (fun x => F x i) Ω) :
    HasWeakDiv (fun x => ∑ i : Fin d,
      fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1)) F Ω := by
  intro φ hφ hφc hφs
  have hI (i : Fin d) : Integrable (fun x =>
      F x i * fderiv ℝ φ x (EuclideanSpace.single i 1)) (volume.restrict Ω) :=
    (integrable_mul_test hΩ (hF i).continuousOn
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hφs)).restrict
  have hD (i : Fin d) : Integrable (fun x =>
      fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1) * φ x)
      (volume.restrict Ω) :=
    (integrable_mul_test hΩ
      (((hF i).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const)
      hφ.continuous hφc hφs).restrict
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp_rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_contDiffOn
    hΩ (hF _) _ φ hφ hφc hφs]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hD i)]
  simp only [Finset.sum_mul]

theorem HasWeakDiv.eqOn_of_continuousOn
    {Ω : Set E} (hΩ : IsOpen Ω) {f g : E → ℝ} {F : E → E}
    (hf : HasWeakDiv f F Ω) (hg : HasWeakDiv g F Ω)
    (hfc : ContinuousOn f Ω) (hgc : ContinuousOn g Ω) : EqOn f g Ω := by
  have hzero : ∀ᵐ x ∂volume, x ∈ Ω → (f - g) x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hfc.sub hgc).locallyIntegrableOn hΩ.measurableSet)
    intro φ hφ hφc hφs
    have he : (∫ x in Ω, f x * φ x) = ∫ x in Ω, g x * φ x := by
      have h₁ := hf φ hφ hφc hφs
      have h₂ := hg φ hφ hφc hφs
      linarith only [h₁, h₂]
    have hfi := integrable_mul_test hΩ hfc hφ.continuous hφc hφs
    have hgi := integrable_mul_test hΩ hgc hφ.continuous hφc hφs
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => show φ x • (f - g) x = 0 by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)), zero_smul])]
    simp_rw [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub]
    · simp only [mul_comm, he, sub_self]
    · simpa only [mul_comm] using hfi.restrict (s := Ω)
    · simpa only [mul_comm] using hgi.restrict (s := Ω)
  have heq : f =ᵐ[volume.restrict Ω] g := by
    change ∀ᵐ x ∂volume.restrict Ω, f x = g x
    rw [ae_restrict_iff' hΩ.measurableSet]
    filter_upwards [hzero] with x hx hxm
    exact sub_eq_zero.mp (hx hxm)
  exact Measure.eqOn_open_of_ae_eq heq hΩ hfc hgc

theorem HasWeakDiv.eqOn_sum_fderiv
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} {F : E → E}
    (h : HasWeakDiv f F Ω) (hf : ContinuousOn f Ω)
    (hF : ∀ i : Fin d, ContDiffOn ℝ 1 (fun x => F x i) Ω) :
    EqOn f (fun x => ∑ i : Fin d,
      fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1)) Ω := by
  apply h.eqOn_of_continuousOn hΩ (hasWeakDiv_of_contDiffOn hΩ hF) hf
  exact continuousOn_finsetSum Finset.univ fun i _ =>
    ((hF i).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const

end DeGiorgi

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem HasWeakDiv.sum_fderiv_eq_zero
    {Ω : Set V} (hΩ : IsOpen Ω) {F : V → V}
    (hdiv : HasWeakDiv 0 F Ω) (hF : ContDiffOn ℝ 1 F Ω) :
    ∀ x ∈ Ω, (∑ i : Fin d, fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1)) = 0 := by
  intro x hx
  exact (hdiv.eqOn_sum_fderiv hΩ continuousOn_const
    (fun i => (contDiff_piLp_apply (p := 2) (i := i)).comp_contDiffOn hF) hx).symm

end DeGiorgi

end

end
