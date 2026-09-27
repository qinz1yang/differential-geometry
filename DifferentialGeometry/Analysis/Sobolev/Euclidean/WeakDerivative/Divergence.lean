import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open MeasureTheory Set Filter

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakDiv.congr_ae
    {Omega : Set E} {f g : E → ℝ} {F G : E → E}
    (h : HasWeakDiv f F Omega)
    (hf : f =ᵐ[volume.restrict Omega] g)
    (hF : F =ᵐ[volume.restrict Omega] G) : HasWeakDiv g G Omega := by
  intro phi hphi hphi_cpt hphi_sub
  rw [show (∫ x in Omega, ∑ i : Fin d,
      G x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1)) =
        ∫ x in Omega, ∑ i : Fin d,
          F x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1) from
      integral_congr_ae (hF.mono fun x hx => by dsimp only; rw [hx])]
  rw [h phi hphi hphi_cpt hphi_sub]
  congr 1
  exact integral_congr_ae (hf.mono fun x hx => by dsimp only; rw [hx])

theorem HasWeakDiv.const_smul
    {Omega : Set E} {g : E → ℝ} {F : E → E}
    (h : HasWeakDiv g F Omega) (c : ℝ) :
    HasWeakDiv (fun x => c * g x) (fun x => c • F x) Omega := by
  intro phi hphi hphi_cpt hphi_sub
  have heq : (fun x => ∑ i : Fin d,
      (c • F x) i * (fderiv ℝ phi x) (EuclideanSpace.single i 1)) =
      fun x => c * ∑ i : Fin d,
        F x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
    funext x
    simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [heq, integral_const_mul, h phi hphi hphi_cpt hphi_sub]
  simp only [mul_assoc, integral_const_mul, mul_neg]

private theorem integrable_mul_partial
    {Omega : Set E} {f phi : E → ℝ}
    (hf : LocallyIntegrable f (volume.restrict Omega))
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hphi_cpt : HasCompactSupport phi) (i : Fin d) :
    Integrable (fun x => f x * (fderiv ℝ phi x) (EuclideanSpace.single i 1))
      (volume.restrict Omega) := by
  simpa only [smul_eq_mul] using
    hf.integrable_smul_right_of_hasCompactSupport
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))

theorem HasWeakDiv.add
    {Omega : Set E} {f g : E → ℝ} {F G : E → E}
    (h : HasWeakDiv f F Omega) (h' : HasWeakDiv g G Omega)
    (hF : ∀ i : Fin d, LocallyIntegrable (fun x => F x i) (volume.restrict Omega))
    (hG : ∀ i : Fin d, LocallyIntegrable (fun x => G x i) (volume.restrict Omega))
    (hf : LocallyIntegrable f (volume.restrict Omega))
    (hg : LocallyIntegrable g (volume.restrict Omega)) :
    HasWeakDiv (f + g) (F + G) Omega := by
  intro phi hphi hphi_cpt hphi_sub
  have hF_int := integrable_finsetSum Finset.univ
    (fun i _ => integrable_mul_partial (hF i) hphi hphi_cpt i)
  have hG_int := integrable_finsetSum Finset.univ
    (fun i _ => integrable_mul_partial (hG i) hphi hphi_cpt i)
  have hf_int : Integrable (fun x => f x * phi x) (volume.restrict Omega) := by
    simpa only [smul_eq_mul] using
      hf.integrable_smul_right_of_hasCompactSupport hphi.continuous hphi_cpt
  have hg_int : Integrable (fun x => g x * phi x) (volume.restrict Omega) := by
    simpa only [smul_eq_mul] using
      hg.integrable_smul_right_of_hasCompactSupport hphi.continuous hphi_cpt
  simp only [Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  rw [integral_add hF_int hG_int, integral_add hf_int hg_int,
    h phi hphi hphi_cpt hphi_sub, h' phi hphi hphi_cpt hphi_sub, neg_add]

theorem HasWeakDiv.comm
    {Omega : Set E} {f g : E → ℝ} {F G : E → E} {l : Fin d}
    (hdiv : HasWeakDiv f F Omega)
    (hpartial : HasWeakPartialDeriv l g f Omega)
    (hparts : ∀ i : Fin d,
      HasWeakPartialDeriv l (fun x => G x i) (fun x => F x i) Omega)
    (hF : ∀ i : Fin d, LocallyIntegrable (fun x => F x i) (volume.restrict Omega))
    (hG : ∀ i : Fin d, LocallyIntegrable (fun x => G x i) (volume.restrict Omega)) :
    HasWeakDiv g G Omega := by
  intro phi hphi hphi_cpt hphi_sub
  let D : Fin d → E → ℝ := fun i x => (fderiv ℝ phi x) (EuclideanSpace.single i 1)
  have hdphi : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ phi) := hphi.fderiv_right (by simp)
  have hD : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (D i) :=
    fun i => hdphi.clm_apply contDiff_const
  have hD_cpt : ∀ i, HasCompactSupport (D i) :=
    fun i => hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hD_sub : ∀ i, tsupport (D i) ⊆ Omega := fun i =>
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hphi_sub
  have hcomm : ∀ (x : E) (i : Fin d),
      (fderiv ℝ (D i) x) (EuclideanSpace.single l 1) =
        (fderiv ℝ (D l) x) (EuclideanSpace.single i 1) := by
    intro x i
    simp only [D, fderiv_clm_apply (hdphi.differentiable (by simp) x)
      (differentiableAt_const _), fderiv_const_apply, add_apply,
      ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    exact hphi.contDiffAt.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      decide) (EuclideanSpace.single l 1) (EuclideanSpace.single i 1)
  have hparts_int : ∀ i : Fin d,
      (∫ x in Omega, G x i * D i x) =
        -(∫ x in Omega, F x i * (fderiv ℝ (D l) x) (EuclideanSpace.single i 1)) := by
    intro i
    have hi := hparts i (D i) (hD i) (hD_cpt i) (hD_sub i)
    have heq : (∫ x in Omega, F x i * (fderiv ℝ (D i) x) (EuclideanSpace.single l 1)) =
        ∫ x in Omega, F x i * (fderiv ℝ (D l) x) (EuclideanSpace.single i 1) :=
      integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [hcomm x i])
    linarith
  have hG_int : ∀ i : Fin d, Integrable (fun x => G x i * D i x)
      (volume.restrict Omega) := fun i => integrable_mul_partial (hG i) hphi hphi_cpt i
  have hF_int : ∀ i : Fin d,
      Integrable (fun x => F x i * (fderiv ℝ (D l) x) (EuclideanSpace.single i 1))
        (volume.restrict Omega) :=
    fun i => integrable_mul_partial (hF i) (hD l) (hD_cpt l) i
  change (∫ x in Omega, ∑ i : Fin d, G x i * D i x) = _
  rw [integral_finsetSum _ (fun i _ => hG_int i)]
  simp_rw [hparts_int, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun i _ => hF_int i),
    hdiv (D l) (hD l) (hD_cpt l) (hD_sub l), neg_neg]
  exact hpartial phi hphi hphi_cpt hphi_sub

end DeGiorgi
