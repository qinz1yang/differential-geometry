import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open MeasureTheory Set Filter

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakPartialDeriv.comm
    {Omega : Set E} {u ui uj uij : E → ℝ} {i j : Fin d}
    (hui : HasWeakPartialDeriv i ui u Omega)
    (huj : HasWeakPartialDeriv j uj u Omega)
    (huij : HasWeakPartialDeriv i uij uj Omega) :
    HasWeakPartialDeriv j uij ui Omega := by
  intro phi hphi hphi_cpt hphi_sub
  let phii : E → ℝ := fun x => (fderiv ℝ phi x) (EuclideanSpace.single i 1)
  let phij : E → ℝ := fun x => (fderiv ℝ phi x) (EuclideanSpace.single j 1)
  have hdphi : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ phi) :=
    hphi.fderiv_right (by simp)
  have hphii : ContDiff ℝ (⊤ : ℕ∞) phii := hdphi.clm_apply contDiff_const
  have hphij : ContDiff ℝ (⊤ : ℕ∞) phij := hdphi.clm_apply contDiff_const
  have h1 := hui phij hphij
    (hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hphi_sub)
  have h2 := huj phii hphii
    (hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hphi_sub)
  have h3 := huij phi hphi hphi_cpt hphi_sub
  have hcomm : ∀ x : E,
      (fderiv ℝ phij x) (EuclideanSpace.single i 1) =
        (fderiv ℝ phii x) (EuclideanSpace.single j 1) := by
    intro x
    have heval : ∀ k : Fin d,
        fderiv ℝ (fun y => (fderiv ℝ phi y) (EuclideanSpace.single k 1)) x =
          (fderiv ℝ (fderiv ℝ phi) x).flip (EuclideanSpace.single k 1) := by
      intro k
      rw [fderiv_clm_apply (hdphi.differentiable (by simp) x) (differentiableAt_const _),
        fderiv_const_apply]
      simp
    change (fderiv ℝ (fun y => (fderiv ℝ phi y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) =
      (fderiv ℝ (fun y => (fderiv ℝ phi y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single j 1)
    rw [heval j, heval i, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
    exact hphi.contDiffAt.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      decide) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hint : (∫ x in Omega, u x * (fderiv ℝ phij x) (EuclideanSpace.single i 1)) =
      ∫ x in Omega, u x * (fderiv ℝ phii x) (EuclideanSpace.single j 1) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hcomm x]
  linarith

end DeGiorgi

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem chosenWeakPartialOrZero_comm
    {p : ENNReal} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemWkp 2 p u Omega) (i j : Fin d) :
    chosenWeakPartialOrZero p j (chosenWeakPartialOrZero p i u Omega) Omega
      =ᵐ[volume.restrict Omega]
        chosenWeakPartialOrZero p i (chosenWeakPartialOrZero p j u Omega) Omega := by
  have hui : DeGiorgi.MemW1p p (chosenWeakPartialOrZero p i u Omega) Omega :=
    MemWkp.one_iff_memW1p.mp (hu.chosenWeakPartial_mem i)
  have huj : DeGiorgi.MemW1p p (chosenWeakPartialOrZero p j u Omega) Omega :=
    MemWkp.one_iff_memW1p.mp (hu.chosenWeakPartial_mem j)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hOmega
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hui j)
    ((chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p i).comm
      (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p j)
      (chosenWeakPartialOrZero_isWeakPartial_of_mem huj i))
    ((chosenWeakPartialOrZero_memLp_of_mem hui j).locallyIntegrable hp)
    ((chosenWeakPartialOrZero_memLp_of_mem huj i).locallyIntegrable hp)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
