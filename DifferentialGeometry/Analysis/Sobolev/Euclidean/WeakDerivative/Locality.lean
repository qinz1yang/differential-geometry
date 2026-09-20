import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DeGiorgi.MemW1pWitness

variable {d : ℕ} {Ω U : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakGrad_ae_eq_of_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f g : E → ℝ} (hf : MemW1pWitness p f Ω) (hg : MemW1pWitness p g Ω)
    (hfg : f =ᵐ[volume.restrict U] g) :
    hf.weakGrad =ᵐ[volume.restrict U] hg.weakGrad := by
  have hcoord (i : Fin d) : (fun x => hf.weakGrad x i) =ᵐ[volume.restrict U]
      (fun x => hg.weakGrad x i) := by
    have hwf : HasWeakPartialDeriv i (fun x => hf.weakGrad x i) f U :=
      HasWeakPartialDeriv.restrict hU hsub (hf.isWeakGrad i)
    have hwg : HasWeakPartialDeriv i (fun x => hg.weakGrad x i) f U := by
      intro φ hφ hφc hφs
      have hleft : (∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          ∫ x in U, g x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [hfg] with x hx
        rw [hx]
      rw [hleft]
      exact HasWeakPartialDeriv.restrict hU hsub (hg.isWeakGrad i) φ hφ hφc hφs
    exact HasWeakPartialDeriv.ae_eq hU hwf hwg
      (((hf.weakGrad_component_memLp i).mono_measure
        (Measure.restrict_mono_set volume hsub)).locallyIntegrable hp)
      (((hg.weakGrad_component_memLp i).mono_measure
        (Measure.restrict_mono_set volume hsub)).locallyIntegrable hp)
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  exact PiLp.ext hx

end DeGiorgi.MemW1pWitness

end
