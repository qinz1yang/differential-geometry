import DifferentialGeometry.External.DeGiorgi.WeakFormulation.WeakDivergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem EllipticCoeff.memLp_matMulE
    {Omega : Set E} (A : EllipticCoeff d Omega)
    {p : ℝ≥0∞} {F : E → E} (hF : MemLp F p (volume.restrict Omega)) :
    MemLp (fun x => matMulE (A.a x) (F x)) p (volume.restrict Omega) := by
  have hentry : ∀ i j : Fin d, MemLp (fun x => A.a x i j) ⊤ (volume.restrict Omega) := by
    intro i j
    refine memLp_top_of_bound (A.measurable_apply i j).aestronglyMeasurable A.Λ ?_
    filter_upwards [A.mixed_bound] with x hx
    simpa [PiLp.inner_apply, matMulE_apply, Matrix.mulVec, dotProduct] using
      hx (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  have hcomp : ∀ i : Fin d, MemLp (fun x => F x i) p (volume.restrict Omega) := by
    intro i
    exact hF.of_le
      ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hF.aestronglyMeasurable)
      (Eventually.of_forall fun x => PiLp.norm_apply_le (F x) i)
  refine MemLp.of_eval_piLp ?_
  intro i
  simpa only [matMulE_apply, Matrix.mulVec, dotProduct] using
    memLp_finsetSum Finset.univ (fun j _ => (hcomp j).mul' (p := ⊤) (r := p) (hentry i j))

theorem bilinFormOfCoeff_eq_integral_iff_hasWeakDiv
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega) (hf : MemLp f 2 (volume.restrict Omega)) :
    (∀ v, MemH01 v Omega → ∀ hv : MemW1pWitness 2 v Omega,
      bilinFormOfCoeff A hu hv = ∫ x in Omega, f x * v x) ↔
      HasWeakDiv (fun x => -f x) (fun x => matMulE (A.a x) (hu.weakGrad x)) Omega := by
  constructor
  · intro hweak phi hphi hphi_cpt hphi_sub
    let htest : IsSmoothTestOn Omega phi := ⟨hphi, hphi_cpt, hphi_sub⟩
    have h := hweak phi (smoothTest_memH01 hOmega htest) (smoothTestWitness hOmega htest)
    simpa [bilinFormOfCoeff, bilinFormIntegrandOfCoeff, PiLp.inner_apply,
      smoothTestWitness, smoothGradField, neg_mul, integral_neg, mul_comm] using! h
  · intro hdiv v hv0 hv
    have h := weakProblemRHSOfField_eq_integral hOmega
      (A.memLp_matMulE hu.weakGrad_memLp) hf.neg hdiv hv0
    rw [weakProblemRHSOfField_eq_of_memH01 hOmega hv0 hv] at h
    simpa [divergenceRHSOfField, divergenceRHSIntegrandOfField, bilinFormOfCoeff,
      bilinFormIntegrandOfCoeff, neg_mul, integral_neg] using congrArg Neg.neg h

end DeGiorgi
