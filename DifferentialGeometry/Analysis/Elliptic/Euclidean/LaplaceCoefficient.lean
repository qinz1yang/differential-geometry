import DifferentialGeometry.External.DeGiorgi.WeakFormulation.BilinearForm

noncomputable section
open Set Filter MeasureTheory
open scoped RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem matMulE_one (v : V) : matMulE 1 v = v := by
  ext i
  simp only [matMulE_apply, Matrix.one_mulVec]

def EllipticCoeff.identity (d : ℕ) [NeZero d] (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    EllipticCoeff d Ω where
  a := fun _ => 1
  lam := 1
  Λ := 1
  measurable_comp := fun _ _ => measurable_const
  hlam := zero_lt_one
  hΛ := le_rfl
  coercive := Eventually.of_forall fun _ v => by
    rw [one_mul, matMulE_one, real_inner_self_eq_norm_sq]
  coercive_inv := Eventually.of_forall fun _ v => by
    rw [inv_one, one_mul, inv_one, matMulE_one, real_inner_self_eq_norm_sq]

theorem EllipticCoeff.identity_a [NeZero d] (Ω : Set V) (x : V) :
    (EllipticCoeff.identity d Ω).a x = 1 := rfl

theorem EllipticCoeff.identity_lam [NeZero d] (Ω : Set V) :
    (EllipticCoeff.identity d Ω).lam = 1 := rfl

theorem EllipticCoeff.identity_Λ [NeZero d] (Ω : Set V) :
    (EllipticCoeff.identity d Ω).Λ = 1 := rfl

theorem bilinFormOfCoeff_identity [NeZero d] {Ω : Set V} {u v : V → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) :
    bilinFormOfCoeff (EllipticCoeff.identity d Ω) hu hv =
      ∫ x in Ω, inner ℝ (hu.weakGrad x) (hv.weakGrad x) := by
  simp only [bilinFormOfCoeff, bilinFormIntegrandOfCoeff, EllipticCoeff.identity, matMulE_one]

end DeGiorgi

end
