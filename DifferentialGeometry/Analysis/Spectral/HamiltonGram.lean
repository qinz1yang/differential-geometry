import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open scoped BigOperators RealInnerProductSpace

theorem exists_finite_gram_factorization
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (T : V →L[Real] V)
    (hT : T.IsPositive) :
    ∃ (m : Nat) (v : Fin m → V),
      T = ∑ i, InnerProductSpace.rankOne Real (v i) (v i) := by
  exact (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hT

theorem finite_gram_factorization_quadratic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (T : V →L[Real] V)
    (hT : T.IsPositive) :
    ∃ (m : Nat) (v : Fin m → V), ∀ z : V,
      inner Real (T z) z = ∑ i, (inner Real (v i) z) ^ 2 := by
  obtain ⟨m, v, hv⟩ := exists_finite_gram_factorization T hT
  refine ⟨m, v, ?_⟩
  intro z
  rw [hv]
  simp only [sum_apply, InnerProductSpace.rankOne_apply, sum_inner]
  simp_rw [real_inner_smul_left]
  ring_nf

def hamiltonGramK {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (a b c d : ι) : Real :=
  ∑ r, Y r a b * Y r c d

def hamiltonGramP {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real) (a b c : ι) : Real :=
  ∑ r, Y r a b * X r c

def hamiltonGramM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : κ → ι → Real) (a b : ι) : Real :=
  ∑ r, X r a * X r b

def hamiltonGramLinearTerm {ι κ : Type*} [Fintype ι]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) (r : κ) : Real :=
  (∑ a, ∑ b, Y r a b * U a b) + ∑ c, X r c * W c

def hamiltonGramQuadratic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) : Real :=
  ∑ r, (hamiltonGramLinearTerm Y X U W r) ^ 2

def hamiltonGramReaction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) : Real :=
  ∑ r, ∑ s,
    ((∑ a, ∑ c, Y r a c * X s c * W a) -
      (∑ a, ∑ c, Y s a c * X r c * W a) -
      2 * (∑ a, ∑ b, ∑ c, Y r a c * Y s b c * U a b)) ^ 2

def hamiltonGramSigma {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) (a b : ι) : Real :=
  ∑ r, Y r a b * hamiltonGramLinearTerm Y X U W r

theorem hamiltonGram_quadratic_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramQuadratic Y X U W := by
  unfold hamiltonGramQuadratic
  exact Finset.sum_nonneg fun r _ => sq_nonneg _

theorem hamiltonGram_reaction_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramReaction Y X U W := by
  unfold hamiltonGramReaction
  exact Finset.sum_nonneg fun r _ =>
    Finset.sum_nonneg fun s _ => sq_nonneg _

theorem hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hzero : hamiltonGramQuadratic Y X U W = 0) (a b : ι) :
    hamiltonGramSigma Y X U W a b = 0 := by
  have hterm : ∀ r : κ, hamiltonGramLinearTerm Y X U W r = 0 := by
    intro r
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s _ => sq_nonneg (hamiltonGramLinearTerm Y X U W s))).mp hzero
    exact (sq_eq_zero_iff.mp (hterms r (Finset.mem_univ r)))
  unfold hamiltonGramSigma
  simp [hterm]

end DifferentialGeometry.Analysis.Spectral
