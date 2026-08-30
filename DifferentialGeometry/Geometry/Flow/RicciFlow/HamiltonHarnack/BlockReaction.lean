import DifferentialGeometry.Analysis.Spectral.HamiltonGramReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockEvolution

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx]

def hamiltonBlockJ
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  2 * (∑ a, ∑ b, ∑ c, ∑ d,
    K a c b d * M c d * W a * W b) -
  2 * (∑ a, ∑ b, ∑ c, ∑ d,
    P a c d * P b d c * W a * W b) +
  8 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    K a d c e * P d b e * U a b * W c) +
  4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    K a e c f * K b e d f * U a b * U c d)

def hamiltonBlockPreSquare
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  hamiltonBlockJ K P M U W +
    hamiltonBlockSigmaSquareExpanded K P U W

theorem hamiltonBlock_pre_square_eq_j_add_sigma_square
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockPreSquare K P M U W =
      hamiltonBlockJ K P M U W + hamiltonBlockSigmaSquare K P U W := by
  unfold hamiltonBlockPreSquare
  rw [hamiltonBlock_sigma_square_expand]

theorem hamiltonBlockJ_eq_reaction_polynomial_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real) :
    hamiltonBlockJ
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W =
      DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  rfl

theorem hamiltonBlockJ_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockJ
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  rw [hamiltonBlockJ_eq_reaction_polynomial_of_gram]
  exact DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial_nonneg_of_gram
    Y X U W hY hU

theorem hamiltonBlock_pre_square_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockPreSquare
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  rw [hamiltonBlock_pre_square_eq_j_add_sigma_square]
  exact add_nonneg
    (hamiltonBlockJ_nonneg_of_gram Y X U W hY hU)
    (by
      unfold hamiltonBlockSigmaSquare
      exact Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => sq_nonneg _)

end DifferentialGeometry.PDE.RicciFlow
