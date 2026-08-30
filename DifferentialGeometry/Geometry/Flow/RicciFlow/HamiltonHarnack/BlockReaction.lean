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

end DifferentialGeometry.PDE.RicciFlow
