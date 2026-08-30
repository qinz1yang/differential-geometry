import DifferentialGeometry.Analysis.Spectral.HamiltonGram

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators
open DifferentialGeometry.Analysis.Spectral

variable {Idx : Type*} [Fintype Idx]

def hamiltonBlockPolarized
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U V : Idx -> Idx -> Real) (W Z : Idx -> Real) : Real :=
  (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * V c d) +
    ∑ a, ∑ b, ∑ c, P a b c * (U a b * Z c + V a b * W c) +
    ∑ a, ∑ b, M a b * W a * Z b

def hamiltonBlockSigma
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b : Idx) : Real :=
  ∑ c, P a b c * W c + ∑ c, ∑ d, K a b c d * U c d

theorem hamiltonBlockPolarized_diag
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockPolarized K P M U U W W =
      hamiltonQuadraticForm K P M U W := by
  unfold hamiltonBlockPolarized hamiltonQuadraticForm
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf

end DifferentialGeometry.PDE.RicciFlow
