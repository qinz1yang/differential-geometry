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

def hamiltonBlockTrace
    (gInv : Idx -> Idx -> Real) (M : Idx -> Idx -> Real) : Real :=
  ∑ a, ∑ b, gInv a b * M a b

theorem hamiltonBlockTrace_shift
    (gInv M Ric : Idx -> Idx -> Real) (c : Real) :
    hamiltonBlockTrace gInv (fun a b => M a b + c * Ric a b) =
      hamiltonBlockTrace gInv M + c * hamiltonBlockTrace gInv Ric := by
  unfold hamiltonBlockTrace
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

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

theorem hamiltonGramSigma_eq_hamiltonBlockSigma
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real) (a b : ι) :
    DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma Y X U W a b =
      hamiltonBlockSigma
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X) U W a b := by
  unfold hamiltonBlockSigma
  exact DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma_eq_block
    Y X U W a b

theorem hamiltonBlockPolarized_diag_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real) :
    0 ≤ hamiltonBlockPolarized
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U U W W := by
  rw [hamiltonBlockPolarized_diag,
    ← DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_hamiltonQuadraticForm
      Y X U W]
  exact DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_nonneg Y X U W

end DifferentialGeometry.PDE.RicciFlow
