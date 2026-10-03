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

private theorem hamiltonBlock_sum_swap_four
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ b, ∑ a, ∑ c, ∑ d, F a b c d := by rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, ∑ d, F a b c d := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ d, ∑ a, F a b c d := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ b, ∑ d, ∑ a, F a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_comm]

theorem hamiltonBlockPolarized_comm
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (hK : ∀ a b c d, K a b c d = K c d a b)
    (hM : ∀ a b, M a b = M b a)
    (U V : Idx -> Idx -> Real) (W Z : Idx -> Real) :
    hamiltonBlockPolarized K P M U V W Z =
      hamiltonBlockPolarized K P M V U Z W := by
  unfold hamiltonBlockPolarized
  have hKsum :
      (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * V c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, K a b c d * V a b * U c d := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * V c d) =
          ∑ c, ∑ d, ∑ a, ∑ b, K a b c d * U a b * V c d :=
        hamiltonBlock_sum_swap_four _
      _ = ∑ c, ∑ d, ∑ a, ∑ b, K c d a b * V c d * U a b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hK c d a b]
        ring
      _ = ∑ a, ∑ b, ∑ c, ∑ d, K a b c d * V a b * U c d := by
        rw [hamiltonBlock_sum_swap_four]
  have hMsum :
      (∑ a, ∑ b, M a b * W a * Z b) =
        ∑ a, ∑ b, M a b * Z a * W b := by
    calc
      (∑ a, ∑ b, M a b * W a * Z b) =
          ∑ b, ∑ a, M a b * W a * Z b := Finset.sum_comm
      _ = ∑ b, ∑ a, M b a * Z b * W a := by
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hM b a]
        ring
      _ = ∑ a, ∑ b, M a b * Z a * W b := by rw [Finset.sum_comm]
  have hPsum :
      (∑ a, ∑ b, ∑ c, P a b c * (U a b * Z c + V a b * W c)) =
        ∑ a, ∑ b, ∑ c, P a b c * (V a b * W c + U a b * Z c) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [add_comm]
  rw [hKsum, hMsum, hPsum]

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

theorem hamiltonBlockSigma_eq_zero_of_gram_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hzero : hamiltonBlockPolarized
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U U W W = 0)
    (a b : ι) :
    hamiltonBlockSigma
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X) U W a b = 0 := by
  rw [← hamiltonGramSigma_eq_hamiltonBlockSigma Y X U W a b]
  apply DifferentialGeometry.Analysis.Spectral.hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero
    Y X U W
  have hblock :
      hamiltonQuadraticForm
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W = 0 := by
    rw [← hamiltonBlockPolarized_diag]
    exact hzero
  rw [← DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_hamiltonQuadraticForm
    Y X U W] at hblock
  exact hblock

end DifferentialGeometry.PDE.RicciFlow
