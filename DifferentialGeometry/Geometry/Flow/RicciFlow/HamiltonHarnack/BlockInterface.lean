import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.ExactBlockEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.CurvatureBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceHarnackAlgebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.AncientLimit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

variable {Idx : Type*} [Fintype Idx]

def hamiltonBlockQuadratic
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  hamiltonBlockPolarized K P M U U W W

theorem hamiltonBlockQuadratic_eq_hamiltonQuadraticForm
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockQuadratic K P M U W =
      hamiltonQuadraticForm K P M U W := by
  unfold hamiltonBlockQuadratic
  exact hamiltonBlockPolarized_diag K P M U W

theorem hamiltonBlockQuadratic_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real) :
    0 ≤ hamiltonBlockQuadratic
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  unfold hamiltonBlockQuadratic
  exact hamiltonBlockPolarized_diag_nonneg_of_gram Y X U W

def hamiltonBlockPSD
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real) : Prop :=
  ∀ (U : Idx -> Idx -> Real) (W : Idx -> Real),
    0 ≤ hamiltonBlockQuadratic K P M U W

theorem hamiltonBlockPSD_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real) :
    hamiltonBlockPSD
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) := by
  intro U W
  exact hamiltonBlockQuadratic_nonneg_of_gram Y X U W

theorem hamiltonBlockPSD_iff_hamiltonQuadratic_nonneg
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real) :
    hamiltonBlockPSD K P M ↔
      ∀ (U : Idx -> Idx -> Real) (W : Idx -> Real),
        0 ≤ hamiltonQuadraticForm K P M U W := by
  constructor
  · intro h U W
    rw [← hamiltonBlockQuadratic_eq_hamiltonQuadraticForm K P M U W]
    exact h U W
  · intro h U W
    rw [hamiltonBlockQuadratic_eq_hamiltonQuadraticForm K P M U W]
    exact h U W

theorem hamiltonBlockPSD_iff_exists_gram_factorization
    {K : Idx -> Idx -> Idx -> Idx -> Real}
    {P : Idx -> Idx -> Idx -> Real}
    {M : Idx -> Idx -> Real}
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a) :
    hamiltonBlockPSD K P M ↔
      ∃ (m : Nat) (Y : Fin m -> Idx -> Idx -> Real)
          (X : Fin m -> Idx -> Real),
        (∀ r a b, Y r a b = -Y r b a) ∧
        K = hamiltonGramK Y ∧
        P = hamiltonGramP Y X ∧
        M = hamiltonGramM X := by
  constructor
  · intro hPSD
    apply exists_hamiltonGram_factorization K P M hKPair hKSkew hPSkew hMSymm
    intro U W
    rw [← hamiltonBlockQuadratic_eq_hamiltonQuadraticForm K P M U W]
    exact hPSD U W
  · rintro ⟨m, Y, X, hY, rfl, rfl, rfl⟩
    exact hamiltonBlockPSD_of_gram Y X

theorem hamilton_trace_from_quadratic_nonneg
    {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → Real)
    (P : ι → ι → ι → Real)
    (M : ι → ι → Real)
    (v dR : ι → Real)
    (hQ : ∀ (U : ι → ι → Real) (W : ι → Real),
      0 ≤ hamiltonQuadraticForm (fun a b c d => R a b d c) P M U W)
    (hPFirst : ∀ a, (∑ c, P c a c) = -(1 / 2 : Real) * dR a)
    (hPSecond : ∀ a, (∑ c, P a c c) = (1 / 2 : Real) * dR a)
    (hRFirst : ∀ a b c d, R a b c d = -R b a c d)
    (hRLast : ∀ a b c d, R a b c d = -R a b d c)
    (hRPair : ∀ a b c d, R a b c d = R c d a b) :
    0 ≤ (∑ a, M a a) + ∑ a, dR a * v a +
      ∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b := by
  classical
  apply hamilton_trace_from_block_nonneg R P M v dR
  · intro r
    rw [hamiltonBlockPolarized_diag]
    exact hQ (fun a b => hamiltonTraceWedge v r a b)
      (hamiltonTraceWeight r)
  · exact hPFirst
  · exact hPSecond
  · exact hRFirst
  · exact hRLast
  · exact hRPair

def hamiltonBlockExactEvolution
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  hamiltonBlockPreSquare K P M U W

theorem hamiltonBlockPSD_reaction_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockExactEvolution
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  unfold hamiltonBlockExactEvolution
  exact hamiltonBlock_pre_square_nonneg_of_gram Y X U W hY hU

theorem hamiltonBlockJ_eq_gram_reaction
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    hamiltonBlockJ
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W =
      DifferentialGeometry.Analysis.Spectral.hamiltonGramReaction Y X U W := by
  rw [hamiltonBlockJ_eq_reaction_polynomial_of_gram]
  exact (DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_eq_hamiltonReactionPolynomial
    Y X U W hY hU).symm

theorem exists_hamiltonGram_square_factorization_card_le
    {ι : Type*} [Fintype ι]
    (K : ι -> ι -> ι -> ι -> Real)
    (P : ι -> ι -> ι -> Real)
    (M : ι -> ι -> Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hQ : ∀ (U : ι -> ι -> Real) (W : ι -> Real),
      (∀ a b, U a b = -U b a) → 0 ≤ hamiltonQuadraticForm K P M U W) :
    ∃ (m : Nat) (Y : Fin m -> ι -> ι -> Real) (X : Fin m -> ι -> Real),
      m ≤ Fintype.card ι * (Fintype.card ι + 1) / 2 ∧
      (∀ r a b, Y r a b = -Y r b a) ∧
      (∀ (U : ι -> ι -> Real) (W : ι -> Real),
        hamiltonQuadraticForm K P M U W =
          ∑ r, ((∑ a, ∑ b, Y r a b * U a b) + ∑ c, X r c * W c) ^ 2) ∧
      (∀ (U : ι -> ι -> Real) (W : ι -> Real),
        (∀ a b, U a b = -U b a) ->
        hamiltonBlockJ K P M U W =
          ∑ r, ∑ s,
            ((∑ a, ∑ c, Y r a c * X s c * W a) -
              (∑ a, ∑ c, Y s a c * X r c * W a) -
              2 * (∑ a, ∑ b, ∑ c, Y r a c * Y s b c * U a b)) ^ 2) := by
  obtain ⟨m, Y, X, hm, hY, hK, hP, hM⟩ :=
    exists_hamiltonGram_factorization_card_le K P M hKPair hKSkew hPSkew hMSymm hQ
  refine ⟨m, Y, X, hm, hY, ?_, ?_⟩
  · intro U W
    rw [hK, hP, hM, ← hamiltonGram_quadratic_eq_hamiltonQuadraticForm]
    rfl
  · intro U W hU
    rw [hK, hP, hM, hamiltonBlockJ_eq_gram_reaction Y X U W hY hU]
    rfl


theorem exists_hamiltonGram_square_factorization
    {ι : Type*} [Fintype ι]
    (K : ι -> ι -> ι -> ι -> Real)
    (P : ι -> ι -> ι -> Real)
    (M : ι -> ι -> Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hQ : ∀ (U : ι -> ι -> Real) (W : ι -> Real),
      0 ≤ hamiltonQuadraticForm K P M U W) :
    ∃ (m : Nat) (Y : Fin m -> ι -> ι -> Real) (X : Fin m -> ι -> Real),
      (∀ r a b, Y r a b = -Y r b a) ∧
      (∀ (U : ι -> ι -> Real) (W : ι -> Real),
        hamiltonQuadraticForm K P M U W =
          ∑ r, ((∑ a, ∑ b, Y r a b * U a b) + ∑ c, X r c * W c) ^ 2) ∧
      (∀ (U : ι -> ι -> Real) (W : ι -> Real),
        (∀ a b, U a b = -U b a) ->
        hamiltonBlockJ K P M U W =
          ∑ r, ∑ s,
            ((∑ a, ∑ c, Y r a c * X s c * W a) -
              (∑ a, ∑ c, Y s a c * X r c * W a) -
              2 * (∑ a, ∑ b, ∑ c, Y r a c * Y s b c * U a b)) ^ 2) := by
  obtain ⟨m, Y, X, hm, hY, hq, hJ⟩ :=
    exists_hamiltonGram_square_factorization_card_le K P M hKPair hKSkew hPSkew hMSymm
      (fun U W _ => hQ U W)
  exact ⟨m, Y, X, hY, hq, hJ⟩

theorem hamiltonBlockJ_nonneg_of_gram_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a)
    (hzero : hamiltonBlockQuadratic
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W = 0) :
    0 ≤ hamiltonBlockJ
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  rw [hamiltonBlockJ_eq_gram_reaction Y X U W hY hU]
  apply DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg_of_quadratic_eq_zero
    Y X U W
  rw [hamiltonBlockQuadratic_eq_hamiltonQuadraticForm] at hzero
  rw [DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_hamiltonQuadraticForm
    Y X U W]
  exact hzero

theorem hamiltonBlockJ_nonneg_of_psd_quadratic_eq_zero
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hKPair : forall a b c d, K a b c d = K c d a b)
    (hKSkew : forall a b c d, K a b c d = -K b a c d)
    (hPSkew : forall a b c, P a b c = -P b a c)
    (hMSymm : forall a b, M a b = M b a)
    (hPSD : hamiltonBlockPSD K P M)
    (hU : forall a b, U a b = -U b a)
    (hzero : hamiltonBlockQuadratic K P M U W = 0) :
    0 <= hamiltonBlockJ K P M U W := by
  obtain ⟨m, Y, X, hY, hK, hP, hM⟩ :=
    (hamiltonBlockPSD_iff_exists_gram_factorization
      (K := K) (P := P) (M := M) hKPair hKSkew hPSkew hMSymm).mp hPSD
  rw [hK, hP, hM] at hzero ⊢
  exact hamiltonBlockJ_nonneg_of_gram_quadratic_eq_zero
    Y X U W hY hU hzero

theorem hamiltonBlock_exact_evolution_eq_pre_square
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockExactEvolution K P M U W =
      hamiltonBlockPreSquare K P M U W := by
  rfl

theorem hamiltonBlock_exact_evolution_eq_j_add_sigma_square
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonBlockExactEvolution K P M U W =
      hamiltonBlockJ K P M U W + hamiltonBlockSigmaSquare K P U W := by
  unfold hamiltonBlockExactEvolution
  exact hamiltonBlock_pre_square_eq_j_add_sigma_square K P M U W

theorem hamiltonBlockExactEvolution_eq_gram_reaction_add_sigma_square
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    hamiltonBlockExactEvolution
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W =
      DifferentialGeometry.Analysis.Spectral.hamiltonGramReaction Y X U W +
        hamiltonBlockSigmaSquare
          (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
          (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X) U W := by
  rw [hamiltonBlock_exact_evolution_eq_j_add_sigma_square,
    hamiltonBlockJ_eq_gram_reaction Y X U W hY hU]

theorem hamiltonBlock_exact_evolution_nonneg_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (U : ι -> ι -> Real) (W : ι -> Real)
    (hY : ∀ r a b, Y r a b = -Y r b a)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockExactEvolution
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) U W := by
  unfold hamiltonBlockExactEvolution
  exact hamiltonBlock_pre_square_nonneg_of_gram Y X U W hY hU

theorem hamiltonBlock_exact_evolution_nonneg_of_psd
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hPSD : hamiltonBlockPSD K P M)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockExactEvolution K P M U W := by
  obtain ⟨m, Y, X, hY, hK, hP, hM⟩ :=
    (hamiltonBlockPSD_iff_exists_gram_factorization
      (K := K) (P := P) (M := M) hKPair hKSkew hPSkew hMSymm).mp hPSD
  rw [hK, hP, hM]
  exact hamiltonBlock_exact_evolution_nonneg_of_gram Y X U W hY hU

theorem hamiltonBlockJ_add_sigmaSquare_nonneg_of_psd
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hPSD : hamiltonBlockPSD K P M)
    (hU : ∀ a b, U a b = -U b a) :
    0 ≤ hamiltonBlockJ K P M U W + hamiltonBlockSigmaSquare K P U W := by
  rw [← hamiltonBlock_exact_evolution_eq_j_add_sigma_square]
  exact hamiltonBlock_exact_evolution_nonneg_of_psd K P M U W
    hKPair hKSkew hPSkew hMSymm hPSD hU

theorem hamiltonBlockSigma_eq_zero_of_psd_quadratic_eq_zero
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hPSD : hamiltonBlockPSD K P M)
    (hzero : hamiltonBlockQuadratic K P M U W = 0)
    (a b : Idx) :
    hamiltonBlockSigma K P U W a b = 0 := by
  obtain ⟨m, Y, X, hY, hK, hP, hM⟩ :=
    (hamiltonBlockPSD_iff_exists_gram_factorization
      (K := K) (P := P) (M := M) hKPair hKSkew hPSkew hMSymm).mp hPSD
  rw [hK, hP, hM] at hzero
  rw [hK, hP]
  exact hamiltonBlockSigma_eq_zero_of_gram_quadratic_eq_zero
    Y X U W hzero a b

def hamiltonShiftedM
    (clock : HarnackClock) (M Ric : Idx -> Idx -> Real) : Idx -> Idx -> Real :=
  fun a b => M a b + (1 / (2 * clock.elapsed) : Real) * Ric a b

def hamiltonShiftedBlockQuadratic
    (clock : HarnackClock)
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M Ric : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) : Real :=
  hamiltonBlockQuadratic K P (hamiltonShiftedM clock M Ric) U W

theorem hamiltonShiftedBlockQuadratic_expand
    (clock : HarnackClock)
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M Ric : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real) :
    hamiltonShiftedBlockQuadratic clock K P M Ric U W =
      hamiltonBlockQuadratic K P M U W +
        (1 / (2 * clock.elapsed) : Real) *
          (∑ a, ∑ b, Ric a b * W a * W b) := by
  unfold hamiltonShiftedBlockQuadratic hamiltonBlockQuadratic hamiltonShiftedM
    hamiltonBlockPolarized
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  have hscale :
      (∑ a, ∑ b,
          (1 / (2 * clock.elapsed) : Real) * Ric a b * W a * W b) =
        (1 / (2 * clock.elapsed) : Real) *
          (∑ a, ∑ b, Ric a b * W a * W b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hscale]
  ring_nf

theorem hamiltonShiftedBlockQuadratic_nonneg_of_origin
    (clock : HarnackClock)
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M Ric : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hQ : 0 ≤ hamiltonBlockQuadratic K P M U W)
    (hRic : 0 ≤ ∑ a, ∑ b, Ric a b * W a * W b) :
    0 ≤ hamiltonShiftedBlockQuadratic clock K P M Ric U W := by
  rw [hamiltonShiftedBlockQuadratic_expand]
  exact add_nonneg hQ (mul_nonneg (le_of_lt (by
    exact one_div_pos.mpr (mul_pos (by norm_num) clock.elapsed_pos))) hRic)

theorem hamiltonShiftedBlockPSD_of_origin
    (clock : HarnackClock)
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M Ric : Idx -> Idx -> Real)
    (hPSD : hamiltonBlockPSD K P M)
    (hRic : ∀ (W : Idx -> Real), 0 ≤ ∑ a, ∑ b, Ric a b * W a * W b) :
    hamiltonBlockPSD K P (hamiltonShiftedM clock M Ric) := by
  intro U W
  change 0 ≤ hamiltonShiftedBlockQuadratic clock K P M Ric U W
  exact hamiltonShiftedBlockQuadratic_nonneg_of_origin clock K P M Ric U W
    (hPSD U W) (hRic W)

theorem hamiltonBlockQuadratic_nonneg_of_all_shifted
    {q c t : Real}
    (hshift : ∀ α : Real, α < t → 0 ≤ q + c / (2 * (t - α)))
    (hc : 0 ≤ c) :
    0 ≤ q := by
  exact hamilton_ancient_matrix_limit hshift hc

theorem hamiltonBlockQuadratic_nonneg_of_shifted_family
    (t : Real)
    (K : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (M Ric : Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hshift : ∀ (α : Real) (hα : α < t),
      0 ≤ hamiltonShiftedBlockQuadratic
        ⟨α, t, hα⟩ K P M Ric U W)
    (hRic : 0 ≤ ∑ a, ∑ b, Ric a b * W a * W b) :
    0 ≤ hamiltonBlockQuadratic K P M U W := by
  apply hamilton_ancient_matrix_limit (q := hamiltonBlockQuadratic K P M U W)
    (c := ∑ a, ∑ b, Ric a b * W a * W b)
  · intro α hα
    have h := hshift α hα
    rw [hamiltonShiftedBlockQuadratic_expand] at h
    change 0 ≤ hamiltonBlockQuadratic K P M U W +
      (1 / (2 * (t - α)) : Real) *
        (∑ a, ∑ b, Ric a b * W a * W b) at h
    convert h using 1
    all_goals ring
  · exact hRic

theorem hamiltonShiftedBlockPSD_of_gram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (clock : HarnackClock)
    (Y : κ -> ι -> ι -> Real) (X : κ -> ι -> Real)
    (Ric : ι -> ι -> Real)
    (hRic : ∀ (W : ι -> Real), 0 ≤ ∑ a, ∑ b, Ric a b * W a * W b) :
    hamiltonBlockPSD
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
      (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
      (hamiltonShiftedM clock
        (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) Ric) := by
  exact hamiltonShiftedBlockPSD_of_origin clock
    (DifferentialGeometry.Analysis.Spectral.hamiltonGramK Y)
    (DifferentialGeometry.Analysis.Spectral.hamiltonGramP Y X)
    (DifferentialGeometry.Analysis.Spectral.hamiltonGramM X) Ric
    (hamiltonBlockPSD_of_gram Y X) hRic

theorem hamiltonBlockPSD_of_shifted_family
    {ι : Type*} [Fintype ι]
    (t : Real)
    (K : ι -> ι -> ι -> ι -> Real)
    (P : ι -> ι -> ι -> Real)
    (M Ric : ι -> ι -> Real)
    (hshift : ∀ (α : Real) (hα : α < t),
      hamiltonBlockPSD K P (hamiltonShiftedM ⟨α, t, hα⟩ M Ric))
    (hRic : ∀ (W : ι -> Real), 0 ≤ ∑ a, ∑ b, Ric a b * W a * W b) :
    hamiltonBlockPSD K P M := by
  intro U W
  exact hamiltonBlockQuadratic_nonneg_of_shifted_family t K P M Ric
    U W (fun α hα => hshift α hα U W) (hRic W)

theorem hamilton_trace_from_shifted_quadratic_nonneg
    {ι : Type*} [Fintype ι]
    (t : Real)
    (R : ι -> ι -> ι -> ι -> Real)
    (P : ι -> ι -> ι -> Real)
    (M Ric : ι -> ι -> Real)
    (v dR : ι -> Real)
    (hshift : ∀ (α : Real) (hα : α < t)
      (U : ι -> ι -> Real) (W : ι -> Real),
      0 ≤ hamiltonShiftedBlockQuadratic
        ⟨α, t, hα⟩ (fun a b c d => R a b d c) P M Ric U W)
    (hRic : ∀ (W : ι -> Real), 0 ≤ ∑ a, ∑ b, Ric a b * W a * W b)
    (hPFirst : ∀ a, (∑ c, P c a c) = -(1 / 2 : Real) * dR a)
    (hPSecond : ∀ a, (∑ c, P a c c) = (1 / 2 : Real) * dR a)
    (hRFirst : ∀ a b c d, R a b c d = -R b a c d)
    (hRLast : ∀ a b c d, R a b c d = -R a b d c)
    (hRPair : ∀ a b c d, R a b c d = R c d a b) :
    0 ≤ (∑ a, M a a) + ∑ a, dR a * v a +
      ∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b := by
  apply hamilton_trace_from_quadratic_nonneg R P M v dR
  · intro U W
    rw [← hamiltonBlockQuadratic_eq_hamiltonQuadraticForm
      (fun a b c d => R a b d c) P M U W]
    exact hamiltonBlockQuadratic_nonneg_of_shifted_family t
      (fun a b c d => R a b d c) P M Ric U W
      (fun α hα => hshift α hα U W) (hRic W)
  · exact hPFirst
  · exact hPSecond
  · exact hRFirst
  · exact hRLast
  · exact hRPair

theorem hamilton_trace_from_shifted_PSD
    {ι : Type*} [Fintype ι]
    (t : Real)
    (R : ι -> ι -> ι -> ι -> Real)
    (P : ι -> ι -> ι -> Real)
    (M Ric : ι -> ι -> Real)
    (v dR : ι -> Real)
    (hshift : ∀ (α : Real) (hα : α < t),
      hamiltonBlockPSD (fun a b c d => R a b d c) P
        (hamiltonShiftedM ⟨α, t, hα⟩ M Ric))
    (hRic : ∀ (W : ι -> Real), 0 ≤ ∑ a, ∑ b, Ric a b * W a * W b)
    (hPFirst : ∀ a, (∑ c, P c a c) = -(1 / 2 : Real) * dR a)
    (hPSecond : ∀ a, (∑ c, P a c c) = (1 / 2 : Real) * dR a)
    (hRFirst : ∀ a b c d, R a b c d = -R b a c d)
    (hRLast : ∀ a b c d, R a b c d = -R a b d c)
    (hRPair : ∀ a b c d, R a b c d = R c d a b) :
    0 ≤ (∑ a, M a a) + ∑ a, dR a * v a +
      ∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b := by
  apply hamilton_trace_from_shifted_quadratic_nonneg t R P M Ric v dR
  · intro α hα U W
    exact hshift α hα U W
  · exact hRic
  · exact hPFirst
  · exact hPSecond
  · exact hRFirst
  · exact hRLast
  · exact hRPair

def hamiltonCoordinateCurvature
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {x : M}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b c d : Idx) : Real :=
  tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
    (basis a) (basis b) (basis d) (basis c)

def hamiltonCoordinateTwoForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (a b : Idx) : Real :=
  U (vec2 (I := I) (basis a) (basis b))

private theorem sum_fin_three_fun {A : Type*} [Fintype A]
    {B : Type*} [AddCommMonoid B] (F : (Fin 3 -> A) -> B) :
    (∑ slots : Fin 3 -> A, F slots) =
      ∑ a, ∑ b, ∑ c, F ![a, b, c] := by
  rw [Tensor0SBundle.sum_fin_succ_fun 2]
  apply Finset.sum_congr rfl
  intro a _
  rw [Tensor0SBundle.sum_fin_succ_fun 1]
  apply Finset.sum_congr rfl
  intro b _
  rw [Tensor0SBundle.sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem sum_fin_two_fun {A : Type*} [Fintype A]
    {B : Type*} [AddCommMonoid B] (F : (Fin 2 -> A) -> B) :
    (∑ slots : Fin 2 -> A, F slots) =
      ∑ a, ∑ b, F ![a, b] := by
  rw [Tensor0SBundle.sum_fin_succ_fun 1]
  apply Finset.sum_congr rfl
  intro a _
  rw [Tensor0SBundle.sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem sum_fin_four_fun {A : Type*} [Fintype A]
    {B : Type*} [AddCommMonoid B] (F : (Fin 4 -> A) -> B) :
    (∑ slots : Fin 4 -> A, F slots) =
      ∑ a, ∑ b, ∑ c, ∑ d, F ![a, b, c, d] := by
  rw [Tensor0SBundle.sum_fin_succ_fun 3]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_fin_three_fun]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rfl

theorem hamiltonQuadraticAt_eq_hamiltonBlockQuadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {A : Type*} [Fintype A] [DecidableEq A]
    {x : M} (g : SmoothRiemannianMetric I M)
    (R : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (P : Tensor0SSpace 3 I x) (Mbar : Tensor0SSpace 2 I x)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x)
    (basis : Module.Basis A Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := A))) :
    hamiltonQuadraticAt g R P Mbar U W =
      hamiltonBlockQuadratic
        (fun a b c d => tensor04StdAt (I := I) (M := M)
          (R : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis d) (basis c))
        (fun a b c => P ![basis a, basis b, basis c])
        (fun a b => Mbar ![basis a, basis b])
        (fun a b => U ![basis a, basis b])
        (fun a => W ![basis a]) := by
  rw [hamiltonQuadraticAt, curvatureBlock_eq_sum g R U U basis hinv,
    Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 3 basis hinv,
    Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 2 basis hinv]
  rw [sum_fin_four_fun]
  rw [hamiltonBlockQuadratic_eq_hamiltonQuadraticForm]
  unfold hamiltonQuadraticForm
  simp only [component0S_apply]
  rw [sum_fin_three_fun, sum_fin_two_fun]
  have hPprod (a b c : A) :
      (U.toTensor0S.product W) (fun i => basis (![a, b, c] i)) =
        U ![basis a, basis b] * W ![basis c] := by
    rw [Tensor0SSpace.product_apply,
      HamiltonHarnackTwoForm.toTensor0S_apply]
    congr 1
    · congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i
      rfl
  have hMprod (a b : A) :
      (W.product W) (fun i => basis (![a, b] i)) =
        W ![basis a] * W ![basis b] := by
    rw [Tensor0SSpace.product_apply]
    congr 1
    · congr 1
      funext i
      fin_cases i
      rfl
    · congr 1
      funext i
      fin_cases i
      rfl
  have hvec2 (a b : A) :
      (fun i => basis (![a, b] i)) = ![basis a, basis b] := by
    funext i
    fin_cases i <;> rfl
  have hvec3 (a b c : A) :
      (fun i => basis (![a, b, c] i)) = ![basis a, basis b, basis c] := by
    funext i
    fin_cases i <;> rfl
  have hvec2' (a b : A) :
      vec2 (I := I) (basis a) (basis b) = ![basis a, basis b] := by
    funext i
    fin_cases i <;> simp [vec2]
  simp_rw [hPprod, hMprod]
  simp_rw [hvec2, hvec3, hvec2']
  simp
  simp only [mul_assoc]

theorem curvatureBlock_eq_hamiltonCoordinate_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {x : M} [DecidableEq Idx] (g : SmoothRiemannianMetric I M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (U V : HamiltonHarnackTwoForm (TangentSpace I x))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Idx))) :
    curvatureBlock g A U V =
      ∑ slots : Fin 4 → Idx,
        hamiltonCoordinateCurvature A basis (slots 0) (slots 1)
            (slots 2) (slots 3) *
          (hamiltonCoordinateTwoForm basis U (slots 0) (slots 1) *
            hamiltonCoordinateTwoForm basis V (slots 2) (slots 3)) := by
  exact curvatureBlock_eq_sum g A U V basis hinv

end DifferentialGeometry.PDE.RicciFlow
