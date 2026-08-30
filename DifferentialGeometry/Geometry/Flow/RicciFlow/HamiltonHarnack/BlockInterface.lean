import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockReaction
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
    [IsManifold I ∞ M]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (a b : Idx) : Real :=
  U (vec2 (I := I) (basis a) (basis b))

theorem curvatureBlock_eq_hamiltonCoordinate_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    [IsManifold I 1 M]
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
