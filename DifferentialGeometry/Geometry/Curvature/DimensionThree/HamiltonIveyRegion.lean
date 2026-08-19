import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import DifferentialGeometry.Analysis.Convex.MatrixRayleigh
import DifferentialGeometry.Analysis.InnerProductSpace.MatrixEuclidean
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open scoped BigOperators Matrix.Norms.Frobenius

def sectionalSum3 (l1 l2 l3 : Real) : Real :=
  l1 + l2 + l3

def pinchHeight3 (l3 : Real) : Real :=
  max (-l3) 0

def hamiltonIveyBarrier (K τ X : Real) : Real :=
  X * (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 3)

def hamiltonIveyEpigraph (K τ : Real) : Set (Real × Real) :=
  {p | 0 ≤ p.1 ∧ hamiltonIveyBarrier K τ p.1 ≤ p.2}

def scalarSectionalLowerBarrier3 (K τ : Real) : Real :=
  -3 * K / (1 + 4 * K * τ)

def hamiltonIveyConvexBarrier (K τ X : Real) : Real :=
  max (scalarSectionalLowerBarrier3 K τ) (hamiltonIveyBarrier K τ X)

def hamiltonIveyConvexEpigraph (K τ : Real) : Set (Real × Real) :=
  {p | 0 ≤ p.1 ∧ hamiltonIveyConvexBarrier K τ p.1 ≤ p.2}

def hamiltonIveyConvexMatrixRegion (K τ : Real) : Set (Matrix (Fin 3) (Fin 3) Real) :=
  {A | A.IsHermitian ∧
    hamiltonIveyConvexBarrier K τ
      (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0) ≤ A.trace}

theorem nonempty_hamiltonIveyConvexMatrixRegion
    {K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) :
    (hamiltonIveyConvexMatrixRegion K τ).Nonempty := by
  refine ⟨0, ?_⟩
  have hden : 0 < 1 + 4 * K * τ := by
    nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : Real) < 4) hK).le hτ]
  have hscalar : scalarSectionalLowerBarrier3 K τ ≤ 0 := by
    unfold scalarSectionalLowerBarrier3
    have hnonpos : -(3 * K) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (by norm_num : (0 : Real) ≤ 3) (le_of_lt hK))
    have hdiv := div_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hden)
    simpa using hdiv
  refine ⟨by simp, ?_⟩
  · unfold hamiltonIveyConvexBarrier
    have hbar : hamiltonIveyBarrier K τ
        (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 0) 0) ≤ 0 := by
      rw [DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_zero]
      simp [hamiltonIveyBarrier]
    simpa using (max_le (by simpa using hscalar) hbar)

private theorem hamiltonIveyConvexMatrixRegion_conj_mem
    {K τ : Real} {A Q : Matrix (Fin 3) (Fin 3) Real}
    (hQ2 : Q * Q.transpose = 1)
    (hA : A ∈ hamiltonIveyConvexMatrixRegion K τ) :
    Q.transpose * A * Q ∈ hamiltonIveyConvexMatrixRegion K τ := by
  rcases hA with ⟨hAh, hbar⟩
  refine ⟨?_, ?_⟩
  · have hconj : (Q.conjTranspose * A * Q).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul Q hAh
    simpa using hconj
  · have htrace : (Q.transpose * A * Q).trace = A.trace := by
      have hcyc := Matrix.trace_mul_cycle Q.transpose A Q
      rw [hQ2] at hcyc
      simpa [Matrix.one_mul] using hcyc
    have hB : (Q.transpose * A * Q).IsHermitian := by
      have hconj : (Q.conjTranspose * A * Q).IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul Q hAh
      simpa using hconj
    have hchar : (Q.transpose * A * Q).charpoly = A.charpoly := by
      have hmul := Matrix.charpoly_mul_comm Q.transpose (A * Q)
      rw [show Q.transpose * (A * Q) = Q.transpose * A * Q by simp [Matrix.mul_assoc]] at hmul
      rw [hmul]
      rw [show (A * Q) * Q.transpose = A * (Q * Q.transpose) by simp [Matrix.mul_assoc]]
      rw [hQ2, Matrix.mul_one]
    have heig := eigenvalues₀_eq_of_charpoly_eq_real hB hAh hchar
    rw [DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue hB,
      htrace, heig,
      ← DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue hAh]
    exact hbar

theorem hamiltonIveyConvexMatrixRegion_orthogonal_conj
    {K τ : Real} {A Q : Matrix (Fin 3) (Fin 3) Real}
    (hQ1 : Q.transpose * Q = 1) (hQ2 : Q * Q.transpose = 1) :
    A ∈ hamiltonIveyConvexMatrixRegion K τ ↔
      Q.transpose * A * Q ∈ hamiltonIveyConvexMatrixRegion K τ := by
  constructor
  · exact hamiltonIveyConvexMatrixRegion_conj_mem (K := K) (τ := τ) hQ2
  · intro hB
    have hQ2T : Q.transpose * Q.transpose.transpose = 1 := by
      simpa using hQ1
    have hconj := hamiltonIveyConvexMatrixRegion_conj_mem
      (K := K) (τ := τ) (A := Q.transpose * A * Q) (Q := Q.transpose) hQ2T hB
    have hmat : Q * (Q.transpose * A * Q) * Q.transpose = A := by
      rw [show Q * (Q.transpose * A * Q) * Q.transpose =
          ((Q * Q.transpose) * A) * (Q * Q.transpose) by
        repeat rw [Matrix.mul_assoc]]
      rw [hQ2]
      simp only [Matrix.one_mul, Matrix.mul_one]
    simpa [Matrix.transpose_transpose, hmat] using hconj


theorem hamiltonIveyBarrier_eq_mul_log_add_linear
    {K τ X : Real} (hK : 0 < K) :
    hamiltonIveyBarrier K τ X =
      X * Real.log X +
        X * (Real.log (1 + 2 * K * τ) - 3 - Real.log K) := by
  unfold hamiltonIveyBarrier
  by_cases hX : X = 0
  · subst hX
    simp
  · rw [Real.log_div hX hK.ne']
    ring

theorem continuous_hamiltonIveyBarrier
    {K τ : Real} (hK : 0 < K) :
    Continuous (fun X : Real => hamiltonIveyBarrier K τ X) := by
  have hfun : (fun X : Real => hamiltonIveyBarrier K τ X) =
      fun X : Real => X * Real.log X +
        X * (Real.log (1 + 2 * K * τ) - 3 - Real.log K) := by
    funext X
    exact hamiltonIveyBarrier_eq_mul_log_add_linear (K := K) (τ := τ) (X := X) hK
  rw [hfun]
  exact Real.continuous_mul_log.add (continuous_id.mul continuous_const)

theorem hamiltonIveyBarrier_convexOn
    {K τ : Real} (hK : 0 < K) :
    ConvexOn Real (Set.Ici (0 : Real)) (fun X : Real => hamiltonIveyBarrier K τ X) := by
  let c : Real := Real.log (1 + 2 * K * τ) - 3 - Real.log K
  have hmul : ConvexOn Real (Set.Ici (0 : Real)) (fun X : Real => X * Real.log X) :=
    Real.convexOn_mul_log
  have hlin : ConvexOn Real (Set.Ici (0 : Real)) (fun X : Real => X * c) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp [smul_eq_mul, add_mul, mul_assoc, mul_left_comm, mul_comm]
  have hsum : ConvexOn Real (Set.Ici (0 : Real))
      (fun X : Real => X * Real.log X + X * c) :=
    hmul.add hlin
  refine hsum.congr ?_
  intro x hx
  exact (hamiltonIveyBarrier_eq_mul_log_add_linear (K := K) (τ := τ) (X := x) hK).symm

theorem convex_hamiltonIveyEpigraph
    {K τ : Real} (hK : 0 < K) :
    Convex Real (hamiltonIveyEpigraph K τ) := by
  rw [convex_iff_forall_pos]
  intro p hp q hq a b ha hb hab
  have hconv := (hamiltonIveyBarrier_convexOn (K := K) (τ := τ) hK).2
  have hxnonneg : 0 ≤ a * p.1 + b * q.1 := by
    nlinarith [mul_nonneg ha.le hp.1, mul_nonneg hb.le hq.1]
  have hbar :
      hamiltonIveyBarrier K τ (a * p.1 + b * q.1) ≤
        a * (hamiltonIveyBarrier K τ p.1) + b * (hamiltonIveyBarrier K τ q.1) := by
    simpa using hconv hp.1 hq.1 ha.le hb.le hab
  have hy : a * hamiltonIveyBarrier K τ p.1 + b * hamiltonIveyBarrier K τ q.1 ≤
      a * p.2 + b * q.2 := by
    nlinarith [mul_le_mul_of_nonneg_left hp.2 ha.le, mul_le_mul_of_nonneg_left hq.2 hb.le]
  exact ⟨hxnonneg, hbar.trans hy⟩

theorem isClosed_hamiltonIveyEpigraph
    {K τ : Real} (hK : 0 < K) :
    IsClosed (hamiltonIveyEpigraph K τ) := by
  have hbar_cont : Continuous (fun p : Real × Real => hamiltonIveyBarrier K τ p.1) := by
    exact (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).comp continuous_fst
  have hmain : IsClosed {p : Real × Real | hamiltonIveyBarrier K τ p.1 ≤ p.2} :=
    isClosed_le hbar_cont continuous_snd
  have hnonneg : IsClosed {p : Real × Real | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hset : hamiltonIveyEpigraph K τ =
      {p : Real × Real | hamiltonIveyBarrier K τ p.1 ≤ p.2} ∩
        {p : Real × Real | 0 ≤ p.1} := by
    ext p
    simp [hamiltonIveyEpigraph, and_comm]
  rw [hset]
  exact hmain.inter hnonneg

theorem hamiltonIveyBarrier_le_hamiltonIveyConvexBarrier (K τ X : Real) :
    hamiltonIveyBarrier K τ X ≤ hamiltonIveyConvexBarrier K τ X := by
  unfold hamiltonIveyConvexBarrier
  exact le_max_right _ _

theorem scalarSectionalLowerBarrier3_le_hamiltonIveyConvexBarrier (K τ X : Real) :
    scalarSectionalLowerBarrier3 K τ ≤ hamiltonIveyConvexBarrier K τ X := by
  unfold hamiltonIveyConvexBarrier
  exact le_max_left _ _

theorem continuous_hamiltonIveyConvexBarrier
    {K τ : Real} (hK : 0 < K) :
    Continuous (fun X : Real => hamiltonIveyConvexBarrier K τ X) := by
  unfold hamiltonIveyConvexBarrier
  exact (continuous_const.max (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK))

theorem isClosed_hamiltonIveyConvexMatrixRegion
    {K τ : Real} (hK : 0 < K) :
    IsClosed (hamiltonIveyConvexMatrixRegion K τ) := by
  rw [hamiltonIveyConvexMatrixRegion]
  let X : Matrix (Fin 3) (Fin 3) Real → Real := fun A =>
    max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0
  have hXcont : Continuous X := by
    dsimp [X]
    exact DifferentialGeometry.Analysis.Convex.continuous_minimumRayleighQuotient3.neg.max
      continuous_const
  have hbarcont : Continuous (fun A : Matrix (Fin 3) (Fin 3) Real =>
      hamiltonIveyConvexBarrier K τ (X A) - A.trace) := by
    have ht : Continuous (fun A : Matrix (Fin 3) (Fin 3) Real => A.trace) := by
      unfold Matrix.trace
      fun_prop
    exact ((continuous_hamiltonIveyConvexBarrier hK).comp hXcont).sub ht
  have hHermClosed : IsClosed {A : Matrix (Fin 3) (Fin 3) Real | A.IsHermitian} := by
    have hset : {A : Matrix (Fin 3) (Fin 3) Real | A.IsHermitian} =
        {A : Matrix (Fin 3) (Fin 3) Real | A.transpose = A} := by
      ext B
      simp [Matrix.IsHermitian]
    rw [hset]
    have htrans : Continuous (fun A : Matrix (Fin 3) (Fin 3) Real => A.transpose) := by
      fun_prop
    exact isClosed_eq htrans continuous_id
  change IsClosed ({A : Matrix (Fin 3) (Fin 3) Real | A.IsHermitian} ∩
    {A : Matrix (Fin 3) (Fin 3) Real |
      hamiltonIveyConvexBarrier K τ (X A) ≤ A.trace})
  have hsecond : IsClosed {A : Matrix (Fin 3) (Fin 3) Real |
      hamiltonIveyConvexBarrier K τ (X A) ≤ A.trace} :=
    isClosed_le ((continuous_hamiltonIveyConvexBarrier hK).comp hXcont)
      (by unfold Matrix.trace; fun_prop)
  exact hHermClosed.inter hsecond



theorem hamiltonIveyConvexBarrier_convexOn
    {K τ : Real} (hK : 0 < K) :
    ConvexOn Real (Set.Ici (0 : Real))
      (fun X : Real => hamiltonIveyConvexBarrier K τ X) := by
  unfold hamiltonIveyConvexBarrier
  exact (convexOn_const _ (convex_Ici 0)).sup
    (hamiltonIveyBarrier_convexOn (K := K) (τ := τ) hK)

theorem convex_hamiltonIveyConvexEpigraph
    {K τ : Real} (hK : 0 < K) :
    Convex Real (hamiltonIveyConvexEpigraph K τ) := by
  rw [convex_iff_forall_pos]
  intro p hp q hq a b ha hb hab
  have hconv := (hamiltonIveyConvexBarrier_convexOn (K := K) (τ := τ) hK).2
  have hxnonneg : 0 ≤ a * p.1 + b * q.1 := by
    nlinarith [mul_nonneg ha.le hp.1, mul_nonneg hb.le hq.1]
  have hbar :
      hamiltonIveyConvexBarrier K τ (a * p.1 + b * q.1) ≤
        a * (hamiltonIveyConvexBarrier K τ p.1) + b * (hamiltonIveyConvexBarrier K τ q.1) := by
    simpa using hconv hp.1 hq.1 ha.le hb.le hab
  have hy : a * hamiltonIveyConvexBarrier K τ p.1 + b * hamiltonIveyConvexBarrier K τ q.1 ≤
      a * p.2 + b * q.2 := by
    nlinarith [mul_le_mul_of_nonneg_left hp.2 ha.le, mul_le_mul_of_nonneg_left hq.2 hb.le]
  exact ⟨hxnonneg, hbar.trans hy⟩

theorem isClosed_hamiltonIveyConvexEpigraph
    {K τ : Real} (hK : 0 < K) :
    IsClosed (hamiltonIveyConvexEpigraph K τ) := by
  have hbar_cont : Continuous (fun p : Real × Real =>
      hamiltonIveyConvexBarrier K τ p.1) := by
    exact (continuous_hamiltonIveyConvexBarrier (K := K) (τ := τ) hK).comp continuous_fst
  have hmain : IsClosed {p : Real × Real | hamiltonIveyConvexBarrier K τ p.1 ≤ p.2} :=
    isClosed_le hbar_cont continuous_snd
  have hnonneg : IsClosed {p : Real × Real | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hset : hamiltonIveyConvexEpigraph K τ =
      {p : Real × Real | hamiltonIveyConvexBarrier K τ p.1 ≤ p.2} ∩
        {p : Real × Real | 0 ≤ p.1} := by
    ext p
    simp [hamiltonIveyConvexEpigraph, and_comm]
  rw [hset]
  exact hmain.inter hnonneg

theorem nonempty_hamiltonIveyConvexEpigraph
    {K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) :
    (hamiltonIveyConvexEpigraph K τ).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  constructor
  · simp
  · unfold hamiltonIveyConvexBarrier scalarSectionalLowerBarrier3 hamiltonIveyBarrier
    have hden : 0 < 1 + 4 * K * τ := by
      nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : Real) < 4) hK).le hτ]
    have hnonpos :
        -(3 * K) / (1 + 4 * K * τ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg (by norm_num : (0 : Real) ≤ 3) (le_of_lt hK)))
        (le_of_lt hden)
    exact max_le (by simpa using hnonpos) (by simp)

theorem nonempty_hamiltonIveyEpigraph (K τ : Real) :
    (hamiltonIveyEpigraph K τ).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  unfold hamiltonIveyEpigraph hamiltonIveyBarrier
  simp

theorem hamiltonIveyBarrier_log_arguments_pos
    {K τ ν : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hν : ν < 0) :
    0 < (-ν) / K ∧ 0 < 1 + 2 * K * τ := by
  constructor
  · exact div_pos (neg_pos.mpr hν) hK
  · nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]

theorem hamiltonIveyBarrier_scaling
    {K τ X c : Real} (hK : 0 < K) (hc : 0 < c) :
    hamiltonIveyBarrier (K / c) (c * τ) (X / c) =
      hamiltonIveyBarrier K τ X / c := by
  by_cases hX : X = 0
  · subst hX
    simp [hamiltonIveyBarrier]
  · unfold hamiltonIveyBarrier
    have hquot : (X / c) / (K / c) = X / K := by
      field_simp [hc.ne']
    have hden : 1 + 2 * (K / c) * (c * τ) = 1 + 2 * K * τ := by
      field_simp [hc.ne']
    rw [hquot, hden]
    field_simp [hc.ne']

theorem scalarSectionalLowerBarrier3_scaling
    {K τ c : Real} (hc : 0 < c) :
    scalarSectionalLowerBarrier3 (K / c) (c * τ) =
      scalarSectionalLowerBarrier3 K τ / c := by
  unfold scalarSectionalLowerBarrier3
  have hden : 1 + 4 * (K / c) * (c * τ) = 1 + 4 * K * τ := by
    field_simp [hc.ne']
  rw [hden]
  field_simp [hc.ne']

theorem scalarCurvatureLowerBarrier_scaling
    {K τ c : Real} (hc : 0 < c) :
    (-6 * (K / c) / (1 + 4 * (K / c) * (c * τ))) =
      (-6 * K / (1 + 4 * K * τ)) / c := by
  have hscaled := scalarSectionalLowerBarrier3_scaling (K := K) (τ := τ) (c := c) hc
  unfold scalarSectionalLowerBarrier3 at hscaled
  field_simp [hc.ne']

theorem hamiltonIveyConvexBarrier_scaling
    {K τ X c : Real} (hK : 0 < K) (hc : 0 < c) :
    hamiltonIveyConvexBarrier (K / c) (c * τ) (X / c) =
      hamiltonIveyConvexBarrier K τ X / c := by
  unfold hamiltonIveyConvexBarrier
  rw [scalarSectionalLowerBarrier3_scaling hc,
    hamiltonIveyBarrier_scaling hK hc]
  exact max_div_div_right hc.le _ _

def reactionSectionalSum3 (l1 l2 l3 : Real) : Real :=
  DifferentialGeometry.Dim3Reaction.sectionalReaction12 l1 l2 l3 +
    DifferentialGeometry.Dim3Reaction.sectionalReaction13 l1 l2 l3 +
    DifferentialGeometry.Dim3Reaction.sectionalReaction23 l1 l2 l3

def reactionPinchHeight3 (l1 l2 l3 : Real) : Real :=
  -DifferentialGeometry.Dim3Reaction.sectionalReaction23 l1 l2 l3

private theorem hamiltonIveyBarrierLog_nonpos_of_subregion
    {K τ X : Real} (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ) (hXpos : 0 < X)
    (hXsub : X ≤ K / (1 + 2 * K * τ)) :
    Real.log (X / K) + Real.log (1 + 2 * K * τ) ≤ 0 := by
  have hquot_pos : 0 < X * (1 + 2 * K * τ) / K := by
    positivity
  have hmul : X * (1 + 2 * K * τ) ≤ K := by
    calc
      X * (1 + 2 * K * τ) ≤ (K / (1 + 2 * K * τ)) * (1 + 2 * K * τ) :=
        mul_le_mul_of_nonneg_right hXsub (le_of_lt hden)
      _ = K := by
        exact div_mul_cancel₀ K hden.ne'
  have hquot_le : X * (1 + 2 * K * τ) / K ≤ 1 := by
    rw [div_le_one hK]
    exact hmul
  have hlog : Real.log (X * (1 + 2 * K * τ) / K) ≤ Real.log 1 :=
    Real.log_le_log hquot_pos hquot_le
  have hlogmul : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
      Real.log ((X / K) * (1 + 2 * K * τ)) := by
    rw [Real.log_mul (div_pos hXpos hK).ne' hden.ne']
  rw [hlogmul]
  have hquot' : (X / K) * (1 + 2 * K * τ) = X * (1 + 2 * K * τ) / K := by
    ring
  rw [hquot']
  simpa using hlog

theorem hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion
    {K τ X : Real} (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ) (hX : 0 ≤ X)
    (hXsub : X ≤ K / (1 + 2 * K * τ)) :
    hamiltonIveyBarrier K τ X ≤ -3 * X := by
  unfold hamiltonIveyBarrier
  by_cases hX0 : X = 0
  · subst hX0
    simp
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
    have hsum : Real.log (X / K) + Real.log (1 + 2 * K * τ) - 3 ≤ -3 := by
      have hlog := hamiltonIveyBarrierLog_nonpos_of_subregion hK hden hXpos hXsub
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hX
    nlinarith

theorem hamiltonIveyBarrier_le_sectionalSum_of_subregion
    {K τ X S : Real} (hS : -3 * X ≤ S) (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ)
    (hX : 0 ≤ X) (hXsub : X ≤ K / (1 + 2 * K * τ)) :
    hamiltonIveyBarrier K τ X ≤ S :=
  (hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion hK hden hX hXsub).trans hS

theorem hamiltonIveyBarrier_initial_le_sectionalSum
    {K X S : Real} (hS : -3 * X ≤ S) (hK : 0 < K) (hX : 0 ≤ X) (hXK : X ≤ K) :
    hamiltonIveyBarrier K 0 X ≤ S := by
  refine hamiltonIveyBarrier_le_sectionalSum_of_subregion hS hK ?_ hX ?_
  · norm_num
  · simpa using hXK

theorem hamiltonIveyBarrier_initial_le_sectionalSum_of_ordered
    {l1 l2 l3 K : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hpinch : -K ≤ l3) (hK : 0 < K) :
    hamiltonIveyBarrier K 0 (pinchHeight3 l3) ≤ sectionalSum3 l1 l2 l3 := by
  have hS : -3 * pinchHeight3 l3 ≤ sectionalSum3 l1 l2 l3 := by
    unfold pinchHeight3 sectionalSum3
    by_cases hl3 : l3 ≤ 0
    · rw [max_eq_left (neg_nonneg.mpr hl3)]
      linarith
    · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
      linarith
  have hX : 0 ≤ pinchHeight3 l3 := by
    unfold pinchHeight3
    exact le_max_right _ _
  have hXK : pinchHeight3 l3 ≤ K := by
    unfold pinchHeight3
    by_cases hl3 : l3 ≤ 0
    · rw [max_eq_left (neg_nonneg.mpr hl3)]
      linarith
    · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
      exact le_of_lt hK
  exact hamiltonIveyBarrier_initial_le_sectionalSum hS hK hX hXK

theorem hamiltonIveyConvexBarrier_initial_le_sectionalSum_of_ordered
    {l1 l2 l3 K : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2)
    (hpinch : -K ≤ l3) (hK : 0 < K) :
    hamiltonIveyConvexBarrier K 0 (pinchHeight3 l3) ≤ sectionalSum3 l1 l2 l3 := by
  have hbar := hamiltonIveyBarrier_initial_le_sectionalSum_of_ordered h21 h32 hpinch hK
  have hscalar : scalarSectionalLowerBarrier3 K 0 ≤ sectionalSum3 l1 l2 l3 := by
    unfold scalarSectionalLowerBarrier3 sectionalSum3
    have hX : pinchHeight3 l3 ≤ K := by
      unfold pinchHeight3
      by_cases hl3 : l3 ≤ 0
      · rw [max_eq_left (neg_nonneg.mpr hl3)]
        linarith
      · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
        exact le_of_lt hK
    have hS : -3 * pinchHeight3 l3 ≤ l1 + l2 + l3 := by
      unfold pinchHeight3
      by_cases hl3 : l3 ≤ 0
      · rw [max_eq_left (neg_nonneg.mpr hl3)]
        linarith
      · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
        linarith
    norm_num
    nlinarith
  unfold hamiltonIveyConvexBarrier
  exact max_le hscalar hbar

theorem hamiltonIveyConvexBarrier_initial_le_sectionalSum_of_constant
    {σ K : Real} (hpinch : -K ≤ σ) (hK : 0 < K) :
    hamiltonIveyConvexBarrier K 0 (pinchHeight3 σ) ≤ sectionalSum3 σ σ σ :=
  hamiltonIveyConvexBarrier_initial_le_sectionalSum_of_ordered
    (l1 := σ) (l2 := σ) (l3 := σ) le_rfl le_rfl hpinch hK

theorem diagonal_constant_mem_hamiltonIveyConvexMatrixRegion
    {σ K : Real} (hpinch : -K ≤ σ) (hK : 0 < K) :
    Matrix.diagonal (fun _ : Fin 3 => σ) ∈ hamiltonIveyConvexMatrixRegion K 0 := by
  let d : Fin 3 → Real := fun _ => σ
  have hd : Antitone d := by
    intro i j _hij
    rfl
  have heig : (Matrix.isHermitian_diagonal d).eigenvalues₀ = d :=
    diagonal_eigenvalues₀_eq_of_antitone d hd
  have hbar := hamiltonIveyConvexBarrier_initial_le_sectionalSum_of_constant
    (σ := σ) (K := K) hpinch hK
  refine ⟨Matrix.isHermitian_diagonal d, ?_⟩
  · have htrace : (Matrix.diagonal d).trace = sectionalSum3 σ σ σ := by
      rw [Matrix.trace_diagonal]
      simp [d, sectionalSum3]
      ring
    have heig₂ : (Matrix.isHermitian_diagonal d).eigenvalues₀ 2 = σ := by
      rw [heig]
    have hmin : DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3
        (Matrix.diagonal d) = σ := by
      rw [DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue
        (Matrix.isHermitian_diagonal d), heig₂]
    rw [htrace]
    simpa [d, hmin, pinchHeight3] using hbar

theorem diagonal_constant_mem_hamiltonIveyConvexMatrixRegion_k_one
    {σ : Real} (hpinch : -1 ≤ σ) :
    Matrix.diagonal (fun _ : Fin 3 => σ) ∈ hamiltonIveyConvexMatrixRegion 1 0 :=
  diagonal_constant_mem_hamiltonIveyConvexMatrixRegion (K := 1) hpinch
    (by norm_num : 0 < (1 : Real))

theorem hamiltonIveyBarrier_le_sectionalSum_of_ordered_subregion
    {l1 l2 l3 K τ : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hK : 0 < K)
    (hden : 0 < 1 + 2 * K * τ) (hsub : pinchHeight3 l3 ≤ K / (1 + 2 * K * τ)) :
    hamiltonIveyBarrier K τ (pinchHeight3 l3) ≤ sectionalSum3 l1 l2 l3 := by
  have hS : -3 * pinchHeight3 l3 ≤ sectionalSum3 l1 l2 l3 := by
    unfold pinchHeight3 sectionalSum3
    by_cases hl3 : l3 ≤ 0
    · rw [max_eq_left (neg_nonneg.mpr hl3)]
      linarith
    · rw [max_eq_right (neg_nonpos.mpr (le_of_lt (not_le.mp hl3)))]
      linarith
  have hX : 0 ≤ pinchHeight3 l3 := by
    unfold pinchHeight3
    exact le_max_right _ _
  exact hamiltonIveyBarrier_le_sectionalSum_of_subregion hS hK hden hX hsub

private theorem pinchingRatioLog_core_nonneg
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0) :
    0 ≤ l1 * l2 * (l1 + l2 - l3) - l3 * (l1 ^ 2 + l2 ^ 2) := by
  let X : Real := -l3
  let a : Real := l1 - l3
  let b : Real := l2 - l3
  have hX : 0 ≤ X := by
    dsimp [X]
    exact neg_nonneg.mpr (le_of_lt hl3)
  have ha : 0 ≤ a := by
    dsimp [a]
    linarith
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith
  have hX3 : 0 ≤ X ^ 3 := pow_nonneg hX 3
  have hp2 : 0 ≤ a ^ 2 * b := mul_nonneg (sq_nonneg a) hb
  have hp3 : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
  have hsum : (3 : Real)⁻¹ + (3 : Real)⁻¹ + (3 : Real)⁻¹ = 1 := by norm_num
  have hamgm := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (3 : Real)⁻¹) (w₂ := (3 : Real)⁻¹) (w₃ := (3 : Real)⁻¹)
    (p₁ := X ^ 3) (p₂ := a ^ 2 * b) (p₃ := a * b ^ 2)
    (by norm_num) (by norm_num) (by norm_num) hX3 hp2 hp3 hsum
  have hpow1 : (X ^ 3) ^ ((3 : Real)⁻¹) = X :=
    Real.pow_rpow_inv_natCast hX (by norm_num : (3 : ℕ) ≠ 0)
  have hpow2 : (a ^ 2 * b) ^ ((3 : Real)⁻¹) * (a * b ^ 2) ^ ((3 : Real)⁻¹) = a * b := by
    rw [← Real.mul_rpow hp2 hp3]
    rw [show a ^ 2 * b * (a * b ^ 2) = (a * b) ^ 3 by ring]
    exact Real.pow_rpow_inv_natCast (mul_nonneg ha hb) (by norm_num : (3 : ℕ) ≠ 0)
  have hle : X * (a * b) ≤ (3 : Real)⁻¹ * (X ^ 3 + a ^ 2 * b + a * b ^ 2) := by
    have h1 := hamgm
    rw [hpow1] at h1
    rw [mul_assoc, hpow2] at h1
    convert h1 using 1
    ring
  have h3 : 3 * X * (a * b) ≤ X ^ 3 + a ^ 2 * b + a * b ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hle (by norm_num : (0 : Real) ≤ 3)
    nlinarith
  have hcore : 0 ≤ X ^ 3 - 3 * a * b * X + a * b * (a + b) := by
    nlinarith
  have heq : l1 * l2 * (l1 + l2 - l3) - l3 * (l1 ^ 2 + l2 ^ 2) =
      X ^ 3 - 3 * a * b * X + a * b * (a + b) := by
    dsimp [X, a, b]
    ring
  rw [heq]
  exact hcore

theorem pinchingRatioLog_reaction_derivative_eq
    (l1 l2 l3 : Real) :
    reactionSectionalSum3 l1 l2 l3 * (-l3)
        - sectionalSum3 l1 l2 l3 * reactionPinchHeight3 l1 l2 l3
        - reactionPinchHeight3 l1 l2 l3 * (-l3) - 2 * (-l3) ^ 3 =
      2 * (l1 * l2 * (l1 + l2 - l3) - l3 * (l1 ^ 2 + l2 ^ 2)) := by
  unfold reactionSectionalSum3 reactionPinchHeight3 sectionalSum3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  ring

theorem pinchingRatioLog_reaction_derivative_ge
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0) :
    2 * (-l3) ^ 3 ≤
      reactionSectionalSum3 l1 l2 l3 * (-l3)
        - sectionalSum3 l1 l2 l3 * reactionPinchHeight3 l1 l2 l3
        - reactionPinchHeight3 l1 l2 l3 * (-l3) := by
  have hcore := pinchingRatioLog_core_nonneg h21 h32 hl3
  have heq := pinchingRatioLog_reaction_derivative_eq l1 l2 l3
  nlinarith

theorem hamiltonIveyBarrier_reaction_derivative_ge_on_boundary
    {l1 l2 l3 K τ : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hden : 0 < 1 + 2 * K * τ)
    (hboundary : hamiltonIveyBarrier K τ (-l3) = sectionalSum3 l1 l2 l3) :
    2 * (-l3) * ((-l3) - K / (1 + 2 * K * τ)) ≤
      reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) := by
  have hXpos : 0 < -l3 := neg_pos.mpr hl3
  have hG := pinchingRatioLog_reaction_derivative_ge h21 h32 hl3
  have hderivX : 2 * (-l3) ^ 3 ≤ reactionSectionalSum3 l1 l2 l3 * (-l3)
      - (sectionalSum3 l1 l2 l3 + (-l3)) * reactionPinchHeight3 l1 l2 l3 := by
    convert hG using 1; ring
  have hquot : sectionalSum3 l1 l2 l3 / (-l3) + 1 =
      Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2 := by
    unfold hamiltonIveyBarrier at hboundary
    have hb : sectionalSum3 l1 l2 l3 / (-l3) =
        Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3 := by
      have hb' : sectionalSum3 l1 l2 l3 =
          (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3) := by
        simpa [sectionalSum3] using hboundary.symm
      have hdiv := congrArg (fun t : Real => t / (-l3)) hb'
      dsimp only at hdiv
      have hshow :
          (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3) / (-l3) =
            Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 3 := by
        rw [mul_comm]
        exact mul_div_cancel_right₀ _ hXpos.ne'
      rw [hshow] at hdiv
      exact hdiv
    linarith
  have hquot' : sectionalSum3 l1 l2 l3 + (-l3) =
      (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) := by
    have hmul := congrArg (fun t : Real => t * (-l3)) hquot
    dsimp only at hmul
    rw [add_mul, div_mul_cancel₀ _ hXpos.ne', one_mul] at hmul
    convert hmul using 1; ring
  have hquotX' :
      (sectionalSum3 l1 l2 l3 + (-l3)) * reactionPinchHeight3 l1 l2 l3 =
        (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2)
          * reactionPinchHeight3 l1 l2 l3 := by
    rw [hquot']
  have hderiv2 : 2 * (-l3) ^ 3 ≤
      (-l3) * reactionSectionalSum3 l1 l2 l3
        - (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2)
          * reactionPinchHeight3 l1 l2 l3 := by
    nlinarith [hderivX, hquotX']
  have hbase : 2 * (-l3) ^ 2 ≤ reactionSectionalSum3 l1 l2 l3
      - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3 := by
    have hd : 2 * (-l3) ^ 2 = (-l3) * (2 * (-l3) ^ 2) / (-l3) := by
      field_simp [hXpos.ne']
    rw [hd]
    exact (div_le_iff₀ hXpos).mpr (by
      convert hderiv2 using 1 <;> ring)
  have hfinal := sub_le_sub_right hbase ((-l3) * (2 * K / (1 + 2 * K * τ)))
  have hfinal' : 2 * (-l3) * ((-l3) - K / (1 + 2 * K * τ)) ≤
      reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) := by
    field_simp [hden.ne'] at hfinal ⊢
    nlinarith
  exact hfinal'

theorem pinchHeight_ge_one_of_normalized_boundary
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hboundary : hamiltonIveyBarrier 1 0 (-l3) = sectionalSum3 l1 l2 l3) :
    1 ≤ -l3 := by
  have hXpos : 0 < -l3 := neg_pos.mpr hl3
  have hS : -3 * (-l3) ≤ sectionalSum3 l1 l2 l3 := by
    unfold sectionalSum3
    linarith
  have hb : sectionalSum3 l1 l2 l3 = (-l3) * (Real.log (-l3) - 3) := by
    unfold hamiltonIveyBarrier at hboundary
    have hb' : sectionalSum3 l1 l2 l3 =
        (-l3) * (Real.log ((-l3) / 1) + Real.log (1 + 2 * (1 : Real) * 0) - 3) :=
      hboundary.symm
    simpa using hb'
  have hnonneg : 0 ≤ (-l3) * Real.log (-l3) := by
    nlinarith
  have hlog : 0 ≤ Real.log (-l3) := by
    exact nonneg_of_mul_nonneg_right hnonneg hXpos
  have hloge : 1 ≤ -l3 := (Real.log_nonneg_iff hXpos).mp hlog
  exact hloge

theorem hamiltonIveyBarrier_rescaled_reaction_derivative_ge_on_boundary
    {l1 l2 l3 : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hboundary : hamiltonIveyBarrier 1 0 (-l3) = sectionalSum3 l1 l2 l3) :
    2 * (-l3) ^ 2 ≤
      reactionSectionalSum3 l1 l2 l3
        - (Real.log (-l3) - 2) * reactionPinchHeight3 l1 l2 l3 := by
  have hgen := hamiltonIveyBarrier_reaction_derivative_ge_on_boundary h21 h32 hl3
    (by norm_num : 0 < 1 + 2 * (1 : Real) * 0) hboundary
  have hnorm : 2 * (-l3) * ((-l3) - 1) ≤
      reactionSectionalSum3 l1 l2 l3 - (Real.log (-l3) - 2) * reactionPinchHeight3 l1 l2 l3
        - 2 * (-l3) := by
    norm_num [Real.log_one, div_one] at hgen ⊢
    ring_nf at hgen ⊢
    exact hgen
  nlinarith

theorem reactionSectionalSum3_ge_quadratic (l1 l2 l3 : Real) :
    (4 / 3 : Real) * sectionalSum3 l1 l2 l3 ^ 2 ≤ reactionSectionalSum3 l1 l2 l3 := by
  unfold reactionSectionalSum3 sectionalSum3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  nlinarith [sq_nonneg (l1 - l2), sq_nonneg (l2 - l3), sq_nonneg (l3 - l1)]

theorem hamiltonIveyBarrier_reaction_derivative_pos_on_boundary
    {l1 l2 l3 K τ : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ)
    (hboundary : hamiltonIveyBarrier K τ (-l3) = sectionalSum3 l1 l2 l3) :
    0 < reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) := by
  have hXpos : 0 < -l3 := neg_pos.mpr hl3
  have hgen := hamiltonIveyBarrier_reaction_derivative_ge_on_boundary h21 h32 hl3 hden hboundary
  by_cases hXsub : -l3 ≤ K / (1 + 2 * K * τ)
  · have hS' : sectionalSum3 l1 l2 l3 = -3 * (-l3) := by
      have hbar := hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion
        hK hden (neg_nonneg.mpr hl3.le) hXsub
      have hS : -3 * (-l3) ≤ sectionalSum3 l1 l2 l3 := by
        unfold sectionalSum3
        nlinarith [h21, h32]
      nlinarith [hbar, hboundary, hS]
    have hlog : Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) = 0 := by
      have hXlog : (-l3) * (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ)) = 0 := by
        unfold hamiltonIveyBarrier at hboundary
        nlinarith [hboundary, hS']
      exact (mul_eq_zero.mp hXlog).resolve_left hXpos.ne'
    have hXeq : -l3 = K / (1 + 2 * K * τ) := by
      have hquot : (-l3) * (1 + 2 * K * τ) / K = 1 := by
        have hlm : Real.log ((-l3) / K * (1 + 2 * K * τ)) = 0 := by
          rw [Real.log_mul (div_ne_zero hXpos.ne' hK.ne') hden.ne']
          simpa using hlog
        have heq : (-l3) / K * (1 + 2 * K * τ) = (-l3) * (1 + 2 * K * τ) / K := by ring
        rw [heq] at hlm
        rcases (Real.log_eq_zero.mp hlm) with h0 | h1 | h2
        · have hpos : 0 < (-l3) * (1 + 2 * K * τ) / K := by positivity
          linarith
        · exact h1
        · have hpos : 0 < (-l3) * (1 + 2 * K * τ) / K := by positivity
          linarith
      have hmul : (-l3) * (1 + 2 * K * τ) = K := by
        have hmul' : (-l3) * (1 + 2 * K * τ) / K * K = 1 * K :=
          congrArg (fun t : ℝ => t * K) hquot
        rw [div_mul_cancel₀ _ hK.ne', one_mul] at hmul'
        exact hmul'
      rw [eq_div_iff hden.ne']
      exact hmul
    have hl1 : l1 = l3 := by
      unfold sectionalSum3 at hS'
      have hdiff : l1 - l3 = 0 := by
        have hsum : (l1 - l3) + (l2 - l3) = 0 := by nlinarith
        have h1 : 0 ≤ l1 - l3 := by linarith
        have h2 : 0 ≤ l2 - l3 := by linarith
        nlinarith [hsum]
      linarith
    have hl2 : l2 = l3 := by
      unfold sectionalSum3 at hS'
      have hdiff : l2 - l3 = 0 := by
        have hsum : (l1 - l3) + (l2 - l3) = 0 := by nlinarith
        have h1 : 0 ≤ l1 - l3 := by linarith
        have h2 : 0 ≤ l2 - l3 := by linarith
        nlinarith [hsum]
      linarith
    have hphi : reactionSectionalSum3 l1 l2 l3
        - (Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2) * reactionPinchHeight3 l1 l2 l3
        - (-l3) * (2 * K / (1 + 2 * K * τ)) = 2 * (-l3) ^ 2 := by
      rw [hl1, hl2, hlog]
      have h1 : reactionSectionalSum3 l3 l3 l3 = 12 * l3 ^ 2 := by
        unfold reactionSectionalSum3
          DifferentialGeometry.Dim3Reaction.sectionalReaction12
          DifferentialGeometry.Dim3Reaction.sectionalReaction13
          DifferentialGeometry.Dim3Reaction.sectionalReaction23
        ring
      have h2 : reactionPinchHeight3 l3 l3 l3 = -4 * l3 ^ 2 := by
        unfold reactionPinchHeight3
          DifferentialGeometry.Dim3Reaction.sectionalReaction23
        ring
      rw [h1, h2]
      have h3 : 12 * l3 ^ 2 - (0 - 2) * (-4 * l3 ^ 2) - (-l3) * (2 * K / (1 + 2 * K * τ)) =
          4 * l3 ^ 2 + 2 * K * l3 / (1 + 2 * K * τ) := by
        ring
      rw [h3]
      have h4 : 2 * (-l3) ^ 2 = 2 * l3 ^ 2 := by ring
      rw [h4]
      have h5 : l3 + K / (1 + 2 * K * τ) = 0 := by nlinarith [hXeq]
      have h6 : K / (1 + 2 * K * τ) = -l3 := by linarith
      rw [show 2 * K * l3 / (1 + 2 * K * τ) = 2 * (K / (1 + 2 * K * τ)) * l3 by ring]
      rw [h6]
      ring
    rw [hphi]
    exact mul_pos two_pos (sq_pos_of_ne_zero hXpos.ne')
  · have hgt : K / (1 + 2 * K * τ) < -l3 := lt_of_not_ge hXsub
    have hpos : 0 < 2 * (-l3) * ((-l3) - K / (1 + 2 * K * τ)) :=
      mul_pos (mul_pos two_pos hXpos) (sub_pos.mpr hgt)
    exact lt_of_lt_of_le hpos hgen


def hamiltonIveyTangentLine (K τ a X : Real) : Real :=
  a * X - K * Real.exp (a + 2) / (1 + 2 * K * τ)

theorem hamiltonIveyTangentLine_le_hamiltonIveyBarrier
    {K τ a X : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 ≤ X) :
    hamiltonIveyTangentLine K τ a X ≤ hamiltonIveyBarrier K τ X := by
  by_cases hX0 : X = 0
  · subst X
    unfold hamiltonIveyTangentLine hamiltonIveyBarrier
    have hD : 0 < 1 + 2 * K * τ := by
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    have hexp : 0 < K * Real.exp (a + 2) / (1 + 2 * K * τ) := by positivity
    linarith
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
    let D : Real := 1 + 2 * K * τ
    let y : Real := X * D / K
    let z : Real := a + 2 - Real.log y
    have hDpos : 0 < D := by
      dsimp [D]
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    have hypos : 0 < y := by
      dsimp [y]
      positivity
    have hz : z + 1 ≤ Real.exp z := by
      dsimp [z]
      exact Real.add_one_le_exp (a + 2 - Real.log y)
    have hwle : (z + 1) * Real.exp (-z) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hz (le_of_lt (Real.exp_pos (-z)))
      have hcalc : Real.exp z * Real.exp (-z) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith
    have hexp_eq : Real.exp (a + 2) * Real.exp (-z) = y := by
      dsimp [z]
      rw [← Real.exp_add]
      have hsum : a + 2 + -(a + 2 - Real.log y) = Real.log y := by ring
      rw [hsum, Real.exp_log hypos]
    have hwy : y * (z + 1) ≤ Real.exp (a + 2) := by
      have hmul := mul_le_mul_of_nonneg_left hwle (le_of_lt (Real.exp_pos (a + 2)))
      calc
        y * (z + 1) = Real.exp (a + 2) * ((z + 1) * Real.exp (-z)) := by
          rw [← hexp_eq]
          ring
        _ ≤ Real.exp (a + 2) := by
          simpa using hmul
    have hbracket : 0 ≤ Real.exp (a + 2) - y * (z + 1) := sub_nonneg.mpr hwy
    have hlogy : Real.log y = Real.log X + Real.log D - Real.log K := by
      dsimp [y]
      rw [Real.log_div (mul_pos hXpos hDpos).ne' hK.ne']
      rw [Real.log_mul hXpos.ne' hDpos.ne']
    have hlogXK : Real.log (X / K) = Real.log X - Real.log K :=
      Real.log_div hXpos.ne' hK.ne'
    have hlogD : Real.log (1 + 2 * K * τ) = Real.log D := by
      dsimp [D]
    have hdiff : hamiltonIveyBarrier K τ X - hamiltonIveyTangentLine K τ a X =
        K / D * (Real.exp (a + 2) - y * (z + 1)) := by
      unfold hamiltonIveyBarrier hamiltonIveyTangentLine
      dsimp [D, y, z]
      rw [hlogy, hlogXK, hlogD]
      field_simp [hK.ne', hDpos.ne']
      ring_nf
    have hnonneg : 0 ≤ hamiltonIveyBarrier K τ X - hamiltonIveyTangentLine K τ a X := by
      rw [hdiff]
      exact mul_nonneg (div_nonneg hK.le hDpos.le) hbracket
    linarith

theorem pinchHeight_le_linear_sectionalSum_of_barrier
    {K τ X S δ : Real} (hK : 0 < K) (hδ : 0 < δ) (hτ : 0 ≤ τ)
    (hX : 0 ≤ X)
    (hbarrier : hamiltonIveyBarrier K τ X ≤ S) :
    X ≤ 2 * δ * S +
      2 * δ * K * Real.exp (2 + (2 * δ)⁻¹) / (1 + 2 * K * τ) := by
  have htangent := hamiltonIveyTangentLine_le_hamiltonIveyBarrier
    (K := K) (τ := τ) (a := (2 * δ)⁻¹) (X := X) hK hτ hX
  have hline :
      (2 * δ)⁻¹ * X - K * Real.exp (2 + (2 * δ)⁻¹) / (1 + 2 * K * τ) ≤ S := by
    simpa [hamiltonIveyTangentLine, add_comm] using htangent.trans hbarrier
  have hlinear :
      (2 * δ)⁻¹ * X ≤
        S + K * Real.exp (2 + (2 * δ)⁻¹) / (1 + 2 * K * τ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg (by norm_num : (0 : Real) ≤ 2) hδ.le)
  calc
    X = (2 * δ) * ((2 * δ)⁻¹ * X) := by
      field_simp [hδ.ne']
    _ ≤ (2 * δ) *
        (S + K * Real.exp (2 + (2 * δ)⁻¹) / (1 + 2 * K * τ)) := hmul
    _ = 2 * δ * S +
        2 * δ * K * Real.exp (2 + (2 * δ)⁻¹) / (1 + 2 * K * τ) := by ring

theorem hamiltonIveyTangentLine_initial_le_neg_three_mul
    {K a X : Real} (hK : 0 < K) (hX : 0 ≤ X) (hXK : X ≤ K) :
    hamiltonIveyTangentLine K 0 a X ≤ -3 * X := by
  unfold hamiltonIveyTangentLine
  norm_num
  have hE : a + 3 ≤ Real.exp (a + 2) := by
    have hE0 := Real.add_one_le_exp (a + 2)
    have hsum : a + 2 + 1 = a + 3 := by ring
    simpa [hsum] using hE0
  have hEpos : 0 < Real.exp (a + 2) := Real.exp_pos _
  by_cases hcoef : 0 ≤ a + 3
  · have h1 := mul_le_mul_of_nonneg_left hXK (le_of_lt hEpos)
    have h2 := mul_le_mul_of_nonneg_right hE hX
    have h12 : (a + 3) * X ≤ Real.exp (a + 2) * K := h2.trans h1
    nlinarith
  · have hleft : (a + 3) * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hcoef)) hX
    nlinarith [hleft, mul_nonneg hK.le hEpos.le]

theorem hamiltonIveyBarrier_eq_tangentLine_of_slope
    {K τ X : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 < X) :
    hamiltonIveyBarrier K τ X =
      hamiltonIveyTangentLine K τ
        (Real.log (X * (1 + 2 * K * τ) / K) - 2) X := by
  unfold hamiltonIveyBarrier hamiltonIveyTangentLine
  have hD : 0 < 1 + 2 * K * τ := by
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  have harg : 0 < X * (1 + 2 * K * τ) / K := by positivity
  have hlog : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
      Real.log (X * (1 + 2 * K * τ) / K) := by
    rw [Real.log_div hX.ne' hK.ne']
    rw [Real.log_div (mul_pos hX hD).ne' hK.ne']
    rw [Real.log_mul hX.ne' hD.ne']
    ring
  rw [hlog]
  rw [show Real.log (X * (1 + 2 * K * τ) / K) - 2 + 2 =
      Real.log (X * (1 + 2 * K * τ) / K) by ring]
  rw [Real.exp_log harg]
  field_simp [hK.ne', hD.ne']
  ring

theorem exists_hamiltonIveyTangentLine_eq_barrier
    {K τ X : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 < X) :
    ∃ a : Real,
      hamiltonIveyBarrier K τ X = hamiltonIveyTangentLine K τ a X := by
  refine ⟨Real.log (X * (1 + 2 * K * τ) / K) - 2, ?_⟩
  exact hamiltonIveyBarrier_eq_tangentLine_of_slope hK hτ hX

theorem hamiltonIveyTangentLine_le_hamiltonIveyConvexBarrier
    {K τ a X : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 ≤ X) :
    hamiltonIveyTangentLine K τ a X ≤ hamiltonIveyConvexBarrier K τ X := by
  unfold hamiltonIveyConvexBarrier
  exact (hamiltonIveyTangentLine_le_hamiltonIveyBarrier hK hτ hX).trans
    (hamiltonIveyBarrier_le_hamiltonIveyConvexBarrier K τ X)

theorem hamiltonIveyConvexMatrixRegion_subset_tangent_halfspace
    {K τ a : Real} {A : Matrix (Fin 3) (Fin 3) Real}
    (hK : 0 < K) (hτ : 0 ≤ τ)
    (hA : A ∈ hamiltonIveyConvexMatrixRegion K τ) :
    hamiltonIveyTangentLine K τ a
        (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0) ≤
      A.trace := by
  rw [hamiltonIveyConvexMatrixRegion] at hA
  exact (hamiltonIveyTangentLine_le_hamiltonIveyConvexBarrier
    (K := K) (τ := τ) (a := a)
    (X := max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0)
    hK hτ (le_max_right _ _)).trans hA.2


theorem mem_hamiltonIveyConvexMatrixRegion_of_forall_tangent_halfspace
    {K τ : Real} {A : Matrix (Fin 3) (Fin 3) Real}
    (hK : 0 < K) (hτ : 0 ≤ τ) (hA : A.IsHermitian)
    (htrace0 : 0 ≤ A.trace)
    (hscalar : scalarSectionalLowerBarrier3 K τ ≤ A.trace)
    (hforall : ∀ a : Real,
      hamiltonIveyTangentLine K τ a
          (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0) ≤
        A.trace) :
    A ∈ hamiltonIveyConvexMatrixRegion K τ := by
  rw [hamiltonIveyConvexMatrixRegion]
  refine ⟨hA, ?_⟩
  let X : Real := max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0
  have hX : 0 ≤ X := le_max_right _ _
  have hbar : hamiltonIveyBarrier K τ X ≤ A.trace := by
    by_cases hX0 : X = 0
    · rw [hX0]
      unfold hamiltonIveyBarrier
      ring_nf
      exact htrace0
    · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
      let a : Real := Real.log (X * (1 + 2 * K * τ) / K) - 2
      have hEq := hamiltonIveyBarrier_eq_tangentLine_of_slope hK hτ hXpos
      have hle : hamiltonIveyTangentLine K τ a X ≤ A.trace := by
        simpa [X, a] using hforall a
      rw [hEq]
      exact hle
  unfold hamiltonIveyConvexBarrier
  exact max_le hscalar hbar


def hamiltonIveySupportGap (K τ a X S : Real) : Real :=
  S - hamiltonIveyTangentLine K τ a X

def hamiltonIveySupportEigenGap (K τ a l3 S : Real) : Real :=
  S + K * Real.exp (a + 2) / (1 + 2 * K * τ) + a * l3

theorem hamiltonIveySupportGap_eq_of_pinch_eq
    {K τ a X l3 S : Real} (hX : X = pinchHeight3 l3) :
    hamiltonIveySupportEigenGap K τ a l3 S =
      hamiltonIveySupportGap K τ a X S + a * (X + l3) := by
  unfold hamiltonIveySupportEigenGap hamiltonIveySupportGap hamiltonIveyTangentLine
  rw [hX]
  ring

theorem hamiltonIveySupportGap_le_supportEigenGap
    {K τ a l3 S : Real} (ha : 0 ≤ a) :
    hamiltonIveySupportGap K τ a (pinchHeight3 l3) S ≤
      hamiltonIveySupportEigenGap K τ a l3 S := by
  have hmain := hamiltonIveySupportGap_eq_of_pinch_eq
    (K := K) (τ := τ) (a := a) (l3 := l3) (S := S) rfl
  rw [hmain]
  unfold pinchHeight3
  by_cases hl : l3 < 0
  · have hX : max (-l3) 0 = -l3 := max_eq_left (neg_nonneg.mpr hl.le)
    rw [hX]
    linarith
  · have hX : max (-l3) 0 = 0 := max_eq_right (neg_nonpos.mpr (not_lt.mp hl))
    rw [hX]
    have hsum : 0 ≤ 0 + l3 := by linarith
    nlinarith [mul_nonneg ha hsum]

theorem hamiltonIveySupportEigenGap_eq_supportGap_of_pinch_neg
    {K τ a l3 S : Real} (hl3 : l3 < 0) :
    hamiltonIveySupportEigenGap K τ a l3 S =
      hamiltonIveySupportGap K τ a (pinchHeight3 l3) S := by
  have hpinch : pinchHeight3 l3 = -l3 := by
    unfold pinchHeight3
    exact max_eq_left (neg_nonneg.mpr hl3.le)
  have hmain := hamiltonIveySupportGap_eq_of_pinch_eq
    (K := K) (τ := τ) (a := a) (X := pinchHeight3 l3) (l3 := l3)
    (S := S) rfl
  rw [hpinch] at hmain ⊢
  linarith

theorem hamiltonIveyBarrier_sub_le_supportGap
    {K τ a X S : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 ≤ X) :
    S - hamiltonIveyBarrier K τ X ≤ hamiltonIveySupportGap K τ a X S := by
  unfold hamiltonIveySupportGap
  exact sub_le_sub_left
    (hamiltonIveyTangentLine_le_hamiltonIveyBarrier hK hτ hX) S

theorem hamiltonIveyBarrier_sub_le_supportEigenGap
    {K τ a l3 S : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (ha : 0 ≤ a) :
    S - hamiltonIveyBarrier K τ (pinchHeight3 l3) ≤
      hamiltonIveySupportEigenGap K τ a l3 S := by
  exact (hamiltonIveyBarrier_sub_le_supportGap (K := K) (τ := τ) (a := a)
    (X := pinchHeight3 l3) (S := S) hK hτ (le_max_right _ _)).trans
    (hamiltonIveySupportGap_le_supportEigenGap (K := K) (τ := τ) (a := a)
      (l3 := l3) (S := S) ha)

theorem hamiltonIveySupportGap_eq_barrier_sub_of_slope
    {K τ X S : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 < X) :
    hamiltonIveySupportGap K τ
        (Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2) X S =
      S - hamiltonIveyBarrier K τ X := by
  unfold hamiltonIveySupportGap
  have hD : 0 < 1 + 2 * K * τ := by
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  have hlogeq : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
      Real.log (X * (1 + 2 * K * τ) / K) := by
    rw [Real.log_div hX.ne' hK.ne']
    rw [Real.log_div (mul_pos hX hD).ne' hK.ne']
    rw [Real.log_mul hX.ne' hD.ne']
    ring
  have hline : hamiltonIveyBarrier K τ X =
      hamiltonIveyTangentLine K τ
        (Real.log (X * (1 + 2 * K * τ) / K) - 2) X :=
    hamiltonIveyBarrier_eq_tangentLine_of_slope hK hτ hX
  rw [hline]
  congr 1
  unfold hamiltonIveyTangentLine
  rw [hlogeq]

theorem hamiltonIveyConvexBarrier_failure_pinch_pos
    {K τ X S : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 ≤ X)
    (hS3 : -3 * X ≤ S)
    (hscalar : scalarSectionalLowerBarrier3 K τ ≤ S)
    (hfail : S < hamiltonIveyConvexBarrier K τ X) :
    0 < X ∧ S < hamiltonIveyBarrier K τ X := by
  have hden4 : 0 < 1 + 4 * K * τ := by
    nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : Real) < 4) hK).le hτ]
  have hscalar_neg : scalarSectionalLowerBarrier3 K τ < 0 := by
    unfold scalarSectionalLowerBarrier3
    exact div_neg_of_neg_of_pos (by nlinarith) hden4
  have hbarrier_pos_at_zero : hamiltonIveyConvexBarrier K τ 0 = 0 := by
    unfold hamiltonIveyConvexBarrier hamiltonIveyBarrier
    simp only [zero_mul]
    exact max_eq_right (le_of_lt hscalar_neg)
  have hXpos : 0 < X := by
    by_contra hnot
    have hzero : X = 0 := le_antisymm (not_lt.mp hnot) hX
    rw [hzero, hbarrier_pos_at_zero] at hfail
    nlinarith [hS3]
  refine ⟨hXpos, ?_⟩
  have hnotbarrier : ¬ hamiltonIveyBarrier K τ X ≤ scalarSectionalLowerBarrier3 K τ := by
    intro h
    have hmax : hamiltonIveyConvexBarrier K τ X = scalarSectionalLowerBarrier3 K τ := by
      unfold hamiltonIveyConvexBarrier
      exact max_eq_left h
    rw [hmax] at hfail
    linarith
  have hbar_gt : scalarSectionalLowerBarrier3 K τ < hamiltonIveyBarrier K τ X :=
    lt_of_not_ge hnotbarrier
  have hmaxval : hamiltonIveyConvexBarrier K τ X = hamiltonIveyBarrier K τ X := by
    unfold hamiltonIveyConvexBarrier
    exact max_eq_right (le_of_lt hbar_gt)
  rw [hmaxval] at hfail
  exact hfail

theorem hamiltonIveyTangentLine_eq_barrier_at_tangentPoint
    {K τ a : Real} (hK : 0 < K) (hτ : 0 ≤ τ) :
    hamiltonIveyTangentLine K τ a (K * Real.exp (a + 2) / (1 + 2 * K * τ)) =
      hamiltonIveyBarrier K τ (K * Real.exp (a + 2) / (1 + 2 * K * τ)) := by
  unfold hamiltonIveyTangentLine hamiltonIveyBarrier
  have hD : 0 < 1 + 2 * K * τ := by
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  have hXpos : 0 < K * Real.exp (a + 2) / (1 + 2 * K * τ) := by positivity
  have hlog : Real.log (K * Real.exp (a + 2) / (1 + 2 * K * τ) / K) +
      Real.log (1 + 2 * K * τ) = a + 2 := by
    have h1 : K * Real.exp (a + 2) / (1 + 2 * K * τ) / K =
        Real.exp (a + 2) / (1 + 2 * K * τ) := by
      field_simp [hK.ne', hD.ne']
    rw [h1, Real.log_div (Real.exp_pos (a + 2)).ne' hD.ne',
      Real.log_exp]
    ring
  rw [hlog]
  field_simp [hK.ne', hD.ne']
  ring

def sectionalReactionMatrix3 (l : Fin 3 → Real) : Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    if i = j then
      if i = 0 then DifferentialGeometry.Dim3Reaction.sectionalReaction12 (l 0) (l 1) (l 2)
      else if i = 1 then DifferentialGeometry.Dim3Reaction.sectionalReaction13 (l 0) (l 1) (l 2)
      else DifferentialGeometry.Dim3Reaction.sectionalReaction23 (l 0) (l 1) (l 2)
    else 0

theorem sectionalReactionMatrix3_trace
    (l : Fin 3 → Real) :
    (sectionalReactionMatrix3 l).trace = reactionSectionalSum3 (l 0) (l 1) (l 2) := by
  unfold sectionalReactionMatrix3 reactionSectionalSum3
  simp [Matrix.trace, Fin.sum_univ_three]

def sectionalReactionPinchMatrix3 (l : Fin 3 → Real) : Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    if i = j then
      if i = 2 then reactionPinchHeight3 (l 0) (l 1) (l 2) else 0
    else 0

theorem sectionalReactionPinchMatrix3_trace
    (l : Fin 3 → Real) :
    (sectionalReactionPinchMatrix3 l).trace = reactionPinchHeight3 (l 0) (l 1) (l 2) := by
  unfold sectionalReactionPinchMatrix3
  simp [Matrix.trace]

theorem sectionalReactionMatrix3_trace_sub_coef_pinch_trace_pos_on_barrier
    {l : Fin 3 → Real} {K τ : Real}
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) (hl3 : l 2 < 0)
    (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ)
    (hboundary : hamiltonIveyBarrier K τ (-l 2) = sectionalSum3 (l 0) (l 1) (l 2)) :
    0 < (sectionalReactionMatrix3 l).trace -
      (Real.log ((-l 2) / K) + Real.log (1 + 2 * K * τ) - 2) *
        (sectionalReactionPinchMatrix3 l).trace -
      (-l 2) * (2 * K / (1 + 2 * K * τ)) := by
  rw [sectionalReactionMatrix3_trace, sectionalReactionPinchMatrix3_trace]
  exact hamiltonIveyBarrier_reaction_derivative_pos_on_boundary
    h21 h32 hl3 hK hden hboundary

private theorem supportHalfspace_reaction_derivative_eq
    {l1 l2 l3 a C : Real} (ha : a ≠ -3)
    (hboundary : sectionalSum3 l1 l2 l3 + a * l3 + C = 0) :
    reactionSectionalSum3 l1 l2 l3 - a * reactionPinchHeight3 l1 l2 l3 =
      2 * (2 * C ^ 2 - a * C * ((l1 - l2) + 2 * (l2 - l3)) +
        (l1 - l2) ^ 2 + (a + 1) ^ 2 * (l1 - l2) * (l2 - l3) +
          (a + 1) ^ 2 * (l2 - l3) ^ 2) / (a + 3) := by
  let u : Real := l1 - l2
  let v : Real := l2 - l3
  have hsum : u + 2 * v + (a + 3) * l3 + C = 0 := by
    dsimp [u, v]
    unfold sectionalSum3 at hboundary
    nlinarith
  have hz : l3 = (-C - u - 2 * v) / (a + 3) := by
    dsimp [u, v]
    have hden : a + 3 ≠ 0 := by
      intro hzero
      apply ha
      linarith
    rw [eq_div_iff hden]
    nlinarith [hsum]
  have hl1 : l1 = u + v + l3 := by
    dsimp [u, v]
    ring
  have hl2 : l2 = v + l3 := by
    dsimp [u, v]
    ring
  unfold reactionSectionalSum3 reactionPinchHeight3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  rw [hl1, hl2, hz]
  dsimp [u, v]
  have hden : a + 3 ≠ 0 := by
    intro hzero
    apply ha
    linarith
  field_simp [hden]
  ring

theorem supportHalfspace_reaction_derivative_nonneg_of_boundary
    {l1 l2 l3 a C : Real}
    (h21 : l2 ≤ l1) (h32 : l3 ≤ l2)
    (ha_low : -3 < a) (ha_sq : a ^ 2 ≤ 8) (hC : 0 < C)
    (hboundary : sectionalSum3 l1 l2 l3 + a * l3 + C = 0) :
    0 ≤ reactionSectionalSum3 l1 l2 l3 - a * reactionPinchHeight3 l1 l2 l3 := by
  let u : Real := l1 - l2
  let v : Real := l2 - l3
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith
  have hv : 0 ≤ v := by
    dsimp [v]
    linarith
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have huv_plus : 0 ≤ u * v + v ^ 2 := by
    nlinarith [huv, sq_nonneg v]
  have hden_pos : 0 < a + 3 := by nlinarith
  have hcalc := supportHalfspace_reaction_derivative_eq
    (show a ≠ -3 by
      intro h
      linarith) hboundary
  rw [hcalc]
  have hnonneg_num :
      0 ≤ 2 * C ^ 2 - a * C * (u + 2 * v) + u ^ 2 +
        (a + 1) ^ 2 * u * v + (a + 1) ^ 2 * v ^ 2 := by
    by_cases hle : a ≤ 0
    · have hlin : 0 ≤ -a * C * (u + 2 * v) := by
        have hcoef : 0 ≤ -a := by linarith
        have hsum : 0 ≤ u + 2 * v := by nlinarith [hu, hv]
        exact mul_nonneg (mul_nonneg hcoef (le_of_lt hC)) hsum
      have hcross_base : 0 ≤ (a + 1) ^ 2 * u :=
        mul_nonneg (sq_nonneg (a + 1)) hu
      have hcross : 0 ≤ (a + 1) ^ 2 * u * v :=
        mul_nonneg hcross_base hv
      have hsquare : 0 ≤ (a + 1) ^ 2 * v ^ 2 :=
        mul_nonneg (sq_nonneg (a + 1)) (sq_nonneg v)
      nlinarith [sq_nonneg C, sq_nonneg u, hlin, hcross, hsquare]
    · have hpos_a : 0 ≤ a := le_of_lt (lt_of_not_ge hle)
      have hsq8 : 0 ≤ 8 - a ^ 2 := by nlinarith
      have hcoef : 0 ≤ 4 * (a ^ 2 + 4 * a + 2) := by
        have hinside : 0 ≤ a ^ 2 + 4 * a + 2 := by nlinarith [sq_nonneg a, hpos_a]
        positivity
      have hfirst : 0 ≤ 2 * (C - a * (u + 2 * v) / 4) ^ 2 := by positivity
      have hsecond : 0 ≤ ((8 - a ^ 2) * u ^ 2 + 4 * (a ^ 2 + 4 * a + 2) * (u * v + v ^ 2)) / 8 := by
        have hterm : 0 ≤ (8 - a ^ 2) * u ^ 2 := mul_nonneg hsq8 (sq_nonneg u)
        have hterm2 : 0 ≤ 4 * (a ^ 2 + 4 * a + 2) * (u * v + v ^ 2) :=
          mul_nonneg hcoef huv_plus
        exact div_nonneg (add_nonneg hterm hterm2) (by norm_num : (0 : Real) ≤ 8)
      have hid :
          2 * C ^ 2 - a * C * (u + 2 * v) + u ^ 2 +
            (a + 1) ^ 2 * u * v + (a + 1) ^ 2 * v ^ 2 =
          2 * (C - a * (u + 2 * v) / 4) ^ 2 +
            ((8 - a ^ 2) * u ^ 2 + 4 * (a ^ 2 + 4 * a + 2) * (u * v + v ^ 2)) / 8 := by
        ring
      rw [hid]
      exact add_nonneg hfirst hsecond
  exact div_nonneg (mul_nonneg two_pos.le hnonneg_num) (le_of_lt hden_pos)

theorem hamiltonIveyTangentHalfspace_reaction_nonneg_of_boundary
    {K τ a l1 l2 l3 : Real}
    (hK : 0 < K) (hτ : 0 ≤ τ)
    (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (ha_low : -3 < a) (ha_sq : a ^ 2 ≤ 8)
    (hboundary : hamiltonIveyTangentLine K τ a (max (-l3) 0) = sectionalSum3 l1 l2 l3) :
    0 ≤ reactionSectionalSum3 l1 l2 l3 - a * reactionPinchHeight3 l1 l2 l3 := by
  have hX : max (-l3) 0 = -l3 := max_eq_left (neg_nonneg.mpr hl3.le)
  let C : Real := K * Real.exp (a + 2) / (1 + 2 * K * τ)
  have hCpos : 0 < C := by
    dsimp [C]
    have hD : 0 < 1 + 2 * K * τ := by
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    positivity
  have hboundary' : sectionalSum3 l1 l2 l3 + a * l3 + C = 0 := by
    rw [hX] at hboundary
    unfold hamiltonIveyTangentLine at hboundary
    dsimp [C] at hboundary ⊢
    nlinarith
  exact supportHalfspace_reaction_derivative_nonneg_of_boundary
    h21 h32 ha_low ha_sq hCpos hboundary'


theorem diagonal_hamiltonIveyTangentHalfspace_reaction_nonneg_of_boundary
    {K τ a l1 l2 l3 : Real}
    (hK : 0 < K) (hτ : 0 ≤ τ)
    (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (ha_low : -3 < a) (ha_sq : a ^ 2 ≤ 8)
    (hboundary : hamiltonIveyTangentLine K τ a (max (-l3) 0) = sectionalSum3 l1 l2 l3) :
    0 ≤ reactionSectionalSum3 l1 l2 l3 - a * reactionPinchHeight3 l1 l2 l3 :=
  hamiltonIveyTangentHalfspace_reaction_nonneg_of_boundary
    hK hτ h21 h32 hl3 ha_low ha_sq hboundary

theorem hamiltonIveyBarrier_monotoneOn_of_exp_two_le
    {K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) :
    MonotoneOn (hamiltonIveyBarrier K τ)
      (Set.Ici (K * Real.exp 2 / (1 + 2 * K * τ))) := by
  intro x hx y hy hxy
  let D : Real := 1 + 2 * K * τ
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  have hx0 : 0 < K * Real.exp 2 / D := by positivity
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hargpos : 0 < x * D / K := by positivity
  have hle : Real.exp 2 ≤ x * D / K := by
    have hmul := mul_le_mul_of_nonneg_right hx (le_of_lt hDpos)
    have hcalc : (K * Real.exp 2 / D) * D = K * Real.exp 2 := by
      field_simp [hDpos.ne']
    rw [hcalc] at hmul
    have hmul2 := mul_le_mul_of_nonneg_left hmul (le_of_lt (inv_pos.mpr hK))
    have hcalc2 : K⁻¹ * (K * Real.exp 2) = Real.exp 2 := by
      field_simp [hK.ne']
    have hcalc3 : K⁻¹ * (x * D) = x * D / K := by ring
    rw [hcalc2, hcalc3] at hmul2
    exact hmul2
  have hlog : 2 ≤ Real.log (x * D / K) := by
    simpa [Real.log_exp] using (Real.log_le_log_iff (Real.exp_pos 2) hargpos).2 hle
  let a : Real := Real.log (x * (1 + 2 * K * τ) / K) - 2
  have ha : 0 ≤ a := by
    dsimp [a]
    change 0 ≤ Real.log (x * D / K) - 2
    linarith [hlog]
  have hline_le := hamiltonIveyTangentLine_le_hamiltonIveyBarrier
    (K := K) (τ := τ) (a := a) (X := y) hK hτ (le_of_lt hypos)
  have hline_eq : hamiltonIveyBarrier K τ x = hamiltonIveyTangentLine K τ a x := by
    dsimp [a, D]
    exact hamiltonIveyBarrier_eq_tangentLine_of_slope hK hτ hxpos
  have hlin_inc : hamiltonIveyTangentLine K τ a x ≤ hamiltonIveyTangentLine K τ a y := by
    unfold hamiltonIveyTangentLine
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hxy ha) _
  calc
    hamiltonIveyBarrier K τ x = hamiltonIveyTangentLine K τ a x := hline_eq
    _ ≤ hamiltonIveyTangentLine K τ a y := hlin_inc
    _ ≤ hamiltonIveyBarrier K τ y := hline_le

theorem hamiltonIveyBarrier_antitoneOn_of_le_exp_two
    {K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) :
    AntitoneOn (hamiltonIveyBarrier K τ)
      (Set.Ioc 0 (K * Real.exp 2 / (1 + 2 * K * τ))) := by
  intro x hx y hy hxy
  let D : Real := 1 + 2 * K * τ
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  have hxpos : 0 < x := hx.1
  have hypos : 0 < y := hy.1
  have hargpos : 0 < y * D / K := by positivity
  have hle : y * D / K ≤ Real.exp 2 := by
    have hmul := mul_le_mul_of_nonneg_right hy.2 (le_of_lt hDpos)
    have hcalc : (K * Real.exp 2 / D) * D = K * Real.exp 2 := by
      field_simp [hDpos.ne']
    rw [hcalc] at hmul
    have hmul2 := mul_le_mul_of_nonneg_left hmul (le_of_lt (inv_pos.mpr hK))
    have hcalc2 : K⁻¹ * (K * Real.exp 2) = Real.exp 2 := by
      field_simp [hK.ne']
    have hcalc3 : K⁻¹ * (y * D) = y * D / K := by ring
    rw [hcalc2, hcalc3] at hmul2
    exact hmul2
  have hlog : Real.log (y * D / K) ≤ 2 := by
    simpa [Real.log_exp] using (Real.log_le_log_iff hargpos (Real.exp_pos 2)).2 hle
  let a : Real := Real.log (y * (1 + 2 * K * τ) / K) - 2
  have ha : a ≤ 0 := by
    dsimp [a]
    change Real.log (y * D / K) - 2 ≤ 0
    linarith [hlog]
  have hline_le := hamiltonIveyTangentLine_le_hamiltonIveyBarrier
    (K := K) (τ := τ) (a := a) (X := x) hK hτ (le_of_lt hxpos)
  have hline_eq : hamiltonIveyBarrier K τ y = hamiltonIveyTangentLine K τ a y := by
    dsimp [a, D]
    exact hamiltonIveyBarrier_eq_tangentLine_of_slope hK hτ hypos
  have hlin_inc : hamiltonIveyTangentLine K τ a y ≤ hamiltonIveyTangentLine K τ a x := by
    unfold hamiltonIveyTangentLine
    have hprod : 0 ≤ a * (x - y) := by
      exact mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.mpr hxy)
    have hsub : a * y - K * Real.exp (a + 2) / (1 + 2 * K * τ) ≤
        a * x - K * Real.exp (a + 2) / (1 + 2 * K * τ) := by
      nlinarith [hprod]
    exact hsub
  calc
    hamiltonIveyBarrier K τ y = hamiltonIveyTangentLine K τ a y := hline_eq
    _ ≤ hamiltonIveyTangentLine K τ a x := hlin_inc
    _ ≤ hamiltonIveyBarrier K τ x := hline_le

theorem hamiltonIveyBarrier_le_scalarLower_of_ge_subregion_le_expTwo
    {K τ X : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (hX0 : K / (1 + 2 * K * τ) ≤ X)
    (hXe : X ≤ K * Real.exp 2 / (1 + 2 * K * τ)) :
    hamiltonIveyBarrier K τ X ≤ scalarSectionalLowerBarrier3 K τ := by
  let D : ℝ := 1 + 2 * K * τ
  let E : ℝ := K * Real.exp 2 / D
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hX0pos : 0 < K / D := by positivity
  have hXpos : 0 < X := lt_of_lt_of_le hX0pos hX0
  have hX0mem : K / D ∈ Set.Ioc (0 : ℝ) E := by
    dsimp [E]
    constructor
    · exact hX0pos
    · have hle_exp : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)
      have hKnonneg : 0 ≤ K := le_of_lt hK
      have hmul := mul_le_mul_of_nonneg_right hle_exp hKnonneg
      have hdiv := div_le_div_of_nonneg_right hmul hDpos.le
      simpa [D, mul_comm] using hdiv
  have hXmem : X ∈ Set.Ioc (0 : ℝ) E := by
    dsimp [E]
    exact ⟨hXpos, hXe⟩
  have hanti := hamiltonIveyBarrier_antitoneOn_of_le_exp_two (K := K) (τ := τ) hK hτ
  have hleX : hamiltonIveyBarrier K τ X ≤ hamiltonIveyBarrier K τ (K / D) :=
    hanti hX0mem hXmem (by simpa [D] using hX0)
  have hval : hamiltonIveyBarrier K τ (K / D) = -3 * K / D := by
    have hXK : (K / D) / K = (1 : ℝ) / D := by
      field_simp [hK.ne', hDpos.ne']
    have hlog1 : Real.log ((K / D) / K) + Real.log (1 + 2 * K * τ) = 0 := by
      rw [hXK]
      have hlogD : Real.log ((1 : ℝ) / D) = -Real.log D := by
        rw [Real.log_div one_ne_zero hDpos.ne', Real.log_one, zero_sub]
      have hDdef : 1 + 2 * K * τ = D := rfl
      rw [hlogD, hDdef]
      ring
    unfold hamiltonIveyBarrier
    dsimp [D] at hXK hlog1
    rw [hlog1]
    ring
  have hscalar_ge : -3 * K / D ≤ scalarSectionalLowerBarrier3 K τ := by
    unfold scalarSectionalLowerBarrier3
    have hden4 : 0 < 1 + 4 * K * τ := by
      nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 4) hK).le hτ]
    have hDne : D ≠ 0 := ne_of_gt hDpos
    have hden4ne : 1 + 4 * K * τ ≠ 0 := ne_of_gt hden4
    have hmain : -3 * K / D ≤ -3 * K / (1 + 4 * K * τ) := by
      field_simp [hDne, hden4ne]
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hK.le) hτ]
    simpa [D] using hmain
  exact le_trans hleX (le_trans (le_of_eq hval) hscalar_ge)

theorem hamiltonIveyConvexBarrier_monotoneOn_of_ge_subregion
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    MonotoneOn (hamiltonIveyConvexBarrier K τ)
      (Set.Ici (K / (1 + 2 * K * τ))) := by
  let D : ℝ := 1 + 2 * K * τ
  let E : ℝ := K * Real.exp 2 / D
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  intro x hx y hy hxy
  by_cases hxE : x ≤ E
  · have hraw_x : hamiltonIveyBarrier K τ x ≤ scalarSectionalLowerBarrier3 K τ :=
      hamiltonIveyBarrier_le_scalarLower_of_ge_subregion_le_expTwo hK hτ (by simpa [D] using hx) hxE
    have hconv_x : hamiltonIveyConvexBarrier K τ x = scalarSectionalLowerBarrier3 K τ := by
      unfold hamiltonIveyConvexBarrier
      exact max_eq_left hraw_x
    rw [hconv_x]
    exact le_max_left _ _
  · have hx_gt_E : E < x := lt_of_not_ge hxE
    have hx_ge_E : E ≤ x := le_of_lt hx_gt_E
    have hy_ge_E : E ≤ y := le_trans hx_ge_E hxy
    by_cases hy_scalar : hamiltonIveyBarrier K τ y ≤ scalarSectionalLowerBarrier3 K τ
    · have hraw_le : hamiltonIveyBarrier K τ x ≤ hamiltonIveyBarrier K τ y :=
        (hamiltonIveyBarrier_monotoneOn_of_exp_two_le (K := K) (τ := τ) hK hτ) hx_ge_E hy_ge_E hxy
      have hconv_x : hamiltonIveyConvexBarrier K τ x = scalarSectionalLowerBarrier3 K τ := by
        unfold hamiltonIveyConvexBarrier
        exact max_eq_left (le_trans hraw_le hy_scalar)
      have hconv_y : hamiltonIveyConvexBarrier K τ y = scalarSectionalLowerBarrier3 K τ := by
        unfold hamiltonIveyConvexBarrier
        exact max_eq_left hy_scalar
      rw [hconv_x, hconv_y]
    · have hraw_gt : scalarSectionalLowerBarrier3 K τ < hamiltonIveyBarrier K τ y := lt_of_not_ge hy_scalar
      have hconv_y : hamiltonIveyConvexBarrier K τ y = hamiltonIveyBarrier K τ y := by
        unfold hamiltonIveyConvexBarrier
        exact max_eq_right (le_of_lt hraw_gt)
      have hconv_x_le : hamiltonIveyConvexBarrier K τ x ≤ hamiltonIveyBarrier K τ y := by
        by_cases hxE2 : x ≤ E
        · have hraw_x : hamiltonIveyBarrier K τ x ≤ scalarSectionalLowerBarrier3 K τ :=
            hamiltonIveyBarrier_le_scalarLower_of_ge_subregion_le_expTwo hK hτ (by simpa [D] using hx) hxE2
          have hconv_x : hamiltonIveyConvexBarrier K τ x = scalarSectionalLowerBarrier3 K τ := by
            unfold hamiltonIveyConvexBarrier
            exact max_eq_left hraw_x
          rw [hconv_x]
          exact le_of_lt hraw_gt
        · have hx_ge_E2 : E ≤ x := le_of_not_ge hxE2
          have hraw_le : hamiltonIveyBarrier K τ x ≤ hamiltonIveyBarrier K τ y :=
            (hamiltonIveyBarrier_monotoneOn_of_exp_two_le (K := K) (τ := τ) hK hτ) hx_ge_E2 hy_ge_E hxy
          by_cases hrawx_scalar : hamiltonIveyBarrier K τ x ≤ scalarSectionalLowerBarrier3 K τ
          · have hconv_x : hamiltonIveyConvexBarrier K τ x = scalarSectionalLowerBarrier3 K τ := by
              unfold hamiltonIveyConvexBarrier
              exact max_eq_left hrawx_scalar
            rw [hconv_x]
            exact le_of_lt hraw_gt
          · have hscalar_lt_rawx : scalarSectionalLowerBarrier3 K τ < hamiltonIveyBarrier K τ x := lt_of_not_ge hrawx_scalar
            have hconv_x : hamiltonIveyConvexBarrier K τ x = hamiltonIveyBarrier K τ x := by
              unfold hamiltonIveyConvexBarrier
              exact max_eq_right (le_of_lt hscalar_lt_rawx)
            rw [hconv_x]
            exact hraw_le
      rw [hconv_y]
      exact hconv_x_le

theorem convex_hamiltonIveyConvexMatrixRegion
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 ≤ τ) :
    Convex ℝ (hamiltonIveyConvexMatrixRegion K τ) := by
  rw [convex_iff_forall_pos]
  intro A hA B hB a b ha hb hab
  rw [hamiltonIveyConvexMatrixRegion] at hA hB ⊢
  rcases hA with ⟨hAh, hAbar⟩
  rcases hB with ⟨hBh, hBbar⟩
  let C : Matrix (Fin 3) (Fin 3) ℝ := a • A + b • B
  have hCh : C.IsHermitian := by
    have hA' : A.transpose = A := by simpa [Matrix.IsHermitian] using hAh
    have hB' : B.transpose = B := by simpa [Matrix.IsHermitian] using hBh
    change (a • A + b • B).conjTranspose = a • A + b • B
    simp [hA', hB']
  have hx_conv : max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0 ≤
      a * max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0 + b * max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 B) 0 := by
    have hconv := (DifferentialGeometry.Analysis.Convex.convex_negPart_minimumRayleighQuotient3.2) (x := A) (y := B)
      (by trivial) (by trivial) (a := a) (b := b) ha.le hb.le hab
    simpa [C, smul_eq_mul] using hconv
  have hbar_conv : hamiltonIveyConvexBarrier K τ
      (a * max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0 + b * max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 B) 0) ≤ C.trace := by
    have hbarA : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0) ≤ A.trace := by
      simpa [DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue hAh] using hAbar
    have hbarB : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 B) 0) ≤ B.trace := by
      simpa [DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue hBh] using hBbar
    have hconv := ((hamiltonIveyConvexBarrier_convexOn (K := K) (τ := τ) hK).2)
      (x := max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0) (y := max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 B) 0)
      (by exact (le_max_right (a := -DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) (b := 0)))
      (by exact (le_max_right (a := -DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 B) (b := 0)))
      (a := a) (b := b) ha.le hb.le hab
    have hmul : a * hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0) +
          b * hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 B) 0) ≤ C.trace := by
      dsimp [C]
      have hsum := add_le_add (mul_le_mul_of_nonneg_left hbarA ha.le) (mul_le_mul_of_nonneg_left hbarB hb.le)
      simpa [Matrix.trace_add, Matrix.trace_smul, add_comm, add_left_comm, add_assoc] using hsum
    exact le_trans hconv hmul
  have hmain : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0) ≤ C.trace := by
    let x0 : ℝ := K / (1 + 2 * K * τ)
    have hden : 0 < 1 + 2 * K * τ := by
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    by_cases hx0_le : x0 ≤ max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0
    · have hmono := hamiltonIveyConvexBarrier_monotoneOn_of_ge_subregion hK hτ
      have hle1 := hmono hx0_le (le_trans hx0_le hx_conv) hx_conv
      exact le_trans hle1 hbar_conv
    · have hlt : max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0 < x0 := lt_of_not_ge hx0_le
      have hC0x : 0 ≤ max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0 := le_max_right _ _
      have hsub : max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0 ≤ K / (1 + 2 * K * τ) := le_of_lt hlt
      have hraw : hamiltonIveyBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0) ≤
          -3 * max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0 :=
        hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion hK hden hC0x hsub
      have htrace_ge : -3 * max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0 ≤ C.trace := by
        simpa using (DifferentialGeometry.Analysis.Convex.neg_three_mul_negPart_minimumRayleighQuotient3_le_trace hCh)
      have hA_scalar : scalarSectionalLowerBarrier3 K τ ≤ A.trace := by
        have hbar := (scalarSectionalLowerBarrier3_le_hamiltonIveyConvexBarrier K τ
          (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 A) 0)).trans (by
            simpa [DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue hAh] using hAbar)
        exact hbar
      have hB_scalar : scalarSectionalLowerBarrier3 K τ ≤ B.trace := by
        have hbar := (scalarSectionalLowerBarrier3_le_hamiltonIveyConvexBarrier K τ
          (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 B) 0)).trans (by
            simpa [DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue hBh] using hBbar)
        exact hbar
      have hscalar_le : scalarSectionalLowerBarrier3 K τ ≤ C.trace := by
        dsimp [C]
        have hsum := add_le_add (mul_le_mul_of_nonneg_left hA_scalar ha.le)
          (mul_le_mul_of_nonneg_left hB_scalar hb.le)
        have hcalc : a * scalarSectionalLowerBarrier3 K τ + b * scalarSectionalLowerBarrier3 K τ =
            scalarSectionalLowerBarrier3 K τ := by
          rw [← add_mul, hab, one_mul]
        have hsum' : scalarSectionalLowerBarrier3 K τ ≤ a * A.trace + b * B.trace := by
          rwa [hcalc] at hsum
        simpa [Matrix.trace_add, Matrix.trace_smul] using hsum'
      have hconv_le : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3 C) 0) ≤ C.trace := by
        unfold hamiltonIveyConvexBarrier
        exact max_le hscalar_le (le_trans hraw htrace_ge)
      exact hconv_le
  refine ⟨hCh, ?_⟩
  simpa [C, DifferentialGeometry.Analysis.Convex.minimumRayleighQuotient3_eq_min_eigenvalue hCh] using hmain

noncomputable def hamiltonIveyConvexMatrixRegionEuclidean (K τ : Real) :
    Set (EuclideanSpace ℝ (Fin 3 × Fin 3)) :=
  {A | euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ}

theorem mem_hamiltonIveyConvexMatrixRegionEuclidean_iff (K τ : Real)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    A ∈ hamiltonIveyConvexMatrixRegionEuclidean K τ ↔
      euclideanToMatrix A ∈ hamiltonIveyConvexMatrixRegion K τ := by
  rfl

theorem nonempty_hamiltonIveyConvexMatrixRegionEuclidean {K τ : Real}
    (hK : 0 < K) (hτ : 0 ≤ τ) :
    (hamiltonIveyConvexMatrixRegionEuclidean K τ).Nonempty := by
  rcases nonempty_hamiltonIveyConvexMatrixRegion hK hτ with ⟨A, hA⟩
  refine ⟨matrixToEuclidean A, ?_⟩
  rw [mem_hamiltonIveyConvexMatrixRegionEuclidean_iff]
  simpa using hA

theorem isClosed_hamiltonIveyConvexMatrixRegionEuclidean {K τ : Real}
    (hK : 0 < K) :
    IsClosed (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
  have hf : Continuous (euclideanToMatrix :
      EuclideanSpace ℝ (Fin 3 × Fin 3) → Matrix (Fin 3) (Fin 3) ℝ) :=
    (matrixEuclideanLinearIsometryEquiv
      (m := Fin 3) (n := Fin 3)).symm.continuous
  rw [hamiltonIveyConvexMatrixRegionEuclidean]
  change IsClosed (euclideanToMatrix ⁻¹' hamiltonIveyConvexMatrixRegion K τ)
  exact IsClosed.preimage hf (isClosed_hamiltonIveyConvexMatrixRegion hK)

theorem convex_hamiltonIveyConvexMatrixRegionEuclidean {K τ : Real}
    (hK : 0 < K) (hτ : 0 ≤ τ) :
    Convex Real (hamiltonIveyConvexMatrixRegionEuclidean K τ) := by
  let f : EuclideanSpace ℝ (Fin 3 × Fin 3) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    { toFun := euclideanToMatrix
      map_add' := euclideanToMatrix_add
      map_smul' := euclideanToMatrix_smul }
  have hpre : Convex Real (f ⁻¹' hamiltonIveyConvexMatrixRegion K τ) :=
    Convex.linear_preimage (convex_hamiltonIveyConvexMatrixRegion hK hτ) f
  simpa [hamiltonIveyConvexMatrixRegionEuclidean, f] using hpre


lemma continuousOn_hamiltonIveyBarrier_nonneg_time
    {K T : ℝ} (hK : 0 < K) :
    ContinuousOn (fun p : ℝ × ℝ => hamiltonIveyBarrier K p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Ici 0) := by
  let s : Set (ℝ × ℝ) := Set.Icc 0 T ×ˢ Set.Ici 0
  have hX : ContinuousOn (fun p : ℝ × ℝ => p.2) s := continuousOn_snd
  have hlogX : ContinuousOn (fun p : ℝ × ℝ => p.2 * Real.log p.2) s := by
    simpa using (Real.continuous_mul_log.comp_continuousOn (s := s) (f := fun p : ℝ × ℝ => p.2) continuousOn_snd)
  have hlogK : ContinuousOn (fun p : ℝ × ℝ => p.2 * Real.log K) s := by
    simpa [mul_comm] using (continuousOn_snd.mul (continuousOn_const (s := s) (c := Real.log K)))
  have hlogD : ContinuousOn (fun p : ℝ × ℝ => p.2 * Real.log (1 + 2 * K * p.1)) s := by
    have hD : ContinuousOn (fun p : ℝ × ℝ => 1 + 2 * K * p.1) s := by
      simpa [add_comm] using
        ((continuousOn_const (s := s) (c := (1 : ℝ))).add
          ((continuousOn_const (s := s) (c := (2 * K : ℝ))).mul (continuousOn_fst (s := s))))
    have hlog : ContinuousOn (fun p : ℝ × ℝ => Real.log (1 + 2 * K * p.1)) s := by
      refine ContinuousOn.log (α := ℝ × ℝ) hD ?_
      intro p hp
      have hτ : 0 ≤ p.1 := hp.1.1
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    exact continuousOn_snd.mul hlog
  have hlin : ContinuousOn (fun p : ℝ × ℝ => 3 * p.2) s := by
    simpa [mul_comm] using (continuousOn_snd.mul (continuousOn_const (s := s) (c := (3 : ℝ))))
  have hsum1 : ContinuousOn (fun p : ℝ × ℝ =>
      p.2 * Real.log p.2 - p.2 * Real.log K + p.2 * Real.log (1 + 2 * K * p.1) - 3 * p.2) s := by
    exact (((hlogX.sub hlogK).add hlogD).sub hlin)
  have hEq : (fun p : ℝ × ℝ => hamiltonIveyBarrier K p.1 p.2) =
      fun p : ℝ × ℝ =>
        p.2 * Real.log p.2 - p.2 * Real.log K + p.2 * Real.log (1 + 2 * K * p.1) - 3 * p.2 := by
    funext p
    unfold hamiltonIveyBarrier
    by_cases hX0 : p.2 = 0
    · simp [hX0]
    · have hlog : Real.log (p.2 / K) = Real.log p.2 - Real.log K :=
        Real.log_div hX0 hK.ne'
      rw [hlog]
      ring
  rw [hEq]
  exact hsum1

lemma continuousOn_hamiltonIveyConvexBarrier_time_nonneg
    {K T : ℝ} (hK : 0 < K) :
    ContinuousOn (fun p : ℝ × ℝ => hamiltonIveyConvexBarrier K p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Ici 0) := by
  let s : Set (ℝ × ℝ) := Set.Icc 0 T ×ˢ Set.Ici 0
  unfold hamiltonIveyConvexBarrier
  apply ContinuousOn.sup
  · unfold scalarSectionalLowerBarrier3
    have hnum : ContinuousOn (fun p : ℝ × ℝ => -3 * K) s := continuousOn_const
    have hden : ContinuousOn (fun p : ℝ × ℝ => 1 + 4 * K * p.1) s := by
      simpa [add_comm] using
        ((continuousOn_const (s := s) (c := (1 : ℝ))).add
          ((continuousOn_const (s := s) (c := (4 * K : ℝ))).mul (continuousOn_fst (s := s))))
    refine hnum.div hden ?_
    intro p hp
    have hτ : 0 ≤ p.1 := hp.1.1
    have hpos : 0 < 1 + 4 * K * p.1 := by
      nlinarith [mul_nonneg (mul_pos (by norm_num : (0:ℝ) < 4) hK).le hτ]
    exact ne_of_gt hpos
  · exact continuousOn_hamiltonIveyBarrier_nonneg_time hK

end DifferentialGeometry.Geometry.Curvature.DimensionThree
