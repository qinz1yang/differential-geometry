import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import DifferentialGeometry.Analysis.Convex.MatrixRayleigh
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

open scoped BigOperators

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
  {A | ∃ hA : A.IsHermitian,
    0 ≤ max (-hA.eigenvalues₀ 2) 0 ∧
      hamiltonIveyConvexBarrier K τ (max (-hA.eigenvalues₀ 2) 0) ≤ A.trace}

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
  let hM : (0 : Matrix (Fin 3) (Fin 3) Real).IsHermitian := by simp
  refine ⟨hM, ?_, ?_⟩
  · exact le_max_right _ _
  · unfold hamiltonIveyConvexBarrier
    have heig₂ : hM.eigenvalues₀ 2 = 0 := by
      have heig : hM.eigenvalues = 0 :=
        (Matrix.IsHermitian.eigenvalues_eq_zero_iff (hA := hM)).mpr rfl
      let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
      have h0 : hM.eigenvalues (e 2) = 0 := congrFun heig (e 2)
      have hdef : hM.eigenvalues (e 2) = hM.eigenvalues₀ (e.symm (e 2)) := rfl
      rw [hdef, Equiv.symm_apply_apply] at h0
      exact h0
    have hbar : hamiltonIveyBarrier K τ (max (-hM.eigenvalues₀ 2) 0) ≤ 0 := by
      rw [heig₂]
      simp [hamiltonIveyBarrier]
    simpa using (max_le (by simpa using hscalar) hbar)

theorem diagonal_eigenvalues₀_eq_of_antitone
    (d : Fin 3 → Real) (hd : Antitone d) :
    (Matrix.isHermitian_diagonal d).eigenvalues₀ = d := by
  let hA : (Matrix.diagonal d).IsHermitian := Matrix.isHermitian_diagonal d
  have hchar : (Matrix.diagonal d).charpoly = ∏ i : Fin 3, (Polynomial.X - Polynomial.C (d i)) :=
    Matrix.charpoly_diagonal d
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hchar] at hsort
  have hprod_ne : (∏ i : Fin 3, (Polynomial.X - Polynomial.C (d i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Polynomial.X_sub_C_ne_zero (d i)
  have hroots : (∏ i : Fin 3, (Polynomial.X - Polynomial.C (d i))).roots =
      (Finset.univ.val.bind fun i : Fin 3 => (Polynomial.X - Polynomial.C (d i)).roots) := by
    simpa using Polynomial.roots_prod (fun i : Fin 3 => (Polynomial.X - Polynomial.C (d i)))
      Finset.univ hprod_ne
  rw [hroots] at hsort
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at hsort
  change ((Finset.univ.val.map d).sort (· ≥ ·)) = List.ofFn hA.eigenvalues₀ at hsort
  have hd_sorted : (Finset.univ.val.map d).sort (· ≥ ·) = List.ofFn d := by
    change [d 0, d 1, d 2].mergeSort (fun x1 x2 => decide (x2 ≤ x1)) = [d 0, d 1, d 2]
    have hpair : List.Pairwise (· ≥ ·) [d 0, d 1, d 2] := by
      have hs := Antitone.sortedGE_ofFn hd
      simpa using hs.pairwise
    change [d 0, d 1, d 2].mergeSort ((· ≥ ·) · ·) = [d 0, d 1, d 2]
    exact List.mergeSort_eq_self (r := (· ≥ ·)) hpair
  rw [hd_sorted] at hsort
  exact List.ofFn_inj.mp hsort.symm

private theorem eigenvalues₀_eq_of_charpoly_eq_real
    {A B : Matrix (Fin 3) (Fin 3) Real} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hchar : A.charpoly = B.charpoly) :
    hA.eigenvalues₀ = hB.eigenvalues₀ := by
  have hsA := hA.sort_roots_charpoly_eq_eigenvalues₀
  have hsB := hB.sort_roots_charpoly_eq_eigenvalues₀
  rw [← hchar] at hsB
  have hlist : List.ofFn hA.eigenvalues₀ = List.ofFn hB.eigenvalues₀ :=
    hsA.symm.trans hsB
  exact List.ofFn_inj.mp hlist

private theorem hamiltonIveyConvexMatrixRegion_conj_mem
    {K τ : Real} {A Q : Matrix (Fin 3) (Fin 3) Real}
    (hQ2 : Q * Q.transpose = 1)
    (hA : A ∈ hamiltonIveyConvexMatrixRegion K τ) :
    Q.transpose * A * Q ∈ hamiltonIveyConvexMatrixRegion K τ := by
  rcases hA with ⟨hAh, hX, hbar⟩
  refine ⟨?_, ?_, ?_⟩
  · have hconj : (Q.conjTranspose * A * Q).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul Q hAh
    simpa using hconj
  · have hchar : (Q.transpose * A * Q).charpoly = A.charpoly := by
      have hmul := Matrix.charpoly_mul_comm Q.transpose (A * Q)
      rw [show Q.transpose * (A * Q) = Q.transpose * A * Q by simp [Matrix.mul_assoc]] at hmul
      rw [hmul]
      rw [show (A * Q) * Q.transpose = A * (Q * Q.transpose) by simp [Matrix.mul_assoc]]
      rw [hQ2, Matrix.mul_one]
    have hB : (Q.transpose * A * Q).IsHermitian := by
      have hconj : (Q.conjTranspose * A * Q).IsHermitian :=
        Matrix.isHermitian_conjTranspose_mul_mul Q hAh
      simpa using hconj
    have heig := eigenvalues₀_eq_of_charpoly_eq_real hB hAh hchar
    simp [heig, hX]
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
    rw [htrace, heig]
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

def hamiltonIveyConvexMatrixRegionViolation (K τ : Real)
    (A : Matrix (Fin 3) (Fin 3) Real) : Prop :=
  A.IsHermitian ∧
    0 ≤ max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0 ∧
      hamiltonIveyConvexBarrier K τ
          (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0) ≤ A.trace

theorem hamiltonIveyConvexMatrixRegion_eq_violation (K τ : Real) :
    hamiltonIveyConvexMatrixRegion K τ =
      {A : Matrix (Fin 3) (Fin 3) Real | hamiltonIveyConvexMatrixRegionViolation K τ A} := by
  ext A
  constructor
  · rintro ⟨hA, hX, hbar⟩
    refine ⟨hA, ?_, ?_⟩
    · rw [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hA]
      exact hX
    · rw [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hA]
      exact hbar
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · rw [← DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min h.1]
      exact h.2.1
    · rw [← DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min h.1]
      exact h.2.2

theorem isClosed_hamiltonIveyConvexMatrixRegion
    {K τ : Real} (hK : 0 < K) :
    IsClosed (hamiltonIveyConvexMatrixRegion K τ) := by
  rw [hamiltonIveyConvexMatrixRegion_eq_violation]
  let X : Matrix (Fin 3) (Fin 3) Real → Real := fun A =>
    max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0
  have hXcont : Continuous X := by
    dsimp [X]
    exact DifferentialGeometry.Analysis.Convex.continuous_sectionalRayleighMin3.neg.max
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
    ({A : Matrix (Fin 3) (Fin 3) Real | 0 ≤ X A} ∩
      {A : Matrix (Fin 3) (Fin 3) Real | hamiltonIveyConvexBarrier K τ (X A) ≤ A.trace}))
  have hfirst : IsClosed {A : Matrix (Fin 3) (Fin 3) Real | 0 ≤ X A} :=
    isClosed_le continuous_const hXcont
  have hsecond : IsClosed {A : Matrix (Fin 3) (Fin 3) Real |
      hamiltonIveyConvexBarrier K τ (X A) ≤ A.trace} :=
    isClosed_le ((continuous_hamiltonIveyConvexBarrier hK).comp hXcont)
      (by unfold Matrix.trace; fun_prop)
  exact hHermClosed.inter (hfirst.inter hsecond)



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
  refine ⟨Matrix.isHermitian_diagonal d, ?_, ?_⟩
  · exact le_max_right _ _
  · have htrace : (Matrix.diagonal d).trace = sectionalSum3 σ σ σ := by
      rw [Matrix.trace_diagonal]
      simp [d, sectionalSum3]
      ring
    have heig₂ : (Matrix.isHermitian_diagonal d).eigenvalues₀ 2 = σ := by
      rw [heig]
    rw [htrace]
    simpa [d, heig₂, pinchHeight3] using hbar

theorem diagonal_constant_mem_hamiltonIveyConvexMatrixRegion_K_one
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

theorem supportLine_reaction_derivative_nonneg
    {l1 l2 l3 a : Real} (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (ha : 0 < a)
    (hboundary : l1 + l2 + a * l3 = 0) :
    0 ≤ reactionSectionalSum3 l1 l2 l3 - (a - 1) * reactionPinchHeight3 l1 l2 l3 := by
  let u : Real := l1 - l2
  let v : Real := l2 - l3
  let z : Real := l3
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith
  have hv : 0 ≤ v := by
    dsimp [v]
    linarith
  have hz : z = -(u + 2 * v) / (a + 2) := by
    dsimp [u, v, z]
    have hden : a + 2 ≠ 0 := by nlinarith
    field_simp [hden]
    nlinarith
  have hcalc :
      reactionSectionalSum3 l1 l2 l3 - (a - 1) * reactionPinchHeight3 l1 l2 l3 =
        2 * (a ^ 2 * u * v + a ^ 2 * v ^ 2 + u ^ 2) / (a + 2) := by
    unfold reactionSectionalSum3 reactionPinchHeight3
      DifferentialGeometry.Dim3Reaction.sectionalReaction12
      DifferentialGeometry.Dim3Reaction.sectionalReaction13
      DifferentialGeometry.Dim3Reaction.sectionalReaction23
    have hl1 : l1 = z + v + u := by
      dsimp [u, v, z]
      ring
    have hl2 : l2 = z + v := by
      dsimp [u, v, z]
      ring
    have hl3 : l3 = z := by
      rfl
    rw [hl1, hl2, hl3, hz]
    field_simp [show a + 2 ≠ 0 by nlinarith]
    ring
  rw [hcalc]
  have hdenpos : 0 < a + 2 := by nlinarith
  have hterm : 0 ≤ a ^ 2 * u * v + a ^ 2 * v ^ 2 + u ^ 2 := by
    nlinarith [sq_nonneg (a * u), sq_nonneg (a * v), sq_nonneg u,
      mul_nonneg (sq_nonneg a) (mul_nonneg hu hv)]
  exact div_nonneg (mul_nonneg two_pos.le hterm) hdenpos.le

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


private theorem linear_log_lower_bound
    {a b y : Real} (ha : 0 < a) (hy : 0 < y) :
    -a * Real.exp (b / a - 1) ≤ y * (a * Real.log y - b) := by
  let E : Real := Real.exp (b / a - 1)
  let z : Real := y / E
  have hE : 0 < E := by
    dsimp [E]
    exact Real.exp_pos _
  have hz : 0 < z := by
    dsimp [z]
    exact div_pos hy hE
  have hlog : 1 - z⁻¹ ≤ Real.log z :=
    Real.one_sub_inv_le_log_of_pos hz
  have hzlog : z - 1 ≤ z * Real.log z := by
    have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt hz)
    have hcalc : z * (1 - z⁻¹) = z - 1 := by
      field_simp [hz.ne']
    rwa [hcalc] at hm
  have hnonneg : 0 ≤ 1 - z + z * Real.log z := by
    nlinarith
  have hscaled : 0 ≤ a * E * (1 - z + z * Real.log z) := by
    exact mul_nonneg (mul_pos ha hE).le hnonneg
  have hineq : -a * E ≤ a * E * (z * Real.log z - z) := by
    nlinarith
  have hz_eq : E * z = y := by
    dsimp [z]
    field_simp [hE.ne']
  have hlogE : Real.log E = b / a - 1 := by
    dsimp [E]
    exact Real.log_exp _
  have hcalc : a * E * (z * Real.log z - z) = y * (a * Real.log y - b) := by
    rw [← hz_eq]
    have hlogmul : Real.log (E * z) = b / a - 1 + Real.log z := by
      rw [Real.log_mul hE.ne' hz.ne', hlogE]
    rw [hlogmul]
    field_simp [ha.ne']
    ring
  rwa [hcalc] at hineq

theorem pinchHeight_le_linear_sectionalSum_of_barrier
    {K τ X S δ : Real} (hK : 0 < K) (hδ : 0 < δ) (hτ : 0 ≤ τ)
    (hX : 0 ≤ X)
    (hbarrier : hamiltonIveyBarrier K τ X ≤ S) :
    X ≤ 2 * δ * S + 2 * δ * K * Real.exp (2 + (2 * δ)⁻¹) := by
  by_cases hX0 : X = 0
  · subst hX0
    have hS : 0 ≤ S := by
      simpa [hamiltonIveyBarrier] using hbarrier
    have hC : 0 ≤ 2 * δ * K * Real.exp (2 + (2 * δ)⁻¹) := by
      positivity
    nlinarith
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
    let y : Real := X / K
    have hy : 0 < y := div_pos hXpos hK
    have hyK : X = K * y := by
      dsimp [y]
      field_simp [hK.ne']
    have hlogD : 0 ≤ Real.log (1 + 2 * K * τ) := by
      apply Real.log_nonneg
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    let a : Real := 2 * δ
    have ha : 0 < a := mul_pos two_pos hδ
    let B : Real := 6 * δ + 1 - a * Real.log (1 + 2 * K * τ)
    have hBle : B ≤ 6 * δ + 1 := by
      dsimp [B, a]
      nlinarith [mul_nonneg (le_of_lt ha) hlogD]
    have hlemma := linear_log_lower_bound (a := a) (b := B) ha hy
    have hexp_le :
        Real.exp (B / a - 1) ≤ Real.exp (2 + (2 * δ)⁻¹) := by
      apply Real.exp_le_exp.mpr
      have h1 : B / a ≤ (6 * δ + 1) / a :=
        div_le_div_of_nonneg_right hBle (le_of_lt ha)
      have h2 : (6 * δ + 1) / a = 3 + (2 * δ)⁻¹ := by
        dsimp [a]
        field_simp [hδ.ne']
        ring
      nlinarith
    have hlemma_scaled :
        -K * a * Real.exp (2 + (2 * δ)⁻¹) ≤
          K * (y * (a * Real.log y - B)) := by
      have hmul := mul_le_mul_of_nonneg_left hlemma (le_of_lt hK)
      have hexpmul := mul_le_mul_of_nonneg_left hexp_le
        (mul_nonneg (le_of_lt hK) (le_of_lt ha))
      nlinarith [hmul, hexpmul]
    have hmain : 0 ≤
        K * (y * (a * Real.log y - B)) +
          K * a * Real.exp (2 + (2 * δ)⁻¹) := by
      nlinarith
    have hbar_scaled :
        K * (y * (a * Real.log y - B)) ≤ 2 * δ * S - X := by
      have hE_eq :
          K * (y * (a * Real.log y - B)) =
            2 * δ * hamiltonIveyBarrier K τ X - X := by
        unfold hamiltonIveyBarrier
        dsimp [y, a, B]
        have hlogX : Real.log (X / K) = Real.log y := by
          dsimp [y]
        rw [hlogX]
        field_simp [hK.ne', hδ.ne']
        ring
      have hbar_mul := mul_le_mul_of_nonneg_left hbarrier
        (mul_nonneg two_pos.le hδ.le)
      nlinarith [hE_eq, hbar_mul]
    have hgoal : X ≤ 2 * δ * S + K * a * Real.exp (2 + (2 * δ)⁻¹) := by
      nlinarith [hmain, hbar_scaled]
    dsimp [a] at hgoal
    nlinarith

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
        (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0) ≤
      A.trace := by
  rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hA
  exact (hamiltonIveyTangentLine_le_hamiltonIveyConvexBarrier
    (K := K) (τ := τ) (a := a)
    (X := max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0)
    hK hτ (le_max_right _ _)).trans hA.2.2


theorem mem_hamiltonIveyConvexMatrixRegion_of_forall_tangent_halfspace
    {K τ : Real} {A : Matrix (Fin 3) (Fin 3) Real}
    (hK : 0 < K) (hτ : 0 ≤ τ) (hA : A.IsHermitian)
    (htrace0 : 0 ≤ A.trace)
    (hscalar : scalarSectionalLowerBarrier3 K τ ≤ A.trace)
    (hforall : ∀ a : Real,
      hamiltonIveyTangentLine K τ a
          (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0) ≤
        A.trace) :
    A ∈ hamiltonIveyConvexMatrixRegion K τ := by
  rw [hamiltonIveyConvexMatrixRegion_eq_violation]
  refine ⟨hA, le_max_right _ _, ?_⟩
  let X : Real := max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0
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
  rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hA hB ⊢
  rcases hA with ⟨hAh, hA0, hAbar⟩
  rcases hB with ⟨hBh, hB0, hBbar⟩
  let C : Matrix (Fin 3) (Fin 3) ℝ := a • A + b • B
  have hCh : C.IsHermitian := by
    have hA' : A.transpose = A := by simpa [Matrix.IsHermitian] using hAh
    have hB' : B.transpose = B := by simpa [Matrix.IsHermitian] using hBh
    change (a • A + b • B).conjTranspose = a • A + b • B
    simp [hA', hB']
  have hC0 : 0 ≤ max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0 := le_max_right _ _
  have hx_conv : max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0 ≤
      a * max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0 + b * max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 B) 0 := by
    have hconv := (DifferentialGeometry.Analysis.Convex.convex_sectionalRayleighPinchHeight3.2) (x := A) (y := B)
      (by trivial) (by trivial) (a := a) (b := b) ha.le hb.le hab
    simpa [C, smul_eq_mul] using hconv
  have hbar_conv : hamiltonIveyConvexBarrier K τ
      (a * max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0 + b * max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 B) 0) ≤ C.trace := by
    have hbarA : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0) ≤ A.trace := by
      simpa [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hAh] using hAbar
    have hbarB : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 B) 0) ≤ B.trace := by
      simpa [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hBh] using hBbar
    have hconv := ((hamiltonIveyConvexBarrier_convexOn (K := K) (τ := τ) hK).2)
      (x := max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0) (y := max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 B) 0)
      (by exact (le_max_right (a := -DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) (b := 0)))
      (by exact (le_max_right (a := -DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 B) (b := 0)))
      (a := a) (b := b) ha.le hb.le hab
    have hmul : a * hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0) +
          b * hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 B) 0) ≤ C.trace := by
      dsimp [C]
      have hsum := add_le_add (mul_le_mul_of_nonneg_left hbarA ha.le) (mul_le_mul_of_nonneg_left hbarB hb.le)
      simpa [Matrix.trace_add, Matrix.trace_smul, add_comm, add_left_comm, add_assoc] using hsum
    exact le_trans hconv hmul
  have hmain : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0) ≤ C.trace := by
    let x0 : ℝ := K / (1 + 2 * K * τ)
    have hden : 0 < 1 + 2 * K * τ := by
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    by_cases hx0_le : x0 ≤ max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0
    · have hmono := hamiltonIveyConvexBarrier_monotoneOn_of_ge_subregion hK hτ
      have hle1 := hmono hx0_le (le_trans hx0_le hx_conv) hx_conv
      exact le_trans hle1 hbar_conv
    · have hlt : max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0 < x0 := lt_of_not_ge hx0_le
      have hC0x : 0 ≤ max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0 := le_max_right _ _
      have hsub : max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0 ≤ K / (1 + 2 * K * τ) := le_of_lt hlt
      have hraw : hamiltonIveyBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0) ≤
          -3 * max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0 :=
        hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion hK hden hC0x hsub
      have htrace_ge : -3 * max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0 ≤ C.trace := by
        simpa using (DifferentialGeometry.Analysis.Convex.neg_three_mul_sectionalRayleighPinch_le_trace hCh)
      have hA_scalar : scalarSectionalLowerBarrier3 K τ ≤ A.trace := by
        have hbar := (scalarSectionalLowerBarrier3_le_hamiltonIveyConvexBarrier K τ
          (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0)).trans (by
            simpa [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hAh] using hAbar)
        exact hbar
      have hB_scalar : scalarSectionalLowerBarrier3 K τ ≤ B.trace := by
        have hbar := (scalarSectionalLowerBarrier3_le_hamiltonIveyConvexBarrier K τ
          (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 B) 0)).trans (by
            simpa [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hBh] using hBbar)
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
      have hconv_le : hamiltonIveyConvexBarrier K τ (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 C) 0) ≤ C.trace := by
        unfold hamiltonIveyConvexBarrier
        exact max_le hscalar_le (le_trans hraw htrace_ge)
      exact hconv_le
  refine ⟨hCh, hC0, ?_⟩
  simpa [C, DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hCh] using hmain


def hamiltonIveyConvexMatrixSlab (K T : ℝ) :
    Set (WithLp 2 (Matrix (Fin 3) (Fin 3) ℝ × ℝ)) :=
  {q | (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧
    (WithLp.ofLp q).1 ∈ hamiltonIveyConvexMatrixRegion K (WithLp.ofLp q).2}

theorem nonempty_hamiltonIveyConvexMatrixSlab
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T) :
    (hamiltonIveyConvexMatrixSlab K T).Nonempty := by
  refine ⟨WithLp.toLp 2 ((0 : Matrix (Fin 3) (Fin 3) ℝ), (0 : ℝ)), ?_⟩
  rw [hamiltonIveyConvexMatrixSlab]
  change (0 : ℝ) ∈ Set.Icc 0 T ∧
    (0 : Matrix (Fin 3) (Fin 3) ℝ) ∈ hamiltonIveyConvexMatrixRegion K 0
  constructor
  · simp [hT]
  · rw [hamiltonIveyConvexMatrixRegion_eq_violation]
    constructor
    · simp
    constructor
    · simp [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3]
    · have hscalar : scalarSectionalLowerBarrier3 K 0 ≤ 0 := by
        unfold scalarSectionalLowerBarrier3
        have hden : 0 < 1 + 4 * K * 0 := by positivity
        have hnonpos : -(3 * K) ≤ 0 := by nlinarith
        simpa using div_nonpos_of_nonpos_of_nonneg hnonpos hden.le
      have hbar : hamiltonIveyBarrier K 0 (0 : ℝ) ≤ 0 := by
        unfold hamiltonIveyBarrier
        simp
      unfold hamiltonIveyConvexBarrier
      simp only [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_zero,
        Matrix.trace_zero, sup_le_iff]
      have hbar' : hamiltonIveyBarrier K 0 (max (-(0 : ℝ)) 0) ≤ 0 := by
        simpa using hbar
      exact ⟨hscalar, hbar'⟩


@[simp]
theorem mem_hamiltonIveyConvexMatrixSlab {K T : ℝ}
    {q : WithLp 2 (Matrix (Fin 3) (Fin 3) ℝ × ℝ)} :
    q ∈ hamiltonIveyConvexMatrixSlab K T ↔
      (WithLp.ofLp q).2 ∈ Set.Icc 0 T ∧
        (WithLp.ofLp q).1 ∈ hamiltonIveyConvexMatrixRegion K (WithLp.ofLp q).2 := by
  rfl

theorem hamiltonIveyConvexMatrixSlab_orthogonal_conj
    {K T : ℝ} {q : WithLp 2 (Matrix (Fin 3) (Fin 3) ℝ × ℝ)}
    {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ1 : Q.transpose * Q = 1)
    (hQ2 : Q * Q.transpose = 1)
    (hq : q ∈ hamiltonIveyConvexMatrixSlab K T) :
    WithLp.toLp 2 (Q.transpose * (WithLp.ofLp q).1 * Q, (WithLp.ofLp q).2) ∈
      hamiltonIveyConvexMatrixSlab K T := by
  rw [mem_hamiltonIveyConvexMatrixSlab] at hq ⊢
  constructor
  · exact hq.1
  · exact (hamiltonIveyConvexMatrixRegion_orthogonal_conj (K := K)
      (τ := (WithLp.ofLp q).2) hQ1 hQ2).1 hq.2


theorem hamiltonIveyConvexMatrixSlab_subset_time {K T : ℝ} :
    hamiltonIveyConvexMatrixSlab K T ⊆
      {q : WithLp 2 (Matrix (Fin 3) (Fin 3) ℝ × ℝ) | (WithLp.ofLp q).2 ∈ Set.Icc 0 T} := by
  intro q hq
  exact hq.1

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

theorem isClosed_hamiltonIveyConvexMatrixSlab
    {K T : ℝ} (hK : 0 < K) :
    IsClosed (hamiltonIveyConvexMatrixSlab K T) := by
  let Q := WithLp 2 (Matrix (Fin 3) (Fin 3) ℝ × ℝ)
  let X : Matrix (Fin 3) (Fin 3) ℝ → ℝ := fun A => max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 A) 0
  have hA_cont : Continuous (fun q : Q => (WithLp.ofLp q).1) :=
    WithLp.continuous_fst (p := 2) (α := Matrix (Fin 3) (Fin 3) ℝ) (β := ℝ)
  have hτ_cont : Continuous (fun q : Q => (WithLp.ofLp q).2) :=
    WithLp.continuous_snd (p := 2) (α := Matrix (Fin 3) (Fin 3) ℝ) (β := ℝ)
  have hX_cont : Continuous (fun q : Q => X (WithLp.ofLp q).1) := by
    dsimp [X]
    exact (DifferentialGeometry.Analysis.Convex.continuous_sectionalRayleighMin3.neg.max continuous_const).comp hA_cont
  have hT_closed : IsClosed {q : Q | (WithLp.ofLp q).2 ∈ Set.Icc 0 T} :=
    IsClosed.preimage hτ_cont (isClosed_Icc : IsClosed (Set.Icc (0:ℝ) T))
  have hH_closed : IsClosed {q : Q | (WithLp.ofLp q).1.IsHermitian} := by
    have hset : {A : Matrix (Fin 3) (Fin 3) ℝ | A.IsHermitian} = {A | A.transpose = A} := by
      ext A; simp [Matrix.IsHermitian]
    have hclosedA : IsClosed ({A : Matrix (Fin 3) (Fin 3) ℝ | A.IsHermitian}) := by
      rw [hset]
      have htrans : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.transpose) := by fun_prop
      exact isClosed_eq htrans continuous_id
    exact IsClosed.preimage hA_cont hclosedA
  have hD_closed : IsClosed {q : Q | 0 ≤ X (WithLp.ofLp q).1} :=
    isClosed_le continuous_const hX_cont
  let S : Set Q := {q | (WithLp.ofLp q).2 ∈ Set.Icc 0 T}
  let D : Set Q := {q | 0 ≤ X (WithLp.ofLp q).1}
  have hSD_closed : IsClosed (S ∩ D) := hT_closed.inter hD_closed
  have hbar_cont : ContinuousOn
      (fun q : Q => hamiltonIveyConvexBarrier K (WithLp.ofLp q).2 (X (WithLp.ofLp q).1) -
        (WithLp.ofLp q).1.trace) (S ∩ D) := by
    have hpair : ContinuousOn (fun q : Q => ((WithLp.ofLp q).2, X (WithLp.ofLp q).1)) (S ∩ D) := by
      have hτ : ContinuousOn (fun q : Q => (WithLp.ofLp q).2) (S ∩ D) := hτ_cont.continuousOn
      have hXq : ContinuousOn (fun q : Q => X (WithLp.ofLp q).1) (S ∩ D) := hX_cont.continuousOn
      exact hτ.prodMk hXq
    have hmap : Set.MapsTo (fun q : Q => ((WithLp.ofLp q).2, X (WithLp.ofLp q).1))
        (S ∩ D) (Set.Icc 0 T ×ˢ Set.Ici 0) := by
      intro q hq
      exact ⟨hq.1, hq.2⟩
    have hbar := (continuousOn_hamiltonIveyConvexBarrier_time_nonneg (K := K) (T := T) hK).comp hpair hmap
    have htr : ContinuousOn (fun q : Q => (WithLp.ofLp q).1.trace) (S ∩ D) := by
      have htrA : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.trace) := by
        unfold Matrix.trace
        fun_prop
      exact htrA.comp_continuousOn hA_cont.continuousOn
    exact hbar.sub htr
  have hB_closed : IsClosed (S ∩ D ∩ {q : Q |
      hamiltonIveyConvexBarrier K (WithLp.ofLp q).2 (X (WithLp.ofLp q).1) ≤
        (WithLp.ofLp q).1.trace}) := by
    have h := ContinuousOn.preimage_isClosed_of_isClosed hbar_cont hSD_closed
      (isClosed_Iic : IsClosed (Set.Iic (0 : ℝ)))
    simpa [Set.preimage, Set.Iic] using h
  -- Now show slab equals H ∩ (S ∩ D ∩ B) (D redundant but okay)
  have hset : hamiltonIveyConvexMatrixSlab K T =
      {q : Q | (WithLp.ofLp q).1.IsHermitian} ∩
        (S ∩ D ∩ {q : Q |
          hamiltonIveyConvexBarrier K (WithLp.ofLp q).2 (X (WithLp.ofLp q).1) ≤
            (WithLp.ofLp q).1.trace}) := by
    ext q
    constructor
    · intro hq
      rw [mem_hamiltonIveyConvexMatrixSlab] at hq
      rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hq
      rcases hq with ⟨hτ, hmem⟩
      rcases hmem with ⟨hH, hD, hB⟩
      exact ⟨hH, ⟨hτ, hD⟩, hB⟩
    · intro hq
      rw [mem_hamiltonIveyConvexMatrixSlab]
      rw [hamiltonIveyConvexMatrixRegion_eq_violation]
      rcases hq with ⟨hH, hrest⟩
      rcases hrest with ⟨hSD, hB⟩
      rcases hSD with ⟨hτ, hD⟩
      exact ⟨hτ, hH, hD, hB⟩
  rw [hset]
  exact hH_closed.inter hB_closed

theorem convex_hamiltonIveyConvexMatrixSlab_slice
    {K T τ : ℝ} (hK : 0 < K) (hτ : τ ∈ Set.Icc 0 T) :
    Convex ℝ {A : Matrix (Fin 3) (Fin 3) ℝ | (WithLp.toLp 2 (A, τ)) ∈ hamiltonIveyConvexMatrixSlab K T} := by
  -- The slice is exactly hamiltonIveyConvexMatrixRegion K τ
  have hset : {A : Matrix (Fin 3) (Fin 3) ℝ | (WithLp.toLp 2 (A, τ)) ∈ hamiltonIveyConvexMatrixSlab K T} =
      hamiltonIveyConvexMatrixRegion K τ := by
    ext A
    simp [hamiltonIveyConvexMatrixSlab, hτ.1, hτ.2]
  rw [hset]
  exact convex_hamiltonIveyConvexMatrixRegion hK hτ.1

theorem isClosed_hamiltonIveyConvexMatrixSlab_slice
    {K T τ : ℝ} (hK : 0 < K) :
    IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | (WithLp.toLp 2 (A, τ)) ∈ hamiltonIveyConvexMatrixSlab K T} := by
  have hcont : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => WithLp.toLp 2 (A, τ)) := by
    -- toLp continuous, pair continuous
    have hA : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A) := continuous_id
    have hτ : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => τ) := continuous_const
    exact (WithLp.prod_continuous_toLp (p := 2) (α := Matrix (Fin 3) (Fin 3) ℝ) (β := ℝ)).comp (hA.prodMk hτ)
  exact IsClosed.preimage hcont (isClosed_hamiltonIveyConvexMatrixSlab hK)

theorem nonempty_hamiltonIveyConvexMatrixSlab_slice
    {K T τ : ℝ} (hK : 0 < K) (hτ : τ ∈ Set.Icc 0 T) :
    {A : Matrix (Fin 3) (Fin 3) ℝ | (WithLp.toLp 2 (A, τ)) ∈ hamiltonIveyConvexMatrixSlab K T}.Nonempty := by
  rcases nonempty_hamiltonIveyConvexMatrixRegion hK hτ.1 with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  change (WithLp.toLp 2 (A, τ)) ∈ hamiltonIveyConvexMatrixSlab K T
  rw [mem_hamiltonIveyConvexMatrixSlab]
  exact ⟨hτ, hA⟩

theorem hamiltonIveyConvexMatrixSlab_slice_eq
    {K T τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    {A : Matrix (Fin 3) (Fin 3) ℝ | (WithLp.toLp 2 (A, τ)) ∈ hamiltonIveyConvexMatrixSlab K T} =
      hamiltonIveyConvexMatrixRegion K τ := by
  ext A
  simp [hamiltonIveyConvexMatrixSlab, hτ.1, hτ.2]

theorem hamiltonIveyConvexMatrixSlab_hermitian
    {K T : ℝ} {q : WithLp 2 (Matrix (Fin 3) (Fin 3) ℝ × ℝ)}
    (hq : q ∈ hamiltonIveyConvexMatrixSlab K T) :
    (WithLp.ofLp q).1.IsHermitian := by
  rw [mem_hamiltonIveyConvexMatrixSlab] at hq
  rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hq
  exact hq.2.1

theorem hamiltonIveyConvexMatrixSlab_pinch_nonneg
    {K T : ℝ} {q : WithLp 2 (Matrix (Fin 3) (Fin 3) ℝ × ℝ)}
    (hq : q ∈ hamiltonIveyConvexMatrixSlab K T) :
    0 ≤ max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 (WithLp.ofLp q).1) 0 := by
  rw [mem_hamiltonIveyConvexMatrixSlab] at hq
  rw [hamiltonIveyConvexMatrixRegion_eq_violation] at hq
  exact hq.2.2.1

theorem hamiltonIveyConvexMatrixSlab_slice_mem
    {K T τ : ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hτ : τ ∈ Set.Icc 0 T) (hA : A ∈ hamiltonIveyConvexMatrixRegion K τ) :
    WithLp.toLp 2 (A, τ) ∈ hamiltonIveyConvexMatrixSlab K T := by
  rw [mem_hamiltonIveyConvexMatrixSlab]
  exact ⟨hτ, hA⟩

def softMinSectional3 (ε : Real) (l : Fin 3 → Real) : Real :=
  -ε⁻¹ * Real.log (∑ i : Fin 3, Real.exp (-ε * l i))


theorem hamiltonIveyBarrier_slope_pos_of_scalarLower_of_lt
    {K τ X S : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hX : 0 < X)
    (hS3 : -3 * X ≤ S)
    (hscalar : scalarSectionalLowerBarrier3 K τ ≤ S)
    (hfail : S < hamiltonIveyBarrier K τ X) :
    0 < Real.log (X / K) + Real.log (1 + 2 * K * τ) - 2 := by
  have hden : 0 < 1 + 2 * K * τ := by
    nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
  have hsum_nonpos_of_Xle :
      X ≤ K / (1 + 2 * K * τ) →
        hamiltonIveyBarrier K τ X ≤ -3 * X := by
    intro hXle
    exact hamiltonIveyBarrier_le_neg_three_pinchHeight_of_subregion
      hK hden hX.le hXle
  have hmid_barrier :
      hamiltonIveyBarrier K τ (K / (1 + 2 * K * τ)) =
        -3 * K / (1 + 2 * K * τ) := by
    unfold hamiltonIveyBarrier
    have hq : (K / (1 + 2 * K * τ)) / K = (1 + 2 * K * τ)⁻¹ := by
      field_simp [hK.ne', hden.ne']
    rw [hq]
    rw [Real.log_inv (1 + 2 * K * τ)]
    field_simp [hK.ne', hden.ne']
    ring
  have hσ_ge : -3 * K / (1 + 2 * K * τ) ≤ scalarSectionalLowerBarrier3 K τ := by
    unfold scalarSectionalLowerBarrier3
    have hden2 : 0 < 1 + 4 * K * τ := by
      nlinarith [mul_nonneg (mul_pos (by norm_num : (0:ℝ)<4) hK).le hτ]
    have hcmp : (1 + 2 * K * τ) ≤ 1 + 4 * K * τ := by
      nlinarith [mul_nonneg (mul_pos two_pos hK).le hτ]
    have h1 : ((1 + 4 * K * τ)⁻¹ : ℝ) ≤ (1 + 2 * K * τ)⁻¹ :=
      (inv_le_inv₀ hden2 hden).2 hcmp
    have hmul := mul_le_mul_of_nonpos_left h1 (by linarith : -3 * K ≤ 0)
    simpa [div_eq_mul_inv] using hmul
  have hanti := hamiltonIveyBarrier_antitoneOn_of_le_exp_two (K := K) (τ := τ) hK hτ
  by_contra hnonpos
  have hle : Real.log (X / K) + Real.log (1 + 2 * K * τ) ≤ 2 := by nlinarith
  have hlogsum : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
      Real.log ((X / K) * (1 + 2 * K * τ)) :=
    (Real.log_mul (div_pos hX hK).ne' hden.ne').symm
  have hexp_le : Real.exp (Real.log (X / K) + Real.log (1 + 2 * K * τ)) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr hle
  have hlogarg : 0 < (X / K) * (1 + 2 * K * τ) := mul_pos (div_pos hX hK) hden
  have hXbranch : X ≤ K * Real.exp 2 / (1 + 2 * K * τ) := by
    have hexp' : (X / K) * (1 + 2 * K * τ) ≤ Real.exp 2 := by
      calc
        (X / K) * (1 + 2 * K * τ) =
            Real.exp (Real.log (X / K) + Real.log (1 + 2 * K * τ)) := by
              rw [hlogsum, Real.exp_log hlogarg]
        _ ≤ Real.exp 2 := hexp_le
    field_simp [hK.ne', hden.ne'] at hexp' ⊢
    nlinarith
  by_cases hXsmall : X ≤ K / (1 + 2 * K * τ)
  · have hbar := hsum_nonpos_of_Xle hXsmall
    nlinarith [hS3, hfail, hbar]
  · have hXmid : K / (1 + 2 * K * τ) < X := lt_of_not_ge hXsmall
    have hxmid_mem : K / (1 + 2 * K * τ) ∈
        Set.Ioc 0 (K * Real.exp 2 / (1 + 2 * K * τ)) := by
      constructor
      · positivity
      · have h3exp : (3:ℝ) ≤ Real.exp 2 := by
          have h := Real.add_one_le_exp (2:ℝ)
          norm_num at h ⊢
          exact h
        have hexp2 : 1 < Real.exp 2 := by nlinarith
        have hnum : K < K * Real.exp 2 := by
          simpa using (mul_lt_mul_of_pos_left hexp2 hK)
        have hdiv : K / (1 + 2 * K * τ) <
            K * Real.exp 2 / (1 + 2 * K * τ) := by
          exact div_lt_div_of_pos_right hnum hden
        exact le_of_lt (by simpa using hdiv)
    have hx_mem : X ∈ Set.Ioc 0 (K * Real.exp 2 / (1 + 2 * K * τ)) := by
      exact ⟨hX, hXbranch⟩
    have hbar := hanti hxmid_mem hx_mem hXmid.le
    have hbranch_le' :
        hamiltonIveyBarrier K τ X ≤ -3 * K / (1 + 2 * K * τ) := by
      rw [hmid_barrier] at hbar
      exact hbar
    nlinarith [hσ_ge, hscalar, hfail, hbranch_le']


theorem softMinSectional3_le_apply
    {ε : Real} (hε : 0 < ε) (l : Fin 3 → Real) (i : Fin 3) :
    softMinSectional3 ε l ≤ l i := by
  unfold softMinSectional3
  have hsum : Real.exp (-ε * l i) ≤ ∑ j : Fin 3, Real.exp (-ε * l j) := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 3 => Real.exp (-ε * l j))
      (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i)
  have hlog := Real.log_le_log (Real.exp_pos _) hsum
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt (inv_pos.mpr hε))
  have hcalc : ε⁻¹ * (-ε * l i) = -l i := by
    field_simp [hε.ne']
  rw [Real.log_exp] at hmul
  linarith

theorem continuous_softMinSectional3
    {ε : Real} :
    Continuous (fun l : Fin 3 → Real => softMinSectional3 ε l) := by
  unfold softMinSectional3
  rw [continuous_iff_continuousAt]
  intro l
  have hsum : ContinuousAt (fun l : Fin 3 → Real => ∑ i : Fin 3, Real.exp (-ε * l i)) l := by
    have hcont : Continuous (fun l : Fin 3 → Real => ∑ i : Fin 3, Real.exp (-ε * l i)) := by
      exact continuous_finset_sum Finset.univ (fun i _ =>
        Real.continuous_exp.comp (by
          simpa [Pi.mul_apply] using (continuous_const.mul (continuous_apply i)).neg))
    exact hcont.continuousAt
  have hpos : 0 < ∑ i : Fin 3, Real.exp (-ε * l i) := by
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  exact (hsum.log hpos.ne').const_mul (-ε⁻¹)

theorem softMinSectional3_tendsto_inf (l : Fin 3 → Real) :
    Filter.Tendsto (fun ε : Real => softMinSectional3 ε l) Filter.atTop
      (nhds ((Finset.univ : Finset (Fin 3)).inf' (Finset.univ_nonempty) l)) := by
  let m : Real := (Finset.univ : Finset (Fin 3)).inf' (Finset.univ_nonempty) l
  have hm_le : ∀ i : Fin 3, m ≤ l i := by
    intro i
    dsimp [m]
    exact Finset.inf'_le l (Finset.mem_univ i)
  obtain ⟨i0, _hi0mem, hi0min⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 3)) l Finset.univ_nonempty
  have hm_i0 : m = l i0 := by
    dsimp [m]
    exact le_antisymm (Finset.inf'_le l (Finset.mem_univ i0))
      (Finset.le_inf' Finset.univ_nonempty l (fun j hj => hi0min j hj))
  have hi0 : l i0 = m := hm_i0.symm
  have hB1 : ∀ ε : Real, 0 < ε → 1 ≤ ∑ i : Fin 3, Real.exp (-(ε * (l i - m))) := by
    intro ε hε
    have hterm : Real.exp (-(ε * (l i0 - m))) = 1 := by
      have hzero : l i0 - m = 0 := by
        have hmle0 : m ≤ l i0 := hm_le i0
        have hle0 : l i0 ≤ m := by
          rw [hi0]
        linarith
      simp [hzero]
    have hsum := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 3 => Real.exp (-(ε * (l i - m))))
      (fun i _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i0)
    simpa [hterm] using hsum
  have hB3 : ∀ ε : Real, 0 < ε → (∑ i : Fin 3, Real.exp (-(ε * (l i - m)))) ≤ 3 := by
    intro ε hε
    have hle : ∀ i : Fin 3, Real.exp (-(ε * (l i - m))) ≤ 1 := by
      intro i
      have hd : 0 ≤ l i - m := sub_nonneg.mpr (hm_le i)
      have harg : -(ε * (l i - m)) ≤ 0 := by
        exact neg_nonpos.mpr (mul_nonneg (le_of_lt hε) hd)
      exact (Real.exp_le_one_iff.mpr harg)
    calc
      (∑ i : Fin 3, Real.exp (-(ε * (l i - m)))) ≤ ∑ _i : Fin 3, (1 : Real) := by
        exact Finset.sum_le_sum (fun i _ => hle i)
      _ = 3 := by simp
  have hsoft_eq : ∀ ε : Real, 0 < ε →
      softMinSectional3 ε l = m - ε⁻¹ * Real.log (∑ i : Fin 3, Real.exp (-(ε * (l i - m)))) := by
    intro ε hε
    unfold softMinSectional3
    have hsum_mul : (∑ i : Fin 3, Real.exp (-ε * l i)) =
        Real.exp (-ε * m) * (∑ i : Fin 3, Real.exp (-(ε * (l i - m)))) := by
      calc
        (∑ i : Fin 3, Real.exp (-ε * l i)) =
            ∑ i : Fin 3, Real.exp (-ε * m) * Real.exp (-(ε * (l i - m))) := by
          apply Finset.sum_congr rfl
          intro i _
          have harg : -ε * l i = -ε * m + (-(ε * (l i - m))) := by ring
          rw [harg, Real.exp_add]
        _ = Real.exp (-ε * m) * (∑ i : Fin 3, Real.exp (-(ε * (l i - m)))) := by
          rw [Finset.mul_sum]
    rw [hsum_mul, Real.log_mul (Real.exp_pos _).ne' ?_]
    · rw [Real.log_exp]
      field_simp [hε.ne']
      ring
    · have hsumpos : 0 < ∑ i : Fin 3, Real.exp (-(ε * (l i - m))) := by
        have := hB1 ε hε
        positivity
      exact hsumpos.ne'
  have htend_small : Filter.Tendsto (fun ε : Real => ε⁻¹ * Real.log 3) Filter.atTop (nhds 0) := by
    have hmain : Filter.Tendsto (fun ε : Real => ε⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
    simpa [mul_comm] using hmain.const_mul (Real.log 3)
  have hzero : Filter.Tendsto (fun ε : Real => (0 : Real)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have hlog_squeeze : Filter.Tendsto (fun ε : Real => ε⁻¹ * Real.log (∑ i : Fin 3, Real.exp (-(ε * (l i - m))))) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero htend_small ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with ε hε
      have h1 := hB1 ε hε
      have h3 := hB3 ε hε
      have hlog_nonneg : 0 ≤ Real.log (∑ i : Fin 3, Real.exp (-(ε * (l i - m)))) := Real.log_nonneg (by linarith)
      exact mul_nonneg (le_of_lt (inv_pos.mpr hε)) hlog_nonneg
    · filter_upwards [Filter.eventually_gt_atTop 0] with ε hε
      have h3 := hB3 ε hε
      have hsumpos : 0 < ∑ i : Fin 3, Real.exp (-(ε * (l i - m))) := by
        have := hB1 ε hε
        positivity
      have hlog_le := Real.log_le_log hsumpos h3
      exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt (inv_pos.mpr hε))
  have hmain : Filter.Tendsto (fun ε : Real => m - ε⁻¹ * Real.log (∑ i : Fin 3, Real.exp (-(ε * (l i - m))))) Filter.atTop (nhds m) := by
    simpa using hlog_squeeze.const_sub m
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with ε hε
  exact (hsoft_eq ε hε).symm

def softMaxSectional3Upper (ε : Real) (l : Fin 3 → Real) : Real :=
  -softMinSectional3 ε (fun i => -l i)

def softMaxSectional3Lower (ε : Real) (l : Fin 3 → Real) : Real :=
  ε⁻¹ * (Real.log (∑ i : Fin 3, Real.exp (ε * l i)) - Real.log 3)

theorem apply_le_softMaxSectional3Upper
    {ε : Real} (hε : 0 < ε) (l : Fin 3 → Real) (i : Fin 3) :
    l i ≤ softMaxSectional3Upper ε l := by
  unfold softMaxSectional3Upper
  have hmin := softMinSectional3_le_apply hε (fun i : Fin 3 => -l i) i
  linarith

theorem continuous_softMaxSectional3Upper
    {ε : Real} :
    Continuous (fun l : Fin 3 → Real => softMaxSectional3Upper ε l) := by
  unfold softMaxSectional3Upper
  have hneg : Continuous (fun l : Fin 3 → Real => fun i : Fin 3 => -l i) := by
    apply continuous_pi
    intro i
    have hproj : Continuous (fun l : Fin 3 → Real => l i) :=
      continuous_apply (i := i)
    exact hproj.neg
  have hcomp : Continuous
      (fun l : Fin 3 → Real => softMinSectional3 ε (fun i : Fin 3 => -l i)) :=
    (continuous_softMinSectional3 (ε := ε)).comp hneg
  simpa [Function.comp_def] using hcomp.neg

theorem softMaxSectional3Upper_tendsto_sup (l : Fin 3 → Real) :
    Filter.Tendsto (fun ε : Real => softMaxSectional3Upper ε l) Filter.atTop
      (nhds ((Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l)) := by
  have h := softMinSectional3_tendsto_inf (fun i : Fin 3 => -l i)
  have hinf :
      (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty (fun i : Fin 3 => -l i) =
        -((Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l) := by
    obtain ⟨j, hj, hjinf⟩ :=
      Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin 3)))
        (H := Finset.univ_nonempty) (f := fun i : Fin 3 => -l i)
    have hjmax : (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l = l j := by
      apply le_antisymm
      · exact Finset.sup'_le Finset.univ_nonempty l (by
          intro i hi
          have hle : (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty
              (fun i : Fin 3 => -l i) ≤ -l i :=
            Finset.inf'_le (s := (Finset.univ : Finset (Fin 3))) (f := fun i : Fin 3 => -l i) hi
          rw [hjinf] at hle
          linarith)
      · exact Finset.le_sup' (s := (Finset.univ : Finset (Fin 3))) (f := l) hj
    calc
      (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty (fun i : Fin 3 => -l i)
          = -l j := hjinf
      _ = -((Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l) := by
            rw [hjmax]
  simpa [softMaxSectional3Upper, hinf] using h.neg

theorem softMaxSectional3Lower_le_sup
    {ε : Real} (hε : 0 < ε) (l : Fin 3 → Real) :
    softMaxSectional3Lower ε l ≤
      (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l := by
  unfold softMaxSectional3Lower
  let m : Real := (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l
  have hle : ∀ j : Fin 3, ε * l j ≤ ε * m := by
    intro j
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (s := (Finset.univ : Finset (Fin 3)))
        (f := l) (Finset.mem_univ j))
      (le_of_lt hε)
  have hsum : ∑ j : Fin 3, Real.exp (ε * l j) ≤ 3 * Real.exp (ε * m) := by
    calc
      (∑ j : Fin 3, Real.exp (ε * l j)) ≤ ∑ _j : Fin 3, Real.exp (ε * m) := by
        refine Finset.sum_le_sum ?_
        intro j _hj
        exact Real.exp_le_exp.mpr (hle j)
      _ = 3 * Real.exp (ε * m) := by simp
  have hlog := Real.log_le_log
    (Finset.sum_pos (fun j _hj => Real.exp_pos _) Finset.univ_nonempty) hsum
  have hcalc : ε⁻¹ * (Real.log (3 * Real.exp (ε * m)) - Real.log 3) = m := by
    calc
      ε⁻¹ * (Real.log (3 * Real.exp (ε * m)) - Real.log 3)
          = ε⁻¹ * (Real.log 3 + ε * m - Real.log 3) := by
            rw [Real.log_mul (by norm_num : (0 : Real) < 3).ne' (Real.exp_pos _).ne',
              Real.log_exp]
      _ = ε⁻¹ * (ε * m) := by ring
      _ = m := by
        field_simp [hε.ne']
  have hlogsub :
      Real.log (∑ j : Fin 3, Real.exp (ε * l j)) - Real.log 3 ≤
        Real.log (3 * Real.exp (ε * m)) - Real.log 3 :=
    sub_le_sub_right hlog (Real.log 3)
  have hmul := mul_le_mul_of_nonneg_left hlogsub (le_of_lt (inv_pos.mpr hε))
  rw [hcalc] at hmul
  dsimp [m] at hmul ⊢
  exact hmul

theorem continuous_softMaxSectional3Lower
    {ε : Real} :
    Continuous (fun l : Fin 3 → Real => softMaxSectional3Lower ε l) := by
  unfold softMaxSectional3Lower
  have hsum : Continuous (fun l : Fin 3 → Real => ∑ i : Fin 3, Real.exp (ε * l i)) := by
    exact continuous_finset_sum Finset.univ (fun i _ =>
      Real.continuous_exp.comp (by
        simpa [Pi.mul_apply] using
          (continuous_const.mul (continuous_apply (i := i)))))
  have hlog : Continuous (fun l : Fin 3 → Real => Real.log (∑ i : Fin 3, Real.exp (ε * l i))) := by
    exact hsum.log (by
      intro l
      exact (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty).ne')
  exact (hlog.sub continuous_const).const_mul ε⁻¹

theorem softMaxSectional3Lower_tendsto_sup (l : Fin 3 → Real) :
    Filter.Tendsto (fun ε : Real => softMaxSectional3Lower ε l) Filter.atTop
      (nhds ((Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l)) := by
  have hupper := softMaxSectional3Upper_tendsto_sup l
  have htail : Filter.Tendsto (fun ε : Real => ε⁻¹ * Real.log 3) Filter.atTop
      (nhds 0) := by
    simpa [mul_comm] using tendsto_inv_atTop_zero.const_mul (Real.log 3)
  have hmain : Filter.Tendsto
      (fun ε : Real => softMaxSectional3Upper ε l - ε⁻¹ * Real.log 3)
      Filter.atTop (nhds ((Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty l)) := by
    simpa using hupper.sub htail
  have hfun : (fun ε : Real => softMaxSectional3Lower ε l) =
      fun ε : Real => softMaxSectional3Upper ε l - ε⁻¹ * Real.log 3 := by
    funext ε
    unfold softMaxSectional3Upper softMaxSectional3Lower softMinSectional3
    ring_nf
  simpa [hfun] using hmain

def softPinchHeight3Lower (ε : Real) (l : Fin 3 → Real) : Real :=
  max (softMaxSectional3Lower ε (fun i => -l i)) 0

def softPinchHeight3Upper (ε : Real) (l : Fin 3 → Real) : Real :=
  max (softMaxSectional3Upper ε (fun i => -l i)) 0

theorem continuous_pinchHeight3 :
    Continuous (fun l : Fin 3 → Real => pinchHeight3 (l 2)) := by
  unfold pinchHeight3
  exact ((continuous_apply 2).neg).max continuous_const

theorem continuous_softPinchHeight3Lower
    {ε : Real} :
    Continuous (fun l : Fin 3 → Real => softPinchHeight3Lower ε l) := by
  unfold softPinchHeight3Lower
  exact (continuous_softMaxSectional3Lower.comp (by
    apply continuous_pi
    intro i
    exact (continuous_apply (i := i)).neg)).max continuous_const

theorem continuous_softPinchHeight3Upper
    {ε : Real} :
    Continuous (fun l : Fin 3 → Real => softPinchHeight3Upper ε l) := by
  unfold softPinchHeight3Upper
  exact (continuous_softMaxSectional3Upper.comp (by
    apply continuous_pi
    intro i
    exact (continuous_apply (i := i)).neg)).max continuous_const

private theorem neg_sup_eq_neg_min_of_ordered
    {l : Fin 3 → Real} (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) :
    (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty (fun i => -l i) = -l 2 := by
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty (fun i : Fin 3 => -l i) (by
      intro i hi
      fin_cases i <;> simp at hi ⊢ <;> linarith)
  · exact Finset.le_sup' (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 => -l i) (Finset.mem_univ 2)

theorem softPinchHeight3Lower_le
    {ε : Real} (hε : 0 < ε) {l : Fin 3 → Real}
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) :
    softPinchHeight3Lower ε l ≤ pinchHeight3 (l 2) := by
  unfold softPinchHeight3Lower pinchHeight3
  have hsup :
      (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty (fun i => -l i) = -l 2 :=
    neg_sup_eq_neg_min_of_ordered h21 h32
  have hsoft := softMaxSectional3Lower_le_sup hε (fun i => -l i)
  rw [hsup] at hsoft
  exact max_le_max hsoft le_rfl

theorem pinchHeight3_le_softPinchHeight3Upper
    {ε : Real} (hε : 0 < ε) {l : Fin 3 → Real}
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) :
    pinchHeight3 (l 2) ≤ softPinchHeight3Upper ε l := by
  unfold softPinchHeight3Upper pinchHeight3
  have hsup :
      (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty (fun i => -l i) = -l 2 :=
    neg_sup_eq_neg_min_of_ordered h21 h32
  have hsoft : -l 2 ≤ softMaxSectional3Upper ε (fun i => -l i) := by
    have hmem := apply_le_softMaxSectional3Upper hε (fun i => -l i) 2
    simpa [hsup] using hmem
  exact max_le_max hsoft le_rfl

theorem softPinchHeight3Lower_tendsto
    {l : Fin 3 → Real} (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) :
    Filter.Tendsto (fun ε : Real => softPinchHeight3Lower ε l) Filter.atTop
      (nhds (pinchHeight3 (l 2))) := by
  have hsup :
      (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty (fun i => -l i) = -l 2 :=
    neg_sup_eq_neg_min_of_ordered h21 h32
  have hsoft := softMaxSectional3Lower_tendsto_sup (fun i => -l i)
  have hsoft' : Filter.Tendsto (fun ε : Real => softMaxSectional3Lower ε (fun i => -l i))
      Filter.atTop (nhds (-l 2)) := by
    simpa [hsup] using hsoft
  have hmax : Filter.Tendsto (fun ε : Real => max (softMaxSectional3Lower ε (fun i => -l i)) 0)
      Filter.atTop (nhds (max (-l 2) 0)) :=
    hsoft'.max tendsto_const_nhds
  simpa [softPinchHeight3Lower, pinchHeight3] using hmax

theorem softPinchHeight3Upper_tendsto
    {l : Fin 3 → Real} (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) :
    Filter.Tendsto (fun ε : Real => softPinchHeight3Upper ε l) Filter.atTop
      (nhds (pinchHeight3 (l 2))) := by
  have hsup :
      (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty (fun i => -l i) = -l 2 :=
    neg_sup_eq_neg_min_of_ordered h21 h32
  have hsoft := softMaxSectional3Upper_tendsto_sup (fun i => -l i)
  have hsoft' : Filter.Tendsto (fun ε : Real => softMaxSectional3Upper ε (fun i => -l i))
      Filter.atTop (nhds (-l 2)) := by
    simpa [hsup] using hsoft
  have hmax : Filter.Tendsto (fun ε : Real => max (softMaxSectional3Upper ε (fun i => -l i)) 0)
      Filter.atTop (nhds (max (-l 2) 0)) :=
    hsoft'.max tendsto_const_nhds
  simpa [softPinchHeight3Upper, pinchHeight3] using hmax

def hamiltonIveySoftConvexBarrierLower
    (ε K τ : Real) (l : Fin 3 → Real) : Real :=
  hamiltonIveyConvexBarrier K τ (softPinchHeight3Lower ε l)

def hamiltonIveySoftConvexBarrierUpper
    (ε K τ : Real) (l : Fin 3 → Real) : Real :=
  hamiltonIveyConvexBarrier K τ (softPinchHeight3Upper ε l)

theorem continuous_hamiltonIveySoftConvexBarrierLower
    {ε K τ : Real} (hK : 0 < K) :
    Continuous (fun l : Fin 3 → Real => hamiltonIveySoftConvexBarrierLower ε K τ l) := by
  unfold hamiltonIveySoftConvexBarrierLower
  exact (continuous_hamiltonIveyConvexBarrier hK).comp continuous_softPinchHeight3Lower

theorem continuous_hamiltonIveySoftConvexBarrierUpper
    {ε K τ : Real} (hK : 0 < K) :
    Continuous (fun l : Fin 3 → Real => hamiltonIveySoftConvexBarrierUpper ε K τ l) := by
  unfold hamiltonIveySoftConvexBarrierUpper
  exact (continuous_hamiltonIveyConvexBarrier hK).comp continuous_softPinchHeight3Upper

theorem hamiltonIveySoftConvexBarrierLower_tendsto
    {K τ : Real} {l : Fin 3 → Real} (hK : 0 < K)
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) :
    Filter.Tendsto (fun ε : Real => hamiltonIveySoftConvexBarrierLower ε K τ l)
      Filter.atTop (nhds (hamiltonIveyConvexBarrier K τ (pinchHeight3 (l 2)))) := by
  unfold hamiltonIveySoftConvexBarrierLower
  exact (continuous_hamiltonIveyConvexBarrier hK).continuousAt.tendsto.comp
    (softPinchHeight3Lower_tendsto h21 h32)

theorem hamiltonIveySoftConvexBarrierUpper_tendsto
    {K τ : Real} {l : Fin 3 → Real} (hK : 0 < K)
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1) :
    Filter.Tendsto (fun ε : Real => hamiltonIveySoftConvexBarrierUpper ε K τ l)
      Filter.atTop (nhds (hamiltonIveyConvexBarrier K τ (pinchHeight3 (l 2)))) := by
  unfold hamiltonIveySoftConvexBarrierUpper
  exact (continuous_hamiltonIveyConvexBarrier hK).continuousAt.tendsto.comp
    (softPinchHeight3Upper_tendsto h21 h32)

def hamiltonIveyBarrierBranchPoint (K τ : Real) : Real :=
  K * Real.exp 2 / (1 + 2 * K * τ)

theorem hamiltonIveyBarrier_softLower_le_of_branchPoint_le
    {ε K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hε : 0 < ε)
    {l : Fin 3 → Real} (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hX0 : hamiltonIveyBarrierBranchPoint K τ ≤ pinchHeight3 (l 2)) :
    hamiltonIveyBarrier K τ
        (max (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Lower ε l)) ≤
      hamiltonIveyBarrier K τ (pinchHeight3 (l 2)) := by
  have hsoft : softPinchHeight3Lower ε l ≤ pinchHeight3 (l 2) :=
    softPinchHeight3Lower_le hε h21 h32
  have hmax : max (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Lower ε l) ≤
      pinchHeight3 (l 2) :=
    max_le hX0 hsoft
  have hmono := hamiltonIveyBarrier_monotoneOn_of_exp_two_le (K := K) (τ := τ) hK hτ
  have hmaxmem :
      max (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Lower ε l) ∈
        Set.Ici (hamiltonIveyBarrierBranchPoint K τ) := by
    simp [Set.mem_Ici]
  exact hmono hmaxmem hX0 hmax

theorem hamiltonIveyBarrier_softUpperClamped_le_of_le_branchPoint
    {ε K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hε : 0 < ε)
    {l : Fin 3 → Real} (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hXpos : 0 < pinchHeight3 (l 2))
    (hXle : pinchHeight3 (l 2) ≤ hamiltonIveyBarrierBranchPoint K τ) :
    hamiltonIveyBarrier K τ
        (min (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Upper ε l)) ≤
      hamiltonIveyBarrier K τ (pinchHeight3 (l 2)) := by
  have hsoft : pinchHeight3 (l 2) ≤ softPinchHeight3Upper ε l :=
    pinchHeight3_le_softPinchHeight3Upper hε h21 h32
  have hmin : pinchHeight3 (l 2) ≤
      min (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Upper ε l) :=
    le_min hXle hsoft
  have hbpos : 0 <
      min (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Upper ε l) := by
    exact lt_of_lt_of_le hXpos hmin
  have hble : min (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Upper ε l) ≤
      hamiltonIveyBarrierBranchPoint K τ :=
    min_le_left _ _
  have hanti := hamiltonIveyBarrier_antitoneOn_of_le_exp_two (K := K) (τ := τ) hK hτ
  exact hanti ⟨hXpos, hXle⟩ ⟨hbpos, hble⟩ hmin

def softPinchHeight3LowerBranch (ε K τ : Real) (l : Fin 3 → Real) : Real :=
  max (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Lower ε l)

def softPinchHeight3UpperBranch (ε K τ : Real) (l : Fin 3 → Real) : Real :=
  min (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Upper ε l)

theorem continuous_softPinchHeight3LowerBranch
    {ε K τ : Real} :
    Continuous (fun l : Fin 3 → Real => softPinchHeight3LowerBranch ε K τ l) := by
  unfold softPinchHeight3LowerBranch
  exact continuous_const.max continuous_softPinchHeight3Lower

theorem continuous_softPinchHeight3UpperBranch
    {ε K τ : Real} :
    Continuous (fun l : Fin 3 → Real => softPinchHeight3UpperBranch ε K τ l) := by
  unfold softPinchHeight3UpperBranch
  exact continuous_const.min continuous_softPinchHeight3Upper

theorem softPinchHeight3LowerBranch_tendsto
    {K τ : Real} {l : Fin 3 → Real}
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hX0 : hamiltonIveyBarrierBranchPoint K τ ≤ pinchHeight3 (l 2)) :
    Filter.Tendsto (fun ε : Real => softPinchHeight3LowerBranch ε K τ l)
      Filter.atTop (nhds (pinchHeight3 (l 2))) := by
  unfold softPinchHeight3LowerBranch
  have hsoft := softPinchHeight3Lower_tendsto h21 h32
  have hmax : Filter.Tendsto
      (fun ε : Real => max (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Lower ε l))
      Filter.atTop (nhds (max (hamiltonIveyBarrierBranchPoint K τ) (pinchHeight3 (l 2)))) :=
    tendsto_const_nhds.max hsoft
  simpa [max_eq_right hX0] using hmax

theorem softPinchHeight3UpperBranch_tendsto
    {K τ : Real} {l : Fin 3 → Real}
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hXle : pinchHeight3 (l 2) ≤ hamiltonIveyBarrierBranchPoint K τ) :
    Filter.Tendsto (fun ε : Real => softPinchHeight3UpperBranch ε K τ l)
      Filter.atTop (nhds (pinchHeight3 (l 2))) := by
  unfold softPinchHeight3UpperBranch
  have hsoft := softPinchHeight3Upper_tendsto h21 h32
  have hmin : Filter.Tendsto
      (fun ε : Real => min (hamiltonIveyBarrierBranchPoint K τ) (softPinchHeight3Upper ε l))
      Filter.atTop (nhds (min (hamiltonIveyBarrierBranchPoint K τ) (pinchHeight3 (l 2)))) :=
    tendsto_const_nhds.min hsoft
  simpa [min_eq_right hXle] using hmin

def hamiltonIveySoftBarrierLowerBranch
    (ε K τ : Real) (l : Fin 3 → Real) : Real :=
  hamiltonIveyBarrier K τ (softPinchHeight3LowerBranch ε K τ l)

def hamiltonIveySoftBarrierUpperBranch
    (ε K τ : Real) (l : Fin 3 → Real) : Real :=
  hamiltonIveyBarrier K τ (softPinchHeight3UpperBranch ε K τ l)

theorem continuous_hamiltonIveySoftBarrierLowerBranch
    {ε K τ : Real} (hK : 0 < K) :
    Continuous (fun l : Fin 3 → Real => hamiltonIveySoftBarrierLowerBranch ε K τ l) := by
  unfold hamiltonIveySoftBarrierLowerBranch
  exact (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).comp
    continuous_softPinchHeight3LowerBranch

theorem continuous_hamiltonIveySoftBarrierUpperBranch
    {ε K τ : Real} (hK : 0 < K) :
    Continuous (fun l : Fin 3 → Real => hamiltonIveySoftBarrierUpperBranch ε K τ l) := by
  unfold hamiltonIveySoftBarrierUpperBranch
  exact (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).comp
    continuous_softPinchHeight3UpperBranch

theorem hamiltonIveySoftBarrierLowerBranch_le
    {ε K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hε : 0 < ε)
    {l : Fin 3 → Real} (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hX0 : hamiltonIveyBarrierBranchPoint K τ ≤ pinchHeight3 (l 2)) :
    hamiltonIveySoftBarrierLowerBranch ε K τ l ≤
      hamiltonIveyBarrier K τ (pinchHeight3 (l 2)) := by
  unfold hamiltonIveySoftBarrierLowerBranch
  simpa [softPinchHeight3LowerBranch] using
    hamiltonIveyBarrier_softLower_le_of_branchPoint_le hK hτ hε h21 h32 hX0

theorem hamiltonIveySoftBarrierUpperBranch_le
    {ε K τ : Real} (hK : 0 < K) (hτ : 0 ≤ τ) (hε : 0 < ε)
    {l : Fin 3 → Real} (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hXpos : 0 < pinchHeight3 (l 2))
    (hXle : pinchHeight3 (l 2) ≤ hamiltonIveyBarrierBranchPoint K τ) :
    hamiltonIveySoftBarrierUpperBranch ε K τ l ≤
      hamiltonIveyBarrier K τ (pinchHeight3 (l 2)) := by
  unfold hamiltonIveySoftBarrierUpperBranch
  simpa [softPinchHeight3UpperBranch] using
    hamiltonIveyBarrier_softUpperClamped_le_of_le_branchPoint hK hτ hε h21 h32 hXpos hXle

theorem hamiltonIveySoftBarrierLowerBranch_tendsto
    {K τ : Real} {l : Fin 3 → Real} (hK : 0 < K)
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hX0 : hamiltonIveyBarrierBranchPoint K τ ≤ pinchHeight3 (l 2)) :
    Filter.Tendsto (fun ε : Real => hamiltonIveySoftBarrierLowerBranch ε K τ l)
      Filter.atTop (nhds (hamiltonIveyBarrier K τ (pinchHeight3 (l 2)))) := by
  unfold hamiltonIveySoftBarrierLowerBranch
  exact (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).continuousAt.tendsto.comp
    (softPinchHeight3LowerBranch_tendsto h21 h32 hX0)

theorem hamiltonIveySoftBarrierUpperBranch_tendsto
    {K τ : Real} {l : Fin 3 → Real} (hK : 0 < K)
    (h21 : l 1 ≤ l 0) (h32 : l 2 ≤ l 1)
    (hXle : pinchHeight3 (l 2) ≤ hamiltonIveyBarrierBranchPoint K τ) :
    Filter.Tendsto (fun ε : Real => hamiltonIveySoftBarrierUpperBranch ε K τ l)
      Filter.atTop (nhds (hamiltonIveyBarrier K τ (pinchHeight3 (l 2)))) := by
  unfold hamiltonIveySoftBarrierUpperBranch
  exact (continuous_hamiltonIveyBarrier (K := K) (τ := τ) hK).continuousAt.tendsto.comp
    (softPinchHeight3UpperBranch_tendsto h21 h32 hXle)

theorem supportLine_reaction_negative_in_sublevel_example :
    let l1 : Real := 10
    let l2 : Real := -1
    let l3 : Real := -1
    let a : Real := 10
    let C : Real := 1
    l2 ≤ l1 ∧ l3 ≤ l2 ∧
      sectionalSum3 l1 l2 l3 + a * l3 + C ≤ 0 ∧
      reactionSectionalSum3 l1 l2 l3 +
          a * DifferentialGeometry.Dim3Reaction.sectionalReaction23 l1 l2 l3 <
        0 := by
  unfold sectionalSum3 reactionSectionalSum3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  norm_num

theorem supportLine_reaction_negative_on_boundary_example :
    let l1 : Real := 13 / 12
    let l2 : Real := -5 / 12
    let l3 : Real := -5 / 12
    let a : Real := 3
    let C : Real := 1
    l2 ≤ l1 ∧ l3 ≤ l2 ∧
      sectionalSum3 l1 l2 l3 + a * l3 + C = 0 ∧
      reactionSectionalSum3 l1 l2 l3 - a * reactionPinchHeight3 l1 l2 l3 < 0 := by
  unfold sectionalSum3 reactionSectionalSum3 reactionPinchHeight3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  norm_num

theorem hamiltonIveyBarrier_reaction_negative_in_sublevel_example :
    let K : Real := 3 / (5 * Real.exp 5)
    let l1 : Real := 7 / 5
    let l2 : Real := -3 / 5
    let l3 : Real := -3 / 5
    let a : Real := 3
    l2 ≤ l1 ∧ l3 ≤ l2 ∧ 0 < K ∧
      sectionalSum3 l1 l2 l3 < hamiltonIveyBarrier K 0 (-l3) ∧
      reactionSectionalSum3 l1 l2 l3 - a * reactionPinchHeight3 l1 l2 l3 -
          (-l3) * (2 * K / (1 + 2 * K * 0)) < 0 := by
  dsimp only
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · positivity
  constructor
  · unfold sectionalSum3 hamiltonIveyBarrier
    have harg : (3 / 5 : Real) / (3 / (5 * Real.exp 5)) = Real.exp 5 := by
      field_simp [show (3 : Real) ≠ 0 by norm_num, show Real.exp 5 ≠ 0 by positivity]
    have hlog : Real.log ((3 / 5 : Real) / (3 / (5 * Real.exp 5))) = 5 := by
      rw [harg, Real.log_exp]
    rw [show -(-3 / 5 : Real) = 3 / 5 by norm_num]
    rw [show 1 + 2 * (3 / (5 * Real.exp 5)) * 0 = 1 by ring]
    rw [hlog]
    norm_num
  · unfold reactionSectionalSum3 reactionPinchHeight3
      DifferentialGeometry.Dim3Reaction.sectionalReaction12
      DifferentialGeometry.Dim3Reaction.sectionalReaction13
      DifferentialGeometry.Dim3Reaction.sectionalReaction23
    have hterm : 0 < 18 / (25 * Real.exp 5) := by positivity
    norm_num [show 1 + 2 * (3 / (5 * Real.exp 5)) * 0 = 1 by ring]
    have hmain : 0 < 4 / 25 + 18 / (25 * Real.exp 5) := add_pos (by norm_num) hterm
    have hterm' : 3 / 5 * (2 * (3 / (5 * Real.exp 5))) = 18 / (25 * Real.exp 5) := by ring
    rw [hterm']
    nlinarith [hmain]

end DifferentialGeometry.Geometry.Curvature.DimensionThree
