import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open scoped BigOperators RealInnerProductSpace

private theorem move_outer4 {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] (f : κ → ι → ι → ι → ι → R) :
    (∑ r, ∑ a, ∑ b, ∑ c, ∑ d, f r a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, f r a b c d := by
  calc
    _ = ∑ a, ∑ r, ∑ b, ∑ c, ∑ d, f r a b c d :=
      Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ c, ∑ d, f r a b c d := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ r, ∑ d, f r a b c d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, f r a b c d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm

private theorem move_outer3 {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] (f : κ → ι → ι → ι → R) :
    (∑ r, ∑ a, ∑ b, ∑ c, f r a b c) =
      ∑ a, ∑ b, ∑ c, ∑ r, f r a b c := by
  calc
    _ = ∑ a, ∑ r, ∑ b, ∑ c, f r a b c := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ c, f r a b c := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ r, f r a b c := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm

private theorem move_outer2 {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] (f : κ → ι → ι → R) :
    (∑ r, ∑ a, ∑ b, f r a b) = ∑ a, ∑ b, ∑ r, f r a b := by
  calc
    _ = ∑ a, ∑ r, ∑ b, f r a b := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, f r a b := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm

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

def hamiltonGramK {ι κ : Type*} [Fintype κ]
    (Y : κ → ι → ι → Real) (a b c d : ι) : Real :=
  ∑ r, Y r a b * Y r c d

def hamiltonGramP {ι κ : Type*} [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real) (a b c : ι) : Real :=
  ∑ r, Y r a b * X r c

def hamiltonGramM {ι κ : Type*} [Fintype κ]
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

def hamiltonQuadraticForm {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real) (P : ι → ι → ι → Real)
    (M : ι → ι → Real) (U : ι → ι → Real) (W : ι → Real) : Real :=
  (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * U c d) +
    2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
    ∑ a, ∑ b, M a b * W a * W b

def hamiltonReactionPolynomial {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real) (P : ι → ι → ι → Real)
    (M : ι → ι → Real) (U : ι → ι → Real) (W : ι → Real) : Real :=
  2 * ∑ a, ∑ b, ∑ c, ∑ d, K a c b d * M c d * W a * W b -
    2 * ∑ a, ∑ b, ∑ c, ∑ d, P a c d * P b d c * W a * W b +
    8 * ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      K a d c e * P d b e * U a b * W c +
    4 * ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
      K a e c f * K b e d f * U a b * U c d

theorem hamiltonGram_quadratic_eq_hamiltonQuadraticForm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    hamiltonGramQuadratic Y X U W =
      hamiltonQuadraticForm (hamiltonGramK Y) (hamiltonGramP Y X)
        (hamiltonGramM X) U W := by
  unfold hamiltonGramQuadratic hamiltonGramLinearTerm hamiltonQuadraticForm
    hamiltonGramK hamiltonGramP hamiltonGramM
  have hYY (r : κ) :
      (∑ a, ∑ b, Y r a b * U a b) ^ 2 =
        ∑ a, ∑ b, ∑ c, ∑ d,
          (Y r a b * Y r c d) * U a b * U c d := by
    rw [pow_two, Fintype.sum_mul_sum]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hYX (r : κ) :
      (∑ a, ∑ b, Y r a b * U a b) * (∑ c, X r c * W c) =
        ∑ a, ∑ b, ∑ c,
          (Y r a b * X r c) * U a b * W c := by
    rw [Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hXX (r : κ) :
      (∑ c, X r c * W c) ^ 2 =
        ∑ c, ∑ d, (X r c * X r d) * W c * W d := by
    rw [pow_two, Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hsq (r : κ) :
      ((∑ a, ∑ b, Y r a b * U a b) + (∑ c, X r c * W c)) ^ 2 =
        (∑ a, ∑ b, Y r a b * U a b) ^ 2 +
          2 * ((∑ a, ∑ b, Y r a b * U a b) * (∑ c, X r c * W c)) +
          (∑ c, X r c * W c) ^ 2 := by
    ring
  simp_rw [hsq]
  simp_rw [hYY]
  simp_rw [hYX]
  simp_rw [hXX]
  have hYYsum :
      (∑ x, ∑ a, ∑ b, ∑ c, ∑ d,
        Y x a b * Y x c d * U a b * U c d) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          (∑ r, Y r a b * Y r c d) * U a b * U c d := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ x,
          Y x a b * Y x c d * U a b * U c d := move_outer4 _
      _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        calc
          _ = ∑ x, (Y x a b * Y x c d) * (U a b * U c d) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = (∑ x, Y x a b * Y x c d) * (U a b * U c d) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
  have hYXsum :
      (∑ x, 2 * ∑ a, ∑ b, ∑ c,
        Y x a b * X x c * U a b * W c) =
        2 * ∑ a, ∑ b, ∑ c,
          (∑ r, Y r a b * X r c) * U a b * W c := by
    calc
      _ = 2 * (∑ x, ∑ a, ∑ b, ∑ c,
          Y x a b * X x c * U a b * W c) := by
        rw [Finset.mul_sum]
      _ = 2 * (∑ a, ∑ b, ∑ c, ∑ x,
          Y x a b * X x c * U a b * W c) := by
        rw [move_outer3]
      _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        calc
          _ = ∑ x, (Y x a b * X x c) * (U a b * W c) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = (∑ x, Y x a b * X x c) * (U a b * W c) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
  have hXXsum :
      (∑ x, ∑ c, ∑ d,
        X x c * X x d * W c * W d) =
        ∑ c, ∑ d, (∑ r, X r c * X r d) * W c * W d := by
    calc
      _ = ∑ c, ∑ d, ∑ x,
          X x c * X x d * W c * W d := move_outer2 _
      _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        calc
          _ = ∑ x, (X x c * X x d) * (W c * W d) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = (∑ x, X x c * X x d) * (W c * W d) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
  simp only [Finset.sum_add_distrib]
  rw [hYYsum, hYXsum, hXXsum]

theorem hamiltonGramSigma_eq_block
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) (a b : ι) :
    hamiltonGramSigma Y X U W a b =
      (∑ c, hamiltonGramP Y X a b c * W c) +
        ∑ c, ∑ d, hamiltonGramK Y a b c d * U c d := by
  unfold hamiltonGramSigma hamiltonGramLinearTerm hamiltonGramP hamiltonGramK
  simp_rw [Finset.sum_mul]
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  have hX :
      (∑ x, ∑ i, Y x a b * (X x i * W i)) =
        ∑ x, ∑ i, Y i a b * X i x * W x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hU :
      (∑ x, ∑ x_1, ∑ i, Y x a b * (Y x x_1 i * U x_1 i)) =
        ∑ x, ∑ x_1, ∑ i, Y i a b * Y i x x_1 * U x x_1 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x_1 _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hX, hU]
  ring

theorem hamiltonGram_quadratic_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramQuadratic Y X U W := by
  unfold hamiltonGramQuadratic
  exact Finset.sum_nonneg fun r _ => sq_nonneg _

theorem hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hzero : hamiltonGramQuadratic Y X U W = 0) :
    ∀ r, hamiltonGramLinearTerm Y X U W r = 0 := by
  intro r
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun s _ => sq_nonneg (hamiltonGramLinearTerm Y X U W s))).mp hzero
  exact sq_eq_zero_iff.mp (hterms r (Finset.mem_univ r))

theorem hamiltonGram_quadratic_eq_zero_iff_linearTerms_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    hamiltonGramQuadratic Y X U W = 0 ↔
      ∀ r, hamiltonGramLinearTerm Y X U W r = 0 := by
  constructor
  · exact hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero Y X U W
  · intro hterm
    unfold hamiltonGramQuadratic
    apply Finset.sum_eq_zero
    intro r hr
    rw [hterm r]
    simp

theorem hamiltonGram_reaction_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramReaction Y X U W := by
  unfold hamiltonGramReaction
  exact Finset.sum_nonneg fun r _ =>
      Finset.sum_nonneg fun s _ => sq_nonneg _

theorem hamiltonGram_reaction_tangent_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramQuadratic Y X U W + hamiltonGramReaction Y X U W := by
  exact add_nonneg (hamiltonGram_quadratic_nonneg Y X U W)
    (hamiltonGram_reaction_nonneg Y X U W)

theorem hamiltonGram_reaction_tangent_nonneg_of_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hzero : hamiltonGramQuadratic Y X U W = 0) :
    0 ≤ hamiltonGramReaction Y X U W := by
  have h := hamiltonGram_reaction_tangent_nonneg Y X U W
  rw [hzero, zero_add] at h
  exact h

theorem hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hzero : hamiltonGramQuadratic Y X U W = 0) (a b : ι) :
    hamiltonGramSigma Y X U W a b = 0 := by
  have hterm := hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero Y X U W hzero
  unfold hamiltonGramSigma
  simp [hterm]

end DifferentialGeometry.Analysis.Spectral
