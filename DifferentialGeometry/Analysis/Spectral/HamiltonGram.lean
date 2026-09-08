import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions

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

private theorem exists_hamiltonGram_factorization_unbounded
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real)
    (P : ι → ι → ι → Real)
    (M : ι → ι → Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hQ : ∀ (U : ι → ι → Real) (W : ι → Real),
      0 ≤ hamiltonQuadraticForm K P M U W) :
    ∃ (m : Nat) (Y : Fin m → ι → ι → Real) (X : Fin m → ι → Real),
      (∀ r a b, Y r a b = -Y r b a) ∧
      K = hamiltonGramK Y ∧
      P = hamiltonGramP Y X ∧
      M = hamiltonGramM X := by
  classical
  let B : Matrix ((ι × ι) ⊕ ι) ((ι × ι) ⊕ ι) Real := fun i j =>
    match i, j with
    | Sum.inl (a, b), Sum.inl (c, d) => K a b c d
    | Sum.inl (a, b), Sum.inr c => P a b c
    | Sum.inr c, Sum.inl (a, b) => P a b c
    | Sum.inr a, Sum.inr b => M a b
  have hB : B.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by
      unfold Matrix.IsHermitian
      ext i j
      rcases i with i | i
      · rcases i with ⟨a, b⟩
        rcases j with j | j
        · rcases j with ⟨c, d⟩
          change K c d a b = K a b c d
          exact hKPair c d a b
        · change P a b j = P a b j
          rfl
      · rcases j with j | j
        · rcases j with ⟨c, d⟩
          change P c d i = P c d i
          rfl
        · change M j i = M i j
          exact hMSymm j i)
    (by
      intro z
      have hz := hQ (fun a b => z (Sum.inl (a, b))) (fun a => z (Sum.inr a))
      simp only [dotProduct, Matrix.mulVec, B, Fintype.sum_sum_type, star_trivial]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib]
      simp_rw [Finset.mul_sum]
      unfold hamiltonQuadraticForm at hz
      rw [show (∑ x, ∑ a, ∑ b,
          z (Sum.inr x) * (P a b x * z (Sum.inl (a, b)))) =
          ∑ a, ∑ b, ∑ x,
            z (Sum.inr x) * (P a b x * z (Sum.inl (a, b))) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]]
      have hKTerm (a b c d : ι) :
          z (Sum.inl (a, b)) * (K a b c d * z (Sum.inl (c, d))) =
            K a b c d * z (Sum.inl (a, b)) * z (Sum.inl (c, d)) := by
        ring
      have hPFirst (a b c : ι) :
          z (Sum.inl (a, b)) * (P a b c * z (Sum.inr c)) =
            P a b c * z (Sum.inl (a, b)) * z (Sum.inr c) := by
        ring
      have hPSecond (a b c : ι) :
          z (Sum.inr c) * (P a b c * z (Sum.inl (a, b))) =
            P a b c * z (Sum.inl (a, b)) * z (Sum.inr c) := by
        ring
      have hMTerm (a b : ι) :
          z (Sum.inr a) * (M a b * z (Sum.inr b)) =
            M a b * z (Sum.inr a) * z (Sum.inr b) := by
        ring
      simp_rw [hKTerm]
      simp_rw [hPFirst]
      simp_rw [hPSecond]
      simp_rw [hMTerm]
      simpa only [two_mul, add_assoc] using hz)
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  let Y₀ : Fin m → ι → ι → Real := fun r a b => v r (Sum.inl (a, b))
  let X : Fin m → ι → Real := fun r a => v r (Sum.inr a)
  let Y : Fin m → ι → ι → Real := fun r a b =>
    (Y₀ r a b - Y₀ r b a) / 2
  refine ⟨m, Y, X, ?_, ?_, ?_, ?_⟩
  · intro r a b
    simp only [Y]
    ring
  · funext a b c d
    have habcd := congrFun (congrFun hv (Sum.inl (a, b))) (Sum.inl (c, d))
    have habdc := congrFun (congrFun hv (Sum.inl (a, b))) (Sum.inl (d, c))
    have hbacd := congrFun (congrFun hv (Sum.inl (b, a))) (Sum.inl (c, d))
    have hbadc := congrFun (congrFun hv (Sum.inl (b, a))) (Sum.inl (d, c))
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial] at habcd
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial] at habdc
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial] at hbacd
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial] at hbadc
    unfold hamiltonGramK
    simp only [Y]
    change K a b c d = ∑ x,
      ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) *
      ((v x (Sum.inl (c, d)) - v x (Sum.inl (d, c))) / 2)
    have hexpand (x : Fin m) :
        ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) *
            ((v x (Sum.inl (c, d)) - v x (Sum.inl (d, c))) / 2) =
          (v x (Sum.inl (a, b)) * v x (Sum.inl (c, d)) -
            v x (Sum.inl (a, b)) * v x (Sum.inl (d, c)) -
            v x (Sum.inl (b, a)) * v x (Sum.inl (c, d)) +
            v x (Sum.inl (b, a)) * v x (Sum.inl (d, c))) / 4 := by
      ring
    simp_rw [hexpand]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    rw [← habcd, ← habdc, ← hbacd, ← hbadc]
    have hKLast (i j k l : ι) : K i j k l = -K i j l k := by
      rw [hKPair, hKSkew, hKPair]
    linarith [hKLast a b c d, hKSkew a b c d,
      hKLast b a c d, hKSkew a b d c]
  · funext a b c
    have habc := congrFun (congrFun hv (Sum.inl (a, b))) (Sum.inr c)
    have hbac := congrFun (congrFun hv (Sum.inl (b, a))) (Sum.inr c)
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial] at habc hbac
    unfold hamiltonGramP
    change P a b c = ∑ x,
      ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) * v x (Sum.inr c)
    have hexpand (x : Fin m) :
        ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) *
            v x (Sum.inr c) =
          (v x (Sum.inl (a, b)) * v x (Sum.inr c) -
            v x (Sum.inl (b, a)) * v x (Sum.inr c)) / 2 := by
      ring
    simp_rw [hexpand]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    rw [← habc, ← hbac]
    linarith [hPSkew a b c]
  · funext a b
    have hab := congrFun (congrFun hv (Sum.inr a)) (Sum.inr b)
    simpa only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial,
      hamiltonGramM, X] using hab

def hamiltonReactionPolynomial {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real) (P : ι → ι → ι → Real)
    (M : ι → ι → Real) (U : ι → ι → Real) (W : ι → Real) : Real :=
  2 * ∑ a, ∑ b, ∑ c, ∑ d, K a c b d * M c d * W a * W b -
    2 * ∑ a, ∑ b, ∑ c, ∑ d, P a c d * P b d c * W a * W b +
    8 * ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      K a d c e * P d b e * U a b * W c +
    4 * ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
      K a e c f * K b e d f * U a b * U c d

private theorem exists_hamiltonGram_compression
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → ℝ) (X : κ → ι → ℝ)
    (hY : ∀ r a b, Y r a b = -Y r b a) :
    ∃ (m : ℕ) (Y' : Fin m → ι → ι → ℝ) (X' : Fin m → ι → ℝ),
      m ≤ Fintype.card ι * (Fintype.card ι + 1) / 2 ∧
      (∀ r a b, Y' r a b = -Y' r b a) ∧
      hamiltonGramK Y = hamiltonGramK Y' ∧
      hamiltonGramP Y X = hamiltonGramP Y' X' ∧
      hamiltonGramM X = hamiltonGramM X' := by
  classical
  let e := Fintype.equivFin ι
  let : LinearOrder ι := LinearOrder.lift' e e.injective
  let y (a b : ι) : EuclideanSpace ℝ κ := WithLp.toLp 2 (fun r => Y r a b)
  let z (a : ι) : EuclideanSpace ℝ κ := WithLp.toLp 2 (fun r => X r a)
  let η := {p : ι × ι // p.1 < p.2} ⊕ ι
  let v : η → EuclideanSpace ℝ κ := Sum.elim (fun p => y p.1.1 p.1.2) z
  let S := Submodule.span ℝ (Set.range v)
  have hySkew (a b : ι) : y a b = -y b a := by
    ext r
    exact hY r a b
  have hyDiag (a : ι) : y a a = 0 := by
    ext r
    change Y r a a = 0
    linarith [hY r a a]
  have hy (a b : ι) : y a b ∈ S := by
    rcases lt_trichotomy a b with h | rfl | h
    · exact Submodule.subset_span ⟨Sum.inl ⟨(a, b), h⟩, rfl⟩
    · rw [hyDiag]
      exact S.zero_mem
    · rw [hySkew]
      exact S.neg_mem (Submodule.subset_span ⟨Sum.inl ⟨(b, a), h⟩, rfl⟩)
  have hz (a : ι) : z a ∈ S :=
    Submodule.subset_span ⟨Sum.inr a, rfl⟩
  let ys (a b : ι) : S := ⟨y a b, hy a b⟩
  let zs (a : ι) : S := ⟨z a, hz a⟩
  let b := stdOrthonormalBasis ℝ S
  let Y' (r : Fin (Module.finrank ℝ S)) (a c : ι) : ℝ := inner ℝ (b r) (ys a c)
  let X' (r : Fin (Module.finrank ℝ S)) (a : ι) : ℝ := inner ℝ (b r) (zs a)
  have hdim : Module.finrank ℝ S ≤ Fintype.card ι * (Fintype.card ι + 1) / 2 := by
    calc
      Module.finrank ℝ S ≤ Fintype.card η := finrank_range_le_card v
      _ = (Fintype.card ι).choose 2 + Fintype.card ι := by
        simp only [η, Fintype.card_sum, Fintype.card_subtype,
          Fintype.card_product_filter_lt]
      _ = (Fintype.card ι + 1).choose 2 := by
        rw [Nat.choose_succ_succ' (Fintype.card ι) 1, Nat.choose_one_right]
        exact Nat.add_comm _ _
      _ = Fintype.card ι * (Fintype.card ι + 1) / 2 := by
        rw [Nat.choose_two_right]
        simp only [Nat.add_sub_cancel]
        rw [Nat.mul_comm]
  have hinner (u w : S) :
      (∑ r, inner ℝ (b r) u * inner ℝ (b r) w) = inner ℝ (u : EuclideanSpace ℝ κ) w := by
    calc
      _ = ∑ r, inner ℝ u (b r) * inner ℝ (b r) w := by
        congr 1
        funext r
        rw [real_inner_comm u (b r)]
      _ = inner ℝ u w := b.sum_inner_mul_inner u w
      _ = inner ℝ (u : EuclideanSpace ℝ κ) w := Submodule.coe_inner S u w
  refine ⟨Module.finrank ℝ S, Y', X', hdim, ?_, ?_, ?_, ?_⟩
  · intro r a c
    have hys : ys a c = -ys c a := Subtype.ext (hySkew a c)
    change inner ℝ (b r) (ys a c) = -inner ℝ (b r) (ys c a)
    rw [hys, inner_neg_right]
  · funext a c d f
    unfold hamiltonGramK
    change (∑ r, Y r a c * Y r d f) =
      ∑ r, inner ℝ (b r) (ys a c) * inner ℝ (b r) (ys d f)
    rw [hinner]
    simp only [ys, y, PiLp.inner_apply, Real.inner_apply]
  · funext a c d
    unfold hamiltonGramP
    change (∑ r, Y r a c * X r d) =
      ∑ r, inner ℝ (b r) (ys a c) * inner ℝ (b r) (zs d)
    rw [hinner]
    simp only [ys, zs, y, z, PiLp.inner_apply, Real.inner_apply]
  · funext a c
    unfold hamiltonGramM
    change (∑ r, X r a * X r c) =
      ∑ r, inner ℝ (b r) (zs a) * inner ℝ (b r) (zs c)
    rw [hinner]
    simp only [zs, z, PiLp.inner_apply, Real.inner_apply]

private theorem sum_mul_skew_projection
    {ι : Type*} [Fintype ι] (A U : ι → ι → ℝ)
    (hA : ∀ a b, A a b = -A b a) :
    (∑ a, ∑ b, A a b * U a b) =
      ∑ a, ∑ b, A a b * ((U a b - U b a) / 2) := by
  have hswap : (∑ a, ∑ b, A a b * U b a) = -(∑ a, ∑ b, A a b * U a b) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hA b a, neg_mul]
  simp_rw [← mul_div_assoc, mul_sub]
  simp_rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib]
  rw [hswap]
  ring

theorem hamiltonQuadraticForm_skew_projection
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → ℝ) (P : ι → ι → ι → ℝ) (M : ι → ι → ℝ)
    (U : ι → ι → ℝ) (W : ι → ℝ)
    (hKFirst : ∀ a b c d, K a b c d = -K b a c d)
    (hKLast : ∀ a b c d, K a b c d = -K a b d c)
    (hP : ∀ a b c, P a b c = -P b a c) :
    hamiltonQuadraticForm K P M U W =
      hamiltonQuadraticForm K P M (fun a b => (U a b - U b a) / 2) W := by
  let V (a b : ι) := (U a b - U b a) / 2
  have hlast :
      (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * U c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * V c d := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    apply sum_mul_skew_projection (fun c d => K a b c d * U a b) U
    intro c d
    rw [hKLast a b c d, neg_mul]
  have hfirst :
      (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * V c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, K a b c d * V a b * V c d := by
    have hcoeff (a b : ι) :
        (∑ c, ∑ d, K a b c d * V c d) = -(∑ c, ∑ d, K b a c d * V c d) := by
      simp_rw [hKFirst a b, neg_mul]
      simp only [Finset.sum_neg_distrib]
    have h := sum_mul_skew_projection (fun a b => ∑ c, ∑ d, K a b c d * V c d) U hcoeff
    simpa only [Finset.sum_mul, mul_right_comm] using h
  have hcross :
      (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) =
        ∑ a, ∑ b, ∑ c, P a b c * V a b * W c := by
    have hcoeff (a b : ι) :
        (∑ c, P a b c * W c) = -(∑ c, P b a c * W c) := by
      simp_rw [hP a b, neg_mul]
      simp only [Finset.sum_neg_distrib]
    have h := sum_mul_skew_projection (fun a b => ∑ c, P a b c * W c) U hcoeff
    simpa only [Finset.sum_mul, mul_right_comm] using h
  unfold hamiltonQuadraticForm
  rw [hlast, hfirst, hcross]

theorem exists_hamiltonGram_factorization_card_le
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → ℝ)
    (P : ι → ι → ι → ℝ)
    (M : ι → ι → ℝ)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hQ : ∀ (U : ι → ι → ℝ) (W : ι → ℝ),
      (∀ a b, U a b = -U b a) → 0 ≤ hamiltonQuadraticForm K P M U W) :
    ∃ (m : ℕ) (Y : Fin m → ι → ι → ℝ) (X : Fin m → ι → ℝ),
      m ≤ Fintype.card ι * (Fintype.card ι + 1) / 2 ∧
      (∀ r a b, Y r a b = -Y r b a) ∧
      K = hamiltonGramK Y ∧
      P = hamiltonGramP Y X ∧
      M = hamiltonGramM X := by
  obtain ⟨m, Y, X, hY, hK, hP, hM⟩ :=
    exists_hamiltonGram_factorization_unbounded K P M hKPair hKSkew hPSkew hMSymm (by
      intro U W
      have hKLast (a b c d : ι) : K a b c d = -K a b d c := by
        rw [hKPair a b c d, hKSkew c d a b, hKPair d c a b]
      rw [hamiltonQuadraticForm_skew_projection K P M U W hKSkew hKLast hPSkew]
      apply hQ
      intro a b
      ring)
  obtain ⟨m', Y', X', hm', hY', hK', hP', hM'⟩ :=
    exists_hamiltonGram_compression Y X hY
  exact ⟨m', Y', X', hm', hY', hK.trans hK', hP.trans hP', hM.trans hM'⟩


theorem exists_hamiltonGram_factorization
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real)
    (P : ι → ι → ι → Real)
    (M : ι → ι → Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hQ : ∀ (U : ι → ι → Real) (W : ι → Real),
      0 ≤ hamiltonQuadraticForm K P M U W) :
    ∃ (m : Nat) (Y : Fin m → ι → ι → Real) (X : Fin m → ι → Real),
      (∀ r a b, Y r a b = -Y r b a) ∧
      K = hamiltonGramK Y ∧
      P = hamiltonGramP Y X ∧
      M = hamiltonGramM X := by
  obtain ⟨m, Y, X, hm, hY, hK, hP, hM⟩ :=
    exists_hamiltonGram_factorization_card_le K P M hKPair hKSkew hPSkew hMSymm
      (fun U W _ => hQ U W)
  exact ⟨m, Y, X, hY, hK, hP, hM⟩

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
