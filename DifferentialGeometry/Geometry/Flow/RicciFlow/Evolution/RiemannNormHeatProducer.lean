import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Riemann Curvature Norm Heat Equation with Cubic Reaction Bound

Chow-Knopf *The Ricci Flow: An Introduction*, Lemma 7.4 (= MSM144 eq. 14.16):
for a Ricci-flow solution the squared curvature norm satisfies the heat
equation with a cubically bounded reaction term,
`∂ₜ |Rm|² = Δ |Rm|² − 2 |∇Rm|² + reaction`, with `|reaction| ≤ C(n) · |Rm|³`.

The genuinely new content of this file is the **reaction bound**: the reaction
is the degree-three `B`-tensor curvature contraction
`reaction = 4 ∑ Rₐᵦ𝒸𝒹 (Bₐᵦ𝒸𝒹 − Bₐᵦ𝒹𝒸 + Bₐ𝒸ᵦ𝒹 − Bₐ𝒹ᵦ𝒸)`,
and we bound it by `C(n) · (|Rm|²)^{3/2}` with `C(n) = 16 · card⁶` using the
Cauchy–Schwarz / single-component estimates recorded in `compNormSq4`.  The
heat-equation *shape* is assembled from the existing `Rm04NormHeatEquationOn`
component frontier in `Evolution/RiemannNorm.lean`.

Everything is phrased in a fixed **orthonormal** frame, which is the natural
setting for Uhlenbeck's trick (the evolving frame stays orthonormal), so the
inverse metric is the Kronecker delta and the squared norm is the plain sum of
squared components `∑ Rₐᵦ𝒸𝒹²`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

/-! ## Reusable component-norm algebra for `(0,4)` arrays

These are pure, frame-free real-algebra lemmas about a finite four-index real
array `R`.  They live at the reusable abstraction level mandated by the
project's tensor-calculation workflow: no curvature, metric, or Ricci-flow
hypothesis enters.  We bound the cubic `B`-tensor contraction by the `3/2`
power of the squared component norm. -/

section ComponentAlgebra

variable {Idx : Type*} [Fintype Idx]

/-- Squared component norm of a four-index real array, `∑ Rₐᵦ𝒸𝒹²`. -/
def compNormSq4 (R : Idx → Idx → Idx → Idx → Real) : Real :=
  ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx, (R a b c d) ^ 2

theorem compNormSq4_nonneg (R : Idx → Idx → Idx → Idx → Real) :
    0 ≤ compNormSq4 R := by
  unfold compNormSq4
  refine Finset.sum_nonneg fun a _ => ?_
  refine Finset.sum_nonneg fun b _ => ?_
  refine Finset.sum_nonneg fun c _ => ?_
  refine Finset.sum_nonneg fun d _ => ?_
  exact sq_nonneg _

/-- Each squared component is dominated by the squared component norm. -/
theorem sq_le_compNormSq4
    (R : Idx → Idx → Idx → Idx → Real) (a b c d : Idx) :
    (R a b c d) ^ 2 ≤ compNormSq4 R := by
  classical
  unfold compNormSq4
  have hd : (R a b c d) ^ 2 ≤ ∑ d' : Idx, (R a b c d') ^ 2 :=
    Finset.single_le_sum (f := fun d' : Idx => (R a b c d') ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ d)
  have hc : (∑ d' : Idx, (R a b c d') ^ 2) ≤
      ∑ c' : Idx, ∑ d' : Idx, (R a b c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun c' : Idx => ∑ d' : Idx, (R a b c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have hb : (∑ c' : Idx, ∑ d' : Idx, (R a b c' d') ^ 2) ≤
      ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (R a b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun b' : Idx => ∑ c' : Idx, ∑ d' : Idx, (R a b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  have ha : (∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (R a b' c' d') ^ 2) ≤
      ∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (R a' b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun a' : Idx => ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (R a' b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  exact le_trans hd (le_trans hc (le_trans hb ha))

/-- Each component's absolute value is dominated by the component norm. -/
theorem abs_le_sqrt_compNormSq4
    (R : Idx → Idx → Idx → Idx → Real) (a b c d : Idx) :
    |R a b c d| ≤ Real.sqrt (compNormSq4 R) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_compNormSq4 R a b c d)

/-- Uhlenbeck `B`-tensor for an orthonormal-frame component array:
`Bₐᵦ𝒸𝒹 = ∑ₑ ∑_f Rₐₑᵦ_f R𝒸ₑ𝒹_f`.  This is `uhlenbeckBTensorInFrame` with the
inverse metric specialized to the Kronecker delta. -/
def bTensorDown (R : Idx → Idx → Idx → Idx → Real)
    (a b c d : Idx) : Real :=
  ∑ e : Idx, ∑ f : Idx, R a e b f * R c e d f

/-- The `B`-tensor entry is bounded by `card² · ‖R‖²`.  Each factor of the
product is at most `√‖R‖²`, and there are `card²` summands. -/
theorem abs_bTensorDown_le
    (R : Idx → Idx → Idx → Idx → Real) (a b c d : Idx) :
    |bTensorDown R a b c d| ≤
      (Fintype.card Idx : Real) ^ 2 * compNormSq4 R := by
  classical
  have hStep :
      |bTensorDown R a b c d| ≤
        ∑ e : Idx, ∑ f : Idx, |R a e b f * R c e d f| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun e _ => ?_
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans hStep ?_
  have hTerm : ∀ e f : Idx,
      |R a e b f * R c e d f| ≤ compNormSq4 R := by
    intro e f
    rw [abs_mul]
    have h1 : |R a e b f| ^ 2 ≤ compNormSq4 R := by
      rw [sq_abs]; exact sq_le_compNormSq4 R a e b f
    have h2 : |R c e d f| ^ 2 ≤ compNormSq4 R := by
      rw [sq_abs]; exact sq_le_compNormSq4 R c e d f
    have hbnd : |R a e b f| ≤ Real.sqrt (compNormSq4 R) :=
      abs_le_sqrt_compNormSq4 R a e b f
    have hbnd2 : |R c e d f| ≤ Real.sqrt (compNormSq4 R) :=
      abs_le_sqrt_compNormSq4 R c e d f
    have hsqrt_nonneg : 0 ≤ Real.sqrt (compNormSq4 R) := Real.sqrt_nonneg _
    calc
      |R a e b f| * |R c e d f|
          ≤ Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq4 R) :=
            mul_le_mul hbnd hbnd2 (abs_nonneg _) hsqrt_nonneg
      _ = compNormSq4 R := Real.mul_self_sqrt (compNormSq4_nonneg R)
  calc
    (∑ e : Idx, ∑ f : Idx, |R a e b f * R c e d f|)
        ≤ ∑ e : Idx, ∑ f : Idx, compNormSq4 R := by
          refine Finset.sum_le_sum fun e _ => ?_
          exact Finset.sum_le_sum fun f _ => hTerm e f
    _ = (Fintype.card Idx : Real) ^ 2 * compNormSq4 R := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq]
          ring

/-- The curvature reaction term in the orthonormal frame: the degree-three
`B`-tensor contraction
`reaction = 4 ∑ Rₐᵦ𝒸𝒹 (Bₐᵦ𝒸𝒹 − Bₐᵦ𝒹𝒸 + Bₐ𝒸ᵦ𝒹 − Bₐ𝒹ᵦ𝒸)`. -/
def rmReactionDown (R : Idx → Idx → Idx → Idx → Real) : Real :=
  4 * ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
    R a b c d *
      (bTensorDown R a b c d - bTensorDown R a b d c +
        bTensorDown R a c b d - bTensorDown R a d b c)

/-- Triangle inequality for the four-term bracket `w - x + y - z`. -/
private theorem abs_four_bracket_le (w x y z : Real) :
    |w - x + y - z| ≤ |w| + |x| + |y| + |z| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hw := neg_abs_le w
    have hx := le_abs_self x
    have hy := neg_abs_le y
    have hz := le_abs_self z
    linarith
  · have hw := le_abs_self w
    have hx := neg_abs_le x
    have hy := le_abs_self y
    have hz := neg_abs_le z
    linarith

/-- The combined `B`-tensor bracket is bounded by `4 · card² · ‖R‖²`. -/
private theorem abs_bracket_le
    (R : Idx → Idx → Idx → Idx → Real) (a b c d : Idx) :
    |bTensorDown R a b c d - bTensorDown R a b d c +
        bTensorDown R a c b d - bTensorDown R a d b c| ≤
      4 * ((Fintype.card Idx : Real) ^ 2 * compNormSq4 R) := by
  have h1 := abs_bTensorDown_le R a b c d
  have h2 := abs_bTensorDown_le R a b d c
  have h3 := abs_bTensorDown_le R a c b d
  have h4 := abs_bTensorDown_le R a d b c
  calc
    |bTensorDown R a b c d - bTensorDown R a b d c +
        bTensorDown R a c b d - bTensorDown R a d b c|
        ≤ |bTensorDown R a b c d| + |bTensorDown R a b d c| +
            |bTensorDown R a c b d| + |bTensorDown R a d b c| :=
          abs_four_bracket_le _ _ _ _
    _ ≤ ((Fintype.card Idx : Real) ^ 2 * compNormSq4 R) +
          ((Fintype.card Idx : Real) ^ 2 * compNormSq4 R) +
          ((Fintype.card Idx : Real) ^ 2 * compNormSq4 R) +
          ((Fintype.card Idx : Real) ^ 2 * compNormSq4 R) := by
          gcongr
    _ = 4 * ((Fintype.card Idx : Real) ^ 2 * compNormSq4 R) := by ring

/-- For a nonnegative real `x`, the `3/2` power is `x · √x`. -/
theorem rpow_three_halves_eq_mul_sqrt {x : Real} (hx : 0 ≤ x) :
    x ^ (3 / 2 : Real) = x * Real.sqrt x := by
  have hsplit : (3 / 2 : Real) = 1 + 1 / 2 := by norm_num
  rw [hsplit, Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- **Cubic reaction bound.**  The orthonormal-frame curvature reaction term is
bounded by `16 · card⁶ · ‖R‖³`, i.e. `|reaction| ≤ C(n) · (‖R‖²)^{3/2}` with
`C(n) = 16 · card⁶`.

This is the algebraic core of Chow–Knopf Lemma 7.4's reaction estimate: the
reaction is a degree-three contraction in `Rm`, and Cauchy–Schwarz on the frame
components yields the cubic bound. -/
theorem abs_rmReactionDown_le
    (R : Idx → Idx → Idx → Idx → Real) :
    |rmReactionDown R| ≤
      16 * (Fintype.card Idx : Real) ^ 6 *
        (compNormSq4 R * Real.sqrt (compNormSq4 R)) := by
  classical
  set N : Real := compNormSq4 R with hN
  have hNnonneg : 0 ≤ N := compNormSq4_nonneg R
  have hsqrt_nonneg : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- bound the inner sum
  have hInner :
      |∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          R a b c d *
            (bTensorDown R a b c d - bTensorDown R a b d c +
              bTensorDown R a c b d - bTensorDown R a d b c)| ≤
        ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          (Real.sqrt N * (4 * ((Fintype.card Idx : Real) ^ 2 * N))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun a _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun c _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun d _ => ?_
    rw [abs_mul]
    have hbnd1 : |R a b c d| ≤ Real.sqrt N := by
      rw [hN]; exact abs_le_sqrt_compNormSq4 R a b c d
    have hbnd2 :
        |bTensorDown R a b c d - bTensorDown R a b d c +
            bTensorDown R a c b d - bTensorDown R a d b c| ≤
          4 * ((Fintype.card Idx : Real) ^ 2 * N) := by
      rw [hN]; exact abs_bracket_le R a b c d
    have hnn : (0 : Real) ≤ 4 * ((Fintype.card Idx : Real) ^ 2 * N) := by
      have : (0 : Real) ≤ (Fintype.card Idx : Real) ^ 2 * N :=
        mul_nonneg (by positivity) hNnonneg
      linarith
    exact mul_le_mul hbnd1 hbnd2 (abs_nonneg _) hsqrt_nonneg
  -- evaluate the constant sum
  have hConst :
      (∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          (Real.sqrt N * (4 * ((Fintype.card Idx : Real) ^ 2 * N)))) =
        (Fintype.card Idx : Real) ^ 4 *
          (Real.sqrt N * (4 * ((Fintype.card Idx : Real) ^ 2 * N))) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hN] at hInner hConst ⊢
  unfold rmReactionDown
  rw [abs_mul]
  have h4 : |(4 : Real)| = 4 := by norm_num
  rw [h4]
  calc
    4 * |∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          R a b c d *
            (bTensorDown R a b c d - bTensorDown R a b d c +
              bTensorDown R a c b d - bTensorDown R a d b c)|
        ≤ 4 * ((Fintype.card Idx : Real) ^ 4 *
            (Real.sqrt (compNormSq4 R) *
              (4 * ((Fintype.card Idx : Real) ^ 2 * compNormSq4 R)))) := by
          have hInner' := le_trans hInner (le_of_eq hConst)
          exact mul_le_mul_of_nonneg_left hInner' (by norm_num)
    _ = 16 * (Fintype.card Idx : Real) ^ 6 *
          (compNormSq4 R * Real.sqrt (compNormSq4 R)) := by
          ring

end ComponentAlgebra

/-! ## Solution-facing reaction term, norm, and the cubic bound

We now specialize the component algebra to an actual Ricci-flow solution in a
fixed **orthonormal** frame.  In this frame the inverse metric is the Kronecker
delta, so the solution's `|Rm|²` (`rm04NormSqInFrame`) is the plain component
norm and the canonical `B`-tensor reaction reduces to `rmReactionDown`. -/

section Solution

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- A frame is orthonormal for the supplied inverse metric components at `(t,x)`
when the inverse metric is the Kronecker delta there. -/
def InverseMetricOrthonormalAt
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (t : Real) (x : M) : Prop :=
  ∀ i j : Idx, gInv t x i j = (if i = j then 1 else 0)

/-- Canonical curvature reaction term for the Riemann-norm heat equation, the
degree-three `B`-tensor contraction
`4 ∑ Rₐᵦ𝒸𝒹 (Bₐᵦ𝒸𝒹 − Bₐᵦ𝒹𝒸 + Bₐ𝒸ᵦ𝒹 − Bₐ𝒹ᵦ𝒸)`,
with `B = uhlenbeckBTensorInFrame` built from the solution's lowered Riemann
components.  This is the genuine cubic reaction in `Rm`. -/
def rmReactionInFrame
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    4 * ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
      solutionRm04CompInFrame (I := I) Rm04 frame t x a b c d *
        (uhlenbeckBTensorInFrame gInv (solutionRm04CompInFrame (I := I) Rm04 frame) t x a b c d -
          uhlenbeckBTensorInFrame gInv (solutionRm04CompInFrame (I := I) Rm04 frame) t x a b d c +
          uhlenbeckBTensorInFrame gInv (solutionRm04CompInFrame (I := I) Rm04 frame) t x a c b d -
          uhlenbeckBTensorInFrame gInv (solutionRm04CompInFrame (I := I) Rm04 frame) t x a d b c)

/-- In an orthonormal frame the raised Riemann component equals the lowered one. -/
private theorem raisedRm04CompInFrame_orthonormal
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x)
    (a b c d : Idx) :
    raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d =
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d := by
  classical
  rw [raisedRm04CompInFrame_apply]
  unfold InverseMetricOrthonormalAt at horth
  simp only [horth]
  simp [Finset.mem_univ]

/-- In an orthonormal frame the solution's `|Rm|²` equals the component norm. -/
theorem rm04NormSqInFrame_eq_compNormSq4
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x) :
    rm04NormSqInFrame (I := I) Rm04 gInv frame t x =
      compNormSq4 (fun a b c d : Idx =>
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d) := by
  classical
  rw [rm04NormSqInFrame_apply]
  unfold compNormSq4
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [raisedRm04CompInFrame_orthonormal (I := I) Rm04 gInv frame t x horth a b c d]
  ring

/-- In an orthonormal frame the canonical `B`-tensor reduces to `bTensorDown`. -/
private theorem uhlenbeckBTensorInFrame_orthonormal
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x)
    (a b c d : Idx) :
    uhlenbeckBTensorInFrame gInv (solutionRm04CompInFrame (I := I) Rm04 frame) t x a b c d =
      bTensorDown (fun a' b' c' d' : Idx =>
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a' b' c' d')
        a b c d := by
  classical
  unfold uhlenbeckBTensorInFrame bTensorDown
  unfold InverseMetricOrthonormalAt at horth
  simp only [horth, solutionRm04CompInFrame]
  set R : Idx → Idx → Idx → Idx → Real :=
    fun a' b' c' d' =>
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a' b' c' d'
    with hRdef
  -- The B-tensor is ∑e ∑g ∑f ∑r δ(e,g)·δ(f,r)·R(a,e,b,f)·R(c,g,d,r).
  -- Collapse the g-sum (forces g = e) then the r-sum (forces r = f).
  refine Finset.sum_congr rfl fun e _ => ?_
  -- now ∑g ∑f ∑r δ(e,g)·δ(f,r)·R(a,e,b,f)·R(c,g,d,r), reassociate to collapse g
  have hg : ∀ f r : Idx,
      (∑ g : Idx, (if e = g then (1 : Real) else 0) * (if f = r then 1 else 0) *
          R a e b f * R c g d r) =
        (if f = r then (1 : Real) else 0) * R a e b f * R c e d r := by
    intro f r
    rw [Finset.sum_eq_single e]
    · simp
    · intro g _ hge
      rw [if_neg (fun h => hge h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ e) h
  calc
    (∑ g : Idx, ∑ f : Idx, ∑ r : Idx,
        (if e = g then (1 : Real) else 0) * (if f = r then 1 else 0) *
          R a e b f * R c g d r)
        = ∑ f : Idx, ∑ r : Idx, ∑ g : Idx,
            (if e = g then (1 : Real) else 0) * (if f = r then 1 else 0) *
              R a e b f * R c g d r := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ f : Idx, ∑ r : Idx,
          (if f = r then (1 : Real) else 0) * R a e b f * R c e d r := by
          refine Finset.sum_congr rfl fun f _ => ?_
          refine Finset.sum_congr rfl fun r _ => ?_
          exact hg f r
    _ = ∑ f : Idx, R a e b f * R c e d f := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_eq_single f]
          · simp
          · intro r _ hfr
            rw [if_neg (fun h => hfr h.symm)]
            ring
          · intro h; exact absurd (Finset.mem_univ f) h

/-- In an orthonormal frame the canonical reaction reduces to `rmReactionDown`. -/
theorem rmReactionInFrame_eq_rmReactionDown
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x) :
    rmReactionInFrame (I := I) Rm04 gInv frame t x =
      rmReactionDown (fun a b c d : Idx =>
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d) := by
  classical
  unfold rmReactionInFrame rmReactionDown
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [uhlenbeckBTensorInFrame_orthonormal (I := I) Rm04 gInv frame t x horth a b c d,
    uhlenbeckBTensorInFrame_orthonormal (I := I) Rm04 gInv frame t x horth a b d c,
    uhlenbeckBTensorInFrame_orthonormal (I := I) Rm04 gInv frame t x horth a c b d,
    uhlenbeckBTensorInFrame_orthonormal (I := I) Rm04 gInv frame t x horth a d b c]
  rfl

/-- **Reaction bound** (Chow–Knopf Lemma 7.4 estimate), solution form.

In an orthonormal frame the canonical curvature reaction term satisfies
`|reaction t x| ≤ 16 · card⁶ · (|Rm|²)^{3/2}`, i.e. `|reaction| ≤ C(n) · |Rm|³`
with `C(n) = 16 · (dim)⁶`. -/
theorem abs_rmReactionInFrame_le
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x) :
    |rmReactionInFrame (I := I) Rm04 gInv frame t x| ≤
      16 * (Fintype.card Idx : Real) ^ 6 *
        (rm04NormSqInFrame (I := I) Rm04 gInv frame t x) ^ (3 / 2 : Real) := by
  set R : Idx → Idx → Idx → Idx → Real :=
    fun a b c d => DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d
    with hR
  rw [rmReactionInFrame_eq_rmReactionDown (I := I) Rm04 gInv frame t x horth]
  rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) Rm04 gInv frame t x horth]
  rw [rpow_three_halves_eq_mul_sqrt (compNormSq4_nonneg R)]
  exact abs_rmReactionDown_le R

/-- **Riemann-norm heat equation with the canonical cubic reaction** (Chow–Knopf
Lemma 7.4), solution form.

Assembled from the existing raw-derivative / contraction-simplification /
Bochner-Laplacian component frontier in `Evolution/RiemannNorm.lean`, with the
reaction instantiated to the genuine `B`-tensor contraction `rmReactionInFrame`.
The accompanying cubic bound is `abs_rmReactionInFrame_le`. -/
theorem rm04NormHeatEquationOn_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (rmNormLap roughLapInner nablaRmNormSq : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn
      (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapInner
      (rmReactionInFrame (I := I) Rm04 gInv frame))
    (h_lap : Rm04NormLaplacianComponentsOn
      rmNormLap roughLapInner nablaRmNormSq) :
    Rm04NormHeatEquationOn
      (D := D) (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      rmNormLap nablaRmNormSq
      (rmReactionInFrame (I := I) Rm04 gInv frame) :=
  rm04NormHeatEquationOn_of_rawDerivative
    (I := I) S Rm04 gInv frame rm04Dt rmNormLap roughLapInner nablaRmNormSq
    (rmReactionInFrame (I := I) Rm04 gInv frame)
    h_raw h_simplify h_lap

end Solution

end DifferentialGeometry.PDE.RicciFlow
