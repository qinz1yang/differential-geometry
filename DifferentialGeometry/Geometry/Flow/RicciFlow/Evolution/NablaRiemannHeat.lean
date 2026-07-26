import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RiemannNormHeatProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Heat inequality for the covariant-derivative curvature norm `|∇Rm|²`

Chow–Knopf *The Ricci Flow: An Introduction*, eq. 7.2 (= eq. 7.4 at `k = 1`,
= MSM144 eq. 14.17):  for a Ricci-flow solution the squared norm of the
covariant derivative of the Riemann tensor satisfies the heat inequality

`(∂ₜ − Δ) |∇Rm|² ≤ −2 |∇²Rm|² + C(n) · |Rm| · |∇Rm|²`.

This is the first-derivative (`k = 1`) producer in the Bernstein–Bando–Shi
tower, the exact analogue of the `k = 0` curvature-norm producer in
`Evolution/RiemannNormHeatProducer.lean` (which produced
`Rm04NormHeatEquationOn` for `|Rm|²` with a cubic reaction bound).

## Mathematical route (eq 7.2)

Writing `∇Rm` for the lowered `(0,5)` covariant derivative of `Rm` and using the
Uhlenbeck trick (the evolving orthonormal frame stays orthonormal):

* `∂ₜ ∇Rm = Δ ∇Rm + Rm ∗ ∇Rm`, where `∗` packages every contraction of one
  curvature factor against one `∇Rm` factor.  This combines `∂ₜRm = ΔRm + Rm∗Rm`
  (Uhlenbeck), the connection evolution `∂ₜΓ = ∇Rc ∗ 1`, and the Laplacian
  commutator `[∇, Δ]Rm = Rm ∗ ∇Rm`.
* Therefore
  `(∂ₜ − Δ) |∇Rm|² = 2⟨Rm ∗ ∇Rm, ∇Rm⟩ − 2 |∇²Rm|²`,
  and the `∗`-norm bound `|Rm ∗ ∇Rm| ≤ C |Rm| |∇Rm|` (Cauchy–Schwarz) gives the
  reaction estimate `2⟨Rm ∗ ∇Rm, ∇Rm⟩ ≤ C(n) |Rm| |∇Rm|²`.

## The `∗`-convention (the tractability lever)

Following the `k = 0` producer and the task's mandated route, we do **not**
compute the exact reaction tensor.  We model the reaction term schematically as
a contraction of a `Rm ∗ ∇Rm` array against `∇Rm`, and only ever use the
component `∗`-norm bound.  The raw component facts (the time-derivative product
rule, the contraction simplification, the Bochner Laplacian split, and the
`[∇, Δ]` commutator identity) are taken as **hypotheses**; the heat inequality
and the `∗`-norm reaction bound are proved on top of them.

The genuinely new content of this file is therefore:

* `nablaRmReactionStarBound` — the algebraic Cauchy–Schwarz reaction estimate
  `|reaction| ≤ C(n) · |∇Rm|² · √(|Rm|²)`, the `k = 1` analogue of
  `abs_rmReactionDown_le`;
* `nablaRm04NormHeatBoundOn_of_components` — the producer assembling the scalar
  heat-inequality predicate `NablaRm04NormHeatBoundOn` (the `−2|∇²Rm|²` form is
  available as `nablaRm04NormHeatBoundSharp_of_components`).

Everything algebraic is phrased in a fixed **orthonormal** frame, matching the
`InverseMetricOrthonormalAt` convention of `RiemannNormHeatProducer.lean`, so the
inverse metric is the Kronecker delta and `|∇Rm|²` is the plain sum of squared
components.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

/-! ## Reusable component-norm algebra for `(0,5)` arrays

These are pure, frame-free real-algebra lemmas about a finite five-index real
array `T` (the lowered components of `∇Rm`) and a four-index real array `R` (the
lowered components of `Rm`).  No curvature, metric, or Ricci-flow hypothesis
enters.  We bound the schematic `Rm ∗ ∇Rm` reaction, contracted against `∇Rm`,
by `C(n) · |∇Rm|² · √(|Rm|²)`. -/

section ComponentAlgebra

variable {Idx : Type*} [Fintype Idx]

/-- Squared component norm of a five-index real array, `∑ Tₘₐᵦ𝒸𝒹²`.  In an
orthonormal frame this is `|∇Rm|²`. -/
def compNormSq5 (T : Idx → Idx → Idx → Idx → Idx → Real) : Real :=
  ∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx, (T m a b c d) ^ 2

theorem compNormSq5_nonneg (T : Idx → Idx → Idx → Idx → Idx → Real) :
    0 ≤ compNormSq5 T := by
  unfold compNormSq5
  refine Finset.sum_nonneg fun m _ => ?_
  refine Finset.sum_nonneg fun a _ => ?_
  refine Finset.sum_nonneg fun b _ => ?_
  refine Finset.sum_nonneg fun c _ => ?_
  refine Finset.sum_nonneg fun d _ => ?_
  exact sq_nonneg _

/-- Each squared component is dominated by the squared component norm. -/
theorem sq_le_compNormSq5
    (T : Idx → Idx → Idx → Idx → Idx → Real) (m a b c d : Idx) :
    (T m a b c d) ^ 2 ≤ compNormSq5 T := by
  classical
  unfold compNormSq5
  have hd : (T m a b c d) ^ 2 ≤ ∑ d' : Idx, (T m a b c d') ^ 2 :=
    Finset.single_le_sum (f := fun d' : Idx => (T m a b c d') ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ d)
  have hc : (∑ d' : Idx, (T m a b c d') ^ 2) ≤
      ∑ c' : Idx, ∑ d' : Idx, (T m a b c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun c' : Idx => ∑ d' : Idx, (T m a b c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have hb : (∑ c' : Idx, ∑ d' : Idx, (T m a b c' d') ^ 2) ≤
      ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun b' : Idx => ∑ c' : Idx, ∑ d' : Idx, (T m a b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  have ha : (∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a b' c' d') ^ 2) ≤
      ∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a' b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun a' : Idx => ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a' b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  have hm : (∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m a' b' c' d') ^ 2) ≤
      ∑ m' : Idx, ∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m' a' b' c' d') ^ 2 :=
    Finset.single_le_sum
      (f := fun m' : Idx =>
        ∑ a' : Idx, ∑ b' : Idx, ∑ c' : Idx, ∑ d' : Idx, (T m' a' b' c' d') ^ 2)
      (fun i _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ m)
  exact le_trans hd (le_trans hc (le_trans hb (le_trans ha hm)))

/-- Each component's absolute value is dominated by the component norm. -/
theorem abs_le_sqrt_compNormSq5
    (T : Idx → Idx → Idx → Idx → Idx → Real) (m a b c d : Idx) :
    |T m a b c d| ≤ Real.sqrt (compNormSq5 T) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_compNormSq5 T m a b c d)

/-! ### Rank-uniform multi-index component norm

For the general-`k` Bernstein–Bando–Shi tower one needs squared norms of
component arrays of every rank `r = 4 + k`.  We package these uniformly as
functions `(Fin r → Idx) → ℝ`, with `compNormSqMulti` the sum of squared
components over all multi-indices.  This is the rank-free generalization of
`compNormSq4`/`compNormSq5`, and supplies the single-component domination needed
for the general `∗`-norm Cauchy–Schwarz reaction bounds (eq 7.4). -/

/-- Squared component norm of a rank-`r` real array `A : (Fin r → Idx) → ℝ`,
`∑_{m} (A m)²`. -/
def compNormSqMulti {r : ℕ} (A : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, (A m) ^ 2

theorem compNormSqMulti_nonneg {r : ℕ} (A : (Fin r → Idx) → Real) :
    0 ≤ compNormSqMulti A := by
  unfold compNormSqMulti
  exact Finset.sum_nonneg fun m _ => sq_nonneg _

/-- Each squared component is dominated by the squared component norm. -/
theorem sq_le_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    (A m) ^ 2 ≤ compNormSqMulti A := by
  classical
  unfold compNormSqMulti
  exact Finset.single_le_sum (f := fun m' : Fin r → Idx => (A m') ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ m)

/-- Each component's absolute value is dominated by the component norm. -/
theorem abs_le_sqrt_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    |A m| ≤ Real.sqrt (compNormSqMulti A) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_compNormSqMulti A m)

/-- A schematic `Rm ∗ ∇Rm` array entry: a contraction of one curvature factor
against one `∇Rm` factor.  This models the reaction tensor `Rm ∗ ∇Rm` of eq 7.2
at the abstraction level mandated by the project's tensor-calculation workflow —
we never need its exact form, only the `∗`-norm bound below.

Concretely `(Rm ∗ ∇Rm)ₘₐᵦ𝒸𝒹 = ∑ₑ ∑_f Rₐₑ𝒸_f · (∇Rm)ₘₑᵦ_f𝒹`, a single canonical
contraction with the same combinatorial shape as `bTensorDown`. -/
def nablaStarRm (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real)
    (m a b c d : Idx) : Real :=
  ∑ e : Idx, ∑ f : Idx, R a e c f * T m e b f d

/-- The `Rm ∗ ∇Rm` entry is bounded by `card² · √(|Rm|²) · √(|∇Rm|²)`.  Each
product factor is at most a single `Rm` (resp. `∇Rm`) component, dominated by the
respective component norm, and there are `card²` summands. -/
theorem abs_nablaStarRm_le
    (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real)
    (m a b c d : Idx) :
    |nablaStarRm R T m a b c d| ≤
      (Fintype.card Idx : Real) ^ 2 *
        (Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T)) := by
  classical
  have hStep :
      |nablaStarRm R T m a b c d| ≤
        ∑ e : Idx, ∑ f : Idx, |R a e c f * T m e b f d| := by
    unfold nablaStarRm
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun e _ => ?_
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans hStep ?_
  have hsqrtR : 0 ≤ Real.sqrt (compNormSq4 R) := Real.sqrt_nonneg _
  have hsqrtT : 0 ≤ Real.sqrt (compNormSq5 T) := Real.sqrt_nonneg _
  have hTerm : ∀ e f : Idx,
      |R a e c f * T m e b f d| ≤
        Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T) := by
    intro e f
    rw [abs_mul]
    have hbnd : |R a e c f| ≤ Real.sqrt (compNormSq4 R) :=
      abs_le_sqrt_compNormSq4 R a e c f
    have hbnd2 : |T m e b f d| ≤ Real.sqrt (compNormSq5 T) :=
      abs_le_sqrt_compNormSq5 T m e b f d
    exact mul_le_mul hbnd hbnd2 (abs_nonneg _) hsqrtR
  calc
    (∑ e : Idx, ∑ f : Idx, |R a e c f * T m e b f d|)
        ≤ ∑ e : Idx, ∑ f : Idx,
            Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T) := by
          refine Finset.sum_le_sum fun e _ => ?_
          exact Finset.sum_le_sum fun f _ => hTerm e f
    _ = (Fintype.card Idx : Real) ^ 2 *
          (Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T)) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq]
          ring

/-- The schematic curvature reaction term for the `|∇Rm|²` heat inequality:
twice the contraction of `Rm ∗ ∇Rm` against `∇Rm`,
`reaction = 2 ∑ₘₐᵦ𝒸𝒹 (∇Rm)ₘₐᵦ𝒸𝒹 · (Rm ∗ ∇Rm)ₘₐᵦ𝒸𝒹`.

This is the `k = 1` analogue of `rmReactionDown`: a degree-three contraction,
quadratic in `∇Rm` and linear in `Rm`, modeling the `2⟨Rm ∗ ∇Rm, ∇Rm⟩` reaction
of eq 7.2. -/
def nablaRmReactionDown (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real) : Real :=
  2 * ∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
    T m a b c d * nablaStarRm R T m a b c d

/-- **`∗`-reaction bound** (Chow–Knopf eq 7.2 estimate), component form.

The schematic `|∇Rm|²` reaction is bounded by
`2 · card⁷ · |∇Rm|² · √(|Rm|²)`, i.e. `|reaction| ≤ C(n) · |∇Rm|² · |Rm|` with
`C(n) = 2 · card⁷`.

This is the algebraic heart of eq 7.2's reaction estimate and the `k = 1`
analogue of `abs_rmReactionDown_le`: the reaction is `2⟨Rm ∗ ∇Rm, ∇Rm⟩`, and
Cauchy–Schwarz on the frame components yields the bound. -/
theorem abs_nablaRmReactionDown_le
    (R : Idx → Idx → Idx → Idx → Real)
    (T : Idx → Idx → Idx → Idx → Idx → Real) :
    |nablaRmReactionDown R T| ≤
      2 * (Fintype.card Idx : Real) ^ 7 *
        (compNormSq5 T * Real.sqrt (compNormSq4 R)) := by
  classical
  set NT : Real := compNormSq5 T with hNT
  set NR : Real := compNormSq4 R with hNR
  have hNTnonneg : 0 ≤ NT := compNormSq5_nonneg T
  have hsqrtT_nonneg : 0 ≤ Real.sqrt NT := Real.sqrt_nonneg _
  have hsqrtR_nonneg : 0 ≤ Real.sqrt NR := Real.sqrt_nonneg _
  -- bound the inner contraction
  have hInner :
      |∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          T m a b c d * nablaStarRm R T m a b c d| ≤
        ∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          (Real.sqrt NT *
            ((Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun m _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun a _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun c _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun d _ => ?_
    rw [abs_mul]
    have hbnd1 : |T m a b c d| ≤ Real.sqrt NT := by
      rw [hNT]; exact abs_le_sqrt_compNormSq5 T m a b c d
    have hbnd2 :
        |nablaStarRm R T m a b c d| ≤
          (Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT) := by
      rw [hNR, hNT]; exact abs_nablaStarRm_le R T m a b c d
    have hnn : (0 : Real) ≤
        (Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT) :=
      mul_nonneg (by positivity) (mul_nonneg hsqrtR_nonneg hsqrtT_nonneg)
    exact mul_le_mul hbnd1 hbnd2 (abs_nonneg _) hsqrtT_nonneg
  -- evaluate the constant sum
  have hConst :
      (∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          (Real.sqrt NT *
            ((Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT)))) =
        (Fintype.card Idx : Real) ^ 5 *
          (Real.sqrt NT *
            ((Fintype.card Idx : Real) ^ 2 * (Real.sqrt NR * Real.sqrt NT))) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- collapse `√NT * √NT = NT`
  have hsqrtT_sq : Real.sqrt NT * Real.sqrt NT = NT :=
    Real.mul_self_sqrt hNTnonneg
  rw [hNT, hNR] at hInner hConst ⊢
  unfold nablaRmReactionDown
  rw [abs_mul]
  have h2 : |(2 : Real)| = 2 := by norm_num
  rw [h2]
  calc
    2 * |∑ m : Idx, ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
          T m a b c d * nablaStarRm R T m a b c d|
        ≤ 2 * ((Fintype.card Idx : Real) ^ 5 *
            (Real.sqrt (compNormSq5 T) *
              ((Fintype.card Idx : Real) ^ 2 *
                (Real.sqrt (compNormSq4 R) * Real.sqrt (compNormSq5 T))))) := by
          have hInner' := le_trans hInner (le_of_eq hConst)
          exact mul_le_mul_of_nonneg_left hInner' (by norm_num)
    _ = 2 * (Fintype.card Idx : Real) ^ 7 *
          (compNormSq5 T * Real.sqrt (compNormSq4 R)) := by
          have hcollapse :
              Real.sqrt (compNormSq5 T) * Real.sqrt (compNormSq5 T) = compNormSq5 T :=
            Real.mul_self_sqrt (compNormSq5_nonneg T)
          set s : Real := Real.sqrt (compNormSq5 T)
          set r : Real := Real.sqrt (compNormSq4 R)
          set c : Real := (Fintype.card Idx : Real)
          calc
            2 * (c ^ 5 * (s * (c ^ 2 * (r * s))))
                = 2 * c ^ 7 * ((s * s) * r) := by ring
            _ = 2 * c ^ 7 * (compNormSq5 T * r) := by rw [hcollapse]

/-! ### General-`k` `∗`-norm reaction bound (eq 7.4)

We package the general-`k` reaction estimate in the `∗`-convention.  At level
`k` the schematic reaction is a sum over `j ∈ {0,…,k}` of contractions
`⟨∇ʲRm ∗ ∇^{k−j}Rm, ∇ᵏRm⟩`.  Following the task's mandated route we never pin a
specific contraction tensor; we model the `j`-th `∗`-factor as an arbitrary
rank-`(4+k)` "star array" `star j` whose entries obey the per-entry `∗`-norm
bound `|star j m| ≤ card² · √‖∇ʲRm‖² · √‖∇^{k−j}Rm‖²` (the only property a `∗`
product is ever used through), and contract it against `∇ᵏRm`.

The conclusion has exactly the shape of `towerReactionSum` from
`Evolution/BernsteinShiHigher.lean`:
`|reaction| ≤ Σⱼ c · √(wⱼ) · √(w_{k−j}) · √(wₖ)` with the level fields
`wⱼ = ‖∇ʲRm‖²` and a single tower constant `c = 2 · card^{6+k}`. -/

/-- The general-`k` schematic reaction `Σⱼ 2·⟨∇ʲRm ∗ ∇^{k−j}Rm, ∇ᵏRm⟩`, with each
`∗`-factor supplied abstractly as a rank-`(4+k)` star array `star j`. -/
def nablaRmReactionMulti {k : ℕ}
    (Tk : (Fin (4 + k) → Idx) → Real)
    (star : ℕ → (Fin (4 + k) → Idx) → Real) : Real :=
  ∑ j ∈ Finset.range (k + 1),
    2 * ∑ m : Fin (4 + k) → Idx, Tk m * star j m

/-- **General-`k` `∗`-reaction bound** (Chow–Knopf eq 7.4 estimate), component
form.  Given level squared norms `w : ℕ → ℝ` with `√(w j)` controlling the
rank-`(4+j)` factor, and the per-entry `∗`-norm bounds on each star array, the
reaction is bounded termwise by the `towerReactionSum` shape

`|reaction| ≤ Σⱼ (2·card^{6+k}) · √(w j) · √(w (k−j)) · √(w k)`.

This is the rank-uniform generalization of `abs_nablaRmReactionDown_le`; the
single tower constant is `c = 2 · card^{6+k}` (here `card^{4+k}` multi-indices
times `card²` per `∗`-contraction). -/
theorem abs_nablaRmReactionMulti_le {k : ℕ}
    (Tk : (Fin (4 + k) → Idx) → Real)
    (star : ℕ → (Fin (4 + k) → Idx) → Real)
    (w : ℕ → Real)
    (hwk : compNormSqMulti Tk = w k)
    (hstar : ∀ j ∈ Finset.range (k + 1), ∀ m : Fin (4 + k) → Idx,
      |star j m| ≤
        (Fintype.card Idx : Real) ^ 2 * (Real.sqrt (w j) * Real.sqrt (w (k - j)))) :
    |nablaRmReactionMulti Tk star| ≤
      ∑ j ∈ Finset.range (k + 1),
        (2 * (Fintype.card Idx : Real) ^ (6 + k)) *
          Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k) := by
  classical
  unfold nablaRmReactionMulti
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun j hj => ?_
  -- Bound the `j`-th term `|2 · ⟨Tk, star j⟩|`.
  rw [abs_mul]
  have h2 : |(2 : Real)| = 2 := by norm_num
  rw [h2]
  have hsqrtk : 0 ≤ Real.sqrt (w k) := Real.sqrt_nonneg _
  have hsqrtj : 0 ≤ Real.sqrt (w j) := Real.sqrt_nonneg _
  have hsqrtkj : 0 ≤ Real.sqrt (w (k - j)) := Real.sqrt_nonneg _
  -- Per-multi-index Cauchy–Schwarz, then sum the constant.
  have hinner :
      |∑ m : Fin (4 + k) → Idx, Tk m * star j m| ≤
        ∑ m : Fin (4 + k) → Idx,
          (Real.sqrt (w k) *
            ((Fintype.card Idx : Real) ^ 2 *
              (Real.sqrt (w j) * Real.sqrt (w (k - j))))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun m _ => ?_
    rw [abs_mul]
    have hTk : |Tk m| ≤ Real.sqrt (w k) := by
      rw [← hwk]; exact abs_le_sqrt_compNormSqMulti Tk m
    have hst : |star j m| ≤
        (Fintype.card Idx : Real) ^ 2 * (Real.sqrt (w j) * Real.sqrt (w (k - j))) :=
      hstar j hj m
    exact mul_le_mul hTk hst (abs_nonneg _) hsqrtk
  -- Evaluate the constant multi-index sum: there are `card^{4+k}` multi-indices.
  have hcardpi :
      (Fintype.card (Fin (4 + k) → Idx) : Real) =
        (Fintype.card Idx : Real) ^ (4 + k) := by
    rw [Fintype.card_pi]
    simp [Finset.prod_const, Finset.card_univ]
  have hcard :
      (∑ m : Fin (4 + k) → Idx,
          (Real.sqrt (w k) *
            ((Fintype.card Idx : Real) ^ 2 *
              (Real.sqrt (w j) * Real.sqrt (w (k - j)))))) =
        (Fintype.card Idx : Real) ^ (4 + k) *
          (Real.sqrt (w k) *
            ((Fintype.card Idx : Real) ^ 2 *
              (Real.sqrt (w j) * Real.sqrt (w (k - j))))) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardpi]
  have hpow :
      (Fintype.card Idx : Real) ^ (4 + k) * (Fintype.card Idx : Real) ^ 2 =
        (Fintype.card Idx : Real) ^ (6 + k) := by
    rw [← pow_add]; congr 1; omega
  calc
    2 * |∑ m : Fin (4 + k) → Idx, Tk m * star j m|
        ≤ 2 * ((Fintype.card Idx : Real) ^ (4 + k) *
            (Real.sqrt (w k) *
              ((Fintype.card Idx : Real) ^ 2 *
                (Real.sqrt (w j) * Real.sqrt (w (k - j)))))) := by
          exact mul_le_mul_of_nonneg_left (le_trans hinner (le_of_eq hcard)) (by norm_num)
    _ = (2 * (Fintype.card Idx : Real) ^ (6 + k)) *
          Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k) := by
          rw [← hpow]; ring

end ComponentAlgebra

/-! ## Solution-facing reaction term, norm, and the cubic-in-`∇Rm` bound

We now specialize the component algebra to an actual Ricci-flow solution in a
fixed **orthonormal** frame, matching the `InverseMetricOrthonormalAt` convention
of `RiemannNormHeatProducer.lean`.  In this frame the inverse metric is the
Kronecker delta, so the solution's `|∇Rm|²` (`nablaRm04NormSqInFrame`) is the
plain component norm `compNormSq5` and the schematic reaction reduces to
`nablaRmReactionDown`. -/

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

/-- In an orthonormal frame the solution's `|∇Rm|²` (the 5-index component norm
`nablaRm04NormSqInFrame`) equals the plain squared component norm `compNormSq5`. -/
theorem nablaRm04NormSqInFrame_eq_compNormSq5
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x) :
    nablaRm04NormSqInFrame (M := M) nablaRm04 gInv t x =
      compNormSq5 (fun m a b c d : Idx => nablaRm04 t x m a b c d) := by
  classical
  unfold nablaRm04NormSqInFrame compNormSq5
  unfold InverseMetricOrthonormalAt at horth
  -- The 5-index norm carries one "outer derivative" delta `gInv t x a b` and
  -- four "tensor-slot" deltas.  Collapse them all to the diagonal.
  refine Finset.sum_congr rfl fun a _ => ?_
  -- Collapse the outer-derivative delta-sum `∑ b`: it forces `b = a`.
  rw [Finset.sum_eq_single a]
  · -- Diagonal block `b = a`: match the four tensor slots against the RHS.
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    -- Collapse the inner tensor-slot delta-sums `(p,q,r,s)`, outermost first.
    -- Each off-diagonal summand vanishes because the relevant `gInv` Kronecker
    -- delta is `0`; the diagonal summand survives.
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single k]
        · rw [Finset.sum_eq_single l]
          · simp [horth, sq]
          · intro s _ hs; simp [horth, Ne.symm hs]
          · intro h; exact absurd (Finset.mem_univ l) h
        · intro r _ hr; simp [horth, Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ k) h
      · intro q _ hq; simp [horth, Ne.symm hq]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro p _ hp; simp [horth, Ne.symm hp]
    · intro h; exact absurd (Finset.mem_univ i) h
  · -- Off-diagonal `b ≠ a`: the outer Kronecker delta is zero.
    intro b _ hb
    simp [horth, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The schematic curvature reaction term for the `|∇Rm|²` heat inequality, in a
fixed frame: `2 ∑ (∇Rm) · (Rm ∗ ∇Rm)`, with the curvature factor supplied by the
solution's lowered Riemann components.  In an orthonormal frame this reduces to
`nablaRmReactionDown`. -/
def nablaRmReactionInFrame
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    nablaRmReactionDown
      (fun a b c d : Idx =>
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d)
      (fun m a b c d : Idx => nablaRm04 t x m a b c d)

/-- **`∗`-reaction bound** (Chow–Knopf eq 7.2 estimate), solution form.

In an orthonormal frame the schematic curvature reaction term satisfies
`|reaction t x| ≤ 2 · card⁷ · |∇Rm|² · √(|Rm|²)`, i.e.
`|reaction| ≤ C(n) · |∇Rm|² · |Rm|` with `C(n) = 2 · (dim)⁷`. -/
theorem abs_nablaRmReactionInFrame_le
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (horth : InverseMetricOrthonormalAt (M := M) gInv t x) :
    |nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame t x| ≤
      2 * (Fintype.card Idx : Real) ^ 7 *
        (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv t x *
          Real.sqrt (rm04NormSqInFrame (I := I) Rm04 gInv frame t x)) := by
  rw [nablaRmReactionInFrame]
  rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) nablaRm04 gInv t x horth]
  rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) Rm04 gInv frame t x horth]
  exact abs_nablaRmReactionDown_le _ _

/-! ## The assembled time-derivative equation and the heat-inequality producer

Following the `k = 0` architecture of `RiemannNormHeatProducer.lean`, the
assembled time derivative of `|∇Rm|²` is taken as a single hypothesis: it is the
`(0,5)` analogue of `Rm04NormHeatEquationOn`, packaging the time-derivative
product rule, the Uhlenbeck evolution `∂ₜRm = ΔRm + Rm∗Rm`, the connection
evolution `∂ₜΓ = ∇Rc∗1`, the Laplacian commutator `[∇,Δ]Rm = Rm∗∇Rm`, and the
Bochner Laplacian split `Δ|∇Rm|² = 2⟨Δ∇Rm,∇Rm⟩ + 2|∇²Rm|²` into the single
identity

`∂ₜ |∇Rm|² = Δ|∇Rm|² + (−2 |∇²Rm|² + reaction)`,  `reaction = nablaRmReactionInFrame`.

On top of this we prove the two heat inequalities (sharp and dropped). -/

/-- The assembled heat-**equation** for `|∇Rm|²` in `HasDerivWithinAt` form, the
`(0,5)` analogue of `Rm04NormHeatEquationOn`:
`∂ₜ u = uLap + (−2·nabla2RmNormSq + reaction)` at every regular time and point. -/
def NablaRm04NormHeatEquationOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (nablaRmNormSq nablaRmNormLap nabla2RmNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => nablaRmNormSq s x)
      (nablaRmNormLap (t : Real) x +
        (-2 * nabla2RmNormSq (t : Real) x + reaction (t : Real) x))
      D.carrier
      (t : Real)

/-- **Sharp `k = 1` heat inequality** (Chow–Knopf eq 7.2, retaining
`−2|∇²Rm|²`), solution form.

From the assembled heat equation for `|∇Rm|²` with the schematic reaction
`nablaRmReactionInFrame`, and using the `∗`-reaction bound
`|reaction| ≤ 2·card⁷·|∇Rm|²·√(|Rm|²)`, we obtain at every regular time and
point a derivative `d = ∂ₜ|∇Rm|²` with

`d ≤ Δ|∇Rm|² − 2 |∇²Rm|² + (2·card⁷)·√(|Rm|²)·|∇Rm|²`.

The reaction coefficient `cReact = 2·card⁷` packages the dimensional constant
`C(n)`. -/
theorem nablaRm04NormHeatBoundSharp_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRmNormLap nabla2RmNormSq : Real -> M -> Real)
    (horth : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      InverseMetricOrthonormalAt (M := M) gInv (t : Real) x)
    (h_heat : NablaRm04NormHeatEquationOn
      (D := D) (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv)
      nablaRmNormLap nabla2RmNormSq
      (nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame)) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      ∃ d : Real,
        HasDerivWithinAt
          (fun s : Real => nablaRm04NormSqInFrame (M := M) nablaRm04 gInv s x)
          d D.carrier (t : Real) ∧
        d ≤ nablaRmNormLap (t : Real) x +
          (-2 * nabla2RmNormSq (t : Real) x +
            (2 * (Fintype.card Idx : Real) ^ 7) *
              Real.sqrt (rm04NormSqInFrame (I := I) Rm04 gInv frame (t : Real) x) *
                nablaRm04NormSqInFrame (M := M) nablaRm04 gInv (t : Real) x) := by
  intro t x
  refine ⟨_, h_heat t x, ?_⟩
  -- The reaction is at most its absolute value, which the `∗`-bound controls.
  set u : Real := nablaRm04NormSqInFrame (M := M) nablaRm04 gInv (t : Real) x with hu
  set v : Real := rm04NormSqInFrame (I := I) Rm04 gInv frame (t : Real) x with hv
  have hreact_le :
      nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame (t : Real) x ≤
        2 * (Fintype.card Idx : Real) ^ 7 * (u * Real.sqrt v) := by
    have habs := abs_nablaRmReactionInFrame_le (I := I) Rm04 nablaRm04 gInv frame
      (t : Real) x (horth t x)
    rw [← hu, ← hv] at habs
    exact le_trans (le_abs_self _) habs
  -- Rearrange `2·card⁷·(u·√v) = (2·card⁷)·√v·u`.
  have hrewrite :
      2 * (Fintype.card Idx : Real) ^ 7 * (u * Real.sqrt v) =
        (2 * (Fintype.card Idx : Real) ^ 7) * Real.sqrt v * u := by ring
  rw [hrewrite] at hreact_le
  -- Conclude the bound on the derivative value.
  linarith [hreact_le]

/-- **`k = 1` heat inequality** (Chow–Knopf eq 7.2 / eq 7.4 at `k = 1`, =
MSM144 eq 14.17), solution form: the `NablaRm04NormHeatBoundOn` predicate.

Dropping the favourable `−2|∇²Rm|² ≤ 0` term from the sharp inequality yields the
predicate consumed by the Bernstein–Bando–Shi maximum-principle stage
(`bernstein_first_derivative_estimate`):

`(∂ₜ − Δ) |∇Rm|² ≤ C(n) · |Rm| · |∇Rm|²`,  `C(n) = 2·(dim)⁷`.

This is the `k = 1` producer, the exact analogue of the `k = 0` curvature-norm
producer `rm04NormHeatEquationOn_of_solution`. -/
theorem nablaRm04NormHeatBoundOn_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRmNormLap nabla2RmNormSq : Real -> M -> Real)
    (horth : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      InverseMetricOrthonormalAt (M := M) gInv (t : Real) x)
    (hnabla2_nonneg : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), 0 ≤ nabla2RmNormSq (t : Real) x)
    (h_heat : NablaRm04NormHeatEquationOn
      (D := D) (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv)
      nablaRmNormLap nabla2RmNormSq
      (nablaRmReactionInFrame (I := I) Rm04 nablaRm04 frame)) :
    NablaRm04NormHeatBoundOn
      (D := D) (nablaRm04NormSqInFrame (M := M) nablaRm04 gInv)
      nablaRmNormLap (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      (2 * (Fintype.card Idx : Real) ^ 7) := by
  intro t x
  obtain ⟨d, hderiv, hle⟩ :=
    nablaRm04NormHeatBoundSharp_of_components (I := I) Rm04 nablaRm04 gInv frame
      nablaRmNormLap nabla2RmNormSq horth h_heat t x
  refine ⟨d, hderiv, ?_⟩
  -- Drop the favourable `−2|∇²Rm|² ≤ 0` term.
  have hdrop : 0 ≤ 2 * nabla2RmNormSq (t : Real) x := by
    have := hnabla2_nonneg t x; linarith
  linarith [hle, hdrop]

end Solution

end DifferentialGeometry.PDE.RicciFlow
