import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContrNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompLinear

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# `m`-fold contraction-Leibniz norm bound (component algebra)

`ric_bound` (MSM135 Lemma 3.11, Claim 1) needs the iterated Leibniz norm bound
`|∇ᵐ(A ∗ B)| ≤ ∑_c \binom m c |∇ᶜA| |∇^{m-c}B|`, obtained by iterating the single-step
`covDerivStepCompU_contrTail_leibniz`.  This file sets up the abstract tower iterators
`iterDl` (lower, rank `r+m`) and `iterDU` (upper, rank `(p+c)+1`), chosen so the ranks
stay *definitionally* equal across the recursion (no `Fin` casts in the definitions).
The `m`-fold norm bound is then a strong induction on `m` using the single-step (passed
as a hypothesis, discharged for the frame step later), `compL2` Minkowski/contraction
bounds, slot-reindex invariance, and Pascal's rule.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Iterate a rank-raising lower covariant-derivative step `D` (any rank `r ↦ r+1`)
`m` times.  Rank `r+m`, definitionally (`D` accepts any input rank). -/
def iterDl (D : ∀ {r : ℕ}, ((Fin r → Idx) → Real) → ((Fin (r + 1) → Idx) → Real))
    {r : ℕ} : (m : ℕ) → ((Fin r → Idx) → Real) → ((Fin (r + m) → Idx) → Real)
  | 0, T => T
  | (m + 1), T => D (iterDl D m T)

/-- Iterate a rank-raising upper covariant-derivative step `DU` (`r+1 ↦ r+2`) `c` times.
Rank `(p+c)+1`, keeping the `+1` last so `DU`'s `_+1`-shaped input matches definitionally. -/
def iterDU (DU : ∀ {r : ℕ}, ((Fin (r + 1) → Idx) → Real) → ((Fin (r + 2) → Idx) → Real))
    {p : ℕ} : (c : ℕ) → ((Fin (p + 1) → Idx) → Real) → ((Fin ((p + c) + 1) → Idx) → Real)
  | 0, A => A
  | (c + 1), A => DU (iterDU DU c A)

@[simp] theorem iterDl_zero
    (D : ∀ {r : ℕ}, ((Fin r → Idx) → Real) → ((Fin (r + 1) → Idx) → Real))
    {r : ℕ} (T : (Fin r → Idx) → Real) : iterDl D 0 T = T := rfl

@[simp] theorem iterDl_succ
    (D : ∀ {r : ℕ}, ((Fin r → Idx) → Real) → ((Fin (r + 1) → Idx) → Real))
    {r : ℕ} (m : ℕ) (T : (Fin r → Idx) → Real) :
    iterDl D (m + 1) T = D (iterDl D m T) := rfl

@[simp] theorem iterDU_zero
    (DU : ∀ {r : ℕ}, ((Fin (r + 1) → Idx) → Real) → ((Fin (r + 2) → Idx) → Real))
    {p : ℕ} (A : (Fin (p + 1) → Idx) → Real) : iterDU DU 0 A = A := rfl

@[simp] theorem iterDU_succ
    (DU : ∀ {r : ℕ}, ((Fin (r + 1) → Idx) → Real) → ((Fin (r + 2) → Idx) → Real))
    {p : ℕ} (c : ℕ) (A : (Fin (p + 1) → Idx) → Real) :
    iterDU DU (c + 1) A = DU (iterDU DU c A) := rfl

end DifferentialGeometry.PDE.RicciFlow
