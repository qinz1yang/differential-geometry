import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiply
import DifferentialGeometry.Analysis.Sobolev.Tools.WeakPartialLimit
import DifferentialGeometry.External.DeGiorgi.BallExtension.RoughInput
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Higher-order chain rule infrastructure for `W^{k,p}` under smooth bounded diffeomorphisms

This file packages the classical (Faà di Bruno-style) pointwise bound on the
iterated `fderiv` of a composition `u ∘ Φ` for a smooth bounded
diffeomorphism `Φ`, along with related infrastructure used in the
non-smooth chain rule for `W^{k,p}`.

## Main results

* `SmoothDiffeoBounded.norm_iteratedFDeriv_comp_toFun_le`: the cruder
  Faà di Bruno-style pointwise bound
  `‖∂^n (u ∘ Φ)(x)‖ ≤ n! · C · D^n`,
  where `C` bounds `‖∂^i u(Φ x)‖` for `i ≤ n` and `D = max Φ.deriv_bound 1`.

* `SmoothDiffeoBounded.comp_toFun_contDiff`: smoothness of the
  composition `u ∘ Φ` is preserved.

The non-smooth version of the chain rule (`MemWkp.comp_smoothDiffeoBounded`
and `wkpNorm_comp_smoothDiffeoBounded_lt_top`) requires additional
infrastructure that is currently outside the scope of this file
(specifically, smooth density in `W^{k,p}` for non-compactly-supported
functions, or alternatively a Piola-type identity for the chain-rule
test-function transform).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace SmoothDiffeoBounded

/-- The geometric constant used in the iterated-derivative bound:
`max Φ.deriv_bound 1`. This is `≥ 1`, so its powers are increasing. -/
def derivBoundMaxOne {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω') : ℝ :=
  max Φ.deriv_bound 1

lemma derivBoundMaxOne_pos {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω') :
    0 < Φ.derivBoundMaxOne := by
  unfold derivBoundMaxOne
  have h1 : (0 : ℝ) < 1 := by norm_num
  exact lt_of_lt_of_le h1 (le_max_right _ _)

lemma derivBoundMaxOne_ge_one {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') :
    1 ≤ Φ.derivBoundMaxOne :=
  le_max_right _ _

lemma deriv_bound_le_derivBoundMaxOne {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') :
    Φ.deriv_bound ≤ Φ.derivBoundMaxOne :=
  le_max_left _ _

/-- The Faà di Bruno-style cruder bound:
`‖∂^n (u ∘ Φ.toFun)(x)‖ ≤ n! · C · D^n`
where `C` bounds `‖∂^i u(Φ x)‖` for all `i ≤ n` and
`D = max Φ.deriv_bound 1`.

This is a direct corollary of Mathlib's `norm_iteratedFDeriv_comp_le`,
with the bound on `‖iteratedFDeriv ℝ i Φ.toFun x‖ ≤ D^i` (for `1 ≤ i`)
following from `Φ.iter_deriv_bounded` together with `D ≥ 1`. -/
lemma norm_iteratedFDeriv_comp_toFun_le
    {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (n : ℕ) (x : E) {C : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i u (Φ.toFun x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => u (Φ.toFun y)) x‖ ≤
      n.factorial * C * Φ.derivBoundMaxOne ^ n := by
  classical
  set D := Φ.derivBoundMaxOne with hD_def
  have hD_ge_1 : 1 ≤ D := Φ.derivBoundMaxOne_ge_one
  have hD_pos : 0 < D := Φ.derivBoundMaxOne_pos
  have hΦ_smooth_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ.toFun := by
    simpa using Φ.toFun_smooth
  have hu_smooth_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := by
    simpa using hu
  have hn_le : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact_mod_cast h1
  have hfun_eq : (fun y => u (Φ.toFun y)) = (u ∘ Φ.toFun) := rfl
  rw [hfun_eq]
  have hΦ_iter : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i Φ.toFun x‖ ≤ D ^ i := by
    intro i hi1 _hin
    have hbound := Φ.iter_deriv_bounded i x
    have hbnd' : ‖iteratedFDeriv ℝ i Φ.toFun x‖ ≤ D :=
      hbound.trans Φ.deriv_bound_le_derivBoundMaxOne
    rcases i with _ | i
    · exact (Nat.lt_irrefl 0 hi1).elim
    · have h_pow_mono : D ≤ D ^ (i + 1) := by
        have hpw : 1 ≤ D ^ i := one_le_pow₀ hD_ge_1
        calc D = D * 1 := by ring
          _ ≤ D * D ^ i := mul_le_mul_of_nonneg_left hpw (by linarith)
          _ = D ^ (i + 1) := by ring
      exact hbnd'.trans h_pow_mono
  exact norm_iteratedFDeriv_comp_le (𝕜 := ℝ)
    (g := u) (f := Φ.toFun) (n := n) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (x := x) hu_smooth_top hΦ_smooth_top hn_le
    (C := C) (D := D) (fun i hi => hC i hi) hΦ_iter

/-- The composition `u ∘ Φ.toFun` is `C^∞` whenever `u` is. -/
lemma comp_toFun_contDiff
    {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => u (Φ.toFun x)) :=
  hu.comp Φ.toFun_smooth

end SmoothDiffeoBounded

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
