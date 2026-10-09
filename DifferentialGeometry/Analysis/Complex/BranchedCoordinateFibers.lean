import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Analysis

/-- A literal nonzero-order power coordinate gives finite fibers of the
original map, including at the branch value. Only the coordinate is injective. -/
theorem finite_fiber_of_normalized_power_coordinate
    {M : Type*} {U : ℂ → M} {π : M → ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} {m : ℕ} {c : ℂ}
    (hpower : ∀ z ∈ e.source,
      π (U z) = c + (e z) ^ (m + 1) / ((m + 1 : ℕ) : ℂ))
    (y : M) : {z : ℂ | z ∈ e.source ∧ U z = y}.Finite := by
  let p : Polynomial ℂ := Polynomial.X ^ (m + 1)
  have hp : p.natDegree ≠ 0 := by
    simpa only [p, Polynomial.natDegree_X_pow] using Nat.succ_ne_zero m
  have hroots : {w : ℂ | w ^ (m + 1) =
      (π y - c) * ((m + 1 : ℕ) : ℂ)}.Finite := by
    have ht := (Filter.tendstoCofinite_iff_finite_preimage_singleton p.eval).mp
      (p.tendstoCofinite_of_natDegree_ne_zero hp)
    refine (ht ((π y - c) * ((m + 1 : ℕ) : ℂ))).subset ?_
    intro w hw
    change w ^ (m + 1) = (π y - c) * ((m + 1 : ℕ) : ℂ) at hw
    simpa only [mem_preimage, mem_singleton_iff, p, Polynomial.eval_pow,
      Polynomial.eval_X] using hw
  refine Set.Finite.of_injOn (f := (e : ℂ → ℂ)) ?_
    (e.injOn.mono fun _ hz => hz.1) hroots
  intro z hz
  have heq : c + (e z) ^ (m + 1) / ((m + 1 : ℕ) : ℂ) = π y :=
    (hpower z hz.1).symm.trans (congrArg π hz.2)
  have hdiv : (e z) ^ (m + 1) / ((m + 1 : ℕ) : ℂ) = π y - c :=
    (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using heq)
  exact (div_eq_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))).mp hdiv

end DifferentialGeometry.Analysis
