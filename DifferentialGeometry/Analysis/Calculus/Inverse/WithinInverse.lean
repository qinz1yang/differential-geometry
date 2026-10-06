import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

/-- A continuous right inverse on sets with unique derivatives inherits every
finite order of differentiability when the forward derivative is invertible.
All regularity and inverse identities are required only on the stated sets. -/
theorem contDiffOn_rightInverse_of_invertible_fderivWithin
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {t : Set F} {f : E → F} {g : F → E}
    (r : ℕ) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hf : ContDiffOn ℝ r f s) (hg : ContinuousOn g t)
    (hgs : MapsTo g t s)
    (hfg : ∀ y ∈ t, f (g y) = y)
    (hinv : ∀ y ∈ t,
      (fderivWithin ℝ f s (g y)).IsInvertible) :
    ContDiffOn ℝ r g t := by
  induction r with
  | zero => exact contDiffOn_zero.mpr hg
  | succ r ih =>
    have hfsucc : ContDiffOn ℝ ((r : ℕ∞ω) + 1) f s := by
      simpa only [Nat.cast_add, Nat.cast_one] using hf
    have hfd := (contDiffOn_succ_iff_fderivWithin hs).mp hfsucc
    have hgr : ContDiffOn ℝ r g t :=
      ih (hf.of_le (by exact_mod_cast Nat.le_succ r))
    have hderiv : ∀ y ∈ t, HasFDerivWithinAt g
        (ContinuousLinearMap.inverse (fderivWithin ℝ f s (g y))) t y := by
      intro y hy
      obtain ⟨A, hA⟩ := hinv y hy
      have hdf : HasFDerivWithinAt f (A : E →L[ℝ] F) s (g y) := by
        rw [hA]
        exact (hfd.1 (g y) (hgs hy)).hasFDerivWithinAt
      have hid : ∀ᶠ z in 𝓝[t] y, f (g z) = z :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => hfg z hz)
      have h := HasFDerivWithinAt.of_local_left_inverse
        ((hg y hy).tendsto_nhdsWithin hgs) hdf hy hid
      simpa only [← hA, ContinuousLinearMap.inverse_equiv] using h
    have hcomp : ContDiffOn ℝ r
        (fun y => fderivWithin ℝ f s (g y)) t :=
      hfd.2.2.comp hgr hgs
    have hreg : ContDiffOn ℝ r
        (fun y => ContinuousLinearMap.inverse (fderivWithin ℝ f s (g y))) t := by
      intro y hy
      exact (hinv y hy).contDiffAt_map_inverse.comp_contDiffWithinAt y (hcomp y hy)
    have hsucc : ContDiffOn ℝ ((r : ℕ∞ω) + 1) g t :=
      (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ht).mpr
        ⟨by simp, _, hreg, hderiv⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hsucc

end DifferentialGeometry.Analysis
