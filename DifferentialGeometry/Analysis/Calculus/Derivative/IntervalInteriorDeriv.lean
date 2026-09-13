import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open Filter Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

theorem derivWithin_Icc_eq_deriv_of_mem_Ioo {f : ℝ → ℝ} {a b t : ℝ} (ht : t ∈ Ioo a b) :
    derivWithin f (Icc a b) t = deriv f t :=
  derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

theorem uniqueDiffWithinAt_Icc_zero_one : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
  uniqueDiffWithinAt_convex (convex_Icc 0 1)
    (by rw [interior_Icc]; exact ⟨1 / 2, by norm_num, by norm_num⟩)
    (by rw [closure_Icc]; norm_num)

theorem derivWithin_abs_Icc_eq_one :
    derivWithin (fun x : ℝ => |x|) (Icc (0 : ℝ) 1) 0 = 1 := by
  have hh : HasDerivWithinAt (fun x : ℝ => |x|) 1 (Icc (0 : ℝ) 1) 0 :=
    (hasDerivWithinAt_id (0 : ℝ) (Icc (0 : ℝ) 1)).congr_of_mem
      (fun x hx => abs_of_nonneg hx.1) (by norm_num)
  exact hh.derivWithin uniqueDiffWithinAt_Icc_zero_one

theorem derivWithin_abs_Icc_zero_ne_deriv_abs_zero :
    derivWithin (fun x : ℝ => |x|) (Icc (0 : ℝ) 1) 0 ≠ deriv (fun x : ℝ => |x|) 0 := by
  rw [deriv_abs_zero, derivWithin_abs_Icc_eq_one]
  norm_num

theorem Ici_mem_nhdsWithin_Icc_leftEndpoint (a b : ℝ) : Ici a ∈ 𝓝[Icc a b] a := by
  rw [mem_nhdsWithin]
  exact ⟨Iio (a + 1), isOpen_Iio, by simp, fun x hx => hx.2.1⟩

theorem hasDerivWithinAt_Icc_of_hasDerivWithinAt_Ici_leftEndpoint {f : ℝ → ℝ} {c a b : ℝ}
    (h : HasDerivWithinAt f c (Ici a) a) : HasDerivWithinAt f c (Icc a b) a :=
  h.mono_of_mem_nhdsWithin (Ici_mem_nhdsWithin_Icc_leftEndpoint a b)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mfderivWithin_Icc_eq_mfderiv_of_mem_Ioo {f : ℝ → M} {a b t : ℝ} (ht : t ∈ Ioo a b) :
    mfderivWithin 𝓘(ℝ, ℝ) I f (Icc a b) t = mfderiv 𝓘(ℝ, ℝ) I f t :=
  mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

end DifferentialGeometry
