import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Topology.Algebra.Support

noncomputable section
open Set Topology
open scoped ContDiff

namespace Poincare.Analysis

theorem tsupport_integralCurveFamily_sub_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E → E} (hv : ContDiff ℝ 1 v) {Γ : E → ℝ → E}
    (hzero : ∀ x, Γ x 0 = x)
    (hderiv : ∀ x t, HasDerivAt (Γ x) (v (Γ x t)) t) (t : ℝ) :
    tsupport (fun x ↦ Γ x t - x) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxt
  have hvx : v x = 0 := image_eq_zero_of_notMem_tsupport hxt
  let R := |t| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hc (s : ℝ) : HasDerivAt (fun _ : ℝ ↦ x) (v x) s := by
    rw [hvx]
    exact hasDerivAt_const s x
  have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth hv
    (a := -R) (b := R) (t₀ := 0) ⟨by linarith, hR⟩
    (fun s _ ↦ hderiv x s) (fun s _ ↦ hc s) (hzero x)
  exact hx (sub_eq_zero.mpr (he
    ⟨by dsimp [R]; linarith [neg_abs_le t], by dsimp [R]; linarith [le_abs_self t]⟩))

end Poincare.Analysis
