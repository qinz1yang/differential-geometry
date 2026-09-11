import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis

variable {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X]

theorem hasDerivAt_of_inner_hilbertBasis
    (b : HilbertBasis ι ℝ X)
    {u v : ℝ → X} {J : Set ℝ}
    (hJ : IsOpen J) (hv : ContinuousOn v J)
    (hinner : ∀ t ∈ J, ∀ i : ι,
      HasDerivAt (fun s : ℝ => ⟪b i, u s⟫_ℝ) ⟪b i, v t⟫_ℝ t)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt u (v t) t := by
  obtain ⟨a, c, htac, hac_mem, hac⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds ht)
  have hat : a ≤ t := htac.1
  let primitive : ℝ → X := fun s => u a + ∫ r in a..s, v r
  have hv_at : ContinuousAt v t := hv.continuousAt (hJ.mem_nhds ht)
  have hv_int : IntervalIntegrable v volume a t := by
    exact (hv.mono (fun r hr => hac (by
      rw [uIcc_of_le hat] at hr
      exact ⟨hr.1, hr.2.trans htac.2⟩))).intervalIntegrable
  have hprimitive : HasDerivAt primitive (v t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right hv_int
      (ContinuousOn.stronglyMeasurableAtFilter hJ hv t ht) hv_at).const_add (u a)
  have heq : u =ᶠ[nhds t] primitive := by
    filter_upwards [hac_mem] with s hs
    apply b.repr.injective
    ext i
    rw [b.repr_apply_apply, b.repr_apply_apply]
    change ⟪b i, u s⟫_ℝ = ⟪b i, u a + ∫ r in a..s, v r⟫_ℝ
    rw [inner_add_right]
    let ℓ : X →L[ℝ] ℝ := innerSL (𝕜 := ℝ) (E := X) (b i)
    have hvs : ContinuousOn v (uIcc a s) := by
      exact hv.mono (fun r hr => hac (by
        have hs' : s ∈ Icc a c := hs
        rw [uIcc_of_le hs'.1] at hr
        exact ⟨hr.1, hr.2.trans hs'.2⟩))
    have hv_inner : ContinuousOn (fun r : ℝ => ⟪b i, v r⟫_ℝ) (uIcc a s) := by
      exact ℓ.continuous.comp_continuousOn hvs
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hinner r (hac (by
        have hs' : s ∈ Icc a c := hs
        rw [uIcc_of_le hs'.1] at hr
        exact ⟨hr.1, hr.2.trans hs'.2⟩)) i)
      hv_inner.intervalIntegrable
    have hcomm : ⟪b i, ∫ r in a..s, v r⟫_ℝ =
        ∫ r in a..s, ⟪b i, v r⟫_ℝ := by
      exact (ℓ.intervalIntegral_comp_comm hvs.intervalIntegrable).symm
    rw [hcomm, hftc]
    abel
  exact hprimitive.congr_of_eventuallyEq heq

end Analysis
end DifferentialGeometry

end
