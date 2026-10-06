import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false
noncomputable section

open Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem exists_finite_order_factor_of_analytic_inverse_gauge
    {P : ℂ → V →L[ℂ] V} {ξ : ℂ → V} {a : ℂ} {n : ℕ∞ω}
    (hP : ContDiffAt ℝ n P a) (hunit : IsUnit (P a))
    (hF : AnalyticAt ℂ (fun z => (Ring.inverse (P z)) (ξ z)) a)
    (hgerm : ¬ ∀ᶠ z in 𝓝 a, ξ z = 0) :
    analyticOrderAt (fun z => (Ring.inverse (P z)) (ξ z)) a ≠ ⊤ ∧
      ∃ G : ℂ → V,
        AnalyticAt ℂ G a ∧ G a ≠ 0 ∧
        ContDiffAt ℝ n (fun z => P z (G z)) a ∧ P a (G a) ≠ 0 ∧
        ∀ᶠ z in 𝓝 a,
          ξ z = (z - a) ^
            analyticOrderNatAt (fun w => (Ring.inverse (P w)) (ξ w)) a •
              P z (G z) := by
  let F : ℂ → V := fun z => (Ring.inverse (P z)) (ξ z)
  have hunitN : ∀ᶠ z in 𝓝 a, IsUnit (P z) :=
    hP.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  have hfactor : ∀ᶠ z in 𝓝 a, ξ z = P z (F z) := by
    filter_upwards [hunitN] with z hz
    change ξ z = (P z * Ring.inverse (P z)) (ξ z)
    rw [Ring.mul_inverse_cancel _ hz]
    rfl
  have hFgerm : ¬ ∀ᶠ z in 𝓝 a, F z = 0 := by
    intro hzero
    apply hgerm
    filter_upwards [hfactor, hzero] with z hz hFz
    rw [hz, hFz, map_zero]
  have horder : analyticOrderAt F a ≠ ⊤ := by
    intro htop
    exact hFgerm (analyticOrderAt_eq_top.mp htop)
  obtain ⟨G, hG, hGzero, hFG⟩ := hF.analyticOrderAt_ne_top.mp horder
  have hGreg : ContDiffAt ℝ n G a := hG.contDiffAt.restrict_scalars ℝ
  let r : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).toContinuousLinearMap
  have hPreg : ContDiffAt ℝ n (fun z => (P z).restrictScalars ℝ) a :=
    r.contDiff.contDiffAt.comp a hP
  refine ⟨horder, G, hG, hGzero, hPreg.clm_apply hGreg, ?_, ?_⟩
  · intro hzero
    apply hGzero
    have hcancel : (Ring.inverse (P a)) (P a (G a)) = G a := by
      change (Ring.inverse (P a) * P a) (G a) = G a
      rw [Ring.inverse_mul_cancel _ hunit]
      rfl
    rw [← hcancel, hzero, map_zero]
  · filter_upwards [hfactor, hFG] with z hz hGz
    change F z = (z - a) ^ analyticOrderNatAt F a • G z at hGz
    calc
      ξ z = P z (F z) := hz
      _ = (z - a) ^ analyticOrderNatAt F a • P z (G z) := by
        rw [hGz, map_smul]

end DifferentialGeometry.Analysis
