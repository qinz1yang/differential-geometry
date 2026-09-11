import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.Deriv.Add
import DifferentialGeometry.Analysis.ODE.Flow.Planar.SmoothGlobalFlow

noncomputable section
open Set Filter Topology Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_uniform_localIntegralCurve_of_eq_const_off_compact
    {v : E → E} (hv : ContDiff ℝ ∞ v) (c : E)
    (hc : HasCompactSupport (fun x ↦ v x - c)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, ∃ γ : ℝ → E,
      γ 0 = x ∧ ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (v (γ t)) t := by
  obtain ⟨R, _, hR⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  obtain ⟨ε₀, hε₀, hlocal⟩ := DifferentialGeometry.Analysis.ODE.Flow.exists_uniform_flow hv
    (isCompact_closedBall (0 : E) (R + 1))
  let ε := min ε₀ (‖c‖ + 1)⁻¹
  have hcpos : 0 < ‖c‖ + 1 := by positivity
  have hε : 0 < ε := lt_min hε₀ (inv_pos.mpr hcpos)
  refine ⟨ε, hε, fun x ↦ ?_⟩
  by_cases hx : x ∈ closedBall (0 : E) (R + 1)
  · obtain ⟨U, _, hxU, Ψ, hinit, _, hderiv⟩ := hlocal x hx
    refine ⟨fun t ↦ Ψ (x, t), hinit x hxU, fun t ht ↦ hderiv x hxU t ?_⟩
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
      ht.2.trans_le (min_le_left _ _)⟩
  · let γ : ℝ → E := fun t ↦ x + t • c
    refine ⟨γ, by simp [γ], fun t ht ↦ ?_⟩
    have htε : |t| < ε := abs_lt.mpr ht
    have htravel : ‖t • c‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |t| * ‖c‖ ≤ |t| * (‖c‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
        _ < ε * (‖c‖ + 1) := mul_lt_mul_of_pos_right htε hcpos
        _ ≤ (‖c‖ + 1)⁻¹ * (‖c‖ + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hcpos.le
        _ = 1 := inv_mul_cancel₀ hcpos.ne'
    have hxnorm : R + 1 < ‖x‖ := by simpa [mem_closedBall, dist_eq_norm] using hx
    have hγnorm : R < ‖γ t‖ := by
      have hn : ‖x‖ ≤ ‖γ t‖ + ‖t • c‖ := by
        calc ‖x‖ = ‖γ t - t • c‖ := by simp [γ]
          _ ≤ ‖γ t‖ + ‖t • c‖ := norm_sub_le _ _
      linarith
    have hout : γ t ∉ tsupport (fun x ↦ v x - c) := by
      intro hs
      have hb := hR hs
      have hn : ‖γ t‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hb
      exact hγnorm.not_ge hn
    have he : v (γ t) = c := sub_eq_zero.mp
      (image_eq_zero_of_notMem_tsupport (f := fun x : E ↦ v x - c) hout)
    rw [he]
    simpa only [γ, one_smul, id_eq] using
      (((hasDerivAt_id t).smul_const c).const_add x)

set_option backward.isDefEq.respectTransparency false in
theorem exists_globalIntegralCurve_of_eq_const_off_compact
    {v : E → E} (hv : ContDiff ℝ ∞ v) (c : E)
    (hc : HasCompactSupport (fun x ↦ v x - c)) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t : ℝ, HasDerivAt γ (v (γ t)) t := by
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_localIntegralCurve_of_eq_const_off_compact hv c hc
  let V : (x : E) → TangentSpace 𝓘(ℝ, E) x := v
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x ↦ (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv1
  have hlocalM (x : E) : ∃ γ : ℝ → E, γ 0 = x ∧
      IsMIntegralCurveOn γ V (Ioo (-ε) ε) := by
    obtain ⟨γ, hγ₀, hγ⟩ := hlocal x
    exact ⟨γ, hγ₀, fun t ht ↦ (hγ t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt⟩
  obtain ⟨γ, hγ₀, hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn hV hε hlocalM x
  exact ⟨γ, hγ₀, fun t ↦ (hγ t).hasFDerivAt⟩

theorem exists_smoothFlow_of_eq_const_off_compact
    {v : E → E} (hv : ContDiff ℝ ∞ v) (c : E)
    (hc : HasCompactSupport (fun x ↦ v x - c)) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E ↦ D p.1 p.2) ∧
      (∀ x t, HasDerivAt (fun r ↦ D r x) (v (D t x)) t) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ s t, D (s + t) = (D s).trans (D t)) ∧
      ∀ t, (D t).symm = D (-t) :=
  exists_smoothFlow_of_globalIntegralCurves hv
    (exists_globalIntegralCurve_of_eq_const_off_compact hv c hc)

end DifferentialGeometry.Analysis
