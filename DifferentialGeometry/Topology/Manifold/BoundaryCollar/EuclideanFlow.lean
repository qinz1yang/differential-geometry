import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport

open Set Function Manifold Filter
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_complete_smooth_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (g : E → E) (hg : ContDiff ℝ ∞ g) (hgK : HasCompactSupport g) :
    ∃ Φ : E × ℝ → E, ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (x, 0) = x) ∧
      (∀ x s t, Φ (Φ (x, s), t) = Φ (x, s + t)) ∧
      (∀ t, Injective (fun x => Φ (x, t))) ∧
      ∀ x t, HasDerivAt (fun s => Φ (x, s)) (g (Φ (x, t))) t := by
  let V : (x : E) → TangentSpace 𝓘(ℝ, E) x := g
  have hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hg
  let hc := DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport V hV hgK
  let Φ : E × ℝ → E := fun p => DifferentialGeometry.Analysis.ODE.curveAt V hc p.1 p.2
  have hΦ : ContDiff ℝ ∞ Φ := by
    have hh := (DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      V hV hgK).comp (contMDiff_snd.prodMk contMDiff_fst)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact contMDiff_iff_contDiff.mp hh
  refine ⟨Φ, hΦ, DifferentialGeometry.Analysis.ODE.curveAt_zero V hc, ?_, ?_, ?_⟩
  · intro x s t
    exact (DifferentialGeometry.Analysis.ODE.curveAt_add V
      (hV.of_le (by norm_num)) hc x s t).symm
  · exact DifferentialGeometry.Analysis.ODE.curveAt_injective V (hV.of_le (by norm_num)) hc
  · intro x t
    have hd : HasFDerivAt (fun s => Φ (x, s))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (g (Φ (x, t)))) t := by
      exact (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve V hc x t).hasFDerivAt
    simpa using hd.hasDerivAt

end DifferentialGeometry.Manifold.BoundaryCollar
