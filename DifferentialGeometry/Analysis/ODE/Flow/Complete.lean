import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.CompactTrajectory

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

noncomputable def curveAtDiffeomorph [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (t : ℝ) : Diffeomorph I I M M ∞ := by
  have hv1 : CMDiff 1 (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hsmooth (s : ℝ) :
      ContMDiff I I ∞ (fun x : M ↦ curveAt v hcomplete x s) := by
    have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
        (fun x : M ↦ (s, x)) :=
      contMDiff_const.prodMk contMDiff_id
    simpa [Function.comp_def] using
      (contMDiff_curveAt v hv hcomplete).comp hpair
  exact
    { toEquiv :=
        { toFun := fun x ↦ curveAt v hcomplete x t
          invFun := fun x ↦ curveAt v hcomplete x (-t)
          left_inv := by
            intro x
            have h := curveAt_add v hv1 hcomplete x t (-t)
            simpa only [add_neg_cancel, curveAt_zero] using h.symm
          right_inv := by
            intro x
            have h := curveAt_add v hv1 hcomplete x (-t) t
            simpa only [neg_add_cancel, curveAt_zero] using h.symm }
      contMDiff_toFun := hsmooth t
      contMDiff_invFun := hsmooth (-t) }

section Diffeomorph

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  (v : (x : M) → TangentSpace I x)
  (hv : ContMDiff I I.tangent ∞
    (fun x : M ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)

@[simp]
theorem curveAtDiffeomorph_apply (t : ℝ) (x : M) :
    curveAtDiffeomorph v hv hcomplete t x = curveAt v hcomplete x t := rfl

@[simp]
theorem curveAtDiffeomorph_symm (t : ℝ) :
    (curveAtDiffeomorph v hv hcomplete t).symm =
      curveAtDiffeomorph v hv hcomplete (-t) := by
  ext x
  rfl

@[simp]
theorem curveAtDiffeomorph_zero :
    curveAtDiffeomorph v hv hcomplete 0 = Diffeomorph.refl I M ∞ := by
  ext x
  exact curveAt_zero v hcomplete x

theorem curveAtDiffeomorph_add (s t : ℝ) :
    curveAtDiffeomorph v hv hcomplete (s + t) =
      (curveAtDiffeomorph v hv hcomplete s).trans
        (curveAtDiffeomorph v hv hcomplete t) := by
  ext x
  exact curveAt_add v (hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
    hcomplete x s t

end Diffeomorph

end DifferentialGeometry.Analysis.ODE
