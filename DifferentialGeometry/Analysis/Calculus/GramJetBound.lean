import DifferentialGeometry.Analysis.Calculus.MapConvergenceDeriv
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false

namespace DifferentialGeometry

open scoped ContDiff
noncomputable section

variable {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local instance formNormedAdd : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable def realInnerCLM : F →L[ℝ] F →L[ℝ] ℝ :=
  (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)

private noncomputable def gramLinear :
    (E →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  LinearMap.mk₂ ℝ
    (fun A B => realInnerCLM.bilinearComp A B)
    (by
      intro A₁ A₂ B
      ext u v
      change realInnerCLM ((A₁ + A₂) u) (B v) =
        realInnerCLM (A₁ u) (B v) + realInnerCLM (A₂ u) (B v)
      simp)
    (by
      intro c A B
      ext u v
      change realInnerCLM ((c • A) u) (B v) = c • realInnerCLM (A u) (B v)
      simp)
    (by
      intro A B₁ B₂
      ext u v
      change realInnerCLM (A u) ((B₁ + B₂) v) =
        realInnerCLM (A u) (B₁ v) + realInnerCLM (A u) (B₂ v)
      simp)
    (by
      intro c A B
      ext u v
      change realInnerCLM (A u) ((c • B) v) = c • realInnerCLM (A u) (B v)
      simp)

private theorem gramLinear_bound (A B : E →L[ℝ] F) :
    ‖gramLinear A B‖ ≤ ‖A‖ * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg A) (norm_nonneg B)) ?_
  intro u
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg B)) (norm_nonneg u)) ?_
  intro v
  calc
    ‖realInnerCLM (A u) (B v)‖ ≤
        ‖A u‖ * ‖B v‖ := by
      simpa only [realInnerCLM, innerSL_apply_apply] using
        (norm_inner_le_norm (𝕜 := ℝ) (A u) (B v))
    _ ≤ (‖A‖ * ‖u‖) * (‖B‖ * ‖v‖) := by
      gcongr
      · exact A.le_opNorm u
      · exact B.le_opNorm v
    _ = (‖A‖ * ‖B‖) * ‖u‖ * ‖v‖ := by ring

noncomputable def gramBilinear :
    (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  (gramLinear (E := E) (F := F)).mkContinuous₂ 1 (by
    intro A B
    change ‖gramLinear (E := E) (F := F) A B‖ ≤ 1 * ‖A‖ * ‖B‖
    simpa only [one_mul] using gramLinear_bound (E := E) (F := F) A B)

@[simp]
theorem gramBilinear_apply (A B : E →L[ℝ] F) (u v : E) :
    gramBilinear A B u v =
      (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (A u) (B v) :=
  rfl

theorem gram_jet_le {N : WithTop ℕ∞} {J : D → (E →L[ℝ] F)}
    (hJ : ContDiff ℝ N J) (x : D) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun z => gramBilinear (J z) (J z)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i J x‖ *
          ‖iteratedFDeriv ℝ (n - i) J x‖ :=
  by
    letI gramNorm :
        Norm ((E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
      ⟨fun T => ContinuousLinearMap.opNorm
        (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := E →L[ℝ] F)
        (F := (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
        (σ₁₂ := RingHom.id ℝ) T⟩
    have hGram : ‖gramBilinear (E := E) (F := F)‖ ≤ 1 := by
      exact ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun A B => by
        simpa only [one_mul] using gramLinear_bound (E := E) (F := F) A B
    exact
      (gramBilinear (E := E) (F := F)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
        hJ hJ x hn hGram

end
end DifferentialGeometry
