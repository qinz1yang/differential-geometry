import DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients
import DifferentialGeometry.Bundle.TangentOpenRestriction

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem symmL_open_model_space (U : Opens E) (x₀ x : U) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x =
      (1 : E →L[ℝ] E) := by
  have hx : x ∈ (chartAt E x₀).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact mem_univ _
  rw [TangentBundle.symmL_trivializationAt_eq_core hx,
    tangentCoordChange_opens x₀ x x (mem_univ _), TangentBundle.coordChange_model_space]

private def openMetricInner (U : Opens E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : U) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ := by
  exact B x.1

theorem exists_smoothMetric_of_contDiffOn_bilinearField
    (U : Opens E) (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, x ∈ U → ∀ v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiffOn ℝ ∞ B U) :
    ∃ g : SmoothRiemannianMetric 𝓘(ℝ, E) U,
      ∀ x v w, g.inner x v w = B x.1 v w := by
  let gm : ∀ x : U, TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
    openMetricInner U B
  have hsymm' : ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, E) x), gm x v w = gm x w v := by
    intro x v w
    exact hsymm x.1 x.2 v w
  have hpos' : ∀ (x : U) (v : TangentSpace 𝓘(ℝ, E) x), v ≠ 0 → 0 < gm x v v := by
    intro x v hv
    exact hpos x.1 x.2 v hv
  have hcoeff : ∀ x₀ : U, ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (fun x => gm x (frameVec (I := 𝓘(ℝ, E)) x₀ i x)
          (frameVec (I := 𝓘(ℝ, E)) x₀ j x))
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := by
    intro x₀ i j
    simp only [gm, openMetricInner, frameVec]
    simp only [symmL_open_model_space]
    exact (((hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const).contMDiffOn.comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U)).contMDiffOn
      (fun x _ => x.property))
  exact smoothMetric_of_localCoeff gm hsymm' hpos' hcoeff

end DifferentialGeometry.Geometry

end
