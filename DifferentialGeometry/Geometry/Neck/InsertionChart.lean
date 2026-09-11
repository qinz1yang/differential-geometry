import DifferentialGeometry.Geometry.Neck.InsertionInput

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem controlledMap_isLocalDiffeomorph (d : normalizedDatum g x₀ δ k) :
    IsLocalDiffeomorph IC I ∞ d.controlledMap := by
  apply isLocalDiffeomorph_of_injective_mfderiv d.controlledMap d.controlledMap_smooth
  · intro q v w hvw
    rw [controlledMap_mfderiv, controlledMap_mfderiv] at hvw
    exact d.immersion _ hvw
  · rw [show Module.finrank ℝ E = 3 from Fact.out]
    simp

def controlledImage (d : normalizedDatum g x₀ δ k) : Opens M :=
  d.controlledMap_isLocalDiffeomorph.image

theorem controlledImage_coe (d : normalizedDatum g x₀ δ k) :
    (d.controlledImage : Set M) = range d.controlledMap := rfl

theorem controlledMap_mem_controlledImage (d : normalizedDatum g x₀ δ k)
    (q : openCylinder δ⁻¹) : d.controlledMap q ∈ d.controlledImage :=
  ⟨q, rfl⟩

theorem center_mem_controlledImage (d : normalizedDatum g x₀ δ k) :
    x₀ ∈ d.controlledImage := by
  have hδ : 0 < δ⁻¹ := inv_pos.mpr d.precision_pos
  let q : openCylinder δ⁻¹ := ⟨(spherePoint, 0), by
    change -δ⁻¹ < 0 ∧ (0 : ℝ) < δ⁻¹
    exact ⟨neg_neg_of_pos hδ, hδ⟩⟩
  refine ⟨q, ?_⟩
  change d.map (cylinderCenter δ d.precision_pos) = x₀
  exact d.center_eq

def controlledChart (d : normalizedDatum g x₀ δ k) :
    openCylinder δ⁻¹ ≃ₘ⟮IC, I⟯ d.controlledImage :=
  diffeomorphOntoImage d.controlledMap d.controlledMap_isLocalDiffeomorph
    d.controlledMap_isOpenEmbedding.injective

theorem controlledChart_apply (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹) :
    (d.controlledChart q : M) = d.controlledMap q := rfl

theorem controlledChart_symm_apply (d : normalizedDatum g x₀ δ k)
    (p : d.controlledImage) :
    d.controlledMap (d.controlledChart.symm p) = p.val :=
  diffeomorphOntoImage_symm_apply d.controlledMap d.controlledMap_isLocalDiffeomorph
    d.controlledMap_isOpenEmbedding.injective p

theorem controlledChart_symm_controlledMap (d : normalizedDatum g x₀ δ k)
    (q : openCylinder δ⁻¹) :
    d.controlledChart.symm ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ = q :=
  d.controlledChart.symm_apply_apply q

theorem controlledChart_mfderiv (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹)
    (v : TangentSpace IC q) :
    mfderiv IC I d.controlledChart q v = mfderiv IC I d.controlledMap q v := by
  have he : (Subtype.val : d.controlledImage → M) ∘ d.controlledChart = d.controlledMap := rfl
  rw [← he, mfderiv_comp q
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    (d.controlledChart.contMDiff.mdifferentiableAt (by decide)), mfderiv_subtype_val]
  rfl

theorem controlledMetric_eq_pullback_controlledChart (d : normalizedDatum g x₀ δ k) :
    d.controlledMetric = Diffeomorph.pullbackMetricCross
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (g.restrictOpen d.controlledImage))
      d.controlledChart := by
  have he : d.controlledMetric = pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos g) d.controlledMap
      d.controlledMap_isLocalDiffeomorph d.controlledMap_isOpenEmbedding.injective := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [controlledMetric_inner, pullbackMetricOfInjectiveLocalDiffeomorph_inner,
      scaleMetric_inner]
  exact he.trans (pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart
    g d.controlledMap d.controlledMap_isLocalDiffeomorph d.controlledMap_isOpenEmbedding.injective
    (metricScalarAt g x₀) d.scalar_pos d.controlledImage d.controlledChart d.controlledChart_apply)

private theorem controlledChart_mfderiv_symm (d : normalizedDatum g x₀ δ k)
    (p : d.controlledImage) (v : TangentSpace I p) :
    mfderiv IC I d.controlledChart (d.controlledChart.symm p)
      (mfderiv I IC d.controlledChart.symm p v) = v := by
  have hc := mfderiv_comp p
    (d.controlledChart.contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    (d.controlledChart.symm.contMDiff.mdifferentiableAt (by decide))
  have he : d.controlledChart ∘ d.controlledChart.symm = id :=
    funext d.controlledChart.apply_symm_apply
  rw [he, mfderiv_id] at hc
  exact (congrArg (fun f => f v) hc).symm

theorem pullback_controlledMetric_controlledChart_symm (d : normalizedDatum g x₀ δ k) :
    Diffeomorph.pullbackMetricCross d.controlledMetric d.controlledChart.symm =
      scaleMetric (metricScalarAt g x₀) d.scalar_pos (g.restrictOpen d.controlledImage) := by
  rw [controlledMetric_eq_pullback_controlledChart]
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner,
    controlledChart_mfderiv_symm, controlledChart_mfderiv_symm,
    d.controlledChart.apply_symm_apply]

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
