import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Model
import DifferentialGeometry.Geometry.Boundary.ModelExtension
import DifferentialGeometry.Geometry.Metric.LocalRealization

/-!
The original boundary chart tensor has a positive smooth extension to an ambient open set.
This local metric supplies ambient geodesic equations without changing the manifold metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E]
  [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M]

theorem exists_boundaryChart_metric_extension (g : SmoothRiemannianMetric I M) (p : M)
    (hp : I.IsBoundaryPoint p) :
    ∃ U : TopologicalSpace.Opens E,
      extChartAt I p p ∈ U ∧ (U : Set E) ⊆ I.symm ⁻¹' (chartAt H p).target ∧
        ∃ k : SmoothRiemannianMetric 𝓘(ℝ, E) U,
          ∀ y : U, (y : E) ∈ range I → ∀ v w : E,
            k.inner y v w = metricFlatModelInChart g p (y : E) v w := by
  let O : Set E := I.symm ⁻¹' (chartAt H p).target
  have hO : IsOpen O := (chartAt H p).open_target.preimage I.continuous_symm
  have hpO : extChartAt I p p ∈ O := by
    have hpt := mem_extChartAt_target (I := I) p
    rw [extChartAt_target] at hpt
    exact hpt.1
  have hB : ContDiffOn ℝ ∞ (metricFlatModelInChart g p) (O ∩ range I) := by
    intro y hy
    exact (metricFlatModelInChart_contDiffWithinAt_of_mem g p
      (by simpa only [extChartAt_target, O] using hy)).mono inter_subset_right
  obtain ⟨V, hV, hpV, hVO, B, hBext, hBeq⟩ :=
    Boundary.exists_contDiffOn_extension_of_model I hO hpO hp hB
  let C : E → E →L[ℝ] E →L[ℝ] ℝ := fun y => (1 / 2 : ℝ) • (B y + (B y).flip)
  have hC : ContDiffOn ℝ ∞ C V := by
    exact (hBext.add
      ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff.comp_contDiffOn hBext)).const_smul
      (1 / 2 : ℝ)
  have hCsymm (y v w : E) : C y v w = C y w v := by
    dsimp [C]
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  have hCeq {y : E} (hy : y ∈ V ∩ range I) : C y = metricFlatModelInChart g p y := by
    have hyt : y ∈ (extChartAt I p).target := by
      rw [extChartAt_target]
      exact ⟨hVO hy.1, hy.2⟩
    ext v w
    dsimp [C]
    rw [hBeq hy]
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [metricFlatModelInChart_apply_of_target g p hyt,
      metricFlatModelInChart_apply_of_target g p hyt, g.symm]
    ring
  have hpR : extChartAt I p p ∈ range I := extChartAt_target_subset_range p
    (mem_extChartAt_target (I := I) p)
  have hCpos : ∀ v : E, v ≠ 0 → 0 < C (extChartAt I p p) v v := by
    intro v hv
    rw [hCeq ⟨hpV, hpR⟩, metricFlatModelInChart_center_eq]
    change 0 < metricFlatContinuousEquiv g p v v
    rw [metricFlatContinuousEquiv_apply]
    apply g.pos
    intro hvzero
    let e := trivializationAt E (TangentSpace I) p
    have hbase : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
    have hz := congrArg (e.continuousLinearMapAt ℝ p) hvzero
    rw [e.continuousLinearMapAt_symmL hbase, map_zero] at hz
    exact hv hz
  let U : TopologicalSpace.Opens E :=
    ⟨V ∩ {y | ∀ v : E, v ≠ 0 → 0 < C y v v},
      hC.continuousOn.isOpen_inter_preimage hV Analysis.isOpen_pos_diagonal⟩
  have hpU : extChartAt I p p ∈ U := ⟨hpV, hCpos⟩
  have hsection : ContMDiffOn 𝓘(ℝ, E)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : E => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y
        (show TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ from C y)) V := by
    intro y hy
    apply (contMDiffWithinAt_section (IB := 𝓘(ℝ, E))
      (F := E →L[ℝ] E →L[ℝ] ℝ) (E := fun z : E => TangentSpace 𝓘(ℝ, E) z →L[ℝ]
        TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ)).2
    convert hC.contMDiffOn y hy using 1
    ext z v w
    have hzbase : z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).baseSet := by
      simp [TangentBundle.trivializationAt_baseSet]
    have he := BilinearForm.trivializationAt_apply (I := 𝓘(ℝ, E)) y hzbase
      (show TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ from C z) v w
    convert he using 1
    simp only [TangentBundle.symmL_model_space]
    rfl
  refine ⟨U, hpU, fun y hy => hVO hy.1, ?_⟩
  refine ⟨{
    inner := fun y => C (y : E)
    symm := fun y v w => hCsymm (y : E) v w
    pos := fun y v hv => y.2.2 v hv
    isVonNBounded := fun y => posDef_isVonNBounded (C (y : E)) y.2.2
    contMDiff := ?_ }, ?_⟩
  · exact Metric.contMDiff_bilinear_restrictOpen
      (fun y : E => C y) U (hsection.mono fun y hy => hy.1)
  · intro y hy v w
    exact congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) (hCeq ⟨y.2.1, hy⟩)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
