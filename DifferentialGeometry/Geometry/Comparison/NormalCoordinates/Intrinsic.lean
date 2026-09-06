import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.RawIntrinsicC2

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Bundle Filter Set Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem normalChartAt_intrinsicGeodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) (x : E)
    {t : ℝ} (htx : ‖t • x‖ < expMapC2Radius g p) :
    normalChartAt g p
      (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t) = t • x := by
  have he : intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) t =
      expMap g p (show TangentSpace I p from t • x) :=
    (intrinsicGeodesic_smul g hEnorm p (show TangentSpace I p from x) t).symm.trans
      ((expMapIntrinsic_def g hEnorm p _).symm.trans (exp_eq_intr_of_c2 g hEnorm p htx).symm)
  rw [he]
  apply normalChartAt_expMap_smul g p x t
  rw [normalChartAt_target_eq]
  exact mem_expMapDiffeo_source_of_norm_lt_radius g p htx

theorem normalChartAt_intrinsicGeodesic_eventuallyEq
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (p : M) (x : E)
    {t : ℝ} (htx : ‖t • x‖ < expMapC2Radius g p) :
    (fun s : ℝ => normalChartAt g p
      (intrinsicGeodesic g hEnorm p (show TangentSpace I p from x) s)) =ᶠ[𝓝 t]
      fun s => s • x := by
  have hev : ∀ᶠ s : ℝ in 𝓝 t, ‖s • x‖ < expMapC2Radius g p :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds htx
  filter_upwards [hev] with s hs
  exact normalChartAt_intrinsicGeodesic g hEnorm p x hs

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
