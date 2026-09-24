import DifferentialGeometry.Topology.LocallyLipschitzOperations
import DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff.ChartLipschitz
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem locallyLipschitzOn_mul_radialDistanceCutoff_comp_extChartAt_symm
    [PreconnectedSpace M] {T : Type*} [PseudoEMetricSpace T]
    (g : SmoothRiemannianMetric I M) (p α : M) {R : ℝ} (hR : 0 < R)
    {J : Set T} {η : T → ℝ} (hη : LocallyLipschitzOn J η) :
    LocallyLipschitzOn (J ×ˢ (extChartAt I α).target)
      (fun z : T × E => η z.1 * radialDistanceCutoff g p R ((extChartAt I α).symm z.2)) := by
  have hmul : LocallyLipschitz (fun z : ℝ × ℝ => z.1 * z.2) :=
    (contDiff_fst.mul contDiff_snd :
      ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 * z.2)).locallyLipschitz
  exact hmul.locallyLipschitzOn.comp
    (hη.prod_map (locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm g p α hR))
    (Set.mapsTo_univ _ _)

end DifferentialGeometry.Geometry.Riemannian

end
