import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension


noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]

theorem exists_lipschitzOnWith_extChartAt_symm_near_isCompact
    (p : M) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I p).target) :
    ∃ C : ℝ≥0, ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
      closure V ⊆ (extChartAt I p).target ∧ IsCompact (closure V) ∧
      LipschitzOnWith C (extChartAt I p).symm (closure V) := by
  obtain ⟨V, hV, hKV, hVt, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK (isOpen_extChartAt_target p) hKt
  have hlocal : LocallyLipschitzOn (extChartAt I p).target (extChartAt I p).symm := by
    intro x hx
    have hsmooth : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I p).symm x :=
      ((contMDiffOn_extChartAt_symm (I := I) (n := 1) p) x hx).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds hx)
    obtain ⟨L, s, hs, hLs⟩ :=
      (hsmooth.contMDiffWithinAt (s := univ)).exists_lipschitzOnWith (convex_univ : Convex ℝ univ)
    have hs' : s ∈ 𝓝 x := by simpa only [nhdsWithin_univ] using hs
    exact ⟨L, s, nhdsWithin_le_nhds hs', hLs⟩
  obtain ⟨C, hC⟩ := (hlocal.mono hVt).exists_lipschitzOnWith_of_compact hVc
  exact ⟨C, V, hV, hKV, hVt, hVc, hC⟩

end DifferentialGeometry.Geometry.Riemannian
