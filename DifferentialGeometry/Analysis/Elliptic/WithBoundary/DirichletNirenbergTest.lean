import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartPullback
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_h1ComplDirichlet_standardNirenbergTest
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : H1ComplDirichlet q) {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let f := standardNirenbergTest k h η (fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))
    ∃ w : H1ComplDirichlet q,
      (H1ComplDirichletToLp q w : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α f ∧
      ∀ i, (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i w : EuStd → ℝ)
        =ᵐ[volume.restrict Ω] chosenWeakPartial' 2 i f Ω := by
  let v : EuStd → ℝ := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let f := standardNirenbergTest k h η v
  have hv : MemWkp 1 2 v Ω := memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u
  have hf : MemWkp 1 2 f Ω :=
    (memWkp_standardNirenbergTest_of_memWkp_local hΩ hv hη hηc k h hηs).mono_set
      (by norm_num) hΩ (subset_univ _)
  have hfs : tsupport f ⊆ Ω :=
    (standardNirenbergTest_tsupport_subset_cthickening k h η v).trans hηs
  refine ⟨h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs,
    h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs, ?_⟩
  intro i
  exact dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae q α hΩ hΩc hΩs hf hfs i
    ((chosenWeakPartial'_memLp_of_mem hf.memW1p i).locallyIntegrable (by norm_num))
    (chosenWeakPartial'_isWeakPartial_of_mem hf.memW1p i)

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
