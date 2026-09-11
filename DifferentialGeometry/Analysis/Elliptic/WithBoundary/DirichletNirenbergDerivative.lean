import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergOperator
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakDerivative

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
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

open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.Chart


theorem dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) (u : H1ComplDirichlet q) :
    let v := fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let g := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u) : EuStd → ℝ)
      =ᵐ[volume.restrict Ω]
        DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) (fun x => (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g : EuStd → ℝ) x +
          2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h v x) := by
  let v := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let g := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u
  let f := nirenbergTestFunction k h η v
  let G := DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) (fun x => (η x)^2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g : EuStd → ℝ) x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h v x)
  have hv : MemWkp 1 2 v Ω := memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u
  have hf : MemWkp 1 2 f Ω :=
    (memWkp_nirenbergTestFunction_of_memWkp_local hΩ hv hη hηc k h hηs).mono_set
      (by norm_num) hΩ (subset_univ _)
  have hGp : MemLp G 2 volume := memLp_nirenbergTestFunction_partial_local hΩ hv.memLp
    (Lp.memLp g) k j h hη hηc hηs
  have hG : DeGiorgi.HasWeakPartialDeriv j G f univ :=
    hasWeakPartialDeriv_nirenbergTestFunction_local hΩ hv.memLp (Lp.memLp g) k j h
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u) hη hηc hηs
  have hGΩ : DeGiorgi.HasWeakPartialDeriv j G f Ω := by
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ (subset_univ _) hG
  apply (dirichletLocalWeakPartialLp_dirichletNirenbergTest_coeFn q α hΩ hΩc hΩs
    hη hηc k j h hηs u).trans
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hf.memW1p j) hGΩ
    ((chosenWeakPartialOrZero_memLp_of_mem hf.memW1p j).locallyIntegrable (by norm_num))
    ((hGp.restrict Ω).locallyIntegrable (by norm_num))

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
