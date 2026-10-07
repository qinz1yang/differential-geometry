import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background

/-!
# CH12-S52: `|Δ R| ≤ c · |∇² Rm|` along a smooth Ricci flow on a 3-manifold

`lapR_le_jet_S52` is `hLapR_S48_shape` (frozen in `[FROZEN v2] CH12-S48`, `scratch/FrozenS48.lean`),
verbatim, with the explicit constant `c = 3 ^ 6`.

The S48 handover believed this lemma missing from the tree.  It is not: the whole tensor calculus
(the Hessian of `R` is the metric contraction of `∇² Ric`, `∇² Ric` is the contraction of `∇² Rm`,
`|Δ f| ≤ √n |Hess f|`) is already proved in `Estimates/ScalarLaplacian.lean`
(`abs_laplacian_scalar_le_second_curvature`, flow-side norm `nablaKRm04NormSqIntrinsic`).
The only new content here is the bridge to `curvDerivNormSq` (`nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq`,
exact equality of the two towers) and the specialisation to `n = 3`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

/-- `[FROZEN v2] CH12-S48` `hLapR_S48_shape`, proved: `|Δ_{g(t)} R(t)|(x) ≤ 3⁶ · |∇² Rm|_{g(t)}(x)`
along any smooth Ricci-flow solution on a 3-manifold.  The hypotheses `IsSolutionOn S` and
`t ∈ D.carrier` are kept only to match the frozen consumer shape (the estimate is pointwise tensor
calculus at the metric `S.base.metric t`). -/
theorem lapR_le_jet_S52 :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : Type) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
      [IsManifold ThreeModel ∞ N] [T2Space N]
      {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := N) D),
      IsSolutionOn (I := ThreeModel) S →
      ∀ (t : ℝ) (x : N), t ∈ D.carrier →
        |laplacianAt (I := ThreeModel) (flowG (I := ThreeModel) S) t (S.scalar t) x| ≤
          c * Real.sqrt (DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq
            (I := ThreeModel) 2 (S.base.metric t) x) := by
  refine ⟨(3 : ℝ) ^ 6, by positivity, ?_⟩
  intro N _ _ _ _ D S _ t x _
  have : IsManifold ThreeModel 1 N :=
    IsManifold.of_le (I := ThreeModel) (M := N) (n := ∞) (by decide)
  have : IsManifold ThreeModel 2 N :=
    IsManifold.of_le (I := ThreeModel) (M := N) (n := ∞) (by decide)
  have hrank : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by rw [hrank]; norm_num⟩
  have h := DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.abs_laplacian_scalar_le_second_curvature
    (I := ThreeModel) (M := N) S t x
  rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, hrank] at h
  simpa using h

end GC.LongTime.Ch12
