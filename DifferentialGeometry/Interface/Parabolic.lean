import DifferentialGeometry.Interface.Heat
import DifferentialGeometry.Analysis.HeatEquation.Duhamel

/-!
# Public Duhamel mild-solution adapters

This file is a consumption-facing facade exposing the Duhamel mild
solution of the inhomogeneous heat equation `∂_t u = Δ_g u + f` on a
closed Riemannian manifold under a single namespace. It pairs the raw
`L²`-valued primitive with a friendly one-line adapter that accepts a
smooth scalar function as the initial datum.

For scalars on a closed Riemannian manifold `(M, g)`:
- `duhamel g u_0 f t` is the Duhamel mild solution with `Lp` initial
  datum `u_0` and `Lp`-valued forcing `f`.
- `duhamelSmoothInitial g u_0 hu_0 f t` lifts a smooth scalar initial
  datum into `Lp` and applies `duhamel`.
- The homogeneous reduction `duhamel_zero_forcing` shows that with
  `f ≡ 0` the Duhamel formula collapses to the heat semigroup; its
  smooth-initial counterpart collapses to `heatFlow`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Interface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.HeatEquation

/-- Public alias for the Duhamel mild solution of the inhomogeneous heat
equation `∂_t u = Δ_g u + f`, `u(0) = u_0`, on the closed Riemannian
manifold `(M, g)`. -/
noncomputable def duhamel (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  mildSolution (I := I) (M := M) g u_0 f t

set_option linter.unusedSectionVars false in
/-- At `t = 0`, the Duhamel mild solution recovers the initial datum. -/
theorem duhamel_zero (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    duhamel (I := I) (M := M) g u_0 f 0 = u_0 := by
  unfold duhamel
  exact mildSolution_zero (I := I) (M := M) g u_0 f

set_option linter.unusedSectionVars false in
/-- With `f ≡ 0`, the Duhamel mild solution reduces to
`heatSemigroup g t u_0`. -/
theorem duhamel_zero_forcing (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) :
    duhamel (I := I) (M := M) g u_0 (fun _ => 0) t =
      heatSemigroup (I := I) (M := M) g t u_0 := by
  unfold duhamel
  exact mildSolution_zero_forcing (I := I) (M := M) g u_0 t

/-- One-line adapter: feed a smooth real scalar `u_0 : M → ℝ` as the
initial datum of the Duhamel mild solution, with an `Lp`-valued forcing
term `f`. -/
noncomputable def duhamelSmoothInitial (g : SmoothRiemannianMetric I M)
    (u_0 : M → ℝ) (hu_0 : ContMDiff I 𝓘(ℝ, ℝ) ∞ u_0)
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  duhamel (I := I) (M := M) g
    (smoothScalarToLp (I := I) (M := M) g u_0 hu_0) f t

set_option linter.unusedSectionVars false in
/-- With `f ≡ 0`, the smooth-initial Duhamel adapter reduces to the
smooth-scalar heat flow `heatFlow g t u_0 hu_0`. -/
theorem duhamelSmoothInitial_zero_forcing (g : SmoothRiemannianMetric I M)
    (u_0 : M → ℝ) (hu_0 : ContMDiff I 𝓘(ℝ, ℝ) ∞ u_0) (t : ℝ) :
    duhamelSmoothInitial (I := I) (M := M) g u_0 hu_0 (fun _ => 0) t =
      heatFlow (I := I) (M := M) g t u_0 hu_0 := by
  unfold duhamelSmoothInitial heatFlow
  exact duhamel_zero_forcing (I := I) (M := M) g
    (smoothScalarToLp (I := I) (M := M) g u_0 hu_0) t

end Interface
end DifferentialGeometry

namespace DifferentialGeometry.Interface

export DifferentialGeometry.Analysis.HeatEquation
  (mildSolution mildSolution_zero mildSolution_add_initial
   mildSolution_smul_initial mildSolution_add_forcing
   mildSolution_continuous mildSolution_zero_forcing)

end DifferentialGeometry.Interface

end
