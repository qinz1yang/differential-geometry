/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.ChartConformality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.NormalizedDerivative

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.NormalizedDerivative

open DerivativeEccentricity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

variable [MeasurableSpace E] [BorelSpace E]

section Boundary

open HyperbolicBoundary Horospherical EuclideanBoundary GeodesicFlow
open BoundaryChartAction BoundaryChartConformal

variable {m : ℕ} [Nonempty (Fin m)]

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)

theorem ae_normalizedTensor_conjugacy (g h : IsometryGroup m)
    (ψ : BoundaryH (m + 1) → BoundaryH (m + 1)) (F : Horizontal m → Horizontal m)
    (hF : ∀ x, embed (F x) = ψ (embed x))
    (heq : ∀ v, ψ (g • v) = h • ψ v)
    (hdiff : ∀ᵐ x ∂(volume : Measure (Horizontal m)), DifferentiableAt ℝ F x) :
    ∀ᵐ x ∂(volume : Measure (Horizontal m)),
      normalizedTensor ((fderiv ℝ F (chartAction g x)).comp (fderiv ℝ (chartAction g) x)) =
        chartTensor F x := by
  filter_upwards [ae_fderiv_conjugacy g h ψ F hF heq hdiff] with x hx
  rw [hx.2.2]
  exact normalizedTensor_conformal_left _ _ (isConformalMap_fderiv_chartAction h hx.2.1)

end Boundary

end DifferentialGeometry.NormalizedDerivative
