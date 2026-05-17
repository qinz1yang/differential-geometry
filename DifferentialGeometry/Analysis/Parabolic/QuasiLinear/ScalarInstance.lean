import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.AbstractSemigroup

/-!
# Bounded `C₀`-semigroup instance for the scalar spectral heat semigroup

Once strong continuity of the extended scalar heat semigroup
`heatSemigroupHsExt g σ : ℝ → scalarHs g σ →L[ℝ] scalarHs g σ` is in
hand (proved in `…Hs.HeatSemigroupContinuity`), the four-field record
`BoundedC0Semigroup (scalarHs g σ)` is filled in directly: identity at
`t = 0`, semigroup law on `t, s ≥ 0`, contraction `‖·‖ ≤ 1` on
`t ≥ 0`, and strong continuity.

This is the scalar analogue of `…QuasiLinear.TensorInstance`, and the
entry point used by `…QuasiLinear.Scalar` to invoke the abstract
semilinear-existence machinery.

## Main definitions

* `scalarHsBoundedC0Semigroup g σ` — the heat semigroup on `scalarHs g σ`
  packaged as a `BoundedC0Semigroup`.
* `hkScalarBoundedC0Semigroup g k` — the integer-exponent specialisation
  on `HkScalar g k`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The scalar spectral heat semigroup `e^{t Δ_g}` on `scalarHs g σ`
packaged as a bounded strongly continuous one-parameter contraction
semigroup. -/
def scalarHsBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    BoundedC0Semigroup (scalarHs (I := I) (M := M) g σ) where
  toFun := fun t => heatSemigroupHsExt (I := I) (M := M) g σ t
  apply_zero := heatSemigroupHsExt_zero (I := I) (M := M) g σ
  apply_add := fun _ _ ht hs =>
    heatSemigroupHsExt_add (I := I) (M := M) (g := g) (σ := σ) ht hs
  opNorm_le_one := fun _ ht =>
    heatSemigroupHsExt_opNorm_le_one (I := I) (M := M)
      (g := g) (σ := σ) ht
  continuousOn_apply := fun u =>
    heatSemigroupHsExt_continuousOn (I := I) (M := M) g σ u

/-- The underlying one-parameter family of `scalarHsBoundedC0Semigroup`
is the extended scalar heat semigroup. -/
@[simp]
theorem scalarHsBoundedC0Semigroup_apply
    (g : SmoothRiemannianMetric I M) (σ : ℝ) (t : ℝ) :
    scalarHsBoundedC0Semigroup (I := I) (M := M) g σ t =
      heatSemigroupHsExt (I := I) (M := M) g σ t := rfl

/-- The scalar spectral heat semigroup on `HkScalar g k`, packaged as a
bounded strongly continuous one-parameter contraction semigroup. -/
abbrev hkScalarBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    BoundedC0Semigroup (HkScalar (I := I) (M := M) g k) :=
  scalarHsBoundedC0Semigroup (I := I) (M := M) g (k : ℝ)

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
