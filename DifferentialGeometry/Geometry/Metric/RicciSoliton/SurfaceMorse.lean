import DifferentialGeometry.Topology.Morse.Riemannian
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_isNondegenerateCriticalPointAt_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hcrit : IsCriticalPointAt I f x) :
    IsNondegenerateCriticalPointAt I f x := by
  apply isNondegenerateCriticalPointAt_of_hessFun_eq_smul_metric
    (c := (1 - metricScalarAt (I := I) (M := M) g x) / 2) g f x hcrit
  · intro hzero
    apply hnonconstant
    have hscalarx : metricScalarAt (I := I) (M := M) g x = 1 := by
      linarith
    have hgradx : gradFun (I := I) g f x = 0 :=
      gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hcrit
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  · intro v w
    exact normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
      (I := I) h hdim x v w

end DifferentialGeometry.Geometry
