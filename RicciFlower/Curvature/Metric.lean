import RicciFlower.Realized.CurvatureProducers
import RicciFlower.RoughLaplacian
import RicciFlower.Tensor.RSTensor.MetricTrace
import RicciFlower.LeviCivita.Curvature
import RicciFlower.LeviCivita.Smooth

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Static metric curvature

This file contains metric-derived curvature objects for one fixed smooth
Riemannian metric.  It is deliberately below the Ricci-flow layer: no time
parameter, Ricci-flow equation, or solution predicate is involved.
-/

noncomputable section

namespace RicciFlower
namespace Curvature

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- The canonical Levi-Civita connection associated to a metric. -/
noncomputable def metricCov (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  LeviCivita.leviCivitaConnectionOfMetric (I := I) g

/-- The Levi-Civita connection of a smooth metric is locally smooth. -/
theorem metricCov_smooth (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) (M := M) g) ∞ := by
  simpa [metricCov] using
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g

/-- The pointwise `(1,3)` Riemann tensor canonically associated to a metric. -/
noncomputable def metricRm13At (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor13At (I := I) (M := M) x :=
  Riemann.CovariantDerivative.riemannCurvatureAt
    (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) x

/-- The pointwise lowered `(0,4)` Riemann tensor canonically associated to a metric. -/
noncomputable def metricRm04At (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  Riemann.CovariantDerivative.riemannCurvature04At
    (I := I) g
    (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) x

/-- The pointwise Ricci tensor canonically associated to a metric. -/
noncomputable def metricRicciAt (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  Riemann.CovariantDerivative.ricciCurvatureAt
    (I := I)
    (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) x

/-- The scalar curvature canonically associated to a metric. -/
noncomputable def metricScalarAt (g : SmoothRiemannianMetric I M) (x : M) :
    Real :=
  Realized.metricTracePair0SAt (I := I) g (metricRicciAt (I := I) (M := M) g x)

/-- The lowered Riemann tensor section canonically associated to a metric. -/
noncomputable def metricRm04 (g : SmoothRiemannianMetric I M) :
    Realized.Tensor04Section (I := I) (M := M) :=
  Riemann.CovariantDerivative.rm04Section
    (I := I) g (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g)

/-- The `(1,3)` Riemann tensor section canonically associated to a metric. -/
noncomputable def metricRm13 (g : SmoothRiemannianMetric I M) :
    Realized.Tensor13Section (I := I) (M := M) :=
  Riemann.CovariantDerivative.rm13Section
    (I := I) (M := M) (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g)

/-- The Ricci tensor section canonically associated to a metric. -/
noncomputable def metricRicci (g : SmoothRiemannianMetric I M) :
    Realized.Tensor02Section (I := I) (M := M) :=
  Riemann.CovariantDerivative.ricciSection
    (I := I) (M := M) (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g)

@[simp] theorem metricRm04_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04 (I := I) (M := M) g x =
      metricRm04At (I := I) (M := M) g x := by
  simp [metricRm04, metricRm04At]

@[simp] theorem metricRm13_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm13 (I := I) (M := M) g x =
      metricRm13At (I := I) (M := M) g x := by
  simp [metricRm13, metricRm13At]

@[simp] theorem metricRicci_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicci (I := I) (M := M) g x =
      metricRicciAt (I := I) (M := M) g x := by
  simp [metricRicci, metricRicciAt]

/-- Canonical curvature producer attached to a metric. -/
noncomputable def metricCurvData
    (g : SmoothRiemannianMetric I M) :
    Realized.CurvatureSectionProducerData (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g where
  rm13 := metricRm13 (I := I) (M := M) g
  rm04 := metricRm04 (I := I) (M := M) g
  ricci := metricRicci (I := I) (M := M) g
  h_rm13 := by
    simpa [metricRm13, metricCov] using
      (Realized.rm13Section_realizes (I := I) (M := M)
        (cov := metricCov (I := I) (M := M) g)
        (hcov := metricCov_smooth (I := I) (M := M) g))
  h_rm04 := by
    simpa [metricRm04, metricCov] using
      (Realized.rm04Section_realizes (I := I) (M := M) g
        (cov := metricCov (I := I) (M := M) g)
        (hcov := metricCov_smooth (I := I) (M := M) g))
  h_ricci13 := by
    intro x
    simp [metricRicci, metricRm13]

/-- Static smoothness of the scalar curvature of a smooth metric.

This is the static specialization of the generic smooth metric-trace theorem
for smooth `(0,2)` tensor fields. -/
theorem metricScalar_smooth
    (g : SmoothRiemannianMetric I M) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => metricScalarAt (I := I) (M := M) g x) := by
  simpa [metricScalarAt] using
    Realized.trace02_smooth (I := I) (M := M) g
      (metricRicci (I := I) (M := M) g)

/-- Component symmetry of the canonical Ricci tensor of a smooth metric. -/
theorem metricRicciSymm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (i j : Idx) :
    metricRicciAt (I := I) (M := M) g x
        (Realized.vec2 (I := I) (basis i) (basis j)) =
      metricRicciAt (I := I) (M := M) g x
        (Realized.vec2 (I := I) (basis j) (basis i)) := by
  let K := metricCurvData (I := I) (M := M) g
  have hLower :
      Realized.Rm04LowersRm13At (I := I) g x
        (metricRm13 (I := I) (M := M) g x)
        (metricRm04 (I := I) (M := M) g x) :=
    Realized.rm04LowersRm13At_of_realizes
      (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.h_rm13 K.h_rm04 x
  have hTrace :
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (metricRicciAt (I := I) (M := M) g x)
        (metricRm04At (I := I) (M := M) g x) gInv basis := by
    have hTrace' :=
      Realized.ricciFirstTraceAt_of_rm13_section
        (I := I) g basis gInv hinv
        (metricRicci (I := I) (M := M) g)
        (metricRm13 (I := I) (M := M) g)
        (metricRm04 (I := I) (M := M) g)
        K.h_ricci13 hLower
        (invMetric_symm (I := I) (M := M) g x basis gInv hinv)
    simpa using hTrace'
  have hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (1 : WithTop ℕ∞) :=
    LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g
  have hPair :
      ∀ W X Y Z : TangentSpace I x,
        metricRm04At (I := I) (M := M) g x
            (Realized.vec4 (I := I) W X Y Z) =
          metricRm04At (I := I) (M := M) g x
            (Realized.vec4 (I := I) Y Z W X) := by
    simpa using
      (LeviCivita.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g hcov1 (metricRm04 (I := I) (M := M) g) K.h_rm04
        (x := x))
  have hOutput :
      Realized.Rm04OutputSkewAt (I := I)
        (metricRm04At (I := I) (M := M) g x) := by
    simpa using
      (LeviCivita.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g hcov1 (metricRm04 (I := I) (M := M) g) K.h_rm04
        (x := x))
  have hInput :
      ∀ W X Y Z : TangentSpace I x,
        metricRm04At (I := I) (M := M) g x
            (Realized.vec4 (I := I) W Y X Z) =
          -metricRm04At (I := I) (M := M) g x
            (Realized.vec4 (I := I) W X Y Z) := by
    simpa using
      (LeviCivita.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04
        (x := x))
  exact
    Realized.ricciSymm_of_rm04 (I := I) basis gInv
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x)
      hTrace hPair hOutput hInput
      (invMetric_symm (I := I) (M := M) g x basis gInv hinv) i j

end Curvature
end RicciFlower
