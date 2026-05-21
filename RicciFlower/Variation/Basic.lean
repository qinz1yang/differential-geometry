import RicciFlower.LeviCivita.Basic
import RicciFlower.Realized.MetricFamily
import RicciFlower.Tensor.RSTensor.Components

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Canonical first-variation paths

This file contains the book-facing variation interface used by Perelman's
functionals.  It intentionally does not define a line path `g + s v`: in Lean a
smooth Riemannian metric is not a linear object, and positivity of `g + s v`
near `s = 0` is a separate theorem.

The coordinate derivative packages in `LeviCivita/Variation.lean` are lower
level proof tools.  They should be produced from this admissible-path layer,
not used as the definition of variation.
-/

noncomputable section

namespace RicciFlower
namespace Variation

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Evaluation of a symmetric metric-variation direction on two tangent
vectors.  Symmetry is deliberately not built into the definition; it can be a
separate theorem or assumption for metric variations. -/
def metricVariationComponent
    (v : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) (X Y : TangentSpace I x) : Real :=
  v x (fun q : Fin 2 => if q = 0 then X else Y)

/-- A one-parameter admissible path through `(g, f)`.

This records only the path and its base values.  Regularity and the first
variation direction are supplied by `IsMetricPotentialVariationPath`. -/
structure MetricPotentialVariationPath
    (g : SmoothRiemannianMetric I M) (potential : M -> Real) where
  G : Realized.RealizedMetricFamily (I := I) (M := M) Real
  potentialPath : Real -> M -> Real
  base : Real
  metricBase : G.metric base = g
  potentialBase : potentialPath base = potential

namespace MetricPotentialVariationPath

variable {g : SmoothRiemannianMetric I M} {potential : M -> Real}

@[simp] theorem metric_base
    (path : MetricPotentialVariationPath (I := I) g potential) :
    path.G.metric path.base = g :=
  path.metricBase

@[simp] theorem potential_base
    (path : MetricPotentialVariationPath (I := I) g potential) :
    path.potentialPath path.base = potential :=
  path.potentialBase

end MetricPotentialVariationPath

/-- The path `(g_s, f_s)` is a variation of `(g, f)` in direction `(v, h)`.

This is the canonical book-level definition corresponding to
`δ_(v,h)`.  Higher mixed space/time regularity needed by coordinate proofs is
not part of the definition; it belongs to separate regularity producers. -/
structure IsMetricPotentialVariationPath
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : MetricPotentialVariationPath (I := I) g potential)
    (metricVariation :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation : M -> Real) : Prop where
  leviCivita :
    ∀ s : Real,
      LeviCivita.IsLeviCivita (I := I) (path.G.connection s)
        (path.G.metric s)
  metric_deriv :
    ∀ x : M, ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun s : Real => (path.G.metric s).inner x X Y)
        (metricVariationComponent (I := I) metricVariation x X Y)
        path.base
  potential_deriv :
    ∀ x : M,
      HasDerivAt (fun s : Real => path.potentialPath s x)
        (potentialVariation x) path.base

end Variation
end RicciFlower

