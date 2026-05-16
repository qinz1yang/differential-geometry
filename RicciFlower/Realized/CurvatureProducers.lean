import RicciFlower.Realized.CurvatureTensor
import RicciFlower.LeviCivita.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Curvature Section Producer Interfaces

The curvature tensor layer is data-first: `Tensor13Section`, `Tensor04Section`,
and `Tensor02Section` are ordinary tensor sections, and separate predicates say
that they realize connection curvature, metric lowering, and trace contraction.

This file packages the producer output expected from the future tensoriality
and smoothness proof.  It does not construct curvature sections by choice.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Output package of the curvature-section producer for a static metric and
connection.  Constructing this package from connection laws is the tensoriality
frontier; consuming it is safe and definition-free. -/
structure CurvatureSectionProducerData
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) where
  rm13 : Tensor13Section (I := I) (M := M)
  rm04 : Tensor04Section (I := I) (M := M)
  ricci : Tensor02Section (I := I) (M := M)
  h_rm13 : Rm13RealizesConnection (I := I) cov rm13
  h_rm04 : Rm04RealizesConnection (I := I) g cov rm04
  h_ricci13 : RicciTensorRealizesRm13Trace (I := I) ricci rm13

namespace CurvatureSectionProducerData

theorem rm13_from_connection
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (K : CurvatureSectionProducerData (I := I) cov g) :
    Rm13RealizesConnection (I := I) cov K.rm13 :=
  K.h_rm13

theorem rm04_from_rm13
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (K : CurvatureSectionProducerData (I := I) cov g) :
    Rm04RealizesConnection (I := I) g cov K.rm04 :=
  K.h_rm04

theorem ricci_from_rm13
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (K : CurvatureSectionProducerData (I := I) cov g) :
    RicciTensorRealizesRm13Trace (I := I) K.ricci K.rm13 :=
  K.h_ricci13

end CurvatureSectionProducerData

end Realized
end RicciFlower
