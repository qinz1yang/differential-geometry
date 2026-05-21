import RicciFlower.Realized.RicciFlow
import RicciFlower.Curvature.Metric
import RicciFlower.Coordinates.MetricCompatibility
import RicciFlower.Riemann.Basic
import RicciFlower.Realized.Bochner
import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Realized.CurvatureProducers
import RicciFlower.LeviCivita.Smooth
import RicciFlower.LeviCivita.Torsion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# RicciFlower Ricci-Flow Folder Entry Point

This file is the forward-facing Ricci-flow API.  The older
`RicciFlower.Realized.RicciFlow` module remains as a compatibility layer; this
folder-level module packages a solution as a real-time metric family together
with bundled Ricci tensor sections, then records interval-local validity as a
separate layer.

The Section 6.2 evolution identities are introduced as explicit equation
predicates.  The current file records the interfaces and the algebraic
composition for Lemma 6.7; the geometric producers for Ricci/scalar evolution
are separate proof frontiers.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-! ## Ricci-flow solutions as metric families -/

/-- A time-dependent bundled Ricci tensor section. -/
abbrev RicciSectionFamily : Type _ :=
  Real -> Realized.Tensor02Section (I := I) (M := M)

/-- A time-dependent pointwise Ricci tensor family.

This is the canonical Ricci-flow-facing shape: a metric determines the Ricci
tensor pointwise through its Levi-Civita curvature.  Bundled tensor sections are
kept as compatibility/realization data, not as the source of the metric Ricci
definition. -/
abbrev RicciAtFamily : Type _ :=
  Real -> (x : M) -> Curvature.Tensor02At (I := I) (M := M) x

namespace RicciAtFamily

/-- View a pointwise Ricci family as the tensor field expected by the older
realized Ricci-flow API. -/
def toTensorField (Ric : RicciAtFamily (I := I) (M := M)) :
    Realized.RicciTensorField (I := I) (M := M) Real :=
  fun t x X Y => Ric t x (Realized.vec2 X Y)

@[simp] theorem toTensorField_apply
    (Ric : RicciAtFamily (I := I) (M := M))
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    toTensorField (I := I) Ric t x X Y =
      Ric t x (Realized.vec2 X Y) := by
  rfl

end RicciAtFamily

namespace RicciSectionFamily

/-- View a bundled Ricci section family as the pointwise tensor field expected
by the compatibility `Realized.RicciFlow` API. -/
def toTensorField (Ric : RicciSectionFamily (I := I) (M := M)) :
    Realized.RicciTensorField (I := I) (M := M) Real :=
  fun t x X Y => Ric t x (Realized.vec2 X Y)

@[simp] theorem toTensorField_apply
    (Ric : RicciSectionFamily (I := I) (M := M))
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    toTensorField (I := I) Ric t x X Y =
      Ric t x (Realized.vec2 X Y) := by
  rfl

end RicciSectionFamily

variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- Ricci-flow compatibility alias for the static Levi-Civita connection. -/
abbrev metricCov (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  Curvature.metricCov (I := I) (M := M) g

/-- Ricci-flow compatibility alias for static Levi-Civita smoothness. -/
theorem metricCov_smooth (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) (M := M) g) ∞ :=
  Curvature.metricCov_smooth (I := I) (M := M) g

/-- Ricci-flow compatibility alias for static pointwise Riemann curvature. -/
abbrev metricRm13At (g : SmoothRiemannianMetric I M) (x : M) :
    Curvature.Tensor13At (I := I) (M := M) x :=
  Curvature.metricRm13At (I := I) (M := M) g x

/-- Ricci-flow compatibility alias for static pointwise lowered Riemann curvature. -/
abbrev metricRm04At (g : SmoothRiemannianMetric I M) (x : M) :
    Curvature.Tensor04At (I := I) (M := M) x :=
  Curvature.metricRm04At (I := I) (M := M) g x

/-- Ricci-flow compatibility alias for static pointwise Ricci curvature. -/
abbrev metricRicciAt (g : SmoothRiemannianMetric I M) (x : M) :
    Curvature.Tensor02At (I := I) (M := M) x :=
  Curvature.metricRicciAt (I := I) (M := M) g x

/-- Ricci-flow compatibility alias for static scalar curvature. -/
abbrev metricScalarAt (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Curvature.metricScalarAt (I := I) (M := M) g x

/-- Ricci-flow compatibility alias for the static lowered Riemann section. -/
abbrev metricRm04 (g : SmoothRiemannianMetric I M) :
    Realized.Tensor04Section (I := I) (M := M) :=
  Curvature.metricRm04 (I := I) (M := M) g

/-- Ricci-flow compatibility alias for the static `(1,3)` Riemann section. -/
abbrev metricRm13 (g : SmoothRiemannianMetric I M) :
    Realized.Tensor13Section (I := I) (M := M) :=
  Curvature.metricRm13 (I := I) (M := M) g

/-- Ricci-flow compatibility alias for the static Ricci section. -/
abbrev metricRicci (g : SmoothRiemannianMetric I M) :
    Realized.Tensor02Section (I := I) (M := M) :=
  Curvature.metricRicci (I := I) (M := M) g

@[simp] theorem metricRm04_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04 (I := I) (M := M) g x =
      metricRm04At (I := I) (M := M) g x :=
  Curvature.metricRm04_apply (I := I) (M := M) g x

@[simp] theorem metricRm13_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm13 (I := I) (M := M) g x =
      metricRm13At (I := I) (M := M) g x :=
  Curvature.metricRm13_apply (I := I) (M := M) g x

@[simp] theorem metricRicci_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicci (I := I) (M := M) g x =
      metricRicciAt (I := I) (M := M) g x :=
  Curvature.metricRicci_apply (I := I) (M := M) g x

/-- Ricci-flow compatibility alias for the static metric curvature producer. -/
abbrev metricCurvData
    (g : SmoothRiemannianMetric I M) :
    Realized.CurvatureSectionProducerData (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g :=
  Curvature.metricCurvData (I := I) (M := M) g

/-- Static scalar curvature of a smooth metric is smooth. -/
theorem metricScalar_smooth
    (g : SmoothRiemannianMetric I M) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => metricScalarAt (I := I) (M := M) g x) :=
  Curvature.metricScalar_smooth (I := I) (M := M) g

/-- Compatibility nonempty form of the metric curvature producer. -/
theorem metricCurvData_exists
    (g : SmoothRiemannianMetric I M) :
    Nonempty (Realized.CurvatureSectionProducerData (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g) :=
  ⟨metricCurvData (I := I) (M := M) g⟩

/-- A data-only real-time Ricci-flow family, independent of a chosen interval.

The connection and Ricci tensor are intentionally not fields: they are the
Levi-Civita connection and Ricci tensor of the metric at that time, exposed
below as accessors for compatibility with the old API. -/
structure SolutionFamily where
  metric : Real -> SmoothRiemannianMetric I M

namespace SolutionFamily

/-- Time translation of a real-time metric family.

The shifted time `s` corresponds to the original time `s + τ`. -/
def timeShift
    (G : SolutionFamily (I := I) (M := M)) (τ : Real) :
    SolutionFamily (I := I) (M := M) where
  metric := fun s => G.metric (s + τ)

@[simp] theorem timeShift_metric
    (G : SolutionFamily (I := I) (M := M)) (τ s : Real) :
    (G.timeShift τ).metric s = G.metric (s + τ) := by
  rfl

/-- The Levi-Civita connection of the family metric at time `t`. -/
noncomputable def connection
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  fun t => LeviCivita.leviCivitaConnectionOfMetric (I := I) (G.metric t)

/-- The `(1,3)` Riemann tensor of the family metric at time `t`. -/
noncomputable def rm13At
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> (x : M) -> Curvature.Tensor13At (I := I) (M := M) x :=
  fun t x => metricRm13At (I := I) (M := M) (G.metric t) x

/-- The lowered pointwise Riemann tensor of the family metric at time `t`. -/
noncomputable def rm04At
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> (x : M) -> Curvature.Tensor04At (I := I) (M := M) x :=
  fun t x => metricRm04At (I := I) (M := M) (G.metric t) x

/-- The pointwise Ricci tensor of the family metric at time `t`. -/
noncomputable def ricciAt
    (G : SolutionFamily (I := I) (M := M)) :
    RicciAtFamily (I := I) (M := M) :=
  fun t x => metricRicciAt (I := I) (M := M) (G.metric t) x

/-- The scalar curvature of the family metric at time `t`. -/
noncomputable def scalar
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> M -> Real :=
  fun t x => metricScalarAt (I := I) (M := M) (G.metric t) x

/-- Compatibility bundled `(1,3)` Riemann tensor of the family metric.

This remains a realization-section API.  The canonical metric curvature used by
the flow core is `rm13At`; this bundled section should be replaced by a real
tensoriality/smoothness producer when downstream code is migrated. -/
noncomputable def rm13
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> Realized.Tensor13Section (I := I) (M := M) :=
  fun t => metricRm13 (I := I) (M := M) (G.metric t)

/-- Compatibility bundled lowered Riemann tensor of the family metric. -/
noncomputable def rm04
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> Realized.Tensor04Section (I := I) (M := M) :=
  fun t => metricRm04 (I := I) (M := M) (G.metric t)

/-- Compatibility bundled Ricci tensor of the family metric.

Core Ricci-flow definitions use `ricciAt`; this bundled section is kept for
legacy component/evolution consumers until their realization inputs are
migrated. -/
noncomputable def ricci
    (G : SolutionFamily (I := I) (M := M)) :
    RicciSectionFamily (I := I) (M := M) :=
  fun t => metricRicci (I := I) (M := M) (G.metric t)

@[simp] theorem ricci_apply
    (G : SolutionFamily (I := I) (M := M))
    (t : Real) (x : M) :
    G.ricci t x = G.ricciAt t x := by
  simp [ricci, ricciAt]

@[simp] theorem scalar_apply
    (G : SolutionFamily (I := I) (M := M))
    (t : Real) (x : M) :
    G.scalar t x =
      Realized.metricTracePair0SAt (I := I) (G.metric t) (G.ricciAt t x) := by
  simp [scalar, metricScalarAt, Curvature.metricScalarAt, ricciAt, metricRicciAt]

/-- The metric and connection are compatible at every flow time of `D`. -/
def MetricCompatibleOn
    (G : SolutionFamily (I := I) (M := M))
    (D : Realized.RealTimeInterval) : Prop :=
  forall t : Realized.RealTimeInterval.FlowTime D,
    RicciFlower.Connection.IsMetricCompatible (I := I)
      (G.connection (t : Real)) (G.metric (t : Real))

end SolutionFamily

/-- A Ricci-flow candidate on a real interval.

The only underlying data is the real-time metric family.  The connection and
Ricci tensor are metric-derived accessors on `SolutionFamily`. -/
structure SolutionOn (D : Realized.RealTimeInterval) where
  base : SolutionFamily (I := I) (M := M)

namespace SolutionOn

/-- Time translation of a solution candidate.

The shifted candidate lives on `D.timeShift τ`, and its time `s` metric is the
original metric at time `s + τ`. -/
def timeShift {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ : Real) :
    SolutionOn (I := I) (M := M) (D.timeShift τ) where
  base := S.base.timeShift τ

@[simp] theorem timeShift_base {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ : Real) :
    (S.timeShift τ).base = S.base.timeShift τ := by
  rfl

@[simp] theorem timeShift_base_metric {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).base.metric s = S.base.metric (s + τ) := by
  rfl

/-- Metric compatibility is automatic because `S.family.connection` is the
Levi-Civita connection of `S.family.metric`. -/
theorem metricCompatible {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.base.MetricCompatibleOn D := by
  intro t
  exact LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible
    (I := I) (S.base.metric (t : Real))

/-- The interval-indexed realized metric family associated to a solution
candidate.  This preserves the previous `S.family` API. -/
def family {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Realized.RealizedMetricFamilyOn (I := I) (M := M) D where
  metric := S.base.metric
  connection := S.base.connection
  metricCompatible := S.metricCompatible

/-- The bundled Ricci tensor section family.  This preserves the previous
`S.ricci` API. -/
def ricci {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    RicciSectionFamily (I := I) (M := M) :=
  S.base.ricci

/-- The canonical pointwise Ricci tensor family of a solution candidate. -/
def ricciAt {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    RicciAtFamily (I := I) (M := M) :=
  S.base.ricciAt

/-- The canonical scalar curvature family of a solution candidate. -/
def scalar {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  S.base.scalar

@[simp] theorem family_metric {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.family.metric = S.base.metric := by
  rfl

@[simp] theorem family_connection {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.family.connection = S.base.connection := by
  rfl

@[simp] theorem ricci_eq {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.ricci = S.base.ricci := by
  rfl

@[simp] theorem ricciAt_eq {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.ricciAt = S.base.ricciAt := by
  rfl

@[simp] theorem scalar_eq {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.scalar = S.base.scalar := by
  rfl

@[simp] theorem scalar_eq_metricTrace {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    S.scalar t x =
      Realized.metricTracePair0SAt (I := I) (S.family.metric t)
        (S.ricciAt t x) := by
  simp [scalar, SolutionFamily.scalar_apply]

@[simp] theorem timeShift_family_metric {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).family.metric s = S.family.metric (s + τ) := by
  rfl

@[simp] theorem timeShift_ricci {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).ricci s = S.ricci (s + τ) := by
  rfl

@[simp] theorem timeShift_ricciAt {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).ricciAt s = S.ricciAt (s + τ) := by
  rfl

@[simp] theorem timeShift_scalar {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).scalar s = S.scalar (s + τ) := by
  rfl

/-- The shifted solution has the same initial metric, evaluated at the shifted
interval's distinguished initial time. -/
theorem timeShift_initial_metric {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ : Real) :
    (S.timeShift τ).family.metric ((D.timeShift τ).initial) =
      S.family.metric D.initial := by
  simp [Realized.RealTimeInterval.timeShift, sub_add_cancel]

@[simp] theorem timeShift_self_initial_metric {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    (S.timeShift D.initial).family.metric 0 = S.family.metric D.initial := by
  simp

/-- Compatibility view as the older realized Ricci-flow candidate. -/
def toRealizedCandidate {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Realized.RealizedRicciFlowCandidateOn (I := I) (M := M) D where
  family := S.family
  ricci := RicciAtFamily.toTensorField (I := I) S.ricciAt

@[simp] theorem toRealizedCandidate_family {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.toRealizedCandidate.family = S.family := by
  rfl

end SolutionOn

/-- The Ricci-flow metric equation for a folder-level solution:
`∂_t g = -2 Ric`, on the interval carrier and at regular times. -/
def MetricVariationEquationOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  Realized.MetricVariationEquationOn (I := I) S.family
    (RicciAtFamily.toTensorField (I := I) S.ricciAt)

/-- Intrinsic Ricci norm square `|Ric|²` for a solution candidate. -/
def ricciNorm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)

/-- Intrinsic `|∇ Ric|²`, using the canonical total covariant derivative. -/
def ricciGradSq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    normSq0S (I := I) (S.family.metric t) x 3
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x)

/-- The all-real realized metric family canonically attached to a Ricci-flow
solution candidate. -/
def flowG
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Realized.RealizedMetricFamily (I := I) (M := M) Real where
  metric := S.base.metric
  connection := S.base.connection
  metricCompatible := by
    intro t
    simpa [SolutionFamily.connection] using
      (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric t))

/-- Canonical intrinsic Laplacian of the Ricci norm square `|Ric|²`. -/
def ricciNormLap
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    Realized.laplacianAt (I := I) (flowG (I := I) S) t
      (ricciNorm (I := I) S t) x

/-- The `(0,4)` tensor with components `Ric_ij Ric_kl` in the slot order used
by the Ricci-norm curvature reaction `Rm04(i,k,j,l) Ric_ij Ric_kl`. -/
def ricciPair04 {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x) :
    Realized.Tensor04At (I := I) (M := M) x :=
  (Bundle.continuousMultilinearMap.product_fun
      (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
      (s := 2) (q := 2) (x := x) Ric Ric).domDomCongr
    (Equiv.swap (1 : Fin 4) (2 : Fin 4))

/-- Intrinsic canonical Ricci-norm curvature reaction scalar.  This is the
coordinate-free version of the Section 6 frame reaction, with the project sign
convention already applied. -/
def ricciReact
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x =>
    -inner0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)
      (ricciPair04 (I := I) (S.ricciAt t x))

/-- Predicate package saying the folder-level candidate is a Ricci-flow
solution. -/
structure IsSolutionOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  smoothMetric : Realized.MetricFamilySmoothOn (I := I) (M := M) D S.family
  smoothConnection : RicciFlower.Connection.ConnectionFamilySmoothOn (I := I) (M := M) S.family
  equation : MetricVariationEquationOn (I := I) S

namespace IsSolutionOn

/-- Levi-Civita-ness is automatic in the metric-only solution model. -/
theorem leviCivita
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (_hS : IsSolutionOn (I := I) S) :
    RicciFlower.LeviCivita.IsLeviCivitaFamilyOn (I := I) S.family := by
  constructor
  · intro t
    exact S.metricCompatible t
  · intro t
    exact LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
      (I := I) (S.base.metric (t : Real))

end IsSolutionOn

/-- Joint spacetime continuity of the canonical scalar curvature of a solution
candidate.

This package deliberately records only scalar spacetime continuity.  It should
not be used as a proxy for full curvature-tensor regularity; Ricci and Riemann
tensor regularity live in `CanonicalRicciRegularOn`. -/
structure ScalarSTContOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  scalar_continuousAt : ∀ p : Real × M,
    ContinuousAt (fun q : Real × M => S.scalar q.1 q.2) p

/-- Regularity of the canonical scalar curvature needed by scalar maximum
principle consumers.

This is deliberately not tied to a particular barrier or comparison theorem.
It records the scalar field's basic time/space differentiability and the fixed
time regularity of its gradient for the evolving metric.  Producer theorems
from spacetime-smooth metrics and canonical curvature should target this
package, while WMP files derive their barrier-specific hypotheses from it. -/
structure CanonicalScalarRegularOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  scalar_continuousAt : ∀ p : Real × M,
    ContinuousAt (fun q : Real × M => S.scalar q.1 q.2) p
  scalar_time_within :
    ∀ {K : Set Real} {t : Real}, t ∈ K -> K ⊆ D.carrier -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => S.scalar s x) K t
  scalar_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar t) x
  scalar_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t) (S.scalar t) y) x
  scalar_mul_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% ((S.scalar t) • fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t) (S.scalar t) y)) x
  scalar_sq_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.scalar t y ^ 2) x
  scalar_sq_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2) y) x
  scalar_sq_div_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.scalar t y ^ 2 / 3) x
  scalar_sq_div_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2 / 3) y) x
  scalar_grad_sub_const :
    ∀ t : Real, t ∈ D.carrier -> ∀ c : Real, ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z - c) y) x
  scalar_grad_const_mul_sub_const :
    ∀ t : Real, t ∈ D.carrier -> ∀ a c : Real, ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (fun z : M => a * (S.scalar t z - c)) y) x

namespace CanonicalScalarRegularOn

/-- Scalar regularity contains scalar spacetime continuity. -/
theorem toScalarSTCont
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalScalarRegularOn (I := I) (M := M) S) :
    ScalarSTContOn (I := I) (M := M) S where
  scalar_continuousAt := hreg.scalar_continuousAt

end CanonicalScalarRegularOn

/-- Regularity of the canonical Ricci tensor and Ricci norm.

This package is deliberately below the Ricci-flow heat equation.  It records
the canonical tensor-family continuity needed by compactness and WMP arguments,
plus the differentiability needed to use scalar Laplacian linearity for
`|Ric|² - R² / 3`.  Ricci evolution and Bochner realization remain separate
producer frontiers. -/
structure CanonicalRicciRegularOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  ricci_cont :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => S.ricci t x)
  rm04_cont :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.carrier
      (fun t x => S.base.rm04 t x)
  nablaRic_cont :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 3 D.carrier
      (fun t x =>
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (S.family.connection t) (S.ricci t) x)
  ricci_norm_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) x
  ricci_norm_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x

namespace CanonicalRicciRegularOn

/-- Canonical Ricci tensor family continuity over the solution interval. -/
theorem ricciTensorFamilyContinuousOnSet
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalRicciRegularOn (I := I) (M := M) S) :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => S.ricci t x) :=
  hreg.ricci_cont

/-- Canonical lowered Riemann tensor family continuity over the solution
interval. -/
theorem rm04FamilyContinuousOnSet
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalRicciRegularOn (I := I) (M := M) S) :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.carrier
      (fun t x => S.base.rm04 t x) :=
  hreg.rm04_cont

/-- Canonical total covariant derivative of Ricci is continuous as a
time-dependent `(0,3)` tensor family over the solution interval. -/
theorem nablaRicFamilyContinuousOnSet
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalRicciRegularOn (I := I) (M := M) S) :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 3 D.carrier
      (fun t x =>
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (S.family.connection t) (S.ricci t) x) :=
  hreg.nablaRic_cont

end CanonicalRicciRegularOn

namespace SolutionOn

/-- Continuity of canonical scalar curvature on any spacetime slab, extracted
from the scalar spacetime-continuity package. -/
theorem scalar_continuousOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (hreg : ScalarSTContOn (I := I) (M := M) S)
    (T : Real) :
    ContinuousOn (fun p : Real × M => S.scalar p.1 p.2)
      ((Set.Icc 0 T).prod (Set.univ : Set M)) := by
  exact (continuous_iff_continuousAt.mpr hreg.scalar_continuousAt).continuousOn

end SolutionOn

/-- Time translation preserves the Ricci-flow solution predicate.

This is the analytic chain-rule bridge for `HasDerivWithinAt` on translated
time carriers, together with the corresponding smoothness pullback statements.
It is the right place to discharge the future time-shift normalization used by
Hamilton's Section 11/12 package. -/
theorem isSolutionOn_timeShift
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) (τ : Real) :
    IsSolutionOn (I := I) (S.timeShift τ) where
  smoothMetric := by
    constructor
    · intro x X Y
      have hOld := hS.smoothMetric.coeff x X Y
      have haff : ContDiff Real ⊤ (fun s : Real => s + τ) :=
        contDiff_id.add contDiff_const
      have hmaps :
          Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
        intro s hs
        exact hs
      have hcomp :
          ContDiffOn Real ⊤
            (fun s : Real => (S.family.metric (s + τ)).inner x X Y)
            (D.timeShift τ).carrier := by
        simpa [Function.comp_def] using hOld.comp haff.contDiffOn hmaps
      simpa [SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift] using hcomp
    · have hmaps :
          Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
        intro s hs
        exact hs
      have htime : Continuous (fun s : Real => s + τ) :=
        (continuous_id.add continuous_const)
      have hcont :=
        Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
          hS.smoothMetric.metricTensor_cont htime hmaps
      simpa [SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift]
        using hcont
  smoothConnection := by
    intro t
    let t' : Realized.RealTimeInterval.FlowTime D := ⟨(t : Real) + τ, t.2⟩
    have hOld := hS.smoothConnection t'
    simpa [t', SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift,
      Realized.RealizedMetricFamilyOn.connectionAt, SolutionFamily.connection] using hOld
  equation := by
    intro t x X Y
    let t' : Realized.RealTimeInterval.RegularTime D := ⟨(t : Real) + τ, t.2⟩
    have hOld := hS.equation t' x X Y
    have hshift :
        HasDerivWithinAt (fun s : Real => s + τ) 1
          (D.timeShift τ).carrier (t : Real) := by
      simpa using
        ((hasDerivWithinAt_id (t : Real) (D.timeShift τ).carrier).add_const τ)
    have hmaps :
        Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
      intro s hs
      exact hs
    have hcomp := hOld.comp (x := (t : Real)) hshift hmaps
    simpa [MetricVariationEquationOn, SolutionOn.family, SolutionOn.timeShift,
      SolutionFamily.timeShift, RicciAtFamily.toTensorField, Function.comp_def] using hcomp

/-- Convert the folder-level solution predicate to the older realized
compatibility predicate. -/
theorem isRealizedRicciFlowSolutionOn_of_isSolutionOn
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) :
    Realized.IsRealizedRicciFlowSolutionOn (I := I) S.toRealizedCandidate := by
  exact
    { smoothMetric := hS.smoothMetric
      smoothConnection := hS.smoothConnection
      leviCivita := hS.leviCivita
      equation := hS.equation }

/-- Extract the interval metric evolution equation from a folder-level solution. -/
theorem metric_derivWithin_eq_neg_two_ricci
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricciAt (t : Real) x (Realized.vec2 X Y))
      D.carrier
      (t : Real) := by
  simpa [MetricVariationEquationOn, RicciAtFamily.toTensorField] using
    hS.equation t x X Y

/-! ## Section 6.2: Ricci and scalar evolution interfaces -/

section Components

variable {Idx : Type*} [Fintype Idx]

private def raise2By
    (G A : Idx -> Idx -> Real) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx, G i a * G j b * A a b

private def oneUpBy
    (G A : Idx -> Idx -> Real) (i k : Idx) : Real :=
  ∑ a : Idx, G k a * A i a

private def quadraticBy
    (G A : Idx -> Idx -> Real) (i j : Idx) : Real :=
  ∑ k : Idx, oneUpBy G A i k * A k j

private theorem split_raise2By_tail
    (G B : Idx -> Idx -> Real) (c : Real) (i j : Idx)
    (P Q : Idx -> Idx -> Real) :
    c * (∑ a : Idx, ∑ b : Idx,
        (P a b + Q a b + G i a * G j b * B a b)) =
      c * (∑ a : Idx, ∑ b : Idx, (P a b + Q a b)) +
        c * raise2By G B i j := by
  classical
  unfold raise2By
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add,
    add_assoc, mul_left_comm, mul_comm]

private theorem sum_two_sub_cancel_scaled
    (L C Q R : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) +
        4 * (∑ i : Idx, ∑ j : Idx, Q i j * R i j) +
        (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * R i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * R i j)) := by
  classical
  let LS : Real := ∑ i : Idx, ∑ j : Idx, L i j * R i j
  let CS : Real := ∑ i : Idx, ∑ j : Idx, C i j * R i j
  let QS : Real := ∑ i : Idx, ∑ j : Idx, Q i j * R i j
  have hpoint (i j : Idx) :
      (L i j - 2 * C i j - 2 * Q i j) * R i j =
        L i j * R i j - (C i j * R i j) * 2 - (Q i j * R i j) * 2 := by
    ring
  have hsum :
      (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) =
        LS - 2 * CS - 2 * QS := by
    calc
      (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j)
          =
        ∑ i : Idx, ∑ j : Idx,
          (L i j * R i j - (C i j * R i j) * 2 - (Q i j * R i j) * 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          exact hpoint i j
      _ =
        (∑ i : Idx, ∑ j : Idx, L i j * R i j) -
          (∑ i : Idx, ∑ j : Idx, (C i j * R i j) * 2) -
            (∑ i : Idx, ∑ j : Idx, (Q i j * R i j) * 2) := by
          simp only [Finset.sum_sub_distrib]
      _ =
        LS - CS * 2 - QS * 2 := by
          simp only [LS, CS, QS, Finset.sum_mul]
      _ =
        LS - 2 * CS - 2 * QS := by
          ring
  rw [hsum]
  change (LS - 2 * CS - 2 * QS) + 4 * QS + (LS - 2 * CS - 2 * QS) =
    2 * LS + 4 * (-CS)
  ring

private theorem sum_mul_raise2By_comm
    (G A B : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i) :
    (∑ i : Idx, ∑ j : Idx, A i j * raise2By G B i j) =
      ∑ i : Idx, ∑ j : Idx, B i j * raise2By G A i j := by
  classical
  unfold raise2By
  calc
    (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx, G i a * G j b * B a b))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
        A i j * (G i a * G j b * B a b) := by
          simp [Finset.mul_sum]
    _ =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
        A i j * (G i a * G j b * B a b) := by
          calc
            (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
              A i j * (G i a * G j b * B a b))
                =
              ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx,
                A i j * (G i a * G j b * B a b) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ i : Idx, ∑ j : Idx, ∑ b : Idx,
                A i j * (G i a * G j b * B a b) := by
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
                A i j * (G i a * G j b * B a b) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  calc
                    (∑ i : Idx, ∑ j : Idx, ∑ b : Idx,
                      A i j * (G i a * G j b * B a b))
                        =
                      ∑ i : Idx, ∑ b : Idx, ∑ j : Idx,
                        A i j * (G i a * G j b * B a b) := by
                          refine Finset.sum_congr rfl fun i _ => ?_
                          rw [Finset.sum_comm]
                    _ =
                      ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
                        A i j * (G i a * G j b * B a b) := by
                          rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
        B a b * (G a i * G b j * A i j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hG i a, hG j b]
          ring
    _ =
      ∑ a : Idx, ∑ b : Idx,
        B a b * (∑ i : Idx, ∑ j : Idx, G a i * G b j * A i j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

private theorem sum_contraction_mul_eq_four_sum
    (R4 : Idx -> Idx -> Idx -> Idx -> Real)
    (A : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx,
      (∑ k : Idx, ∑ l : Idx, R4 i k j l * A k l) * A i j) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        R4 i k j l * A i j * A k l := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx,
      (∑ k : Idx, ∑ l : Idx, R4 i k j l * A k l) * A i j)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (R4 i k j l * A k l) * A i j := by
        simp [Finset.sum_mul]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        R4 i k j l * A i j * A k l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

private theorem quadraticBy_eq_sum_right
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i)
    (i j : Idx) :
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
  classical
  unfold quadraticBy oneUpBy
  calc
    (∑ k : Idx, (∑ a : Idx, G k a * A i a) * A k j)
        =
      ∑ k : Idx, ∑ a : Idx, G k a * A i a * A k j := by
        simp [Finset.sum_mul, mul_assoc]
    _ =
      ∑ k : Idx, ∑ a : Idx, G k a * A i a * A j k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hA k j]
    _ =
      ∑ a : Idx, ∑ k : Idx, G k a * A i a * A j k := by
        rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hG b a]

private theorem quadraticBy_eq_sum_left
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i)
    (i j : Idx) :
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A a i * A b j := by
  classical
  calc
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
        exact quadraticBy_eq_sum_right G A hG hA i j
    _ =
      ∑ a : Idx, ∑ b : Idx, G a b * A a i * A b j := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hA i a, hA j b]

private theorem metricDerivativeQuadraticTerms_eq_four
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i) :
    (∑ i : Idx, ∑ j : Idx,
      A i j *
        (∑ a : Idx, ∑ b : Idx,
          (2 * raise2By G A i a * G j b * A a b +
            G i a * (2 * raise2By G A j b) * A a b))) =
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
  classical
  have hright :
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b)) =
        2 * (∑ i : Idx, ∑ a : Idx,
          quadraticBy G A i a * raise2By G A i a) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
          A i j * (2 * raise2By G A i a * G j b * A a b) := by
            simp [Finset.mul_sum]
      _ =
        ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx,
          A i j * (2 * raise2By G A i a * G j b * A a b) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ =
        ∑ i : Idx, ∑ a : Idx,
          2 * raise2By G A i a *
            (∑ j : Idx, ∑ b : Idx, G j b * A i j * A a b) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ i : Idx, ∑ a : Idx,
          2 * raise2By G A i a * quadraticBy G A i a := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← quadraticBy_eq_sum_right G A hG hA i a]
      _ =
        2 * (∑ i : Idx, ∑ a : Idx,
          quadraticBy G A i a * raise2By G A i a) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
  have hleft :
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b)) =
        2 * (∑ j : Idx, ∑ b : Idx,
          quadraticBy G A j b * raise2By G A j b) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
          A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
            simp [Finset.mul_sum]
      _ =
        ∑ j : Idx, ∑ b : Idx, ∑ i : Idx, ∑ a : Idx,
          A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
            calc
              (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
                A i j * (G i a * (2 * raise2By G A j b) * A a b))
                  =
                ∑ j : Idx, ∑ i : Idx, ∑ a : Idx, ∑ b : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    rw [Finset.sum_comm]
              _ =
                ∑ j : Idx, ∑ i : Idx, ∑ b : Idx, ∑ a : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_comm]
              _ =
                ∑ j : Idx, ∑ b : Idx, ∑ i : Idx, ∑ a : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    rw [Finset.sum_comm]
      _ =
        ∑ j : Idx, ∑ b : Idx,
          2 * raise2By G A j b *
            (∑ i : Idx, ∑ a : Idx, G i a * A i j * A a b) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ j : Idx, ∑ b : Idx,
          2 * raise2By G A j b * quadraticBy G A j b := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← quadraticBy_eq_sum_left G A hG hA j b]
      _ =
        2 * (∑ j : Idx, ∑ b : Idx,
          quadraticBy G A j b * raise2By G A j b) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
  calc
    (∑ i : Idx, ∑ j : Idx,
      A i j *
        (∑ a : Idx, ∑ b : Idx,
          (2 * raise2By G A i a * G j b * A a b +
            G i a * (2 * raise2By G A j b) * A a b)))
        =
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b)) +
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b)) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add,
            mul_left_comm, mul_comm]
    _ =
      2 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) +
      2 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
          rw [hright, hleft]
    _ =
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
          ring

private theorem ricciNormDerivativeSimplifies_pure
    (G A L C : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i) :
    (∑ i : Idx, ∑ j : Idx,
      ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
          raise2By G A i j +
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b +
                G i a * G j b *
                  (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
  classical
  let B : Idx -> Idx -> Real :=
    fun i j => L i j - 2 * C i j - 2 * quadraticBy G A i j
  have hpair :
      (∑ i : Idx, ∑ j : Idx, A i j * raise2By G B i j) =
        ∑ i : Idx, ∑ j : Idx, B i j * raise2By G A i j :=
    sum_mul_raise2By_comm G A B hG
  have hmetric := metricDerivativeQuadraticTerms_eq_four G A hG hA
  calc
    (∑ i : Idx, ∑ j : Idx,
      ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
          raise2By G A i j +
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b +
                G i a * G j b *
                  (L a b - 2 * C a b - 2 * quadraticBy G A a b)))))
        =
      ∑ i : Idx, ∑ j : Idx,
        (B i j * raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b)) +
          A i j * raise2By G B i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          let P : Idx -> Idx -> Real :=
            fun a b => 2 * raise2By G A i a * G j b * A a b
          let Q : Idx -> Idx -> Real :=
            fun a b => G i a * (2 * raise2By G A j b) * A a b
          change
            B i j * raise2By G A i j +
                A i j * (∑ a : Idx, ∑ b : Idx,
                  (P a b + Q a b + G i a * G j b * B a b)) =
              B i j * raise2By G A i j +
                A i j * (∑ a : Idx, ∑ b : Idx, (P a b + Q a b)) +
                  A i j * raise2By G B i j
          rw [split_raise2By_tail]
          ring
    _ =
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) +
      (∑ i : Idx, ∑ j : Idx,
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b))) +
      (∑ i : Idx, ∑ j : Idx,
        A i j * raise2By G B i j) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ =
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) +
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) +
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) := by
          rw [hmetric, hpair]
    _ =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
          simpa [B, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
            sum_two_sub_cancel_scaled
              (Idx := Idx)
              (L := L)
              (C := C)
              (Q := quadraticBy G A)
              (R := raise2By G A)

/-- Interpret the canonical pointwise Ricci family as the two-tensor field used
by the coordinate Bochner layer. -/
def ricciTwoTensorField
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> RicciFlower.Curvature.RawTwoTensorField (I := I) (M := M) :=
  fun t x X Y => S.ricciAt t x (Realized.vec2 X Y)

@[simp] theorem ricciTwoTensorField_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    ricciTwoTensorField (I := I) S t x X Y =
      S.ricciAt t x (Realized.vec2 X Y) := by
  rfl

/-- Canonical Ricci component in a time-dependent frame. -/
def ricciCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  S.ricciAt t x (Realized.vec2 (frame i x) (frame j x))

@[simp] theorem ricciCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      S.ricciAt t x (Realized.vec2 (frame i x) (frame j x)) := by
  rfl

/-- Ricci with both indices raised, as the solution-level projection of the
generic frame algebra in `Bochner.lean`:
`Ric^{ij} = g^{ia} g^{jb} Ric_ab`. -/
abbrev raisedRicciCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  Realized.raisedRicciComponentsInFrame (I := I) (M := M) (Time := Real)
    (ricciTwoTensorField (I := I) S) gInv frame t x i j

@[simp] theorem raisedRicciCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b *
          ricciCompInFrame (I := I) S frame t x a b := by
  rfl

/-- Ricci with the second index raised:
`Ric_i^k = g^{ka} Ric_ia`. -/
def ricciOneUpCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) : Real :=
  ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a

@[simp] theorem ricciOneUpCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) :
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k =
      ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a := by
  rfl

/-- The quadratic term `Ric_i^k Ric_kj` from Lemma 6.3. -/
def ricciQuadraticCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
      ricciCompInFrame (I := I) S frame t x k j

@[simp] theorem ricciQuadraticCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciQuadraticCompInFrame (I := I) S gInv frame t x i j =
      ∑ k : Idx,
        ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
          ricciCompInFrame (I := I) S frame t x k j := by
  rfl

/-- The curvature-Ricci contraction `R_ikjl Ric^{kl}` from Lemma 6.3. -/
def rmRicciContractionCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
      raisedRicciCompInFrame (I := I) S gInv frame t x k l

@[simp] theorem rmRicciContractionCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl

/-- Component RHS for Lemma 6.3 in the project lowered-curvature convention:
`Delta Ric_ij - 2 * rmRicciContractionCompInFrame - 2 Ric_i^k Ric_kj`. -/
-- Convention note: in this file's `Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)` slot order,
-- the implementation below has a minus sign on `rmRicciContractionCompInFrame`.
def ricciEvolutionRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  roughLapRic t x i j -
    2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
      2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j

@[simp] theorem ricciEvolutionRHSInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j =
      roughLapRic t x i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
          2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate Ricci norm square for a folder-level Ricci-flow solution,
projected from the generic frame algebra in `Bochner.lean`. -/
abbrev ricciNormSqInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  Realized.ricciNormSqInFrame (I := I) (M := M) (Time := Real)
    (ricciTwoTensorField (I := I) S) gInv frame

@[simp] theorem ricciNormSqInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- The coordinate Ricci norm in any frame agrees with the intrinsic squared
Ricci norm, provided the supplied inverse components really are the inverse
metric in the matching pointwise basis. -/
theorem ricciNormSq_basis
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {t : Real} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x basis
      (fun i j : Idx => gInv t x i j))
    (hbasis : ∀ i : Idx, basis i = frame i x) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) := by
  classical
  rw [normSq0S_eq_inner]
  rw [inner0S_two_eq_coord
    (I := I) (S.family.metric t) x basis
    (fun i j : Idx => gInv t x i j) hinv (S.ricci t x) (S.ricci t x)]
  simp [ricciNormSqInFrame, Realized.vec2, hbasis, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  have hij :
      RicciFlower.Curvature.vec2 (I := I) (frame i x) (frame j x) =
        (fun a : Fin 2 => if a = 0 then frame i x else frame j x) := by
    funext a
    fin_cases a <;> simp [RicciFlower.Curvature.vec2]
  have hkl :
      RicciFlower.Curvature.vec2 (I := I) (frame k x) (frame l x) =
        (fun a : Fin 2 => if a = 0 then frame k x else frame l x) := by
    funext a
    fin_cases a <;> simp [RicciFlower.Curvature.vec2]
  rw [hij, hkl]

/-- Coordinate inner product `<roughDelta Ric, Ric>` for a folder-level
Ricci-flow solution, projected from the generic frame algebra in
`Bochner.lean`. -/
abbrev roughLapRicciInnerInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  Realized.roughLapRicciInnerInFrame (I := I) (M := M) (Time := Real)
    roughLapRic (ricciTwoTensorField (I := I) S) gInv frame

@[simp] theorem roughLapRicciInnerInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- Coordinate squared norm of `nabla Ric`. -/
def nablaRicComp
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Idx -> Idx -> Idx -> Real :=
  fun t x a i j =>
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t) x
        (Realized.vec3 (I := I) (frame a x) (frame i x) (frame j x))

@[simp] theorem nablaRicComp_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a i j : Idx) :
    nablaRicComp (I := I) S frame t x a i j =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x
          (Realized.vec3 (I := I) (frame a x) (frame i x) (frame j x)) := by
  rfl

/-- Coordinate squared norm of a supplied `nabla Ric` component array,
projected from the generic frame algebra in `Bochner.lean`. -/
abbrev nablaRicciNormSqInFrame
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx) :
    Real -> M -> Real :=
  Realized.nablaRicciNormSqInFrame (M := M) nablaRic gInv

@[simp] theorem nablaRicciNormSqInFrame_apply
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (t : Real) (x : M) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x a b * gInv t x i k * gInv t x j l *
          nablaRic t x a i j * nablaRic t x b k l := by
  rfl

private def fin3Slots (a b c : Idx) : Fin 3 -> Idx :=
  fun q => if q = 0 then a else if q = 1 then b else c

@[simp] private theorem fin3Slots_zero (a b c : Idx) :
    fin3Slots (Idx := Idx) a b c 0 = a := by
  simp [fin3Slots]

@[simp] private theorem fin3Slots_one (a b c : Idx) :
    fin3Slots (Idx := Idx) a b c 1 = b := by
  simp [fin3Slots]

@[simp] private theorem fin3Slots_two (a b c : Idx) :
    fin3Slots (Idx := Idx) a b c 2 = c := by
  simp [fin3Slots]

private def fin3PairEquiv :
    ((Fin 3 -> Idx) × (Fin 3 -> Idx)) ≃
      (((((Idx × Idx) × Idx) × Idx) × Idx) × Idx) where
  toFun p := (((((p.1 0, p.2 0), p.1 1), p.1 2), p.2 1), p.2 2)
  invFun p :=
    (fin3Slots (Idx := Idx) p.1.1.1.1.1 p.1.1.1.2 p.1.1.2,
      fin3Slots (Idx := Idx) p.1.1.1.1.2 p.1.2 p.2)
  left_inv p := by
    ext q <;> fin_cases q <;> simp
  right_inv p := by
    rcases p with ⟨⟨⟨⟨⟨a, b⟩, i⟩, j⟩, k⟩, l⟩
    simp

private theorem coordInner3_eq
    {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 3 gInv A B basis =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv a b * gInv i k * gInv j l *
          A (Realized.vec3 (I := I) (basis a) (basis i) (basis j)) *
            B (Realized.vec3 (I := I) (basis b) (basis k) (basis l)) := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [← Fintype.sum_prod_type']
  rw [Fintype.sum_equiv (fin3PairEquiv (Idx := Idx))
    (fun p : (Fin 3 -> Idx) × (Fin 3 -> Idx) =>
      ((∏ q : Fin 3, gInv (p.1 q) (p.2 q)) *
        A (fun q : Fin 3 => basis (p.1 q))) *
          B (fun q : Fin 3 => basis (p.2 q)))
    (fun p : (((((Idx × Idx) × Idx) × Idx) × Idx) × Idx) =>
      ((∏ q : Fin 3,
          gInv (((fin3PairEquiv (Idx := Idx)).symm p).1 q)
            (((fin3PairEquiv (Idx := Idx)).symm p).2 q)) *
        A (fun q : Fin 3 => basis (((fin3PairEquiv (Idx := Idx)).symm p).1 q))) *
          B (fun q : Fin 3 => basis (((fin3PairEquiv (Idx := Idx)).symm p).2 q)))]
  · repeat rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    change
      ((∏ q : Fin 3,
          gInv (fin3Slots (Idx := Idx) a i j q)
            (fin3Slots (Idx := Idx) b k l q)) *
        A (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) a i j q))) *
          B (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) b k l q)) =
        gInv a b * gInv i k * gInv j l *
          A (Realized.vec3 (I := I) (basis a) (basis i) (basis j)) *
            B (Realized.vec3 (I := I) (basis b) (basis k) (basis l))
    rw [Fin.prod_univ_three]
    have hA :
        (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) a i j q)) =
          Realized.vec3 (I := I) (basis a) (basis i) (basis j) := by
      funext q
      fin_cases q <;> simp [Realized.vec3, RicciFlower.Curvature.vec3]
    have hB :
        (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) b k l q)) =
          Realized.vec3 (I := I) (basis b) (basis k) (basis l) := by
      funext q
      fin_cases q <;> simp [Realized.vec3, RicciFlower.Curvature.vec3]
    rw [hA, hB]
    simp [fin3Slots]
  · intro p
    have h1 :
        fin3Slots (Idx := Idx) (p.1 0) (p.1 1) (p.1 2) = p.1 := by
      funext q
      fin_cases q <;> simp
    have h2 :
        fin3Slots (Idx := Idx) (p.2 0) (p.2 1) (p.2 2) = p.2 := by
      funext q
      fin_cases q <;> simp
    simp [fin3PairEquiv, h1, h2]

/-- A component array realizing the canonical covariant derivative of Ricci has
the same squared norm as the intrinsic tensor `|∇ Ric|²`. -/
private theorem nablaRicciNorm_basis
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {t : Real} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x basis
      (fun i j : Idx => gInv t x i j))
    (hbasis : ∀ i : Idx, basis i = frame i x)
    (hnabla : ∀ a i j : Idx,
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x
          (Realized.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ricciGradSq (I := I) S t x := by
  classical
  rw [ricciGradSq]
  rw [normSq0S_eq_coord
    (I := I) (S.family.metric t) x 3 basis
    (fun i j : Idx => gInv t x i j) hinv]
  rw [coordInner3_eq (I := I) (x := x)
    (fun i j : Idx => gInv t x i j)
    (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t) x)
    (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t) x)
    basis]
  have hnabla' : ∀ a i j : Idx,
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.base.connection t) (S.base.ricci t) x
          (Realized.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j := by
    intro a i j
    simpa [SolutionOn.family, SolutionOn.ricci] using hnabla a i j
  simp [nablaRicciNormSqInFrame, hbasis, hnabla', mul_left_comm, mul_comm]

/-- The canonical frame components of `∇ Ric` have squared norm equal to the
intrinsic `|∇ Ric|²`. -/
theorem nablaRicciNorm_can
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {t : Real} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x basis
      (fun i j : Idx => gInv t x i j))
    (hbasis : ∀ i : Idx, basis i = frame i x) :
    nablaRicciNormSqInFrame (M := M) (nablaRicComp (I := I) S frame) gInv t x =
      ricciGradSq (I := I) S t x :=
  nablaRicciNorm_basis (I := I) S (nablaRicComp (I := I) S frame) gInv frame
    basis hinv hbasis (by intro a i j; rfl)

/-- The curvature-Ricci-Ricci term `R_ikjl Ric^ij Ric^kl`. -/
def curvRicciRicciInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l

@[simp] theorem curvRicciRicciInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j *
            raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl

/-- Canonical curvature reaction in the Ricci-norm evolution formula.

With the project convention `Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)`, the book term
`R_ikjl Ric^{ij} Ric^{kl}` is the negative of `curvRicciRicciInFrame`. -/
def ricciNormCurvatureReactionInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x => -curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x

@[simp] theorem ricciNormCurvatureReactionInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      -curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x := by
  rfl

/-- The inverse-metric part of the Ricci-flow metric evolution:
`partial_t g^{ij} = 2 Ric^{ij}`.  The future geometric proof differentiates
`g^{ik} g_kj = delta^i_j` and uses `partial_t g_ij = -2 Ric_ij`. -/
def inverseMetricEvolutionRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  2 * raisedRicciCompInFrame (I := I) S gInv frame t x i j

/-- Component equation `partial_t g^{ij} = 2 Ric^{ij}`. -/
def InverseMetricEvolutionEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u -> ∀ (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Product-rule RHS for differentiating `Ric^{ij}`. -/
def raisedRicciDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i a *
        gInv t x j b * ricciCompInFrame (I := I) S frame t x a b +
      gInv t x i a *
        inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x j b *
          ricciCompInFrame (I := I) S frame t x a b +
        gInv t x i a * gInv t x j b *
          ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x a b)

/-- Product-rule RHS for differentiating `|Ric|^2 = Ric_ij Ric^ij`. -/
def ricciNormDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j +
      ricciCompInFrame (I := I) S frame t x i j *
        raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j)

/-- The remaining finite-sum simplification in Lemma 6.7.

This is the explicit cancellation/reindexing frontier: after the product rule,
the inverse-metric variation terms cancel the `-2 Ric_i^k Ric_kj` part of
Lemma 6.3, leaving `2 <roughDelta Ric, Ric> + 4 R_ikjl Ric^ij Ric^kl`. -/
def RicciNormDerivativeSimplifiesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x

/-- Pointwise canonical finite-sum simplification for the time derivative of
`|Ric|^2`.

This is the form used by coordinate-frame producers centered at the evaluation
point; it only needs inverse-metric and Ricci symmetry at that point. -/
theorem ricciDerivSimpAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (hInvSym : forall i j, gInv (t : Real) x i j = gInv (t : Real) x j i)
    (hRicSym : forall i j,
      ricciCompInFrame (I := I) S frame (t : Real) x i j =
        ricciCompInFrame (I := I) S frame (t : Real) x j i) :
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame
          (t : Real) x +
        4 * ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame
          (t : Real) x := by
  classical
  let G : Idx -> Idx -> Real := fun i j => gInv (t : Real) x i j
  let A : Idx -> Idx -> Real :=
    fun i j => ricciCompInFrame (I := I) S frame (t : Real) x i j
  let L : Idx -> Idx -> Real := fun i j => roughLapRic (t : Real) x i j
  let C : Idx -> Idx -> Real :=
    fun i j =>
      rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame (t : Real) x i j
  have hG : forall i j, G i j = G j i := by
    intro i j
    exact hInvSym i j
  have hA : forall i j, A i j = A j i := by
    intro i j
    exact hRicSym i j
  have hpure := ricciNormDerivativeSimplifies_pure (Idx := Idx) G A L C hG hA
  have hderiv :
      ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
    change
      (∑ i : Idx, ∑ j : Idx,
        ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
            raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b +
                  G i a * G j b *
                    (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j))
    exact hpure
  have hrough :
      roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x =
        ∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j := by
    simp [G, A, L, roughLapRicciInnerInFrame, raise2By]
  let R4 : Idx -> Idx -> Idx -> Idx -> Real :=
    fun i k j l => Realized.rm04Comp (I := I) (Rm04 (t : Real)) frame x i k j l
  let AR : Idx -> Idx -> Real := fun i j => raise2By G A i j
  have hcurv :
      (∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) =
        curvRicciRicciInFrame (I := I) S Rm04 gInv frame (t : Real) x := by
    change
      (∑ i : Idx, ∑ j : Idx,
        (∑ k : Idx, ∑ l : Idx, R4 i k j l * AR k l) * AR i j) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          R4 i k j l * AR i j * AR k l
    exact sum_contraction_mul_eq_four_sum (Idx := Idx) R4 AR
  have hreaction :
      ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame (t : Real) x =
        -(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) := by
    rw [ricciNormCurvatureReactionInFrame_apply, ← hcurv]
  calc
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := hderiv
    _ =
        2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x +
          4 * ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame
            (t : Real) x := by
          rw [hrough, hreaction]

/-- Canonical finite-sum simplification for the time derivative of
`|Ric|^2`.

After differentiating the inverse metrics and substituting Lemma 6.3, the
inverse-metric derivative terms cancel the Ricci-quadratic terms, and the
curvature term is recorded with the project `Rm04(W,X,Y,Z)` sign convention. -/
theorem ricciNormDerivativeSimplifiesInFrame_canonical
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  intro t x
  let G : Idx -> Idx -> Real := fun i j => gInv (t : Real) x i j
  let A : Idx -> Idx -> Real :=
    fun i j => ricciCompInFrame (I := I) S frame (t : Real) x i j
  let L : Idx -> Idx -> Real := fun i j => roughLapRic (t : Real) x i j
  let C : Idx -> Idx -> Real :=
    fun i j =>
      rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame (t : Real) x i j
  have hG : forall i j, G i j = G j i := by
    intro i j
    exact hInvSym (t : Real) x i j
  have hA : forall i j, A i j = A j i := by
    intro i j
    exact hRicSym (t : Real) x i j
  have hpure := ricciNormDerivativeSimplifies_pure (Idx := Idx) G A L C hG hA
  have hderiv :
      ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
    change
      (∑ i : Idx, ∑ j : Idx,
        ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
            raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b +
                  G i a * G j b *
                    (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j))
    exact hpure
  have hrough :
      roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x =
        ∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j := by
    simp [G, A, L, roughLapRicciInnerInFrame, raise2By]
  let R4 : Idx -> Idx -> Idx -> Idx -> Real :=
    fun i k j l => Realized.rm04Comp (I := I) (Rm04 (t : Real)) frame x i k j l
  let AR : Idx -> Idx -> Real := fun i j => raise2By G A i j
  have hcurv :
      (∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) =
        curvRicciRicciInFrame (I := I) S Rm04 gInv frame (t : Real) x := by
    change
      (∑ i : Idx, ∑ j : Idx,
        (∑ k : Idx, ∑ l : Idx, R4 i k j l * AR k l) * AR i j) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          R4 i k j l * AR i j * AR k l
    exact sum_contraction_mul_eq_four_sum (Idx := Idx) R4 AR
  have hreaction :
      ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame (t : Real) x =
        -(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) := by
    rw [ricciNormCurvatureReactionInFrame_apply, ← hcurv]
  calc
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := hderiv
    _ =
        2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x +
          4 * ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame
            (t : Real) x := by
          rw [hrough, hreaction]

/-- Lemma 6.3 in component/equation form.  This is the geometric frontier
needed before the norm evolution proof can be made constructive. -/
def RicciEvolutionEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Project the inverse-metric evolution equation at fixed components. -/
theorem inverseMetricEvolutionEquationInFrame_apply
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {gInv : Real -> Realized.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    {u : Set M}
    (h : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x hx i j

/-- Constructor for the inverse-metric evolution equation from component
derivative equalities. -/
theorem inverseMetricEvolutionEquationInFrame_of_components
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (h : ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      ∀ (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => gInv s x i j)
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u :=
  h

/-- Project Lemma 6.3's component equation at fixed components. -/
theorem ricciEvolutionEquationInFrame_apply
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M)}
    {gInv : Real -> Realized.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    {roughLapRic : Real -> M -> Idx -> Idx -> Real}
    (h : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x i j

/-- Constructor for Lemma 6.3's component equation from component derivative
equalities. -/
theorem ricciEvolutionEquationInFrame_of_components
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h : ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic :=
  h

/-- Product-rule derivative of the raised Ricci components. -/
theorem raisedRicciCompInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    {u : Set M}
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [raisedRicciCompInFrame, raisedRicciDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun a s =>
        ∑ b : Idx,
          gInv s x i a * gInv s x j b *
            ricciCompInFrame (I := I) S frame s x a b)
      (A' := fun a =>
        ∑ b : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i a *
              gInv (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
            gInv (t : Real) x i a *
              inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
              gInv (t : Real) x i a * gInv (t : Real) x j b *
                ricciEvolutionRHSInFrame
                  (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
      (s := D.carrier) (x := (t : Real))
      (fun a _ha =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun b s =>
                gInv s x i a * gInv s x j b *
                  ricciCompInFrame (I := I) S frame s x a b)
              (A' := fun b =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i a *
                    gInv (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                  gInv (t : Real) x i a *
                    inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                    gInv (t : Real) x i a * gInv (t : Real) x j b *
                      ricciEvolutionRHSInFrame
                        (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
              (s := D.carrier) (x := (t : Real))
              (fun b _hb =>
                by
                  have hia := h_inv t x hx i a
                  have hjb := h_inv t x hx j b
                  have hrab := h_ricci t x a b
                  have hprod := (hia.mul hjb).mul hrab
                  simpa [Pi.mul_apply, mul_assoc, add_mul] using hprod))))

/-- Product-rule derivative of the coordinate Ricci norm square. -/
theorem ricciNormSqInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    {u : Set M}
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) :
    HasDerivWithinAt
      (fun s : Real => ricciNormSqInFrame (I := I) S gInv frame s x)
      (ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [ricciNormSqInFrame, ricciNormDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          ricciCompInFrame (I := I) S frame s x i j *
            raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
              raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
            ricciCompInFrame (I := I) S frame (t : Real) x i j *
              raisedRicciDerivRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                ricciCompInFrame (I := I) S frame s x i j *
                  raisedRicciCompInFrame (I := I) S gInv frame s x i j)
              (A' := fun j =>
                (ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
                    raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
                  ricciCompInFrame (I := I) S frame (t : Real) x i j *
                    raisedRicciDerivRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hRic := h_ricci t x i j
                  have hRaised :=
                    raisedRicciCompInFrame_hasDerivWithinAt
                      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x hx i j
                  have hprod := hRic.mul hRaised
                  simpa [Pi.mul_apply] using hprod))))

end Components

/-- Scalar curvature evolution in Section 6.2:
`∂_t R = Δ R + 2 |Ric|²`. -/
def ScalarEvolutionEquationOn
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (scalarLap (t : Real) x + 2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

/-! ## Lemma 6.7: Ricci norm heat equation, component assembly -/

/-- Time derivative component identity for `|Ric|²`.

This is the point where differentiating inverse metrics and using Lemma 6.3 has
already cancelled the cubic `Ric_i^k Ric_kj` terms. -/
def RicciNormTimeDerivativeComponentsOn
    {D : Realized.RealTimeInterval}
    (ricciNormSq roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x)
      D.carrier
      (t : Real)

section RicciNormDerivative

variable {Idx : Type*} [Fintype Idx]

/-- The time-derivative identity for `|Ric|^2` once the component evolution
equations and the remaining finite-sum simplification are supplied. -/
theorem ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (h_simplify : RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic roughLapInner reaction) :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      roughLapInner reaction := by
  intro t x
  have hnorm :=
    ricciNormSqInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x (by simp)
  simpa [h_simplify t x] using hnorm

/-- Canonical time-derivative identity for `|Ric|^2` from Lemma 6.3 and the
inverse-metric evolution equation. -/
theorem ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) :=
  ricciNormTimeDerivativeComponentsOn_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic
    (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    h_inv h_ricci
    (ricciNormDerivativeSimplifiesInFrame_canonical
      (I := I) S Rm04 gInv frame roughLapRic hInvSym hRicSym)

end RicciNormDerivative

/-- Laplacian component identity for `|Ric|²`:
`Δ |Ric|² = 2 <Δ Ric, Ric> + 2 |∇Ric|²`. -/
def RicciNormLaplacianComponentsOn
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    ricciNormLap t x = 2 * roughLapInner t x + 2 * nablaRicNormSq t x

/-- Bridge from the realized Bochner coordinate predicate to the interval
Ricci-flow predicate. -/
theorem ricciNormLaplacianComponentsOn_of_bochner
    (ricciNormLap roughLapInner nablaRicNormSq : Real -> M -> Real)
    (h_lap : Realized.RicciNormLaplacianComponentsInFrame
      (M := M) (Time := Real) ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormLaplacianComponentsOn ricciNormLap roughLapInner nablaRicNormSq :=
  h_lap

/-- Canonical interval-level Ricci-norm Laplacian identity from the exact
coordinate Bochner expansion for `|Ric|^2`. -/
theorem ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
    {D : Realized.RealTimeInterval}
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic) :
    RicciNormLaplacianComponentsOn
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv) := by
  have hrealized :=
    Realized.ricciNormLaplacianComponentsInFrame_of_normSq_laplacian_expansion
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic h_lap
  intro t x
  simpa [roughLapRicciInnerInFrame, nablaRicciNormSqInFrame] using hrealized t x

/-- Canonical inverse-metric coefficients in the coordinate frame centered at
`x0`, for the metric at time `t`. -/
noncomputable def coordInv
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) :
    Real -> Realized.InverseMetricComponents M
      (Coordinates.CoordinateIdx (𝕜 := Real) E) :=
  fun t x i j =>
    Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.family.metric t) x0 i j (extChartAt I x0 x)

/-- The canonical coordinate inverse really is the inverse metric in the
centered coordinate basis at the center point. -/
theorem coordInvReal
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) (t : Real) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x0
      (Coordinates.coordinateFrameAt_toBasis (I := I) x0)
      (fun i j => coordInv (I := I) S x0 t x0 i j) := by
  simpa [coordInv] using
    Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) (S.family.metric t) x0

/-- Canonical coordinate rough Laplacian components
`g^{ab} (nabla_a nabla_b Ric)_ij` in the coordinate frame centered at `x0`,
once the coordinate components of `nabla^2 Ric` have been produced. -/
noncomputable def coordRoughRic
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M)
    (nabla2Ric : Real -> M ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) :
    Real -> M ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
  fun t x i j =>
    ∑ a : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ b : Coordinates.CoordinateIdx (𝕜 := Real) E,
        coordInv (I := I) S x0 t x a b * nabla2Ric t x a b i j

/-- Canonical coordinate components of the second covariant derivative of the
Ricci tensor, in the coordinate frame centered at `x0`. -/
noncomputable def coordNab2Ric
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) :
    Real -> M ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
  fun t x d a i j =>
    extDerivFun (I := I)
        (fun y : M =>
          nablaRicComp (I := I) S (Coordinates.coordinateFrameAt (I := I) x0)
            t y a i j)
        x
        (Coordinates.coordinateFrameAt (I := I) x0 d x) -
      (∑ p : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Coordinates.christoffelSymbolInFrame
            (S.family.connection t)
            (Coordinates.coordinateFrameAt (I := I) x0)
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0)
            x d a p *
          nablaRicComp (I := I) S (Coordinates.coordinateFrameAt (I := I) x0)
            t x p i j) -
      (∑ p : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Coordinates.christoffelSymbolInFrame
            (S.family.connection t)
            (Coordinates.coordinateFrameAt (I := I) x0)
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0)
            x d i p *
          nablaRicComp (I := I) S (Coordinates.coordinateFrameAt (I := I) x0)
            t x a p j) -
      (∑ p : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Coordinates.christoffelSymbolInFrame
            (S.family.connection t)
            (Coordinates.coordinateFrameAt (I := I) x0)
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0)
            x d j p *
          nablaRicComp (I := I) S (Coordinates.coordinateFrameAt (I := I) x0)
            t x a i p)

/-- Heat-equation form of Lemma 6.7:
`∂_t |Ric|² = Δ |Ric|² - 2 |∇Ric|² + 4 R_ikjl Ric^{ij} Ric^{kl}`. -/
def RicciNormHeatEquationOn
    {D : Realized.RealTimeInterval}
    (ricciNormSq ricciNormLap nablaRicNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => ricciNormSq s x)
      (ricciNormLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x))
      D.carrier
      (t : Real)

/-- Algebraic assembly of Lemma 6.7 from the time-derivative and Laplacian
component identities. -/
theorem ricciNormHeatEquationOn_of_components
    {D : Realized.RealTimeInterval}
    (ricciNormSq ricciNormLap roughLapInner nablaRicNormSq reaction : Real -> M -> Real)
    (h_dt : RicciNormTimeDerivativeComponentsOn
      (D := D) ricciNormSq roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap roughLapInner nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction := by
  intro t x
  have hvalue :
      ricciNormLap (t : Real) x +
          (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x) =
        2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x := by
    rw [h_lap (t : Real) x]
    ring
  rw [hvalue]
  exact h_dt t x

/-- Strong Ricci-flow solution predicate used by global Hamilton packages.

`IsSolutionOn` records the Ricci-flow equation and the interval-wise metric and
connection smoothness currently used by the local evolution files.  The
Hamilton/global layer also needs the canonical scalar and Ricci quantities
supplied by a smooth Ricci flow to be regular on spacetime and to satisfy the
coordinate-frame evolution and Bochner identities used by Section 6. -/
structure IsSmoothSolutionOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  isSolution : IsSolutionOn (I := I) S
  scalarSTCont : ScalarSTContOn (I := I) (M := M) S
  scalarRegular : CanonicalScalarRegularOn (I := I) (M := M) S
  ricciRegular : CanonicalRicciRegularOn (I := I) (M := M) S
  scalarEvolution : ∀
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real),
      (∀ t : Realized.RealTimeInterval.RegularTime D,
        G.metric (t : Real) = S.family.metric (t : Real)) ->
      (∀ t : Realized.RealTimeInterval.RegularTime D,
        G.connection (t : Real) = S.family.connection (t : Real)) ->
      ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
        HasDerivWithinAt
          (fun s : Real => S.scalar s x)
          (Realized.laplacianAt (I := I) G (t : Real)
              (S.scalar (t : Real)) x +
            2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
              (S.ricci (t : Real) x))
          D.carrier
          (t : Real)
  invEvol :
    ∀ x0 : M,
      InverseMetricEvolutionEquationInFrame
        (I := I) S (coordInv (I := I) S x0)
        (Coordinates.coordinateFrameAt (I := I) x0)
        (Coordinates.coordinateFrameSet (I := I) x0)
  ricciEvol :
    ∀ x0 : M,
      RicciEvolutionEquationInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x0)
        (Coordinates.coordinateFrameAt (I := I) x0)
        (coordRoughRic (I := I) S x0 (coordNab2Ric (I := I) S x0))
  invSymm :
    ∀ x0 : M, ∀ t i j,
      coordInv (I := I) S x0 t x0 i j =
        coordInv (I := I) S x0 t x0 j i
  ricciSymm :
    ∀ x0 : M, ∀ t i j,
      ricciCompInFrame (I := I) S
          (Coordinates.coordinateFrameAt (I := I) x0) t x0 i j =
        ricciCompInFrame (I := I) S
          (Coordinates.coordinateFrameAt (I := I) x0) t x0 j i
  ricciLap :
    ∀ t x,
      ricciNormLap (I := I) S t x =
        2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
              (coordInv (I := I) S x)
              (Coordinates.coordinateFrameAt (I := I) x) t x +
          2 * ricciGradSq (I := I) S t x

namespace IsSmoothSolutionOn

/-- A smooth solution is in particular a Ricci-flow solution in the ordinary
folder-level sense. -/
theorem toIsSolutionOn
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    IsSolutionOn (I := I) S :=
  hS.isSolution

/-- A smooth solution supplies the scalar spacetime-continuity package used by
scalar maximum-principle packages. -/
theorem scalarCont
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    ScalarSTContOn (I := I) (M := M) S :=
  hS.scalarSTCont

/-- A smooth solution supplies the canonical scalar regularity package used by
scalar maximum-principle producers. -/
theorem scalarReg
    {D : Realized.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    CanonicalScalarRegularOn (I := I) (M := M) S :=
  hS.scalarRegular

end IsSmoothSolutionOn

section RicciNormAssembly

variable {Idx : Type*} [Fintype Idx]

/-- Section 6.2 Ricci-norm heat identity for a folder-level solution, reduced
to inverse-metric evolution, Ricci evolution, symmetry, and the Bochner
Laplacian component frontier. -/
theorem ricciNormHeatEquationOn_of_solution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap nablaRicNormSq : Real -> M -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : RicciNormLaplacianComponentsOn
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      nablaRicNormSq) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap nablaRicNormSq
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  exact
    ricciNormHeatEquationOn_of_components
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      nablaRicNormSq
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
      (ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
        (I := I) S Rm04 gInv frame roughLapRic
        h_inv h_ricci hInvSym hRicSym)
      h_lap

/-- Canonical Lemma 6.7 consumer using the exact Ricci-norm Bochner expansion
instead of an already-packaged Laplacian component identity. -/
theorem ricciNormHeatEquationOn_of_solution_canonical_laplacian
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  exact
    ricciNormHeatEquationOn_of_solution
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      h_inv h_ricci hInvSym hRicSym
      (ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
        (I := I) S gInv frame roughLapRic ricciNormLap nablaRic h_lap)

/-- Canonical Lemma 6.7 consumer from the metric-compatible `(0,2)` tensor
Bochner producer, without asking callers for a prepackaged Laplacian
expansion predicate. -/
theorem ricci_heat_mc
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (X : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (roughA : Real -> (x : M) -> Realized.Tensor02At (I := I) x)
    (nablaA : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hmc : forall t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I)
        (S.base.connection t) (S.base.metric t))
    (hframe : forall x i, basis x i = frame i x)
    (hinv : forall t x,
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := M) (S.base.metric t) x
        (basis x) (gInv t x))
    (hfields : forall x, Realized.SmoothBasisFieldsAt (I := I) (basis x) (X x))
    (hlapTrace : forall t x,
      ricciNormLap t x =
        Realized.metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hA : forall t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (S.base.connection t) (A t) (nablaA t))
    (h2 : forall t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 3 (S.base.connection t) (nablaA t) (nabla2A t))
    (hdu : forall t,
      Realized.DuFieldRealizes (I := I)
        (fun y : M => Realized.normSq02 (I := I) (S.base.metric t) y (A t y))
        (du t))
    (hHess : forall t x,
      Realized.HessianRealizesNablaDuAt (I := I) (S.base.connection t) (du t)
        (normSecond t) x)
    (hrough : forall t x,
      Realized.RoughLap0SRealizesMetricTraceInBasis (I := I)
        (basis x) (gInv t x) (s := 2) (roughA t x) (nabla2A t x))
    (hAComp : forall t x i j,
      A t x (Realized.vec2 (I := I) (frame i x) (frame j x)) =
        ricciTwoTensorField (I := I) S t x (frame i x) (frame j x))
    (hroughComp : forall t x i j,
      roughA t x (Realized.vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j)
    (hnablaComp : forall t x a i j,
      nablaA t x (Realized.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    RicciNormHeatEquationOn
      (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  let G : Realized.RealizedMetricFamily (I := I) (M := M) Real :=
    { metric := S.base.metric
      connection := S.base.connection
      metricCompatible := hmc }
  exact
    ricciNormHeatEquationOn_of_solution_canonical_laplacian
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
      h_inv h_ricci hInvSym hRicSym
      (Realized.ricci_lap_mc (I := I) (Time := Real) G
        ricciNormLap roughLapRic (ricciTwoTensorField (I := I) S)
        gInv frame nablaRic basis X A roughA nablaA nabla2A du normSecond
        hframe hinv hfields hlapTrace hA h2 hdu hHess hrough
        hAComp hroughComp hnablaComp)

end RicciNormAssembly

end RicciFlow
end RicciFlower
