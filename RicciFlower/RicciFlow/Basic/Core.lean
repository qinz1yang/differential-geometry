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
  /-- Spacetime continuity of scalar curvature supplied by the smooth
  metric-family regularity in the short-time existence package. -/
  scalarCont : ∀ p : Real × M,
    ContinuousAt (fun q : Real × M => S.scalar q.1 q.2) p
  /-- Within-time differentiability of scalar curvature on time sets contained
  in the solution carrier, supplied by the smooth metric-family regularity in
  the short-time existence package. -/
  scalarTime :
    ∀ {K : Set Real} {t : Real}, t ∈ K -> K ⊆ D.carrier -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => S.scalar s x) K t
  /-- Total-space continuity of the canonical Ricci tensor family. -/
  ricciCont :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => S.ricci t x)
  /-- Total-space continuity of the canonical lowered Riemann tensor family. -/
  rm04Cont :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.carrier
      (fun t x => S.base.rm04 t x)
  /-- Total-space continuity of the canonical `∇ Ric` family. -/
  nablaRicCont :
    Realized.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 3 D.carrier
      (fun t x =>
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (S.family.connection t) (S.ricci t) x)
  /-- Fixed-time spatial differentiability of the canonical Ricci norm. -/
  ricciNormSpace :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) x
  /-- Fixed-time smoothness of the canonical Ricci-norm gradient field. -/
  ricciNormGrad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x
  /-- Scalar curvature heat equation supplied by the smooth Ricci-flow
  solution package. -/
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
    · intro Idx _ frame u hframe i j
      have hOld :
          ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
            (fun p : Real × M =>
              (S.family.metric p.1).inner p.2 (frame i p.2) (frame j p.2))
            (D.carrier ×ˢ u) :=
        hS.smoothMetric.frameCompSmooth frame hframe i j
      have hmapSmooth :
          ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ⊤
            (fun p : Real × M => (p.1 + τ, p.2)) := by
        exact (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
      have hmaps :
          Set.MapsTo (fun p : Real × M => (p.1 + τ, p.2))
            ((D.timeShift τ).carrier ×ˢ u) (D.carrier ×ˢ u) := by
        intro p hp
        exact ⟨hp.1, hp.2⟩
      have hcomp :
          ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
            (fun p : Real × M =>
              (S.family.metric (p.1 + τ)).inner p.2
                (frame i p.2) (frame j p.2))
            ((D.timeShift τ).carrier ×ˢ u) := by
        simpa [Function.comp_def] using hOld.comp hmapSmooth.contMDiffOn hmaps
      simpa [SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift]
        using hcomp
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
  scalarCont := by
    intro p
    have hOld := hS.scalarCont (p.1 + τ, p.2)
    have htime : ContinuousAt (fun q : Real × M => q.1 + τ) p :=
      continuousAt_fst.add continuousAt_const
    have hmap : ContinuousAt (fun q : Real × M => (q.1 + τ, q.2)) p :=
      htime.prodMk continuousAt_snd
    have hcomp :
        ContinuousAt
          (fun q : Real × M => S.scalar (q.1 + τ) q.2) p :=
      ContinuousAt.comp
        (x := p)
        (f := fun q : Real × M => (q.1 + τ, q.2))
        (g := fun q : Real × M => S.scalar q.1 q.2)
        hOld hmap
    simpa [Function.comp_def] using hcomp
  scalarTime := by
    intro K t ht hK x
    let shift : Real -> Real := fun s => s + τ
    have ht' : shift t ∈ shift '' K := ⟨t, ht, rfl⟩
    have hK' : shift '' K ⊆ D.carrier := by
      intro r hr
      rcases hr with ⟨s, hs, rfl⟩
      exact hK hs
    have hOld := hS.scalarTime (K := shift '' K) (t := shift t) ht' hK' x
    have hshift : DifferentiableWithinAt Real shift K t := by
      simpa [shift] using
        ((differentiableWithinAt_id' (𝕜 := Real) (s := K) (x := t)).add_const τ)
    have hmaps : Set.MapsTo shift K (shift '' K) := by
      intro s hs
      exact ⟨s, hs, rfl⟩
    have hcomp := hOld.comp t hshift hmaps
    simpa [shift, Function.comp_def] using hcomp
  ricciCont := by
    have hmaps :
        Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => s + τ) :=
      continuous_id.add continuous_const
    have hcont :=
      Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.ricciCont htime hmaps
    simpa [SolutionOn.ricci, SolutionOn.timeShift, SolutionFamily.timeShift] using hcont
  rm04Cont := by
    have hmaps :
        Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => s + τ) :=
      continuous_id.add continuous_const
    have hcont :=
      Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.rm04Cont htime hmaps
    simpa [SolutionOn.timeShift, SolutionFamily.timeShift] using hcont
  nablaRicCont := by
    have hmaps :
        Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => s + τ) :=
      continuous_id.add continuous_const
    have hcont :=
      Realized.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.nablaRicCont htime hmaps
    simpa [SolutionOn.family, SolutionOn.ricci, SolutionOn.timeShift,
      SolutionFamily.timeShift] using hcont
  ricciNormSpace := by
    intro t ht x
    have h := hS.ricciNormSpace (t + τ) ht x
    simpa [ricciNorm, SolutionOn.family, SolutionOn.ricci, SolutionOn.timeShift,
      SolutionFamily.timeShift] using h
  ricciNormGrad := by
    intro t ht x
    have h := hS.ricciNormGrad (t + τ) ht x
    simpa [ricciNorm, SolutionOn.family, SolutionOn.ricci, SolutionOn.timeShift,
      SolutionFamily.timeShift] using h
  scalarEvolution := by
    intro G hmetric hconnection t x
    let G' : Realized.RealizedMetricFamily (I := I) (M := M) Real :=
      { metric := fun r : Real => G.metric (r - τ)
        connection := fun r : Real => G.connection (r - τ)
        metricCompatible := fun r => by
          simpa using G.metricCompatible (r - τ) }
    have hmetric' : ∀ r : Realized.RealTimeInterval.RegularTime D,
        G'.metric (r : Real) = S.family.metric (r : Real) := by
      intro r
      let rs : Realized.RealTimeInterval.RegularTime (D.timeShift τ) :=
        ⟨(r : Real) - τ, by
          rw [Realized.RealTimeInterval.timeShift_regular]
          change (r : Real) - τ + τ ∈ D.regular
          rw [sub_add_cancel]
          exact r.2⟩
      have h := hmetric rs
      simpa [G', rs, SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift,
        sub_add_cancel] using h
    have hconnection' : ∀ r : Realized.RealTimeInterval.RegularTime D,
        G'.connection (r : Real) = S.family.connection (r : Real) := by
      intro r
      let rs : Realized.RealTimeInterval.RegularTime (D.timeShift τ) :=
        ⟨(r : Real) - τ, by
          rw [Realized.RealTimeInterval.timeShift_regular]
          change (r : Real) - τ + τ ∈ D.regular
          rw [sub_add_cancel]
          exact r.2⟩
      have h := hconnection rs
      simpa [G', rs, SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift,
        SolutionFamily.connection, sub_add_cancel] using h
    let t' : Realized.RealTimeInterval.RegularTime D := ⟨(t : Real) + τ, t.2⟩
    have hOld := hS.scalarEvolution G' hmetric' hconnection' t' x
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
    simpa [G', t', Realized.laplacianAt, SolutionOn.family, SolutionOn.ricci,
      SolutionOn.timeShift, SolutionFamily.timeShift, SolutionFamily.connection,
      Function.comp_def, sub_eq_add_neg, add_assoc] using hcomp

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

/-- At a regular time the metric evolution equation is an ordinary time
derivative.  The interval-local `HasDerivWithinAt` form remains the canonical
PDE interface, but `D.regular_mem_nhds` prevents endpoint semantics here. -/
theorem metricDerivAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (X Y : TangentSpace I x) :
    HasDerivAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricciAt (t : Real) x (Realized.vec2 X Y))
      (t : Real) :=
  (metric_derivWithin_eq_neg_two_ricci
    (I := I) S hS t x X Y).hasDerivAt (D.regular_mem_nhds t.2)

/-- At a regular time the scalar evolution equation is an ordinary time
derivative.  This is just the `HasDerivAt` projection of the smooth solution
package's interval-local scalar heat equation. -/
theorem scalarEvolAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hmetric : ∀ t : Realized.RealTimeInterval.RegularTime D,
      G.metric (t : Real) = S.family.metric (t : Real))
    (hconnection : ∀ t : Realized.RealTimeInterval.RegularTime D,
      G.connection (t : Real) = S.family.connection (t : Real))
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) :
    HasDerivAt
      (fun s : Real => S.scalar s x)
      (Realized.laplacianAt (I := I) G (t : Real)
          (S.scalar (t : Real)) x +
        2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
          (S.ricci (t : Real) x))
      (t : Real) :=
  (hS.scalarEvolution G hmetric hconnection t x).hasDerivAt
    (D.regular_mem_nhds t.2)

end RicciFlow
end RicciFlower
