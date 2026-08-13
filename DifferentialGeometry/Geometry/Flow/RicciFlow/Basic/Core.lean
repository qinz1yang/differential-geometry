import DifferentialGeometry.Geometry.Flow.RicciFlow.Realized.RicciFlow
import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Flow.RicciFlow.Realized.Bochner
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureTensor
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureProducers
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricCoord
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Model
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Christoffel
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

abbrev RicciSectionFamily : Type _ :=
  Real -> DifferentialGeometry.Geometry.Curvature.Tensor02Section (I := I) (M := M)

abbrev RicciAtFamily : Type _ :=
  Real -> (x : M) -> DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x

namespace RicciAtFamily

def toTensorField (Ric : RicciAtFamily (I := I) (M := M)) :
    DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real :=
  fun t x X Y => Ric t x (DifferentialGeometry.Geometry.Curvature.vec2 X Y)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp] theorem toTensorField_apply
    (Ric : RicciAtFamily (I := I) (M := M))
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    toTensorField (I := I) Ric t x X Y =
      Ric t x (DifferentialGeometry.Geometry.Curvature.vec2 X Y) := by
  rfl

end RicciAtFamily

namespace RicciSectionFamily

def toTensorField (Ric : RicciSectionFamily (I := I) (M := M)) :
    DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real :=
  fun t x X Y => Ric t x (DifferentialGeometry.Geometry.Curvature.vec2 X Y)

omit [IsManifold I 1 M] in
@[simp] theorem toTensorField_apply
    (Ric : RicciSectionFamily (I := I) (M := M))
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    toTensorField (I := I) Ric t x X Y =
      Ric t x (DifferentialGeometry.Geometry.Curvature.vec2 X Y) := by
  rfl

end RicciSectionFamily

variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

structure SolutionFamily where
  metric : Real -> SmoothRiemannianMetric I M

namespace SolutionFamily

def timeShift
    (G : SolutionFamily (I := I) (M := M)) (τ : Real) :
    SolutionFamily (I := I) (M := M) where
  metric := fun s => G.metric (s + τ)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem timeShift_metric
    (G : SolutionFamily (I := I) (M := M)) (τ s : Real) :
    (G.timeShift τ).metric s = G.metric (s + τ) := by
  rfl


noncomputable def connection
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  fun t => DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
             (G.metric t)


noncomputable def rm13At
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> (x : M) -> DifferentialGeometry.Geometry.Curvature.Tensor13At (I := I) (M := M) x :=
  fun t x => metricRm13At (I := I) (M := M) (G.metric t) x


noncomputable def rm04At
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> (x : M) -> DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x :=
  fun t x => metricRm04At (I := I) (M := M) (G.metric t) x


noncomputable def ricciAt
    (G : SolutionFamily (I := I) (M := M)) :
    RicciAtFamily (I := I) (M := M) :=
  fun t x => metricRicciAt (I := I) (M := M) (G.metric t) x


noncomputable def scalar
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> M -> Real :=
  fun t x => metricScalarAt (I := I) (M := M) (G.metric t) x

noncomputable def rm13
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M) :=
  fun t => metricRm13 (I := I) (M := M) (G.metric t)


noncomputable def rm04
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M) :=
  fun t => metricRm04 (I := I) (M := M) (G.metric t)

noncomputable def ricci
    (G : SolutionFamily (I := I) (M := M)) :
    RicciSectionFamily (I := I) (M := M) :=
  fun t => metricRicci (I := I) (M := M) (G.metric t)

omit [SigmaCompactSpace M] in
@[simp] theorem ricci_apply
    (G : SolutionFamily (I := I) (M := M))
    (t : Real) (x : M) :
    G.ricci t x = G.ricciAt t x := by
  simp [ricci, ricciAt]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem scalar_apply
    (G : SolutionFamily (I := I) (M := M))
    (t : Real) (x : M) :
    G.scalar t x =
      DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (G.metric t)
        (G.ricciAt t x) := by
  simp [scalar, metricScalarAt, DifferentialGeometry.Geometry.Curvature.metricScalarAt, ricciAt,
    metricRicciAt]


def MetricCompatibleOn
    (G : SolutionFamily (I := I) (M := M))
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) : Prop :=
  forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D,
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible_gen (I := I)
      (G.connection (t : Real)) (G.metric (t : Real))

end SolutionFamily

structure SolutionOn (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) where
  base : SolutionFamily (I := I) (M := M)

namespace SolutionOn

def timeShift {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ : Real) :
    SolutionOn (I := I) (M := M) (D.timeShift τ) where
  base := S.base.timeShift τ

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem timeShift_base {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ : Real) :
    (S.timeShift τ).base = S.base.timeShift τ := by
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem timeShift_base_metric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).base.metric s = S.base.metric (s + τ) := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCompatible {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.base.MetricCompatibleOn D := by
  intro t
  exact DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
    (I := I) (S.base.metric (t : Real))

def family {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D where
  metric := S.base.metric
  connection := S.base.connection
  metricCompatible := S.metricCompatible

def ricci {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    RicciSectionFamily (I := I) (M := M) :=
  S.base.ricci


def ricciAt {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    RicciAtFamily (I := I) (M := M) :=
  S.base.ricciAt


def scalar {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  S.base.scalar

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem family_metric {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.family.metric = S.base.metric := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem family_connection {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.family.connection = S.base.connection := by
  rfl

omit [SigmaCompactSpace M] in
@[simp] theorem ricci_eq {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.ricci = S.base.ricci := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciAt_eq {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.ricciAt = S.base.ricciAt := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem scalar_eq {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.scalar = S.base.scalar := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem scalar_eq_metricTrace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    S.scalar t x =
      DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (S.family.metric t)
        (S.ricciAt t x) := by
  simp [scalar, SolutionFamily.scalar_apply]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem timeShift_family_metric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).family.metric s = S.family.metric (s + τ) := by
  rfl

omit [SigmaCompactSpace M] in
@[simp] theorem timeShift_ricci {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).ricci s = S.ricci (s + τ) := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem timeShift_ricciAt {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).ricciAt s = S.ricciAt (s + τ) := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem timeShift_scalar {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).scalar s = S.scalar (s + τ) := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem timeShift_initial_metric {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (τ : Real) :
    (S.timeShift τ).family.metric ((D.timeShift τ).initial) =
      S.family.metric D.initial := by
  simp [DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift, sub_add_cancel]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem timeShift_self_initial_metric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    (S.timeShift D.initial).family.metric 0 = S.family.metric D.initial := by
  simp


def toRealizedCandidate {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    DifferentialGeometry.PDE.RicciFlow.RealizedRicciFlowCandidateOn (I := I) (M := M) D where
  family := S.family
  ricci := RicciAtFamily.toTensorField (I := I) S.ricciAt

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem toRealizedCandidate_family
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.toRealizedCandidate.family = S.family := by
  rfl

end SolutionOn

def MetricVariationEquationOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationOnRaw (I := I) S.family
    (RicciAtFamily.toTensorField (I := I) S.ricciAt)


def ricciNorm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)


def ricciGradSq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    normSq0S (I := I) (S.family.metric t) x 3
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x)

def flowG
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real where
  metric := S.base.metric
  connection := S.base.connection
  metricCompatible := by
    intro t
    simpa [SolutionFamily.connection] using
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric t))


def ricciNormLap
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
      (ricciNorm (I := I) S t) x

def ricciPair04 {x : M}
    (Ric : DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x) :
    DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x :=
  (Bundle.continuousMultilinearMap.product_fun
      (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
      (s := 2) (q := 2) (x := x) Ric Ric).domDomCongr
    (Equiv.swap (1 : Fin 4) (2 : Fin 4))

def ricciReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x =>
    -inner0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)
      (ricciPair04 (I := I) (S.ricciAt t x))

structure IsSolutionOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  smoothMetric : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn (I := I) (M := M) D
    S.family.metric
  smoothConnection : DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn (I := I)
    (M := M) S.family
  equation : MetricVariationEquationOn (I := I) S
  scalarCont : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
    (D.carrier ×ˢ (Set.univ : Set M))
  scalarTime :
    ∀ {K : Set Real} {t : Real}, t ∈ K -> K ⊆ D.carrier -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => S.scalar s x) K t
  ricciCont :
    DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      D.carrier
      (fun t x => S.ricci t x)
  rm04Cont :
    DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      D.carrier
      (fun t x => S.base.rm04 t x)
  ricciNormSpace :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) x
  ricciNormGrad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x

namespace IsSolutionOn


omit [SigmaCompactSpace M] in
theorem leviCivita
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (_hS : IsSolutionOn (I := I) S) :
    DifferentialGeometry.Geometry.Connection.IsLeviCivitaFamilyOn (I := I) S.family := by
  constructor
  · intro t
    exact S.metricCompatible t
  · intro t
    exact DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isTorsionFree
      (I := I) (S.base.metric (t : Real))

end IsSolutionOn

structure ScalarSTContOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  scalar_continuousOn : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
    (D.carrier ×ˢ (Set.univ : Set M))

namespace ScalarSTContOn

omit [SigmaCompactSpace M] [T2Space M] in
theorem continuous_subtype
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : ScalarSTContOn (I := I) (M := M) S) :
    Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
      S.scalar q.1.1 q.2) := by
  have hmap : Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
      ((q.1.1 : Real), q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmem :
      ∀ q : {t : Real // t ∈ D.carrier} × M,
        ((q.1.1 : Real), q.2) ∈ D.carrier ×ˢ (Set.univ : Set M) := by
    intro q
    exact ⟨q.1.2, trivial⟩
  have hcomp := hreg.scalar_continuousOn.comp_continuous hmap hmem
  simpa [Function.comp_def] using hcomp

end ScalarSTContOn

structure CanonicalScalarRegularOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  scalar_continuousOn : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
    (D.carrier ×ˢ (Set.univ : Set M))
  scalar_time_within :
    ∀ {K : Set Real} {t : Real}, t ∈ K -> K ⊆ D.carrier -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => S.scalar s x) K t
  scalar_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar t) x
  scalar_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (S.scalar t) y) x
  scalar_mul_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% ((S.scalar t) • fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (S.scalar t) y)) x
  scalar_sq_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.scalar t y ^ 2) x
  scalar_sq_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2) y) x
  scalar_sq_div_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.scalar t y ^ 2 / 3) x
  scalar_sq_div_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2 / 3) y) x
  scalar_grad_sub_const :
    ∀ t : Real, t ∈ D.carrier -> ∀ c : Real, ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z - c) y) x
  scalar_grad_const_mul_sub_const :
    ∀ t : Real, t ∈ D.carrier -> ∀ a c : Real, ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => a * (S.scalar t z - c)) y) x

namespace CanonicalScalarRegularOn


omit [SigmaCompactSpace M] [T2Space M] in
theorem toScalarSTCont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalScalarRegularOn (I := I) (M := M) S) :
    ScalarSTContOn (I := I) (M := M) S where
  scalar_continuousOn := hreg.scalar_continuousOn

end CanonicalScalarRegularOn

structure CanonicalRicciRegularOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  ricci_cont :
    DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      D.carrier
      (fun t x => S.ricci t x)
  rm04_cont :
    DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      D.carrier
      (fun t x => S.base.rm04 t x)
  ricci_norm_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) x
  ricci_norm_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x

namespace CanonicalRicciRegularOn


omit [SigmaCompactSpace M] in
theorem ricciTensorFamilyContinuousOnSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalRicciRegularOn (I := I) (M := M) S) :
    DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      D.carrier
      (fun t x => S.ricci t x) :=
  hreg.ricci_cont

omit [SigmaCompactSpace M] in
theorem rm04FamilyContinuousOnSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalRicciRegularOn (I := I) (M := M) S) :
    DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      D.carrier
      (fun t x => S.base.rm04 t x) :=
  hreg.rm04_cont

end CanonicalRicciRegularOn

namespace SolutionOn

omit [SigmaCompactSpace M] in
theorem scalar_continuousOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (hreg : ScalarSTContOn (I := I) (M := M) S)
    (T : Real)
    (hT : Set.Icc 0 T ⊆ D.carrier) :
    ContinuousOn (fun p : Real × M => S.scalar p.1 p.2)
      ((Set.Icc 0 T).prod (Set.univ : Set M)) := by
  exact hreg.scalar_continuousOn.mono (Set.prod_mono hT (Set.Subset.rfl))

end SolutionOn

omit [SigmaCompactSpace M] in
theorem isSolutionOn_timeShift
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) (τ : Real) :
    IsSolutionOn (I := I) (S.timeShift τ) where
  smoothMetric := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x X Y
      have hOld := hS.smoothMetric.coeff x X Y
      have haff : ContDiff Real ∞ (fun s : Real => s + τ) :=
        contDiff_id.add contDiff_const
      have hmaps :
          Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).regular D.regular := by
        intro s hs
        exact hs
      have hcomp :
          ContDiffOn Real ∞
            (fun s : Real => (S.family.metric (s + τ)).inner x X Y)
            (D.timeShift τ).regular := by
        simpa [Function.comp_def] using hOld.comp haff.contDiffOn hmaps
      simpa [SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift] using hcomp
    · intro x X Y
      have hOld := hS.smoothMetric.coeff_cont x X Y
      have htime : Continuous (fun s : Real => s + τ) :=
        (continuous_id.add continuous_const)
      have hmaps :
          Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
        intro s hs
        exact hs
      have hcomp :
          ContinuousOn
            (fun s : Real => (S.family.metric (s + τ)).inner x X Y)
            (D.timeShift τ).carrier := by
        simpa [Function.comp_def] using hOld.comp htime.continuousOn hmaps
      simpa [SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift] using hcomp
    · have hmaps :
          Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
        intro s hs
        exact hs
      have htime : Continuous (fun s : Real => s + τ) :=
        (continuous_id.add continuous_const)
      have hcont :=
        DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet.comp_time (I := I)
          (M := M)
          hS.smoothMetric.metricTensor_cont htime hmaps
      simpa [SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift]
        using hcont
    · intro Idx _ frame u hframe i j
      have hOld :
          ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
            (fun p : Real × M =>
              (S.family.metric p.1).inner p.2 (frame i p.2) (frame j p.2))
            (D.regular ×ˢ u) :=
        hS.smoothMetric.frameCompSmooth frame hframe i j
      have hmapSmooth :
          ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
            (fun p : Real × M => (p.1 + τ, p.2)) := by
        exact (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
      have hmaps :
          Set.MapsTo (fun p : Real × M => (p.1 + τ, p.2))
            ((D.timeShift τ).regular ×ˢ u) (D.regular ×ˢ u) := by
        intro p hp
        exact ⟨hp.1, hp.2⟩
      have hcomp :
          ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
            (fun p : Real × M =>
              (S.family.metric (p.1 + τ)).inner p.2
                (frame i p.2) (frame j p.2))
            ((D.timeShift τ).regular ×ˢ u) := by
        simpa [Function.comp_def] using hOld.comp hmapSmooth.contMDiffOn hmaps
      simpa [SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift]
        using hcomp
  smoothConnection := by
    intro t
    let t' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D :=
      ⟨(t : Real) + τ, t.2⟩
    have hOld := hS.smoothConnection t'
    simpa [t', SolutionOn.family, SolutionOn.timeShift, SolutionFamily.timeShift,
      DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt,
        SolutionFamily.connection] using hOld
  equation := by
    intro t x X Y
    let t' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D :=
      ⟨(t : Real) + τ, t.2⟩
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
    have hmap : Continuous (fun q : Real × M => (q.1 + τ, q.2)) :=
      (continuous_fst.add continuous_const).prodMk continuous_snd
    have hmapOn : ContinuousOn (fun q : Real × M => (q.1 + τ, q.2))
        ((D.timeShift τ).carrier ×ˢ (Set.univ : Set M)) :=
      hmap.continuousOn
    have hmaps : Set.MapsTo (fun q : Real × M => (q.1 + τ, q.2))
        ((D.timeShift τ).carrier ×ˢ (Set.univ : Set M))
        (D.carrier ×ˢ (Set.univ : Set M)) := by
      intro q hq
      exact ⟨hq.1, trivial⟩
    have hcomp := hS.scalarCont.comp hmapOn hmaps
    simpa [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.timeShift,
      SolutionFamily.timeShift, Function.comp_def] using hcomp
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
      DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet.comp_time (I := I)
        (M := M)
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
      DifferentialGeometry.Geometry.Curvature.Tensor0SFamilyContinuousOnSet.comp_time (I := I)
        (M := M)
        hS.rm04Cont htime hmaps
    simpa [SolutionOn.timeShift, SolutionFamily.timeShift] using hcont
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

omit [SigmaCompactSpace M] in
theorem isRealizedRicciFlowSolutionOn_of_isSolutionOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) :
    DifferentialGeometry.PDE.RicciFlow.IsRealizedRicciFlowSolutionOn (I := I)
      S.toRealizedCandidate := by
  exact
    { smoothMetric := hS.smoothMetric
      smoothConnection := hS.smoothConnection
      leviCivita := hS.leviCivita
      equation := hS.equation }


omit [SigmaCompactSpace M] in
theorem metric_derivWithin_eq_neg_two_ricci
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricciAt (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec2 X Y))
      D.carrier
      (t : Real) := by
  simpa [MetricVariationEquationOn, RicciAtFamily.toTensorField] using
    hS.equation t x X Y

omit [SigmaCompactSpace M] in
theorem metricDerivAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (X Y : TangentSpace I x) :
    HasDerivAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricciAt (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec2 X Y))
      (t : Real) :=
  (metric_derivWithin_eq_neg_two_ricci
    (I := I) S hS t x X Y).hasDerivAt (D.regular_mem_nhds t.2)

end DifferentialGeometry.PDE.RicciFlow
