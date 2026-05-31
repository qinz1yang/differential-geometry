import RicciFlower.Analysis.Time
import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Metric.Basic
import RicciFlower.Realized.TimeInterval
import RicciFlower.Tensor.RSTensor.MetricCompatibility
import RicciFlower.Tensor.RSTensor.QuadraticBounds
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# RicciFlower Realized Metric Families

The realized V2 core stores the geometric objects: a time-indexed Riemannian
metric, a time-indexed mathlib covariant derivative on the tangent bundle, and
the compatibility proof saying the connection is metric-compatible with the
metric at each time. Smoothness and Ricci-flow evolution remain separate
predicate interfaces.
-/

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

/-- A realized time-dependent metric and connection.

It does not assert that the connection is torsion-free, that the family is
smooth in time, or that it solves Ricci flow.  It does assert the basic
geometric compatibility between the stored metric and connection. -/
structure RealizedMetricFamily (Time : Type*) where
  metric : Time -> SmoothRiemannianMetric I M
  connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : Time,
    RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t)

/-- A realized metric family over a concrete real time interval.

The functions are defined on all real times, but later predicates only require
the Ricci-flow data on the interval's carrier or regular subdomain. -/
structure RealizedMetricFamilyOn (D : RealTimeInterval) where
  metric : Real -> SmoothRiemannianMetric I M
  connection : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : RealTimeInterval.FlowTime D,
    RicciFlower.Connection.IsMetricCompatible (I := I)
      (connection (t : Real)) (metric (t : Real))

namespace RealizedMetricFamily

@[simp] theorem metric_mk
    (metric : Time -> SmoothRiemannianMetric I M)
    (connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricCompatible : forall t : Time,
      RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t))
    (t : Time) :
    (RealizedMetricFamily.mk (I := I) (M := M) metric connection
      metricCompatible).metric t = metric t := by
  rfl

@[simp] theorem connection_mk
    (metric : Time -> SmoothRiemannianMetric I M)
    (connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricCompatible : forall t : Time,
      RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t))
    (t : Time) :
    (RealizedMetricFamily.mk (I := I) (M := M) metric connection
      metricCompatible).connection t =
      connection t := by
  rfl

@[simp] theorem metricCompatible_mk
    (metric : Time -> SmoothRiemannianMetric I M)
    (connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricCompatible : forall t : Time,
      RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t))
    (t : Time) :
    (RealizedMetricFamily.mk (I := I) (M := M) metric connection
      metricCompatible).metricCompatible t = metricCompatible t := by
  rfl

end RealizedMetricFamily

namespace RealizedMetricFamilyOn

/-- View an interval family as a family indexed by its flow-time subtype. -/
def toFlowTimeFamily
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) :
    RealizedMetricFamily (I := I) (M := M) (RealTimeInterval.FlowTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible t

/-- View an interval family as a family indexed by regular times. -/
def toRegularTimeFamily
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) :
    RealizedMetricFamily (I := I) (M := M) (RealTimeInterval.RegularTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible (RealTimeInterval.regularToFlow t)

/-- Metric at a flow time. -/
def metricAt
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    SmoothRiemannianMetric I M :=
  G.metric (t : Real)

/-- Connection at a flow time. -/
def connectionAt
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  G.connection (t : Real)

@[simp] theorem metricAt_eq
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.metricAt t = G.metric (t : Real) := by
  rfl

@[simp] theorem connectionAt_eq
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.connectionAt t = G.connection (t : Real) := by
  rfl

/-- Metric compatibility of the connection and metric at a flow time. -/
theorem metricCompatibleAt
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    RicciFlower.Connection.IsMetricCompatible (I := I) (G.connectionAt t) (G.metricAt t) := by
  exact G.metricCompatible t

/-- Metric compatibility of the connection and metric at a regular time. -/
theorem metricCompatibleAt_regular
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) :
    RicciFlower.Connection.IsMetricCompatible (I := I)
      (G.connection (t : Real)) (G.metric (t : Real)) := by
  exact G.metricCompatible (RealTimeInterval.regularToFlow t)

end RealizedMetricFamilyOn

section FamilyCompatibility

/-- Metric compatibility for an interval metric family. -/
def IsMetricCompatibleFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D,
    RicciFlower.Connection.IsMetricCompatible (I := I) (G.connectionAt t) (G.metricAt t)

/-- The metric-family field supplies interval metric compatibility. -/
theorem isMetricCompatibleFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) :
    IsMetricCompatibleFamilyOn (I := I) G :=
  fun t => G.metricCompatibleAt t

/-- Family metric compatibility at a flow time. -/
theorem metric_compatible_family_apply
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hmc : IsMetricCompatibleFamilyOn (I := I) G)
    (t : RealTimeInterval.FlowTime D)
    {x : M}
    (X Y Z : (p : M) -> TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mfderiv I 𝓘(Real, Real)
        (fun y : M => (G.metricAt t).inner y (Y y) (Z y)) x (X x) =
      (G.metricAt t).inner x ((G.connectionAt t) Y x (X x)) (Z x) +
        (G.metricAt t).inner x (Y x) ((G.connectionAt t) Z x (X x)) :=
  RicciFlower.Connection.metric_compatible_apply (I := I) (hmc t) X Y Z hX hY hZ

end FamilyCompatibility

section TimeSmoothness

variable {A Time : Type*} [CommRing A] [Algebra Real A]

/-- Pointwise time-regularity of the metric coefficients.

This is intentionally a predicate, not a field of `RealizedMetricFamily`. -/
def MetricFamilySmoothInTime
    (td : TimeDerivativeData Real A Time) [TimeRegularFam td]
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall (x : M) (X Y : TangentSpace I x),
    td.isSmoothFam (fun t : Time => (G.metric t).inner x X Y)

/-- Extract a metric coefficient's time smoothness from the predicate interface. -/
theorem metric_smooth_coeff_of_metricFamilySmoothInTime
    (td : TimeDerivativeData Real A Time) [TimeRegularFam td]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : MetricFamilySmoothInTime td G)
    (x : M) (X Y : TangentSpace I x) :
    td.isSmoothFam (fun t : Time => (G.metric t).inner x X Y) :=
  hG x X Y

/-- The pointwise metric time derivative evaluated on fixed tangent vectors. -/
noncomputable def metricTimeDerivative
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (x : M) (X Y : TangentSpace I x) : Real :=
  td.dt_apply (fun s : Time => (G.metric s).inner x X Y) t

@[simp] theorem metricTimeDerivative_eq
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td G t x X Y =
      td.dt_apply (fun s : Time => (G.metric s).inner x X Y) t := by
  rfl

end TimeSmoothness

section IntervalSmoothness

variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Joint total-space continuity of a real-time `(0,s)` tensor family over a
set of times.

This is the reusable time-dependent tensor continuity shape used by compact
time-slab arguments.  It records continuity of `(t, x) |-> A t x` as a section
of the tensor bundle over the product `{t // t in K} x M`. -/
def Tensor0SFamilyContinuousOnSet
    (s : Nat) (K : Set Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Prop :=
  Continuous (fun q : {t : Real // t ∈ K} × M =>
    TotalSpace.mk' (Tensor0SModel s Real E)
      (E := fun x : M => Tensor0SSpace s I x) q.2 (A q.1.1 q.2))

/-- A real-time family of smooth covariant two-tensor fields.  Each fixed time
is a bundled smooth section; time regularity is recorded by separate predicates
such as `SmoothTwoTensorFamilyOnSet`. -/
abbrev SmoothTwoTensorFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 2

/-- Regularity package for a real-time family of smooth two-tensor fields on a
time set.  The fields are spatially smooth by type, have smooth fixed-vector
time coefficients, and are jointly continuous as a tensor section over
`K × M`. -/
structure SmoothTwoTensorFamilyOnSet
    (K : Set Real) (A : SmoothTwoTensorFamily (I := I) (M := M)) : Prop where
  coeff :
    ∀ (x : M) (X Y : TangentSpace I x),
      ContDiffOn Real ⊤
        (fun t : Real => A t x (fun i : Fin 2 => if i = 0 then X else Y)) K
  tensor_cont :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => A t x)

namespace Tensor0SFamilyContinuousOnSet

/-- Restrict a time-dependent tensor continuity statement to a smaller time set. -/
theorem mono
    {s : Nat} {K L : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s L A)
    (hKL : K ⊆ L) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A := by
  unfold Tensor0SFamilyContinuousOnSet at hA ⊢
  let incl : {t : Real // t ∈ K} × M -> {t : Real // t ∈ L} × M :=
    fun q => (⟨q.1.1, hKL q.1.2⟩, q.2)
  have htime : Continuous (fun q : {t : Real // t ∈ K} × M =>
      (⟨q.1.1, hKL q.1.2⟩ : {t : Real // t ∈ L})) := by
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _)
  have hincl : Continuous incl := by
    dsimp [incl]
    exact htime.prodMk continuous_snd
  exact hA.comp hincl

/-- Pull time-dependent tensor continuity back along a continuous time map. -/
theorem comp_time
    {s : Nat} {K L : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s L A)
    {φ : Real -> Real} (hφ : Continuous φ) (hmaps : Set.MapsTo φ K L) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => A (φ t) x) := by
  unfold Tensor0SFamilyContinuousOnSet at hA ⊢
  let pull : {t : Real // t ∈ K} × M -> {t : Real // t ∈ L} × M :=
    fun q => (⟨φ q.1.1, hmaps q.1.2⟩, q.2)
  have htime : Continuous (fun q : {t : Real // t ∈ K} × M =>
      (⟨φ q.1.1, hmaps q.1.2⟩ : {t : Real // t ∈ L})) := by
    exact ((hφ.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _)
  have hpull : Continuous pull := by
    dsimp [pull]
    exact htime.prodMk continuous_snd
  exact hA.comp hpull

/-- Constant scalar multiplication preserves time-dependent tensor continuity. -/
theorem const_smul
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (c : Real)
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => c • A t x) := by
  unfold Tensor0SFamilyContinuousOnSet at hA ⊢
  rw [continuous_iff_continuousAt] at hA ⊢
  intro q
  have hAq := hA q
  rw [FiberBundle.continuousAt_totalSpace] at hAq ⊢
  refine ⟨hAq.1, ?_⟩
  simpa [map_smul] using (hAq.2.const_smul c)

/-- Addition preserves time-dependent tensor continuity. -/
theorem add
    {s : Nat} {K : Set Real}
    {A B : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (hB : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K B) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => A t x + B t x) := by
  unfold Tensor0SFamilyContinuousOnSet at hA hB ⊢
  rw [continuous_iff_continuousAt] at hA hB ⊢
  intro q
  have hAq := hA q
  have hBq := hB q
  rw [FiberBundle.continuousAt_totalSpace] at hAq hBq ⊢
  refine ⟨hAq.1, ?_⟩
  simpa [map_add] using hAq.2.add hBq.2

/-- Multiplication by a jointly continuous scalar family preserves
time-dependent tensor continuity. -/
theorem smul
    {s : Nat} {K : Set Real}
    {f : Real -> M -> Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hf : Continuous (fun q : {t : Real // t ∈ K} × M => f q.1.1 q.2))
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => f t x • A t x) := by
  unfold Tensor0SFamilyContinuousOnSet at hA ⊢
  rw [continuous_iff_continuousAt] at hA ⊢
  intro q
  have hAq := hA q
  have hfq : ContinuousAt (fun q : {t : Real // t ∈ K} × M => f q.1.1 q.2) q :=
    hf.continuousAt
  rw [FiberBundle.continuousAt_totalSpace] at hAq ⊢
  refine ⟨hAq.1, ?_⟩
  simpa [map_smul] using hfq.smul hAq.2

/-- Pull time-dependent tensor continuity from the base product to the
time/tangent-bundle product by using the tangent bundle projection. -/
theorem tangentBundle
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel s Real E)
        (E := fun x : M => Tensor0SSpace s I x) q.2.proj
        (A q.1.1 q.2.proj)) := by
  unfold Tensor0SFamilyContinuousOnSet at hA
  let pull : {t : Real // t ∈ K} × TangentBundle I M -> {t : Real // t ∈ K} × M :=
    fun q => (q.1, q.2.proj)
  have hpull : Continuous pull := by
    dsimp [pull]
    exact continuous_fst.prodMk
      ((FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd)
  exact hA.comp hpull

/-- Evaluate a continuous time-dependent `(0,s)` tensor family on continuous
time and tangent-vector inputs.

This is the component-continuity projection used by local-coordinate
arguments: a jointly continuous tensor family has continuous scalar components
when tested against continuous vector fields. -/
theorem eval_continuous
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    {P : Type*} [TopologicalSpace P]
    {τ : P -> Real} {b : P -> M}
    (hτ : Continuous τ) (hτK : ∀ p : P, τ p ∈ K)
    (hb : Continuous b)
    {v : Fin s -> (p : P) -> TangentSpace I (b p)}
    (hv : ∀ i : Fin s, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p))) :
    Continuous (fun p : P => A (τ p) (b p) (fun i : Fin s => v i p)) := by
  let T : (p : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s (b p) :=
    fun p => A (τ p) (b p)
  have hT : Continuous (fun p : P =>
      TotalSpace.mk' (Tensor0SModel s Real E)
        (E := fun x : M => Tensor0SSpace s I x) (b p) (T p)) := by
    unfold Tensor0SFamilyContinuousOnSet at hA
    let pull : P -> {t : Real // t ∈ K} × M :=
      fun p => (⟨τ p, hτK p⟩, b p)
    have hpull : Continuous pull := by
      dsimp [pull]
      exact ((hτ.subtype_mk _).prodMk hb)
    simpa [T, pull] using hA.comp hpull
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := s)
    b hb T hT v hv
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply,
    T] using hEval

end Tensor0SFamilyContinuousOnSet

/-- Quadratic evaluation of a time-dependent `(0,2)` tensor family on the
tautological tangent vector is continuous on a time/tangent-bundle product. -/
theorem tensor0SFamily_quadCont
    {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      quad02 (I := I) (M := M) (A q.1.1 q.2.proj) q.2.2) := by
  let P := {t : Real // t ∈ K} × TangentBundle I M
  let b : P -> M := fun q => q.2.proj
  let T : (q : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => A q.1.1 (b q)
  let v : Fin 2 -> (q : P) -> TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [P, b, T] using
      Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M) hA
  have hv : ∀ i : Fin 2, Continuous (fun q : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [P, b, v] using (continuous_snd :
      Continuous (fun q : P => (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT v hv
  simpa [quad02, P, b, T, v] using hEval

/-- Time smoothness of metric coefficients over a concrete real interval,
together with joint total-space continuity of the metric tensor family. -/
structure MetricFamilySmoothOn
    (D : RealTimeInterval)
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop where
  coeff :
    forall (x : M) (X Y : TangentSpace I x),
    ContDiffOn Real ⊤ (fun t : Real => (G.metric t).inner x X Y) D.carrier
  metricTensor_cont :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => metricTensorField (I := I) (G.metric t) x)
  frameCompSmooth :
    forall {Idx : Type} [Fintype Idx]
      (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M},
      IsLocalFrameOn I E 1 frame u ->
      forall i j : Idx,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
          (fun p : Real × M =>
            (G.metric p.1).inner p.2 (frame i p.2) (frame j p.2))
          (D.carrier ×ˢ u)

/-- Extract a metric coefficient's interval time smoothness. -/
theorem metric_smooth_coeff_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (x : M) (X Y : TangentSpace I x) :
    ContDiffOn Real ⊤ (fun t : Real => (G.metric t).inner x X Y) D.carrier :=
  hG.coeff x X Y

/-- Extract the metric tensor total-space continuity from a smooth metric family. -/
theorem metricTensor_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => metricTensorField (I := I) (G.metric t) x) :=
  hG.metricTensor_cont

/-- Metric tensor continuity on a smaller time set. -/
theorem metricTensor_cont_restrict_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (hK : K ⊆ D.carrier) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (G.metric t) x) :=
  Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
    hG.metricTensor_cont hK

/-- Metric tensor continuity pulled back to the time/tangent-bundle product. -/
theorem metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        (metricTensorField (I := I) (G.metric q.1.1) q.2.proj)) :=
  Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (metricTensor_cont_restrict_of_metricFamilySmoothOn (I := I) (M := M)
      G hG hK)

/-- The scalar metric quadratic form on a time/tangent-bundle product is
continuous for any time set contained in the smooth metric-family interval. -/
theorem metricTimeBundleQuad_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (hK : K ⊆ D.carrier) :
    Continuous
      (metricTimeBundleQuad (I := I) (M := M) (fun t => G.metric t) K) := by
  have hquad :=
    tensor0SFamily_quadCont (I := I) (M := M)
      (metricTensor_cont_restrict_of_metricFamilySmoothOn (I := I) (M := M)
        G hG hK)
  simpa [metricTimeBundleQuad, quad02, metricTensorField_apply] using hquad

/-- The scalar metric coefficient used in interval derivative statements. -/
noncomputable def metricCoeff
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (x : M) (X Y : TangentSpace I x) : Real -> Real :=
  fun t => (G.metric t).inner x X Y

@[simp] theorem metricCoeff_eq
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (x : M) (X Y : TangentSpace I x) (t : Real) :
    metricCoeff G x X Y t = (G.metric t).inner x X Y := by
  rfl

end IntervalSmoothness

end Realized
end RicciFlower
