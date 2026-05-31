import RicciFlower.Realized.Curvature
import RicciFlower.Realized.TensorOperators
import RicciFlower.Tensor.RSTensor.MetricCompatibility
import RicciFlower.Tensor.RSTensor.QuadraticBounds
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.OneJet
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import RicciFlower.Tensor.RicciIdentity.Tensor0S.Realization
import RicciFlower.Operators.HessianTrace
import RicciFlower.Operators.LaplacianMinimum
import RicciFlower.Metric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.IntermediateValue


set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]


/-!
# TensorWeak Basic

Split-out component of `MaximumPrinciple.TensorWeak`.
-/

abbrev TwoTensorFamily : Type _ :=
  Real -> RawTwoTensorField (I := I) (M := M)

/-- A time-dependent vector field used for drift terms. -/
abbrev TimeDependentVectorField : Type _ :=
  Real -> (x : M) -> TangentSpace I x

/-- A time-dependent quadratic-form evaluation on tangent vectors. -/
abbrev TensorQuadraticFormFamily : Type _ :=
  Real -> (x : M) -> TangentSpace I x -> Real

/-- Supplied first covariant derivative tensors for a time-dependent two-tensor. -/
abbrev TensorNabla1Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x

/-- Supplied second covariant derivative tensors for a time-dependent two-tensor. -/
abbrev TensorNabla2Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

/-- A fiberwise algebraic reaction term for the tensor maximum principle. -/
abbrev TwoTensorReaction : Type _ :=
  Real -> SmoothRiemannianMetric I M -> RawTwoTensorField (I := I) (M := M) ->
    RawTwoTensorField (I := I) (M := M)

/-- Pointwise symmetry of a covariant two-tensor. -/
def TwoTensorSymmetricAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ X Y : TangentSpace I x, A x X Y = A x Y X

/-- Pointwise bilinearity of a raw covariant two-tensor evaluator. -/
structure TwoTensorBilinearAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) :
    Prop where
  add_left : ∀ X Y Z : TangentSpace I x,
    A x (X + Y) Z = A x X Z + A x Y Z
  smul_left : ∀ (c : Real) (X Z : TangentSpace I x),
    A x (c • X) Z = c * A x X Z
  add_right : ∀ X Y Z : TangentSpace I x,
    A x X (Y + Z) = A x X Y + A x X Z
  smul_right : ∀ (c : Real) (X Z : TangentSpace I x),
    A x X (c • Z) = c * A x X Z

/-- Pointwise nonnegativity of a covariant two-tensor as a quadratic form. -/
def TwoTensorNonnegativeAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, 0 ≤ A x v v

/-- Pointwise positive definiteness of a covariant two-tensor as a quadratic form. -/
def TwoTensorPositiveDefiniteAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, v ≠ 0 -> 0 < A x v v

/-- Symmetry of a tensor family on a set of times. -/
def TwoTensorFamilySymmetricOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorSymmetricAt (I := I) (M := M) (S t) x

/-- Nonnegativity of a tensor family on a set of times. -/
def TwoTensorFamilyNonnegativeOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

/-- Nonnegativity of a tensor family at one time. -/
def TwoTensorFamilyNonnegativeAtTime (S : TwoTensorFamily (I := I) (M := M))
    (t : Real) : Prop :=
  ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

/--
Hamilton's positive barrier
`S_epsilon = S + epsilon * (delta + t - t0) * g`.
-/
def tensorBarrierFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w

@[simp] theorem tensorBarrierFamily_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v w =
      S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w := by
  rfl

/-- A time-dependent smooth covariant two-tensor section. -/
abbrev TwoTensorSecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 2

/-- A time-dependent smooth covariant three-tensor section used as `∇S`. -/
abbrev TensorNabla1SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 3

/-- A time-dependent smooth covariant four-tensor section used as `∇²S`. -/
abbrev TensorNabla2SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 4

/-- Convert a section-backed two-tensor family to the pointwise quadratic-form
style used by the tensor WMP statement. -/
def twoTensorSecToFamily
    (S : TwoTensorSecFamily (I := I) (M := M)) :
    TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x (vec2 (I := I) v w)

@[simp]
theorem twoTensorSecToFamily_apply
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M) S t x v w =
      S t x (vec2 (I := I) v w) := by
  rfl

/-- A genuine two-tensor section gives a bilinear raw evaluator at every
point. -/
theorem twoTensorSecToFamily_bilin
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) :
    TwoTensorBilinearAt (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S t) x := by
  constructor
  · intro X Y Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
    have hmap := (S t x).map_update_add m (0 : Fin 2) X Y
    have hleft :
        Function.update m (0 : Fin 2) (X + Y) = vec2 (I := I) (X + Y) Z := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    have hX : Function.update m (0 : Fin 2) X = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    have hY : Function.update m (0 : Fin 2) Y = vec2 (I := I) Y Z := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hX, hY] using hmap
  · intro c X Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
    have hmap := (S t x).map_update_smul m (0 : Fin 2) c X
    have hleft :
        Function.update m (0 : Fin 2) (c • X) = vec2 (I := I) (c • X) Z := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    have hX : Function.update m (0 : Fin 2) X = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hX, smul_eq_mul] using hmap
  · intro X Y Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Y
    have hmap := (S t x).map_update_add m (1 : Fin 2) Y Z
    have hleft :
        Function.update m (1 : Fin 2) (Y + Z) = vec2 (I := I) X (Y + Z) := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    have hY : Function.update m (1 : Fin 2) Y = vec2 (I := I) X Y := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    have hZ : Function.update m (1 : Fin 2) Z = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hY, hZ] using hmap
  · intro c X Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
    have hmap := (S t x).map_update_smul m (1 : Fin 2) c Z
    have hleft :
        Function.update m (1 : Fin 2) (c • Z) = vec2 (I := I) X (c • Z) := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    have hZ : Function.update m (1 : Fin 2) Z = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hZ, smul_eq_mul] using hmap

/-- Section-backed positive barrier.  This is the smooth-section version of
`tensorBarrierFamily`; it is used only as a producer bridge for spatial
covariant derivative data. -/
noncomputable def tensorBarrierSecFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    S t + (epsilon * (delta + t - t0)) •
      Tensor0SBundle.metricTensorField (I := I) (G t)

@[simp]
theorem tensorBarrierSec_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        t x v w =
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v w := by
  simp only [twoTensorSecToFamily, tensorBarrierSecFamily, tensorBarrierFamily,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply]
  change
    (S t x (vec2 (I := I) v w) +
        (epsilon * (delta + t - t0)) *
          (Tensor0SBundle.metricTensorField (I := I) (G t) x)
            (vec2 (I := I) v w)) =
      S t x (vec2 (I := I) v w) +
        epsilon * (delta + t - t0) * (G t).inner x v w
  rw [Tensor0SBundle.metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold vec2 Curvature.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold vec2 Curvature.vec2
    norm_num
  rw [h0, h1]

theorem eval02_sec_eq
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v w : TangentSpace I x) :
    eval02 (I := I) (M := M) (S t x) v w =
      twoTensorSecToFamily (I := I) (M := M) S t x v w := by
  rfl

theorem quad02_sec_eq
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) (S t x) v =
      twoTensorSecToFamily (I := I) (M := M) S t x v v := by
  calc
    quad02 (I := I) (M := M) (S t x) v =
        eval02 (I := I) (M := M) (S t x) v v := by
          rw [eval02_self]
    _ = twoTensorSecToFamily (I := I) (M := M) S t x v v :=
          eval02_sec_eq (I := I) (M := M) S t x v v

/-- The positive metric barrier preserves pointwise symmetry. -/
theorem barrierSymmAt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t : Real} {x : M}
    (hS : TwoTensorSymmetricAt (I := I) (M := M) (S t) x) :
    TwoTensorSymmetricAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x := by
  intro v w
  simp [tensorBarrierFamily, hS v w, (G t).symm x v w]

/-- The metric inner product is bilinear as a raw two-tensor evaluator. -/
theorem metricInner_bilinAt
    (G : Real -> SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    TwoTensorBilinearAt (I := I) (M := M)
      (fun y v w => (G t).inner y v w) x := by
  constructor <;> intros <;> simp

/-- The positive metric barrier preserves pointwise bilinearity. -/
theorem barrierBilinearAt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t : Real} {x : M}
    (hS : TwoTensorBilinearAt (I := I) (M := M) (S t) x) :
    TwoTensorBilinearAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x := by
  constructor
  · intro X Y Z
    simp [tensorBarrierFamily, hS.add_left X Y Z, add_assoc]
    ring
  · intro c X Z
    simp [tensorBarrierFamily, hS.smul_left c X Z, mul_assoc, mul_left_comm]
    ring
  · intro X Y Z
    simp [tensorBarrierFamily, hS.add_right X Y Z, mul_add, add_assoc]
    ring
  · intro c X Z
    simp [tensorBarrierFamily, hS.smul_right c X Z, mul_assoc, mul_left_comm]
    ring

theorem vec2_self_eq_const {x : M} (v : TangentSpace I x) :
    vec2 (I := I) v v = fun _ : Fin 2 => v := by
  funext i
  fin_cases i <;> simp [vec2, Curvature.vec2]

/-- Section-backed barriers are quadratic in the repeated tangent vector. -/
theorem barrierSec_smul2
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (a : Real)
    (v : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        t x (a • v) (a • v) =
      a * a *
        twoTensorSecToFamily (I := I) (M := M)
          (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
          t x v v := by
  have hscale := tensor02_smul2 (I := I) (M := M)
    ((tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0) t x)
    a v
  simpa [quad02, twoTensorSecToFamily, vec2_self_eq_const] using hscale

/-- A section-backed raw barrier keeps the same quadratic scaling. -/
theorem barrierFamily_smul2
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (a : Real)
    (v : TangentSpace I x) :
    tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x (a • v) (a • v) =
      a * a *
        tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 t x v v := by
  rw [← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0 t x
      (a • v) (a • v),
    ← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0 t x v v]
  exact barrierSec_smul2 (I := I) (M := M) G S epsilon delta t0 t x a v

/-- A negative section-backed barrier value can be normalized to a metric-unit
tangent vector at the same time and base point. -/
theorem negBarrier_unit
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ u : TangentSpace I x,
      (G t).inner x u u = 1 ∧
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x u u < 0 := by
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0
  have hv : v ≠ 0 := by
    intro hv0
    have hzero : B t x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
      have hscale := barrierFamily_smul2 (I := I) (M := M)
        G S epsilon delta t0 t x 0 (0 : TangentSpace I x)
      simpa [B] using hscale
    have hnegB : B t x v v < 0 := by
      simpa [B] using hneg
    have hvzero : B t x v v = 0 := by
      simpa [hv0] using hzero
    rw [hvzero] at hnegB
    linarith
  let r : Real := (G t).inner x v v
  have hrpos : 0 < r := (G t).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have hunit : (G t).inner x u u = 1 := by
    have haa : a * a * r = 1 := by
      have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
        field_simp [hsne]
      calc
        a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
          rw [hss]
        _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
        _ = 1 := hmul
    calc
      (G t).inner x u u = a * a * r := by
        simpa [u, r] using metric_smul2 (I := I) (M := M) (G t) a v
      _ = 1 := haa
  have hcoeff_pos : 0 < a * a := mul_pos (inv_pos.mpr hspos) (inv_pos.mpr hspos)
  have hquad :
      B t x u u = a * a * B t x v v := by
    simpa [B, u, a] using
      barrierFamily_smul2 (I := I) (M := M) G S epsilon delta t0 t x a v
  refine ⟨u, hunit, ?_⟩
  change B t x u u < 0
  rw [hquad]
  have hnegB : B t x v v < 0 := by
    simpa [B] using hneg
  exact mul_neg_of_pos_of_neg hcoeff_pos hnegB

/-- The scalar barrier quadratic form on a metric unit-tangent time slab. -/
def barrierUnitQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 tA tB : Real)
    (p : MetricUnitTangentSlab (I := I) (M := M) G tA tB) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 p.1.1
    (MetricUnitTangent.base (I := I) (M := M) p.2)
    (MetricUnitTangent.vec (I := I) (M := M) p.2)
    (MetricUnitTangent.vec (I := I) (M := M) p.2)

@[simp]
theorem barrierUnitQuad_mk
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 tA tB t : Real) (ht : t ∈ Set.Icc tA tB)
    (x : M) (v : TangentSpace I x)
    (hunit : (G t).inner x v v = 1) :
    barrierUnitQuad (I := I) (M := M) G S epsilon delta t0 tA tB
      (⟨⟨t, ht⟩,
        (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
          MetricUnitTangent (I := I) (M := M) (G t))⟩ :
        MetricUnitTangentSlab (I := I) (M := M) G tA tB) =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v v := by
  rfl

/-- A negative section-backed barrier value gives a negative point on the
metric unit-tangent slab at the same time. -/
theorem negBarrier_unitSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 tA tB t : Real) (ht : t ∈ Set.Icc tA tB)
    (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ p : MetricUnitTangentSlab (I := I) (M := M) G tA tB,
      p.1.1 = t ∧
      barrierUnitQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 tA tB p < 0 := by
  obtain ⟨u, hunit, hneg_u⟩ :=
    negBarrier_unit (I := I) (M := M) G S epsilon delta t0 t x v hneg
  refine ⟨⟨⟨t, ht⟩,
      (⟨(⟨x, u⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) (G t))⟩, rfl, ?_⟩
  simpa using hneg_u

/-- Failure of nonnegativity for a section-backed barrier produces a negative
point on the metric unit-tangent time slab. -/
theorem failure_unitSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 tA tB : Real)
    (hfail :
      ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0)
        (Set.Icc tA tB)) :
    ∃ p : MetricUnitTangentSlab (I := I) (M := M) G tA tB,
      barrierUnitQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 tA tB p < 0 := by
  classical
  unfold TwoTensorFamilyNonnegativeOn TwoTensorNonnegativeAt at hfail
  push Not at hfail
  obtain ⟨t, ht, x, v, hneg⟩ := hfail
  obtain ⟨p, _hpt, hpneg⟩ :=
    negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0 tA tB
      t ht x v hneg
  exact ⟨p, hpneg⟩

private theorem metricUnitSlab_time_cont
    (G : Real -> SmoothRiemannianMetric I M) (tA tB : Real) :
    Continuous (fun p : MetricUnitTangentSlab (I := I) (M := M) G tA tB =>
      (p.1 : {t : Real // t ∈ Set.Icc tA tB})) := by
  change Continuous
    (fun p :
      (Σ t : {t : Real // t ∈ Set.Icc tA tB},
        MetricUnitTangent (I := I) (M := M) (G t.1)) => p.1)
  rw [continuous_def]
  intro s hs
  exact isOpen_sigma_fst_preimage s

theorem metricUnitSlab_timeVal_cont
    (G : Real -> SmoothRiemannianMetric I M) (tA tB : Real) :
    Continuous (fun p : MetricUnitTangentSlab (I := I) (M := M) G tA tB =>
      p.1.1) :=
  continuous_subtype_val.comp
    (metricUnitSlab_time_cont (I := I) (M := M) G tA tB)

/-- Metric quadratic evaluation on an ambient time/tangent-bundle product. -/
def metricBundleQuad
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  metricTimeBundleQuad (I := I) (M := M) G K q

/-- Section-backed two-tensor quadratic evaluation on an ambient
time/tangent-bundle product. -/
def tensorSecBundleQuad
    (S : TwoTensorSecFamily (I := I) (M := M)) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  S q.1.1 q.2.proj (fun _ : Fin 2 => q.2.2)

/-- Metric-family quadratic continuity from continuity of the corresponding
metric `(0,2)` tensor section over the time/tangent-bundle product. -/
theorem metricFamQuadCont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (hG :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (metricTensorField (I := I) (G q.1.1) q.2.proj))) :
    Continuous (metricBundleQuad (I := I) (M := M) G K) := by
  let P := {t : Real // t ∈ K} × TangentBundle I M
  let b : P -> M := fun q => q.2.proj
  let T : (q : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => metricTensorField (I := I) (G q.1.1) (b q)
  let v : Fin 2 -> (q : P) -> TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [P, b, T] using hG
  have hv : ∀ i : Fin 2, Continuous (fun q : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [P, b, v] using (continuous_snd :
      Continuous (fun q : P => (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT v hv
  simpa [metricBundleQuad, metricTimeBundleQuad, T, b, v,
    Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply,
    metricTensorField_apply, vec2_self_eq_const] using hEval

/-- Section-backed two-tensor quadratic continuity from continuity of the
two-tensor section over the time/tangent-bundle product. -/
theorem tensorQuadCont
    (S : TwoTensorSecFamily (I := I) (M := M)) (K : Set Real)
    (hS :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (S q.1.1 q.2.proj))) :
    Continuous (tensorSecBundleQuad (I := I) (M := M) S K) := by
  let P := {t : Real // t ∈ K} × TangentBundle I M
  let b : P -> M := fun q => q.2.proj
  let T : (q : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => S q.1.1 (b q)
  let v : Fin 2 -> (q : P) -> TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [P, b, T] using hS
  have hv : ∀ i : Fin 2, Continuous (fun q : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [P, b, v] using (continuous_snd :
      Continuous (fun q : P => (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT v hv
  simpa [tensorSecBundleQuad, T, b, v, vec2_self_eq_const,
    Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

/-- Raw barrier quadratic evaluation on an ambient time/tangent-bundle product. -/
def barrierBundleQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
    q.1.1 q.2.proj q.2.2 q.2.2

/-- The section-backed ambient barrier quadratic form is continuous if the
metric and two-tensor quadratic evaluations are continuous. -/
theorem barrierBundleCont
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (hS : Continuous (tensorSecBundleQuad (I := I) (M := M) S K))
    (hG : Continuous (metricBundleQuad (I := I) (M := M) G K)) :
    Continuous (barrierBundleQuad (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 K) := by
  have htime :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        (q.1.1 : Real)) :=
    continuous_subtype_val.comp continuous_fst
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        epsilon * (delta + q.1.1 - t0)) := by
    exact continuous_const.mul ((continuous_const.add htime).sub continuous_const)
  have hmain :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        tensorSecBundleQuad (I := I) (M := M) S K q +
          (epsilon * (delta + q.1.1 - t0)) *
            metricBundleQuad (I := I) (M := M) G K q) :=
    hS.add (hcoef.mul hG)
  refine hmain.congr ?_
  intro q
  simp [barrierBundleQuad, tensorSecBundleQuad, metricBundleQuad,
    metricTimeBundleQuad, tensorBarrierFamily, twoTensorSecToFamily,
    vec2_self_eq_const, mul_assoc]

/-- The scalar barrier quadratic form on the geometric metric unit-tangent
time slab. -/
def barrierTimeSlabQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (p : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
    (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.base (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)

theorem barrierTimeSlabQuad_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (p : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    barrierTimeSlabQuad (I := I) (M := M) G S epsilon delta t0 K p =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
        (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.base (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p) :=
  rfl

@[simp]
theorem barrierTimeSlabQuad_mk
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (K : Set Real) (ht : t ∈ K)
    (x : M) (v : TangentSpace I x)
    (hunit : (G t).inner x v v = 1) :
    barrierTimeSlabQuad (I := I) (M := M) G S epsilon delta t0 K
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v v := by
  rfl

/-- The geometric time-slab barrier quadratic form is continuous if the
ambient metric and section-backed tensor quadratic evaluations are continuous. -/
theorem barrierTimeCont
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (hS : Continuous (tensorSecBundleQuad (I := I) (M := M) S K))
    (hG : Continuous (metricBundleQuad (I := I) (M := M) G K)) :
    Continuous
      (barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 K) := by
  have hbundle := barrierBundleCont (I := I) (M := M)
    G S epsilon delta t0 K hS hG
  have hsub :
      Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        (p.1 : {t : Real // t ∈ K} × TangentBundle I M)) :=
    continuous_subtype_val
  simpa [barrierTimeSlabQuad, barrierBundleQuad,
    MetricUnitTangentTimeSlab.time, MetricUnitTangentTimeSlab.base,
    MetricUnitTangentTimeSlab.vec, MetricUnitTangentTimeSlab.bundlePoint]
    using hbundle.comp hsub

/-- A negative section-backed barrier value gives a negative point on the
geometric metric unit-tangent time slab at the same time. -/
theorem negBarrier_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) {K : Set Real} (ht : t ∈ K)
    (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ p : MetricUnitTangentTimeSlab (I := I) (M := M) G K,
      MetricUnitTangentTimeSlab.time (I := I) (M := M) p = t ∧
      barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 K p < 0 := by
  obtain ⟨u, hunit, hneg_u⟩ :=
    negBarrier_unit (I := I) (M := M) G S epsilon delta t0 t x v hneg
  refine ⟨⟨(⟨t, ht⟩, (⟨x, u⟩ : TangentBundle I M)), hunit⟩, rfl, ?_⟩
  simpa using hneg_u

/-- Failure of nonnegativity for a section-backed barrier produces a negative
point on the geometric metric unit-tangent time slab. -/
theorem failure_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) {K : Set Real}
    (hfail :
      ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0) K) :
    ∃ p : MetricUnitTangentTimeSlab (I := I) (M := M) G K,
      barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 K p < 0 := by
  classical
  unfold TwoTensorFamilyNonnegativeOn TwoTensorNonnegativeAt at hfail
  push Not at hfail
  obtain ⟨t, ht, x, v, hneg⟩ := hfail
  obtain ⟨p, _hpt, hpneg⟩ :=
    negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 t ht x v hneg
  exact ⟨p, hpneg⟩

theorem metricUnitTimeSlab_timeVal_cont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) :
    Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
      MetricUnitTangentTimeSlab.time (I := I) (M := M) p) := by
  have htime :
      Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        (p.1.1 : {t : Real // t ∈ K})) :=
    continuous_fst.comp continuous_subtype_val
  exact continuous_subtype_val.comp htime

theorem exists_left_neg_of_continuousOn
    {f : Real -> Real} {a b c : Real}
    (hab : a < b) (hbc : b ≤ c)
    (hcont : ContinuousOn f (Set.Icc a c)) (hneg : f b < 0) :
    ∃ s : Real, s ∈ Set.Icc a c ∧ s < b ∧ f s < 0 := by
  have hbmem : b ∈ Set.Icc a c := ⟨le_of_lt hab, hbc⟩
  have hpre :
      {s : Real | f s < 0} ∈ nhdsWithin b (Set.Icc a c) :=
    (hcont.continuousWithinAt hbmem).preimage_mem_nhdsWithin
      (isOpen_Iio.mem_nhds hneg)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with
    ⟨u, hu_nhds, hu_subset⟩
  rcases exists_Ioc_subset_of_mem_nhds' hu_nhds hab with
    ⟨l, hlb, hlu⟩
  let s : Real := (max a l + b) / 2
  have hmax_lt : max a l < b := max_lt hab hlb.2
  have hmax_lt_s : max a l < s := by
    dsimp [s]
    linarith
  have hmax_le_s : max a l ≤ s := le_of_lt hmax_lt_s
  have hs_lt : s < b := by
    dsimp [s]
    linarith
  have ha_le_s : a ≤ s := le_trans (le_max_left a l) hmax_le_s
  have hl_lt_s : l < s := lt_of_le_of_lt (le_max_right a l) hmax_lt_s
  have hs_mem_u : s ∈ u := hlu ⟨hl_lt_s, le_of_lt hs_lt⟩
  have hs_mem_Icc : s ∈ Set.Icc a c := ⟨ha_le_s, le_trans (le_of_lt hs_lt) hbc⟩
  exact ⟨s, hs_mem_Icc, hs_lt, hu_subset ⟨hs_mem_u, hs_mem_Icc⟩⟩

end

end Realized
end RicciFlower
